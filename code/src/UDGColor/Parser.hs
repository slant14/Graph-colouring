-- | A Parsec front end for the surface language. Turns source text into the
-- 'Program' AST of "UDGColor.Ast". The grammar follows @main.tex@, Section
-- "Concrete grammar", and is Haskell-flavored: top-level bindings carry optional
-- @name :: Type@ signatures, and a definition may be written either with an
-- explicit leading keyword (@graph g = ...@) or in the signature-driven form
-- @g = graph { ... }@ where the right-hand side's head keyword fixes the kind.
--
-- We use @parsec@ (not @megaparsec@) so the harness builds against the packages
-- already present in the environment.
module UDGColor.Parser
  ( parseProgram
  , parseProgramFile
  ) where

import           Text.Parsec
import           Text.Parsec.Language (emptyDef)
import           Text.Parsec.String  (Parser)
import qualified Text.Parsec.Token   as T

import           UDGColor.Ast

-- ── Lexer ────────────────────────────────────────────────────────────────────

langDef :: T.LanguageDef st
langDef = emptyDef
  { T.commentLine     = "--"
  , T.identStart      = letter
  , T.identLetter     = alphaNum <|> oneOf "_'"
  , T.reservedOpNames = ["=", "::", "~>", ">>>", "!", ":", "->"]
  , T.caseSensitive   = True
  , T.reservedNames   =
      [ "graph", "palette", "colors", "size", "udg", "radius", "vertices"
      , "edges", "restrictions", "transform", "instance", "compute", "color"
      , "using", "subjectTo", "via", "apply", "to", "chromaticNumber"
      , "toUDG", "exact", "preserve", "compose", "encodeColoring", "superUDG"
      , "colorChoice", "gadgetize", "layout", "emit"
      , "precolor", "allow", "forbid", "sameColor", "differentColor"
      , "useAtMost", "useExactly", "distinctOn", "keep", "drop", "trackOrigin"
      , "kColorable", "chromatic", "bipartite", "true", "false"
      , "safe", "asafe"
      , "Coloring", "IS", "WIS", "UDG", "Dev"
      , "Graph", "Palette", "Restrictions", "Instance", "Result", "Int"
      ]
  }

lexer :: T.TokenParser st
lexer = T.makeTokenParser langDef

reserved :: String -> Parser ()
reserved = T.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = T.reservedOp lexer

identifier :: Parser String
identifier = T.identifier lexer

stringLit :: Parser String
stringLit = T.stringLiteral lexer

natural :: Parser Int
natural = fromIntegral <$> T.natural lexer

symbol :: String -> Parser String
symbol = T.symbol lexer

parens :: Parser a -> Parser a
parens = T.parens lexer

brackets :: Parser a -> Parser a
brackets = T.brackets lexer

braces :: Parser a -> Parser a
braces = T.braces lexer

commaSep :: Parser a -> Parser [a]
commaSep = T.commaSep lexer

whiteSpace :: Parser ()
whiteSpace = T.whiteSpace lexer

-- | A floating- or integer-valued literal, used for radii.
realLit :: Parser Double
realLit = either fromIntegral id <$> T.naturalOrFloat lexer

-- ── Leaf categories ──────────────────────────────────────────────────────────

vertex :: Parser Vertex
vertex = identifier <|> (show <$> natural) <?> "vertex"

colorTok :: Parser Color
colorTok = identifier <|> stringLit <?> "color"

edgeP :: Parser Edge
edgeP = parens ((,) <$> (vertex <* symbol ",") <*> vertex)

-- ── Graph / palette / restriction expressions ────────────────────────────────

graphExpr :: Parser GraphExpr
graphExpr =
      graphLit
  <|> udgLit
  <|> applyT
  <?> "graph expression"
  where
    graphLit = do
      reserved "graph"
      braces $ do
        reserved "vertices"; reservedOp "="
        vs <- brackets (commaSep vertex)
        _  <- symbol ","
        reserved "edges"; reservedOp "="
        es <- brackets (commaSep edgeP)
        pure (GraphLit vs es)
    udgLit = do
      reserved "udg"
      braces $ do
        reserved "radius"; reservedOp "="
        r <- realLit
        _ <- symbol ","
        reserved "edges"; reservedOp "="
        es <- brackets (commaSep edgeP)
        pure (UdgLit r es)
    applyT = do
      reserved "apply"
      t <- identifier
      reserved "to"
      g <- identifier
      pure (ApplyTransform t g)

paletteExpr :: Parser PaletteExpr
paletteExpr =
      (reserved "colors" >> ExplicitPalette <$> brackets (commaSep colorTok))
  <|> (reserved "size"   >> PaletteSize <$> natural)
  <?> "palette expression"

restrictionList :: Parser [Restriction]
restrictionList = braces (semiSepEnd restriction)
  where
    -- restrictions are ';'-separated; allow a trailing ';'
    semiSepEnd p = sepEndBy p (symbol ";")

restriction :: Parser Restriction
restriction =
      (reserved "precolor"        >> Precolor <$> vertex <*> (reservedOp ":" >> colorTok))
  <|> (reserved "allow"           >> Allow <$> vertex <*> (reservedOp ":" >> brackets (commaSep colorTok)))
  <|> (reserved "forbid"          >> Forbid <$> vertex <*> (reservedOp ":" >> brackets (commaSep colorTok)))
  <|> (reserved "sameColor"       >> parens (SameColor <$> (vertex <* symbol ",") <*> vertex))
  <|> (reserved "differentColor"  >> parens (DifferentColor <$> (vertex <* symbol ",") <*> vertex))
  <|> (reserved "useAtMost"       >> UseAtMost <$> natural)
  <|> (reserved "useExactly"      >> UseExactly <$> natural)
  <|> (reserved "distinctOn"      >> DistinctOn <$> brackets (commaSep vertex))
  <?> "restriction"

-- ── Transform expressions (with the >>> pipeline operator) ───────────────────

transformExpr :: Parser TransformExpr
transformExpr = chainl1 transformAtom (reservedOp ">>>" >> pure Pipe)

transformAtom :: Parser TransformExpr
transformAtom =
      (reserved "colorChoice"    >> ColorChoice <$> natural)
  <|> (reserved "gadgetize"      >> pure Gadgetize)
  <|> (reserved "layout"         >> LayoutT <$> optionMaybe identifier)
  <|> (reserved "emit"           >> pure EmitT)
  <|> (reserved "encodeColoring" >> EncodeColoring <$> natural)
  <|> (reserved "superUDG"       >> pure SuperUDG)
  <|> (reserved "compose"        >> Compose <$> brackets (commaSep identifier))
  <|> toUDGExpr
  <|> (TRef <$> identifier)
  <?> "transform"

toUDGExpr :: Parser TransformExpr
toUDGExpr = do
  reserved "toUDG"
  parens $ do
    m    <- transformMode
    opts <- many (symbol "," >> transformOption)
    pure (ToUDG m opts)

transformMode :: Parser TransformMode
transformMode =
      (reserved "exact" >> pure Exact)
  <|> (reserved "preserve" >> Preserve <$> property)
  <?> "transform mode"

property :: Parser Property
property =
      (reserved "kColorable" >> KColorable <$> (parens natural <|> natural))
  <|> (reserved "chromatic"  >> pure Chromatic)
  <|> (reserved "bipartite"  >> pure Bipartite)
  <?> "property"

transformOption :: Parser TransformOption
transformOption =
      (reserved "radius"      >> reservedOp "=" >> RadiusOpt <$> realLit)
  <|> (reserved "keep"        >> reservedOp "=" >> KeepVertices <$> brackets (commaSep vertex))
  <|> (reserved "drop"        >> reservedOp "=" >> DropVertices <$> brackets (commaSep vertex))
  <|> (reserved "trackOrigin" >> reservedOp "=" >> TrackOrigin <$> boolLit)
  <?> "transform option"

boolLit :: Parser Bool
boolLit = (reserved "true" >> pure True) <|> (reserved "false" >> pure False)

-- ── Instance / query ─────────────────────────────────────────────────────────

instanceExpr :: Parser InstanceExpr
instanceExpr = do
  reserved "color"
  g  <- identifier
  mp <- optionMaybe (reserved "using"     >> identifier)
  mr <- optionMaybe (reserved "subjectTo" >> identifier)
  mt <- optionMaybe (reserved "via"       >> identifier)
  pure (InstanceExpr g mp mr mt)

queryExpr :: Parser QueryExpr
queryExpr = reserved "chromaticNumber" >> ChromaticNumber <$> parens identifier

-- ── Types (signatures) ───────────────────────────────────────────────────────

tyP :: Parser Ty
tyP = do
  a <- tyAtomOrProblem
  choice
    [ reservedOp "~>" >> reduceTail a
    , reservedOp "->" >> (TyFun (problemToTy a) <$> tyP)
    , pure (problemToTy a)
    ]
  where
    reduceTail (Left p1) = do
      p2  <- problemP
      eff <- option Safe (reservedOp "!" >> effectP)
      pure (TyReduce p1 p2 eff)
    reduceTail (Right _) = fail "expected a problem-type on the left of ~>"

-- | Either a base type (Right Ty) or a problem-type (Left Problem).
tyAtomOrProblem :: Parser (Either Problem Ty)
tyAtomOrProblem =
      (Left <$> problemP)
  <|> (Right <$> baseTy)

problemToTy :: Either Problem Ty -> Ty
problemToTy (Right t) = t
problemToTy (Left _)  = TyResult  -- a bare problem-type in value position is unusual; treat as opaque

baseTy :: Parser Ty
baseTy =
      (reserved "Graph"        >> pure TyGraph)
  <|> (reserved "Palette"      >> pure TyPalette)
  <|> (reserved "Restrictions" >> pure TyRestrictions)
  <|> (reserved "Instance"     >> pure TyInstance)
  <|> (reserved "Result"       >> pure TyResult)
  <|> (reserved "Int"          >> pure TyInt)
  <?> "type"

problemP :: Parser Problem
problemP =
      (reserved "Coloring" >> PCol <$> optIdx <*> optIdx)
  <|> (reserved "IS"       >> PIS  <$> optIdx)
  <|> (reserved "WIS"      >> PWIS <$> optIdx <*> optIdx)
  <|> (reserved "UDG"      >> PUDG <$> optIdx <* skipMany realLit)
  <|> (reserved "Dev"      >> PDev <$> optIdx)
  <?> "problem-type"
  where
    optIdx = optionMaybe natural

effectP :: Parser Effect
effectP =
      (reserved "safe"  >> pure Safe)
  <|> (reserved "asafe" >> ASafe <$> natural)
  <?> "effect"

-- ── Bindings and the program ─────────────────────────────────────────────────

-- We parse a flat list of items (signatures and definitions), then attach each
-- signature to the next definition that shares its name.
data Item = ISig Name Ty | IDef Definition

itemP :: Parser Item
itemP =
      try sigP
  <|> (IDef <$> definitionP)
  where
    sigP = do
      n <- identifier
      reservedOp "::"
      t <- tyP
      pure (ISig n t)

definitionP :: Parser Definition
definitionP =
      try keywordDef
  <|> nameEqDef
  <?> "definition"

-- | Explicit keyword form: @graph g = ...@, @transform t = ...@, etc.
keywordDef :: Parser Definition
keywordDef = choice
  [ kw "graph"        (\n -> DGraph n        <$> graphExpr)        -- graph g = graph { .. }
  , kw "palette"      (\n -> DPalette n      <$> paletteExpr)
  , kw "restrictions" (\n -> DRestrictions n <$> restrictionList)
  , kw "transform"    (\n -> DTransform n    <$> transformExpr)
  , kw "instance"     (\n -> DInstance n     <$> instanceExpr)
  , kw "compute"      (\n -> DQuery n        <$> queryExpr)
  ]
  where
    kw w mk = try $ do
      reserved w
      n <- identifier
      reservedOp "="
      mk n

-- | Signature-driven form: @n = rhs@, classified by the head of @rhs@.
nameEqDef :: Parser Definition
nameEqDef = do
  n <- identifier
  reservedOp "="
  classifyRhs n

classifyRhs :: Name -> Parser Definition
classifyRhs n =
      (DGraph n        <$> graphExpr)      -- graph / udg / apply
  <|> (DPalette n      <$> paletteExpr)    -- colors / size
  <|> (DRestrictions n <$> restrictionList) -- { ... }
  <|> (DInstance n     <$> instanceExpr)   -- color ...
  <|> (DQuery n        <$> queryExpr)      -- chromaticNumber ( .. )
  <|> (DTransform n    <$> transformExpr)  -- colorChoice / gadgetize / >>> / ... / ref
  <?> "definition body"

programP :: Parser Program
programP = do
  whiteSpace
  items <- many itemP
  eof
  pure (attach items)

-- | Attach each signature to the following definition with the same name.
attach :: [Item] -> Program
attach = Program . go []
  where
    go _    []                 = []
    go sigs (ISig n t : rest)  = go ((n, t) : sigs) rest
    go sigs (IDef d   : rest)  =
      let nm  = defName d
          sig = lookup nm sigs
      in Binding sig d : go (filter ((/= nm) . fst) sigs) rest

-- ── Entry points ─────────────────────────────────────────────────────────────

parseProgram :: FilePath -> String -> Either ParseError Program
parseProgram = runParser programP ()

parseProgramFile :: FilePath -> IO (Either ParseError Program)
parseProgramFile fp = parseProgram fp <$> readFile fp
