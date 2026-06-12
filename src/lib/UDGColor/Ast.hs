-- | Abstract syntax for the surface language (paper @main.tex@, Section "A
-- Language for Certified Coloring Compilation"). This mirrors the Haskell AST
-- given there: ordinary domain declarations (@graph@\/@palette@\/@restrictions@\/
-- @transform@\/@instance@\/@compute@) plus the /problem-types/ and the
-- certified-reduction arrow @~>@ that the type checker ("UDGColor.TypeCheck")
-- works over.
module UDGColor.Ast
  ( Name
  , Vertex
  , Color
  , Edge
  , Program(..)
  , Binding(..)
  , Definition(..)
  , defName
  , GraphExpr(..)
  , PaletteExpr(..)
  , Restriction(..)
  , TransformExpr(..)
  , TransformMode(..)
  , Property(..)
  , TransformOption(..)
  , InstanceExpr(..)
  , QueryExpr(..)
    -- * Types and problem-types
  , Ty(..)
  , Problem(..)
  , Effect(..)
  , Sort(..)
  , problemSort
  , ppTy
  , ppProblem
  , ppEffect
  , ppSort
  ) where

type Name   = String
type Vertex = String
type Color  = String
type Edge   = (Vertex, Vertex)

-- | A whole program: a sequence of typed top-level bindings.
newtype Program = Program [Binding] deriving (Eq, Show)

-- | A binding is an optional signature attached to a definition.
data Binding = Binding
  { bSig :: Maybe Ty
  , bDef :: Definition
  } deriving (Eq, Show)

data Definition
  = DGraph        Name GraphExpr
  | DPalette      Name PaletteExpr
  | DRestrictions Name [Restriction]
  | DTransform    Name TransformExpr
  | DInstance     Name InstanceExpr
  | DQuery        Name QueryExpr
  deriving (Eq, Show)

-- | The name a definition binds.
defName :: Definition -> Name
defName (DGraph n _)        = n
defName (DPalette n _)      = n
defName (DRestrictions n _) = n
defName (DTransform n _)    = n
defName (DInstance n _)     = n
defName (DQuery n _)        = n

data GraphExpr
  = GraphLit [Vertex] [Edge]    -- ^ @graph { vertices = [..], edges = [..] }@
  | UdgLit Double [Edge]        -- ^ @udg { radius = r, edges = [..] }@
  | ApplyTransform Name Name    -- ^ @apply T to G@
  deriving (Eq, Show)

data PaletteExpr
  = ExplicitPalette [Color]     -- ^ @colors [..]@
  | PaletteSize Int             -- ^ @size n@
  deriving (Eq, Show)

data Restriction
  = Precolor Vertex Color
  | Allow Vertex [Color]
  | Forbid Vertex [Color]
  | SameColor Vertex Vertex
  | DifferentColor Vertex Vertex
  | UseAtMost Int
  | UseExactly Int
  | DistinctOn [Vertex]
  deriving (Eq, Show)

data TransformExpr
  = ToUDG TransformMode [TransformOption]
  | EncodeColoring Int                  -- ^ exact gadget encoding (Col ~> WIS)
  | SuperUDG                            -- ^ same-vertex supergraph (carries a safety effect)
  | ColorChoice Int                     -- ^ Stage 1  (Col ~> IS)
  | Gadgetize                           -- ^ Stage 2  (IS ~> WIS)
  | LayoutT (Maybe Name)                -- ^ Stage 3  (WIS ~> UDG)
  | EmitT                               -- ^ device budget  (UDG ~> Dev)
  | Pipe TransformExpr TransformExpr    -- ^ @f >>> g@
  | Compose [Name]                      -- ^ @compose [t1, t2, ...]@
  | TRef Name                           -- ^ reference to a named transform
  deriving (Eq, Show)

data TransformMode = Exact | Preserve Property deriving (Eq, Show)

data Property = KColorable Int | Chromatic | Bipartite deriving (Eq, Show)

data TransformOption
  = RadiusOpt Double
  | KeepVertices [Vertex]
  | DropVertices [Vertex]
  | TrackOrigin Bool
  deriving (Eq, Show)

data InstanceExpr = InstanceExpr
  { instGraph        :: Name
  , instPalette      :: Maybe Name
  , instRestrictions :: Maybe Name
  , instTransform    :: Maybe Name
  } deriving (Eq, Show)

newtype QueryExpr = ChromaticNumber Name deriving (Eq, Show)

-- ── Types and problem-types ──────────────────────────────────────────────────

-- | Surface types. Besides the ordinary base types, a transform's type is a
-- certified reduction @A ~> B ! e@ between two 'Problem'-types carrying an
-- 'Effect'.
data Ty
  = TyGraph
  | TyPalette
  | TyRestrictions
  | TyInstance
  | TyResult
  | TyInt
  | TyReduce Problem Problem Effect
  | TyFun Ty Ty
  deriving (Eq, Show)

-- | The /problem-types/ (the sorts of §"The Type System"). Indices are optional
-- so that the same syntax serves both signatures (often concrete) and inferred
-- transform schemas (often symbolic).
data Problem
  = PCol (Maybe Int) (Maybe Int)   -- ^ @Coloring n k@
  | PIS  (Maybe Int)               -- ^ @IS N@
  | PWIS (Maybe Int) (Maybe Int)   -- ^ @WIS N C@
  | PUDG (Maybe Int)               -- ^ @UDG N (r d)@
  | PDev (Maybe Int)               -- ^ @Dev N@
  deriving (Eq, Show)

-- | Safety effect (the type-and-effect annotation of §"Refinement B").
data Effect = Safe | ASafe Int deriving (Eq, Show)

-- | The bare sort of a problem-type, ignoring indices. Composition adjacency is
-- checked at this granularity.
data Sort = SCol | SIS | SWIS | SUDG | SUDGa | SDev deriving (Eq, Show)

problemSort :: Problem -> Sort
problemSort PCol{} = SCol
problemSort PIS{}  = SIS
problemSort PWIS{} = SWIS
problemSort PUDG{} = SUDG
problemSort PDev{} = SDev

-- ── Pretty printers (for the driver / diagnostics) ───────────────────────────

ppSort :: Sort -> String
ppSort SCol  = "Col"
ppSort SIS   = "IS"
ppSort SWIS  = "WIS"
ppSort SUDG  = "UDG"
ppSort SUDGa = "UDG~"
ppSort SDev  = "Dev"

ppEffect :: Effect -> String
ppEffect Safe      = "safe"
ppEffect (ASafe c) = "asafe " ++ show c

ppProblem :: Problem -> String
ppProblem (PCol n k) = "Coloring" ++ idx n ++ idx k
ppProblem (PIS n)    = "IS" ++ idx n
ppProblem (PWIS n c) = "WIS" ++ idx n ++ idx c
ppProblem (PUDG n)   = "UDG" ++ idx n
ppProblem (PDev n)   = "Dev" ++ idx n

idx :: Maybe Int -> String
idx Nothing  = " _"
idx (Just i) = " " ++ show i

ppTy :: Ty -> String
ppTy TyGraph        = "Graph"
ppTy TyPalette      = "Palette"
ppTy TyRestrictions = "Restrictions"
ppTy TyInstance     = "Instance"
ppTy TyResult       = "Result"
ppTy TyInt          = "Int"
ppTy (TyFun a b)    = ppTy a ++ " -> " ++ ppTy b
ppTy (TyReduce a b e) =
  ppProblem a ++ " ~> " ++ ppProblem b ++ effSuffix e
  where
    effSuffix Safe = ""
    effSuffix ef   = " ! " ++ ppEffect ef
