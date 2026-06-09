-- | The certified-reduction type checker (paper @main.tex@, Section "The Type
-- System"; error catalogue @errors.tex@). It runs two layers over a parsed
-- 'Program':
--
--   * a /static decidable layer/ — kinds, scoping, vertices-in-graph,
--     colors-in-palette, palette-size, keep\/drop disjointness, exact-mode
--     elimination, and signature agreement (the @errors.tex@ catalogue); and
--   * a /certified-reduction layer/ — every transform is typed as an
--     answer-preserving morphism @A ~> B ! e@ between problem-types, composition
--     checks stage-ordering, @emit@ enforces the device budget @N <= Nmax@, and
--     same-vertex (supergraph) transforms carry a safety effect gated by the
--     impossibility side-condition @sigma(G) <= 5@.
--
-- Everything here is /before/ the simulation: it decides whether a program
-- denotes a faithful pipeline, and the companion "UDGColor.Elaborate" then
-- builds the (un-simulated) device instance.
module UDGColor.TypeCheck
  ( -- * Diagnostics
    Severity(..)
  , Diag(..)
  , ppDiag
    -- * Entities and reduction-types
  , Entity(..)
  , RType(..)
  , rtypeToTy
    -- * Checking
  , Env
  , CheckResult(..)
  , checkProgram
  , defaultNmax
    -- * Reusable analyses
  , buildGraph
  , sigmaG
  , estimateAtoms
  ) where

import           Data.List   (intercalate)
import           Data.Map    (Map)
import qualified Data.Map    as Map
import qualified Data.Set    as Set

import           UDGColor.Ast
import qualified UDGColor.Graph  as G
import qualified UDGColor.Oracle as O

-- ── Diagnostics ──────────────────────────────────────────────────────────────

data Severity = Err | Warn deriving (Eq, Show)

-- | A diagnostic: severity, the binding it concerns, a message, and an optional
-- @errors.tex@ catalogue number.
data Diag = Diag
  { dSev  :: Severity
  , dName :: Name
  , dMsg  :: String
  , dCode :: Maybe Int
  } deriving (Eq, Show)

ppDiag :: Diag -> String
ppDiag (Diag sev nm msg code) =
  sev' ++ " [" ++ nm ++ "]" ++ code' ++ ": " ++ msg
  where
    sev'  = case sev of Err -> "error"; Warn -> "warning"
    code' = maybe "" (\c -> " (errors.tex #" ++ show c ++ ")") code

err :: Name -> Maybe Int -> String -> Diag
err nm code msg = Diag Err nm msg code

warn :: Name -> String -> Diag
warn nm msg = Diag Warn nm msg Nothing

-- ── Entities and reduction-types ─────────────────────────────────────────────

-- | The reduction-type of a transform: source sort, target sort, safety effect.
data RType = RType
  { rSrc :: Sort
  , rTgt :: Sort
  , rEff :: Effect
  } deriving (Eq, Show)

rtypeToTy :: RType -> Ty
rtypeToTy (RType s t e) = TyReduce (sortProblem s) (sortProblem t) e

sortProblem :: Sort -> Problem
sortProblem SCol  = PCol Nothing Nothing
sortProblem SIS   = PIS Nothing
sortProblem SWIS  = PWIS Nothing Nothing
sortProblem SUDG  = PUDG Nothing
sortProblem SUDGa = PUDG Nothing
sortProblem SDev  = PDev Nothing

-- | What a top-level name denotes once checked.
data Entity
  = EGraph (G.Graph String)
  | EPalette [Color] (Maybe Int)   -- ^ explicit colors (possibly empty) and\/or a size
  | ERestr [Restriction]
  | ETransform RType (Maybe Int)   -- ^ reduction-type and the pipeline's palette @k@, if fixed
  | EInstance
  | EQueryInt
  deriving (Show)

entityTy :: Entity -> Ty
entityTy EGraph{}          = TyGraph
entityTy EPalette{}        = TyPalette
entityTy ERestr{}          = TyRestrictions
entityTy (ETransform rt _) = rtypeToTy rt
entityTy EInstance         = TyResult   -- an `instance` denotes a solve = a Result
entityTy EQueryInt         = TyInt

-- ── Environment and result ───────────────────────────────────────────────────

type Env = Map Name Entity

data CheckResult = CheckResult
  { crDiags :: [Diag]              -- ^ all diagnostics, in source order
  , crEnv   :: Env                 -- ^ resolved entities (best-effort, even on error)
  , crTypes :: [(Name, Ty)]        -- ^ inferred type per binding, in source order
  } deriving (Show)

-- | QuEra Aquila-class capacity used for the device-budget premise of @emit@.
defaultNmax :: Int
defaultNmax = 256

-- ── Top-level driver ─────────────────────────────────────────────────────────

checkProgram :: Program -> CheckResult
checkProgram (Program bs) = finalize (foldl' step (Acc Map.empty [] []) bs)
  where
    finalize (Acc env ds tys) =
      CheckResult { crDiags = reverse ds, crEnv = env, crTypes = reverse tys }

data Acc = Acc Env [Diag] [(Name, Ty)]

step :: Acc -> Binding -> Acc
step (Acc env ds tys) (Binding msig def) =
  let nm                = defName def
      dup               = [ err nm Nothing "duplicate top-level binding"
                          | Map.member nm env ]
      (ent, ds1)        = inferDef env nm def
      ds2               = sigDiags nm msig (entityTy ent)
      env'              = Map.insert nm ent env
  in Acc env' (reverse (dup ++ ds1 ++ ds2) ++ ds) ((nm, entityTy ent) : tys)

-- ── Signature agreement ──────────────────────────────────────────────────────

sigDiags :: Name -> Maybe Ty -> Ty -> [Diag]
sigDiags _  Nothing    _   = []
sigDiags nm (Just dec) inf
  | tyCompatible dec inf = []
  | otherwise =
      [ err nm Nothing $
          "signature " ++ ppTy dec ++ " does not match inferred type "
            ++ ppTy inf ]

-- | Signature/inferred compatibility: base types must be equal; reductions are
-- compared at the sort + effect level (indices are documentary).
tyCompatible :: Ty -> Ty -> Bool
tyCompatible (TyReduce a b e) (TyReduce a' b' e') =
  problemSort a == problemSort a' && problemSort b == problemSort b' && e == e'
tyCompatible (TyFun a b) (TyFun a' b') = tyCompatible a a' && tyCompatible b b'
tyCompatible a b = a == b

-- ── Per-definition inference ─────────────────────────────────────────────────

inferDef :: Env -> Name -> Definition -> (Entity, [Diag])

inferDef env nm (DGraph _ ge) = inferGraph env nm ge

inferDef _ _ (DPalette _ pe) =
  case pe of
    ExplicitPalette cs -> (EPalette cs (Just (length cs)), [])
    PaletteSize k      -> (EPalette [] (Just k), [])

inferDef _ _ (DRestrictions _ rs) = (ERestr rs, [])

inferDef env nm (DTransform _ te) =
  case typeofTransform env nm te of
    Right rt -> (ETransform rt (transformK env te), optionDiags nm te)
    Left d   -> (ETransform (RType SCol SCol Safe) (transformK env te), d : optionDiags nm te)

inferDef env nm (DInstance _ ie) = (EInstance, inferInstance env nm ie)

inferDef env nm (DQuery _ (ChromaticNumber g)) =
  (EQueryInt, requireGraph env nm g (Just 1))   -- code 1: kind mismatch if not a graph

-- ── Graphs ───────────────────────────────────────────────────────────────────

inferGraph :: Env -> Name -> GraphExpr -> (Entity, [Diag])
inferGraph _ nm (GraphLit vs es) =
  let vset    = Set.fromList vs
      bad     = [ err nm (Just 3) $
                    "edge endpoint not in graph: " ++ show endp
                | (u, v) <- es, endp <- [u, v], not (Set.member endp vset) ]
      -- keep the vertex set exactly the declared one; drop stray-endpoint edges
      goodEs  = [ e | e@(u, v) <- es, Set.member u vset, Set.member v vset ]
      g       = buildGraph vs goodEs
  in (EGraph g, bad)

inferGraph _ _ (UdgLit _ es) =
  -- vertices are implied by the edge list
  let vs = concatMap (\(u, v) -> [u, v]) es
  in (EGraph (buildGraph vs es), [])

inferGraph env nm (ApplyTransform tName gName) =
  let dsScope = scopeChecks env nm
                  [ (tName, isTransform, "transform") , (gName, isGraph, "graph") ]
  in case (Map.lookup tName env, Map.lookup gName env) of
       (Just (ETransform rt _), Just (EGraph g)) ->
         let sameVertex = rSrc rt == SCol && rTgt rt == SCol
             dApply | not sameVertex =
                        [ err nm Nothing $
                            "`apply` needs a same-vertex (Col ~> Col) transform; "
                              ++ tName ++ " : " ++ ppSort (rSrc rt) ++ " ~> "
                              ++ ppSort (rTgt rt)
                              ++ " is vertex-adding — use it in an `instance` pipeline" ]
                    | otherwise = sigmaDiag nm g
         in (EGraph g, dsScope ++ dApply)
       _ -> (EGraph G.empty, dsScope)

-- | Build a 'G.Graph' over the literal vertex tokens, keeping isolated vertices.
buildGraph :: [Vertex] -> [Edge] -> G.Graph String
buildGraph vs es = foldr G.addVertex (G.fromEdges es) vs

-- ── Transforms (the certified-reduction layer) ───────────────────────────────

typeofTransform :: Env -> Name -> TransformExpr -> Either Diag RType
typeofTransform env nm = go
  where
    go (ColorChoice _)    = Right (RType SCol SIS  Safe)
    go Gadgetize          = Right (RType SIS  SWIS Safe)
    go (LayoutT _)        = Right (RType SWIS SUDG Safe)
    go EmitT              = Right (RType SUDG SDev Safe)
    go (EncodeColoring _) = Right (RType SCol SWIS Safe)
    go SuperUDG           = Right (RType SCol SCol (ASafe 1))
    go (ToUDG mode _)     = Right $ case mode of
        Exact          -> RType SCol SUDG Safe
        Preserve _     -> RType SCol SCol Safe   -- supergraph; sigma<=5 gated at use
    go (TRef r)           =
      case Map.lookup r env of
        Just (ETransform rt _) -> Right rt
        Just other             -> Left (err nm (Just 1) $
          "kind mismatch: " ++ r ++ " : " ++ ppTy (entityTy other)
            ++ " used where a transform is expected")
        Nothing                -> Left (err nm Nothing ("not in scope: " ++ r))
    go (Compose [])       = Left (err nm Nothing "empty compose [...]")
    go (Compose (r:rs))   = do
      first <- go (TRef r)
      foldlM (\acc r' -> go (TRef r') >>= pipe acc) first rs
    go (Pipe f g)         = do
      tf <- go f
      tg <- go g
      pipe tf tg

    pipe tf tg
      | rTgt tf == rSrc tg =
          Right (RType (rSrc tf) (rTgt tg) (effPlus (rEff tf) (rEff tg)))
      | otherwise =
          Left (err nm Nothing $
            "stage-ordering error: a " ++ ppSort (rTgt tf)
              ++ "-producing stage cannot feed a stage expecting "
              ++ ppSort (rSrc tg)
              ++ " (no rule applies; cf. Cor. \"ill-ordered pipelines are ill-typed\")")

-- | Static option checks on a @toUDG@ transform (errors.tex #8, #9).
optionDiags :: Name -> TransformExpr -> [Diag]
optionDiags nm (ToUDG mode opts) =
  let keeps = Set.fromList (concat [ vs | KeepVertices vs <- opts ])
      drops = Set.fromList (concat [ vs | DropVertices vs <- opts ])
      overlap = Set.intersection keeps drops
      d8 = [ err nm (Just 8) $
               "overlapping keep/drop: " ++ showSet overlap
           | not (Set.null overlap) ]
      d9 = [ err nm (Just 9) "exact transform cannot drop vertices"
           | Exact <- [mode], not (Set.null drops) ]
  in d8 ++ d9
optionDiags nm (Pipe f g)  = optionDiags nm f ++ optionDiags nm g
optionDiags _  _           = []

-- | Extract the pipeline's palette @k@ (from @colorChoice k@ / @encodeColoring k@
-- / @preserve kColorable(k)@), threading through references.
transformK :: Env -> TransformExpr -> Maybe Int
transformK env = go
  where
    go (ColorChoice k)              = Just k
    go (EncodeColoring k)           = Just k
    go (ToUDG (Preserve (KColorable k)) _) = Just k
    go (Pipe f g)                   = go f `orElse` go g
    go (Compose rs)                 = firstJust (map fromRef rs)
    go (TRef r)                     = fromRef r
    go _                            = Nothing
    fromRef r = case Map.lookup r env of
                  Just (ETransform _ k) -> k
                  _                     -> Nothing

-- ── Instances ────────────────────────────────────────────────────────────────

inferInstance :: Env -> Name -> InstanceExpr -> [Diag]
inferInstance env nm (InstanceExpr gName mPal mRestr mTrans) =
  let dGraph = requireGraph env nm gName (Just 1)
      mg     = case Map.lookup gName env of Just (EGraph g) -> Just g; _ -> Nothing

      (palCols, palSize, dPal) = resolvePalette env nm mPal
      dRestr = case mRestr of
                 Nothing -> []
                 Just r  -> case Map.lookup r env of
                   Just (ERestr rs) -> maybe [] (validateRestrictions nm rs palCols palSize) mg
                   Just other       -> [kindErr nm r other "restrictions"]
                   Nothing          -> [scopeErr nm r]

      (mRt, kTrans, dTrans0) = resolveTransform env nm mTrans
      kPal  = palSize
      dK    = case (kPal, kTrans) of
                (Just a, Just b) | a /= b ->
                  [ err nm Nothing $
                      "palette size k=" ++ show a
                        ++ " disagrees with k=" ++ show b ++ " in the transform" ]
                _ -> []
      k     = kPal `orElse` kTrans

      dTrans = dTrans0 ++ maybe [] (transformUseDiags nm mg k) mRt
  in dGraph ++ dPal ++ dRestr ++ dTrans ++ dK

-- | Checks on the @via@ transform at an instance site: it must start from a
-- coloring instance; supergraph (Col ~> Col) transforms are gated by sigma<=5;
-- a full pipeline (Col ~> Dev) must satisfy the device budget.
transformUseDiags :: Name -> Maybe (G.Graph String) -> Maybe Int -> RType -> [Diag]
transformUseDiags nm mg k rt =
  let dSrc = [ err nm Nothing $
                 "transform used after `via` must start from a coloring instance "
                   ++ "(Col), but starts from " ++ ppSort (rSrc rt)
             | rSrc rt /= SCol ]
      dSigma = case (rTgt rt, mg) of
                 (SCol, Just g) -> sigmaDiag nm g        -- supergraph path
                 _              -> []
      dBudget = case (rTgt rt, mg, k) of
                 (SDev, Just g, Just kk) ->
                   let n = G.order g
                       atoms = estimateAtoms g kk
                   in if atoms > defaultNmax
                        then [ err nm Nothing $
                                 "device budget exceeded: N=" ++ show atoms
                                   ++ " atoms > Nmax=" ++ show defaultNmax
                                   ++ "  (n=" ++ show n ++ ", k=" ++ show kk ++ ")" ]
                        else [ warn nm $
                                 "feasible: N=" ++ show atoms ++ " atoms <= Nmax="
                                   ++ show defaultNmax ]
                 _ -> []
  in dSrc ++ dSigma ++ dBudget

-- | The neighborhood-independence side-condition of Theorem "Supergraph
-- inflation is unbounded": supergraph safety is only available when
-- @sigma(G) = max_v alpha(G[N(v)]) <= 5@.
sigmaDiag :: Name -> G.Graph String -> [Diag]
sigmaDiag nm g =
  let s = sigmaG g
  in [ err nm Nothing $
         "supergraph safety unavailable: sigma(G)=" ++ show s
           ++ " > 5, so no UDG supergraph bounds chromatic inflation "
           ++ "(Thm. impossibility); use the exact gadget path instead"
     | s > 5 ]

sigmaG :: G.Graph String -> Int
sigmaG g =
  maximum (0 : [ O.independenceNumber (G.inducedSubgraph (G.neighbors v g) g)
               | v <- Set.toList (G.vertices g) ])

-- | Worst-case gadgetized atom count used by the budget premise:
-- @|V(A)| = nk + 2|E(G')|@ with @|E(G')| = n*C(k,2) + m*k@.
estimateAtoms :: G.Graph String -> Int -> Int
estimateAtoms g k =
  let n  = G.order g
      m  = G.size g
      e' = n * (k * (k - 1) `div` 2) + m * k
  in n * k + 2 * e'

-- ── Restriction validation (errors.tex #2, #4, #5, #6) ───────────────────────

validateRestrictions
  :: Name -> [Restriction] -> [Color] -> Maybe Int -> G.Graph String -> [Diag]
validateRestrictions nm rs palCols palSize g = concatMap one rs
  where
    vset = G.vertices g
    inV v
      | Set.member v vset = []
      | otherwise = [ err nm (Just 2) $
                        "restriction mentions vertex " ++ show v
                          ++ " not in the instance graph (or wrong restriction set, #6)" ]
    inPal c
      | null palCols          = []   -- size-only palette: no color names to check
      | c `elem` palCols      = []
      | otherwise = [ err nm (Just 4) $ "color " ++ show c ++ " not in palette" ]
    sizeCheck j what
      | Just s <- palSize, j > s =
          [ err nm (Just 5) $
              what ++ " " ++ show j ++ " exceeds palette size " ++ show s ]
      | otherwise = []
    one (Precolor v c)        = inV v ++ inPal c
    one (Allow v cs)          = inV v ++ concatMap inPal cs
    one (Forbid v cs)         = inV v ++ concatMap inPal cs
    one (SameColor u v)       = inV u ++ inV v
    one (DifferentColor u v)  = inV u ++ inV v
    one (UseAtMost j)         = sizeCheck j "useAtMost"
    one (UseExactly j)        = sizeCheck j "useExactly"
    one (DistinctOn vs)       = concatMap inV vs

-- ── Resolution helpers ───────────────────────────────────────────────────────

resolvePalette :: Env -> Name -> Maybe Name -> ([Color], Maybe Int, [Diag])
resolvePalette _   _  Nothing  = ([], Nothing, [])
resolvePalette env nm (Just p) =
  case Map.lookup p env of
    Just (EPalette cs sz) -> (cs, sz, [])
    Just other            -> ([], Nothing, [kindErr nm p other "palette"])
    Nothing               -> ([], Nothing, [scopeErr nm p])

resolveTransform :: Env -> Name -> Maybe Name -> (Maybe RType, Maybe Int, [Diag])
resolveTransform _   _  Nothing  = (Nothing, Nothing, [])
resolveTransform env nm (Just t) =
  case Map.lookup t env of
    Just (ETransform rt k) -> (Just rt, k, [])
    Just other             -> (Nothing, Nothing, [kindErr nm t other "transform"])
    Nothing                -> (Nothing, Nothing, [scopeErr nm t])

requireGraph :: Env -> Name -> Name -> Maybe Int -> [Diag]
requireGraph env nm g code =
  case Map.lookup g env of
    Just (EGraph _) -> []
    Just other      -> [err nm code $
                          "kind mismatch: " ++ g ++ " : " ++ ppTy (entityTy other)
                            ++ " used where a graph is expected"]
    Nothing         -> [scopeErr nm g]

scopeChecks :: Env -> Name -> [(Name, Entity -> Bool, String)] -> [Diag]
scopeChecks env nm = concatMap chk
  where
    chk (r, p, what) = case Map.lookup r env of
      Just e | p e       -> []
             | otherwise -> [err nm (Just 1) $
                               "kind mismatch: " ++ r ++ " : " ++ ppTy (entityTy e)
                                 ++ " used where a " ++ what ++ " is expected"]
      Nothing            -> [scopeErr nm r]

isGraph :: Entity -> Bool
isGraph EGraph{} = True
isGraph _        = False

isTransform :: Entity -> Bool
isTransform ETransform{} = True
isTransform _            = False

kindErr :: Name -> Name -> Entity -> String -> Diag
kindErr nm r other what =
  err nm (Just 1) $
    "kind mismatch: " ++ r ++ " : " ++ ppTy (entityTy other)
      ++ " used where a " ++ what ++ " is expected"

scopeErr :: Name -> Name -> Diag
scopeErr nm r = err nm Nothing ("not in scope: " ++ r)

-- ── Small utilities ──────────────────────────────────────────────────────────

effPlus :: Effect -> Effect -> Effect
effPlus Safe e               = e
effPlus e Safe               = e
effPlus (ASafe a) (ASafe b)  = ASafe (a + b)

orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing  y = y

firstJust :: [Maybe a] -> Maybe a
firstJust = foldr orElse Nothing

foldlM :: Monad m => (b -> a -> m b) -> b -> [a] -> m b
foldlM _ z []       = pure z
foldlM f z (x : xs) = f z x >>= \z' -> foldlM f z' xs

showSet :: Set.Set String -> String
showSet = intercalate ", " . Set.toList
