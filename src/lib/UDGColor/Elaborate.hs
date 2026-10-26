-- | Elaboration: lower a /well-typed/ @instance@ all the way to the device
-- instance the simulator would consume — and stop there. This is "everything
-- before the simulation stage": it runs Stage 1 (color-choice graph), Stage 2
-- (gadgetization), and Stage 3 (the heuristic layout optimizer) from the
-- existing library, and reports the resulting atom count, value offset @C@,
-- blockade radius @r*@, and realization quality. No Rydberg dynamics is run.
module UDGColor.Elaborate
  ( DeviceInstance(..)
  , elaborateProgram
  , elaborateInstance
  , colorIndexFor
  , slotRestrOf
  , isKColorableUnder
  ) where

import           Data.Map    (Map)
import qualified Data.Map    as Map
import qualified Data.Set    as Set

import           UDGColor.Ast
import qualified UDGColor.Graph   as G
import           UDGColor.Gadget  (Gadget(..), gadgetize)
import           UDGColor.Layout
import           UDGColor.Oracle  (properColorings)
import           UDGColor.Stage1  (SlotRestr(..), colorChoiceGraphRestricted, noRestr,
                                   satisfiesRestr)
import           UDGColor.TypeCheck (Entity(..), Env, RType(..))

-- | The compiled, un-simulated hardware instance plus its decode-relevant data.
data DeviceInstance = DeviceInstance
  { diInstance    :: Name     -- ^ the @instance@ binding
  , diGraph       :: Name     -- ^ the source graph
  , diPath        :: String   -- ^ which compilation path the program selected
  , diN           :: Int      -- ^ |V(G)|
  , diK           :: Int      -- ^ palette size
  , diChoiceV     :: Int      -- ^ |V(G')| = nk
  , diChoiceE     :: Int      -- ^ |E(G')|
  , diAtoms       :: Int      -- ^ |V(A)|, total atoms
  , diLogical     :: Int      -- ^ logical atoms
  , diGadgetAtoms :: Int      -- ^ routing/gadget atoms
  , diOffsetC     :: Double   -- ^ MWIS value offset C
  , diRadius      :: Double   -- ^ selected blockade radius r*
  , diMissing     :: Int      -- ^ prescribed edges not realized (should be 0 at r*)
  , diFalse       :: Int      -- ^ realized-but-not-prescribed edges (geometry residual)
  , diColorable   :: Bool     -- ^ oracle: is G k-colorable? (small instances)
  } deriving (Show)

-- | Elaborate every @instance@ in a program, using the checked environment to
-- resolve its graph, palette, restrictions, and transform.
elaborateProgram :: Env -> Program -> [Either (Name, String) DeviceInstance]
elaborateProgram env (Program bs) =
  [ elaborateInstance env nm ie | Binding _ (DInstance nm ie) <- bs ]

elaborateInstance
  :: Env -> Name -> InstanceExpr -> Either (Name, String) DeviceInstance
elaborateInstance env nm (InstanceExpr gName mPal mRestr mTrans) = do
  g  <- need (graphOf gName) ("graph " ++ gName ++ " unresolved")
  k  <- needK
  let sr    = restrOf g k
      gp    = colorChoiceGraphRestricted k g sr
      gad   = gadgetize gp
      ag    = gGraph gad
      lay   = layoutGadget defaultParams ag
      pos   = lPos lay
      r     = lRadius lay
      logical = length (gLogical gad)
      atoms   = G.order ag
  pure DeviceInstance
    { diInstance    = nm
    , diGraph       = gName
    , diPath        = pathLabel
    , diN           = G.order g
    , diK           = k
    , diChoiceV     = G.order gp
    , diChoiceE     = G.size gp
    , diAtoms       = atoms
    , diLogical     = logical
    , diGadgetAtoms = atoms - logical
    , diOffsetC     = gOffset gad
    , diRadius      = r
    , diMissing     = length (missingEdges pos r ag)
    , diFalse       = length (falseEdges pos r ag)
    , diColorable   = isKColorableUnder k g sr
    }
  where
    need (Just x) _   = Right x
    need Nothing  msg = Left (nm, msg)

    graphOf n = case Map.lookup n env of Just (EGraph g) -> Just g; _ -> Nothing

    palette = case mPal of
      Just p -> case Map.lookup p env of Just (EPalette cs sz) -> Just (cs, sz); _ -> Nothing
      Nothing -> Nothing

    transK = case mTrans of
      Just t -> case Map.lookup t env of Just (ETransform _ k) -> k; _ -> Nothing
      Nothing -> Nothing

    needK = case (palette >>= snd, transK) of
      (Just k, _)       -> Right k
      (Nothing, Just k) -> Right k
      _                 -> Left (nm, "cannot elaborate: palette size / k is unknown")

    -- the pairwise restrictions of the instance, in slot form
    restrOf :: G.Graph String -> Int -> SlotRestr String
    restrOf g k = case mRestr of
      Just r -> case Map.lookup r env of
        Just (ERestr rs) ->
          slotRestrOf k (colorIndexFor (fmap fst palette) (Just k)) (G.vertices g) rs
        _ -> noRestr
      Nothing -> noRestr

    pathLabel = case mTrans of
      Just t -> case Map.lookup t env of
        Just (ETransform rt _)
          | rTgt rt == SDev -> "exact gadget pipeline (Col ~> Dev) via " ++ t
          | rTgt rt == SCol -> "supergraph path (Col ~> Col) via " ++ t
                                 ++ "  [elaborated through the exact gadget path]"
          | otherwise       -> "via " ++ t ++ " (" ++ ppSort (rSrc rt) ++ " ~> "
                                 ++ ppSort (rTgt rt) ++ ")"
        _ -> "via " ++ t
      Nothing -> "default exact gadget pipeline (no `via`)"

-- | Color names to 1-based indices: the listed colors of a named palette, or
-- the numerals @1..k@ of a size-only palette.
colorIndexFor :: Maybe [Color] -> Maybe Int -> Map Color Int
colorIndexFor (Just cs@(_ : _)) _      = Map.fromList (zip cs [1 ..])
colorIndexFor _                 (Just k) = Map.fromList [ (show i, i) | i <- [1 .. k] ]
colorIndexFor _                 Nothing  = Map.empty

-- | Translate the pairwise restrictions of a program into slot form
-- ('SlotRestr'). @precolor@, @allow@ and @forbid@ narrow the allowed colors of
-- a vertex; @differentColor@ and @distinctOn@ add different-color pairs;
-- @sameColor@ adds same-color pairs. Counting restrictions (@useAtMost@,
-- @useExactly@) have no slot form; the checker rejects them on the exact path
-- unless they are vacuous.
slotRestrOf :: Int -> Map Color Int -> Set.Set Vertex -> [Restriction] -> SlotRestr Vertex
slotRestrOf k idx vset = foldl one noRestr
  where
    ixs cs = [ i | c <- cs, Just i <- [Map.lookup c idx] ]
    current sr v = Map.findWithDefault [1 .. k] v (srAllowed sr)
    narrow sr v keep
      | Set.member v vset = sr { srAllowed = Map.insert v (filter keep (current sr v))
                                                       (srAllowed sr) }
      | otherwise = sr
    one sr (Precolor v c)       = narrow sr v (`elem` ixs [c])
    one sr (Allow v cs)         = narrow sr v (`elem` ixs cs)
    one sr (Forbid v cs)        = narrow sr v (`notElem` ixs cs)
    one sr (DifferentColor u v) = sr { srDiffer = srDiffer sr ++ [(u, v)] }
    one sr (DistinctOn vs)      = sr { srDiffer = srDiffer sr
                                         ++ [ (u, v) | (i, u) <- zip [0 :: Int ..] vs
                                                     , (j, v) <- zip [0 ..] vs, i < j ] }
    one sr (SameColor u v)      = sr { srSame = srSame sr ++ [(u, v)] }
    one sr (UseAtMost _)        = sr
    one sr (UseExactly _)       = sr

-- | Brute-force oracle: is there a proper @k@-coloring of @g@ that satisfies the
-- restrictions? (Exponential; small instances only.)
isKColorableUnder :: Ord a => Int -> G.Graph a -> SlotRestr a -> Bool
isKColorableUnder k g sr = any (satisfiesRestr sr) (properColorings k g)
