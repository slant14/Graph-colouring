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
  ) where

import           Data.Map    (Map)
import qualified Data.Map    as Map
import qualified Data.Set    as Set

import           UDGColor.Ast
import qualified UDGColor.Graph   as G
import           UDGColor.Gadget  (Gadget(..), gadgetize)
import           UDGColor.Layout
import           UDGColor.Oracle  (isKColorable)
import           UDGColor.Stage1  (colorChoiceGraphPrecolored)
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
  let beta  = betaOf g
      gp    = colorChoiceGraphPrecolored k g beta
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
    , diColorable   = isKColorable k g
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

    -- 1-based color index map, if the palette lists explicit colors.
    colorIndex :: Map Color Int
    colorIndex = case palette of
      Just (cs, _) -> Map.fromList (zip cs [1 ..])
      Nothing      -> Map.empty

    -- boundary precoloring from `precolor v : c` restrictions (when c is a named
    -- palette color), used by the precolored color-choice graph.
    betaOf :: G.Graph String -> Map String Int
    betaOf g = case mRestr of
      Just r -> case Map.lookup r env of
        Just (ERestr rs) ->
          Map.fromList
            [ (v, i)
            | Precolor v c <- rs
            , Just i <- [Map.lookup c colorIndex]
            , Set.member v (G.vertices g) ]
        _ -> Map.empty
      Nothing -> Map.empty

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
