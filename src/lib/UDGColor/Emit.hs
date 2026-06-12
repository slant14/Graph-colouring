-- | Emit a well-typed @instance@ as a JSON spec the neutral-atom simulator
-- consumes. We export the /color-choice graph/ @G'@ (the Stage-1 MWIS instance,
-- the tractable logical object the gadget array realizes) together with the
-- decode map slot |-> (vertex, color), the original graph, and the value offset.
-- The Python simulator (@sim/@) runs the adiabatic Rydberg MWIS on @G'@ and
-- decodes a coloring.
--
-- JSON is hand-rolled to avoid an @aeson@ dependency; the labels involved are
-- plain identifiers/integers, so no escaping is required.
module UDGColor.Emit
  ( instanceJson
  , programInstanceJsons
  ) where

import           Data.List   (intercalate)
import           Data.Map    (Map)
import qualified Data.Map    as Map
import qualified Data.Set    as Set

import           UDGColor.Ast
import qualified UDGColor.Graph  as G
import           UDGColor.Gadget (Gadget(..), gadgetize)
import           UDGColor.Oracle (isKColorable)
import           UDGColor.Stage1 (colorChoiceGraphPrecolored)
import           UDGColor.TypeCheck (Entity(..), Env)

-- | JSON for every @instance@ in the program, paired with the instance name.
programInstanceJsons :: Env -> Program -> [(Name, Either String String)]
programInstanceJsons env (Program bs) =
  [ (nm, instanceJson env nm ie) | Binding _ (DInstance nm ie) <- bs ]

-- | JSON for a single instance, or an error string if it cannot be resolved.
instanceJson :: Env -> Name -> InstanceExpr -> Either String String
instanceJson env nm (InstanceExpr gName mPal mRestr _) = do
  g <- maybe (Left ("graph " ++ gName ++ " unresolved")) Right (graphOf gName)
  k <- maybe (Left "palette size / k unknown") Right kOf
  let beta    = betaOf g k
      gp      = colorChoiceGraphPrecolored k g beta
      gad     = gadgetize gp
      slots   = Set.toAscList (G.vertices gp)              -- canonical order
      idx     = Map.fromList (zip slots [0 :: Int ..])
      epair (a, b) = (idx Map.! a, idx Map.! b)
      cEdges  = map epair (Set.toList (G.edges gp))
  pure $ obj
    [ ("instance",   str nm)
    , ("graph",      str gName)
    , ("n",          int (G.order g))
    , ("k",          int k)
    , ("offsetC",    num (gOffset gad))
    , ("colorable",  bool (isKColorable k g))
    , ("originalVertices", arr (map str (Set.toList (G.vertices g))))
    , ("originalEdges",    arr [ pair (str u) (str v) | (u, v) <- Set.toList (G.edges g) ])
    , ("slots",      arr [ pair (str v) (int i) | (v, i) <- slots ])
    , ("choiceEdges",arr [ pair (int a) (int b) | (a, b) <- cEdges ])
    ]
  where
    graphOf n = case Map.lookup n env of Just (EGraph g) -> Just g; _ -> Nothing

    palSize = case mPal of
      Just p -> case Map.lookup p env of Just (EPalette _ sz) -> sz; _ -> Nothing
      Nothing -> Nothing
    transK = Nothing  -- k is taken from the palette for emission
    kOf = palSize `mplusM` transK

    colorIndex = case mPal of
      Just p -> case Map.lookup p env of
        Just (EPalette cs _) -> Map.fromList (zip cs [1 :: Int ..])
        _                    -> Map.empty
      Nothing -> Map.empty

    betaOf :: G.Graph String -> Int -> Map String Int
    betaOf g _ = case mRestr of
      Just r -> case Map.lookup r env of
        Just (ERestr rs) -> Map.fromList
          [ (v, i)
          | Precolor v c <- rs
          , Just i <- [Map.lookup c colorIndex]
          , Set.member v (G.vertices g) ]
        _ -> Map.empty
      Nothing -> Map.empty

mplusM :: Maybe a -> Maybe a -> Maybe a
mplusM (Just x) _ = Just x
mplusM Nothing  y = y

-- ── tiny JSON writer ─────────────────────────────────────────────────────────

obj :: [(String, String)] -> String
obj kvs = "{" ++ intercalate "," [ str k ++ ":" ++ v | (k, v) <- kvs ] ++ "}"

arr :: [String] -> String
arr xs = "[" ++ intercalate "," xs ++ "]"

pair :: String -> String -> String
pair a b = "[" ++ a ++ "," ++ b ++ "]"

str :: String -> String
str s = "\"" ++ s ++ "\""

int :: Int -> String
int = show

num :: Double -> String
num = show

bool :: Bool -> String
bool True  = "true"
bool False = "false"
