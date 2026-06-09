-- | Brute-force ground truth for small instances.
--
-- These routines are intentionally simple and exponential; their only job is
-- to be /obviously correct/ so the polynomial reduction stages can be checked
-- against them. Do not use on large graphs.
module UDGColor.Oracle
  ( -- * Coloring
    isKColorable
  , chromatic
  , properColorings
    -- * Independence / MWIS
  , independenceNumber
  , maxIndependentSet
  , isIndependent
  , mwisValue
  , maxWeightIS
  ) where

import           Data.List  (maximumBy)
import           Data.Map   (Map)
import qualified Data.Map   as Map
import           Data.Ord   (comparing)
import           Data.Set   (Set)
import qualified Data.Set   as Set

import           UDGColor.Graph

-- ── Coloring ──────────────────────────────────────────────────────────────────

-- | Is @g@ properly @k@-colorable? Backtracking over vertices, assigning a
-- color consistent with already-colored neighbors.
isKColorable :: Ord a => Int -> Graph a -> Bool
isKColorable k g
  | k < 0            = False
  | order g == 0     = True
  | k == 0           = False
  | otherwise        = go (Set.toList (vertices g)) Map.empty
  where
    go [] _ = True
    go (v : vs) assigned =
      or [ go vs (Map.insert v c assigned)
         | c <- [1 .. k]
         , all (\u -> Map.lookup u assigned /= Just c)
               (Set.toList (neighbors v g)) ]

-- | Chromatic number: the least @k@ admitting a proper coloring.
chromatic :: Ord a => Graph a -> Int
chromatic g
  | order g == 0 = 0
  | otherwise    = go 1
  where
    go k | isKColorable k g = k
         | otherwise        = go (k + 1)

-- | All proper @k@-colorings of @g@, as maps. (Exponential; tests only.)
properColorings :: Ord a => Int -> Graph a -> [Map a Int]
properColorings k g = go (Set.toList (vertices g)) Map.empty
  where
    go [] assigned = [assigned]
    go (v : vs) assigned =
      [ result
      | c <- [1 .. k]
      , all (\u -> Map.lookup u assigned /= Just c) (Set.toList (neighbors v g))
      , result <- go vs (Map.insert v c assigned) ]

-- ── Independence / MWIS ─────────────────────────────────────────────────────────

isIndependent :: Ord a => Set a -> Graph a -> Bool
isIndependent s g =
  and [ not (hasEdge u v g)
      | let xs = Set.toList s, (u : rest) <- tailsNE xs, v <- rest ]
  where
    tailsNE []         = []
    tailsNE l@(_ : t)  = l : tailsNE t

-- | Independence number @alpha(g)@ via the standard
-- @alpha(G) = max(alpha(G - v), 1 + alpha(G - N[v]))@ recursion, branching on a
-- maximum-degree vertex. Fast on the structured color-choice graphs.
independenceNumber :: Ord a => Graph a -> Int
independenceNumber g
  | order g == 0    = 0
  | size g == 0     = order g            -- no edges: take everything
  | otherwise       =
      let v       = maximumBy (comparing (`degree` g)) (Set.toList (vertices g))
          without = independenceNumber (removeVertex v g)
          with    = 1 + independenceNumber (removeClosedNeighborhood v g)
      in max without with

-- | One witnessing maximum independent set (not necessarily unique).
maxIndependentSet :: Ord a => Graph a -> Set a
maxIndependentSet g
  | order g == 0 = Set.empty
  | size g == 0  = vertices g
  | otherwise    =
      let v       = maximumBy (comparing (`degree` g)) (Set.toList (vertices g))
          without = maxIndependentSet (removeVertex v g)
          with    = Set.insert v (maxIndependentSet (removeClosedNeighborhood v g))
      in if Set.size with >= Set.size without then with else without

-- | Maximum-weight independent set /value/ for a vertex weighting. Vertices
-- absent from the map default to weight 1 (matching the unit-weight reductions).
mwisValue :: (Ord a) => Map a Double -> Graph a -> Double
mwisValue w g
  | order g == 0 = 0
  | size g == 0  = sum [ wt v | v <- Set.toList (vertices g) ]
  | otherwise    =
      let v       = maximumBy (comparing (`degree` g)) (Set.toList (vertices g))
          without = mwisValue w (removeVertex v g)
          with    = wt v + mwisValue w (removeClosedNeighborhood v g)
      in max without with
  where
    wt v = Map.findWithDefault 1 v w

-- | A witnessing maximum-weight independent set (one of possibly many).
maxWeightIS :: Ord a => Map a Double -> Graph a -> Set a
maxWeightIS w g
  | order g == 0 = Set.empty
  | size g == 0  = vertices g
  | otherwise    =
      let v       = maximumBy (comparing (`degree` g)) (Set.toList (vertices g))
          without = maxWeightIS w (removeVertex v g)
          with    = Set.insert v (maxWeightIS w (removeClosedNeighborhood v g))
      in if weight with >= weight without then with else without
  where
    weight = sum . map (\v -> Map.findWithDefault 1 v w) . Set.toList
