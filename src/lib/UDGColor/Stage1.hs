-- | Stage 1 of the primary path: the colorability -> independent-set reduction
-- (@paper.tex@, Definition \"color-choice graph\" and Theorem \"Exactness of
-- Stage 1\").
--
-- For a graph @G@ and palette size @k@, the color-choice graph @G'@ has vertex
-- set @V x {1..k}@ (a \"slot\" @(v,i)@ meaning \"v takes color i\"), a @k@-clique
-- per original vertex (choose at most one color), and a conflict edge between
-- equal-color slots of adjacent vertices. The theorem: @alpha(G') = n@ iff @G@
-- is @k@-colorable, with size-@n@ independent sets in bijection with proper
-- @k@-colorings.
module UDGColor.Stage1
  ( Slot
  , colorChoiceGraph
  , colorChoiceGraphPrecolored
  , decodeColoring
  , isProperColoring
  ) where

import           Data.Map   (Map)
import qualified Data.Map   as Map
import           Data.Set   (Set)
import qualified Data.Set   as Set

import           UDGColor.Graph

-- | A slot @(v, i)@: \"vertex @v@ takes color @i@\".
type Slot a = (a, Int)

-- | The color-choice graph @G'@ of @(G, k)@.
colorChoiceGraph :: Ord a => Int -> Graph a -> Graph (Slot a)
colorChoiceGraph k g = colorChoiceGraphPrecolored k g Map.empty

-- | The boundary-precolored variant (@decomposition.tex@, Def. 4.1): each
-- vertex in the domain of @beta@ keeps only its single pinned slot and loses its
-- choice clique; all other vertices keep their full @k@-clique. Conflict edges
-- survive among all remaining slots. Passing an empty @beta@ recovers the plain
-- 'colorChoiceGraph'.
colorChoiceGraphPrecolored
  :: Ord a => Int -> Graph a -> Map a Int -> Graph (Slot a)
colorChoiceGraphPrecolored k g beta =
  let vs        = Set.toList (vertices g)
      -- surviving color indices for a vertex
      slotsOf v = case Map.lookup v beta of
                    Just i  -> [i]
                    Nothing -> [1 .. k]
      allSlots  = [ (v, i) | v <- vs, i <- slotsOf v ]
      withVerts = foldr addVertex empty allSlots
      -- choice cliques (only where the vertex is unpinned and has >1 slot)
      choiceEs  = [ ((v, i), (v, j))
                  | v <- vs, Map.notMember v beta
                  , let cs = slotsOf v
                  , (i : rest) <- tailsNE cs, j <- rest ]
      -- conflict edges between equal-color surviving slots of adjacent vertices
      conflictEs = [ ((u, i), (w, i))
                   | (u, w) <- Set.toList (edges g)
                   , i <- [1 .. k]
                   , i `elem` slotsOf u, i `elem` slotsOf w ]
  in foldr (\(a, b) -> addEdge a b) withVerts (choiceEs ++ conflictEs)
  where
    tailsNE []        = []
    tailsNE l@(_ : t) = l : tailsNE t

-- | Stage-1 inverse: read a coloring off a set of slots. Returns the coloring
-- only if every original vertex of @g@ is assigned exactly one slot; otherwise
-- 'Nothing' (the solver did not return a full witness).
decodeColoring :: Ord a => Graph a -> Set (Slot a) -> Maybe (Map a Int)
decodeColoring g chosen =
  let assignments = Set.toList chosen
      m           = Map.fromListWith (++) [ (v, [i]) | (v, i) <- assignments ]
      singleton (v, is) = case is of [i] -> Just (v, i); _ -> Nothing
  in do
       pairs <- traverse singleton (Map.toList m)
       let cmap = Map.fromList pairs
       if Map.keysSet cmap == vertices g then Just cmap else Nothing

-- | Check that a complete coloring is proper for @g@.
isProperColoring :: Ord a => Graph a -> Map a Int -> Bool
isProperColoring g c =
  Map.keysSet c == vertices g
    && and [ Map.lookup u c /= Map.lookup v c | (u, v) <- Set.toList (edges g) ]
