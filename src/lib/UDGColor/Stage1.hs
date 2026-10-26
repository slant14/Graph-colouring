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
  , SlotRestr(..)
  , noRestr
  , colorChoiceGraph
  , colorChoiceGraphPrecolored
  , colorChoiceGraphRestricted
  , satisfiesRestr
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

-- | The pairwise restrictions of the language, in slot form (@paper.tex@,
-- Proposition \"Restrictions\"). Each is an independence constraint on @G'@:
-- an allowed-color list deletes the other slots of its vertex (@precolor@,
-- @allow@, @forbid@); a different-color pair adds the conflict edges of an
-- edge of @G@ (@differentColor@, @distinctOn@); a same-color pair joins every
-- two slots of the pair with different colors (@sameColor@). The counting
-- restrictions @useAtMost@ and @useExactly@ are not independence constraints
-- and have no slot form; the checker rejects them on the exact path.
data SlotRestr a = SlotRestr
  { srAllowed :: Map a [Int]   -- ^ allowed colors of a vertex (absent: all of 1..k)
  , srDiffer  :: [(a, a)]      -- ^ pairs that must receive different colors
  , srSame    :: [(a, a)]      -- ^ pairs that must receive the same color
  } deriving (Show)

noRestr :: SlotRestr a
noRestr = SlotRestr Map.empty [] []

-- | The boundary-precolored variant (@decomposition.tex@, Def. 4.1): each
-- vertex in the domain of @beta@ keeps only its single pinned slot and loses its
-- choice clique; all other vertices keep their full @k@-clique. Conflict edges
-- survive among all remaining slots. Passing an empty @beta@ recovers the plain
-- 'colorChoiceGraph'.
colorChoiceGraphPrecolored
  :: Ord a => Int -> Graph a -> Map a Int -> Graph (Slot a)
colorChoiceGraphPrecolored k g beta =
  colorChoiceGraphRestricted k g noRestr { srAllowed = fmap (: []) beta }

-- | The color-choice graph of @(G, k)@ under pairwise restrictions. Its
-- size-@n@ independent sets are in bijection with the proper @k@-colorings of
-- @G@ that satisfy the restrictions.
colorChoiceGraphRestricted
  :: Ord a => Int -> Graph a -> SlotRestr a -> Graph (Slot a)
colorChoiceGraphRestricted k g sr =
  let vs        = Set.toList (vertices g)
      inG v     = Set.member v (vertices g)
      -- surviving color indices for a vertex
      slotsOf v = case Map.lookup v (srAllowed sr) of
                    Just cs -> [ i | i <- [1 .. k], i `elem` cs ]
                    Nothing -> [1 .. k]
      allSlots  = [ (v, i) | v <- vs, i <- slotsOf v ]
      withVerts = foldr addVertex empty allSlots
      -- choice cliques among the surviving slots of each vertex
      choiceEs  = [ ((v, i), (v, j))
                  | v <- vs, (i : rest) <- tailsNE (slotsOf v), j <- rest ]
      -- conflict edges between equal-color slots of adjacent or
      -- different-color vertices
      differ    = Set.toList (edges g)
                    ++ [ p | p@(u, w) <- srDiffer sr, u /= w, inG u, inG w ]
      conflictEs = [ ((u, i), (w, i))
                   | (u, w) <- differ, i <- slotsOf u, i `elem` slotsOf w ]
      -- same-color pairs: every two slots with different colors conflict
      sameEs    = [ ((u, i), (w, j))
                  | (u, w) <- srSame sr, u /= w, inG u, inG w
                  , i <- slotsOf u, j <- slotsOf w, i /= j ]
  in foldr (\(a, b) -> addEdge a b) withVerts (choiceEs ++ conflictEs ++ sameEs)
  where
    tailsNE []        = []
    tailsNE l@(_ : t) = l : tailsNE t

-- | Does a complete coloring satisfy the restrictions? (Checked directly, not
-- through the slot encoding.)
satisfiesRestr :: Ord a => SlotRestr a -> Map a Int -> Bool
satisfiesRestr sr c =
  and [ maybe False (`elem` cs) (Map.lookup v c) | (v, cs) <- Map.toList (srAllowed sr)
                                                 , Map.member v c ]
    && and [ Map.lookup u c /= Map.lookup w c
           | (u, w) <- srDiffer sr, u /= w, Map.member u c, Map.member w c ]
    && and [ Map.lookup u c == Map.lookup w c
           | (u, w) <- srSame sr, Map.member u c, Map.member w c ]

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
