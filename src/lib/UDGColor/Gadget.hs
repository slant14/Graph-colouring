-- | Stage 2 (combinatorial core): embed the abstract independent-set instance
-- @G'@ into a weighted graph @A@ whose maximum-weight independent set encodes
-- that of @G'@ with a fixed offset, and whose \"logical\" vertices decode an
-- MWIS of @G'@ back out (paper.tex, Theorem \"Gadgetized UD-MWIS embedding\"
-- interface).
--
-- This module implements the /combinatorial/ contract only — the part carrying
-- the correctness claim @MWIS(A) = MWIS(G') + C@ with an exact decoder. The
-- /metric/ unit-disk realization (Nguyen copy/crossing gadgets, actual atom
-- coordinates) is the deferred engineering fork and is not done here; see
-- 'UDGColor.Viz' for a schematic drawing.
--
-- == The gadget
--
-- Each edge @{u,v}@ of @G'@ is replaced by a 4-path
-- @Logical u -- a1 -- a2 -- Logical v@ with logical weight 1 and gadget-atom
-- weight 2. Then every edge gadget contributes exactly 2 to the MWIS /unless/
-- both its logical endpoints are selected, in which case it contributes 0 — a
-- penalty of 2 that makes selecting both endpoints never worthwhile. Hence a
-- maximum-weight independent set of @A@ selects an independent set of @G'@ on
-- the logical atoms, and
-- @MWIS(A) = alpha(G') + 2|E'|@,  i.e. the offset is @C = 2|E'|@.
module UDGColor.Gadget
  ( GVert(..)
  , Gadget(..)
  , gadgetize
  , decodeLogical
  ) where

import           Data.Map   (Map)
import qualified Data.Map   as Map
import           Data.Set   (Set)
import qualified Data.Set   as Set

import           UDGColor.Graph

-- | A vertex of the gadget graph @A@: either a logical atom carrying an
-- original @G'@ vertex, or one of the two atoms of the gadget for edge
-- @{u,v}@ (endpoints stored normalised, @u <= v@; the @Int@ is 1 or 2).
data GVert a
  = Logical a
  | EdgeA a a Int
  deriving (Eq, Ord, Show)

-- | The gadget output: the graph @A@, its weighting, the logical vertices (the
-- original @V'@), and the value offset @C@.
data Gadget a = Gadget
  { gGraph   :: Graph (GVert a)
  , gWeights :: Map (GVert a) Double
  , gLogical :: [a]
  , gOffset  :: Double
  } deriving (Show)

-- | Build the gadget graph @A@ from an abstract instance @G'@.
gadgetize :: Ord a => Graph a -> Gadget a
gadgetize g =
  let logicals = Set.toList (vertices g)
      es       = Set.toList (edges g)

      base     = foldr (addVertex . Logical) empty logicals

      addEdgeGadget (u, v) gr =
        let a1 = EdgeA u v 1
            a2 = EdgeA u v 2
        in addEdge (Logical u) a1
         . addEdge a1 a2
         . addEdge a2 (Logical v)
         $ gr

      graph    = foldr addEdgeGadget base es

      weights  = Map.fromList $
                   [ (Logical v, 1) | v <- logicals ]
                ++ concat [ [(EdgeA u v 1, 2), (EdgeA u v 2, 2)] | (u, v) <- es ]

      offset   = 2 * fromIntegral (length es)
  in Gadget graph weights logicals offset

-- | Decode: restrict a (measured) independent set of @A@ to its logical atoms,
-- recovering a subset of @V'@.
decodeLogical :: Ord a => Set (GVert a) -> Set a
decodeLogical = Set.fromList . concatMap keep . Set.toList
  where
    keep (Logical v) = [v]
    keep _           = []
