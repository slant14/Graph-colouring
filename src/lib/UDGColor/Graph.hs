-- | Finite simple undirected graphs, parameterised over the vertex type.
--
-- Vertices are an arbitrary 'Ord' type (we use @Int@ for plain graphs and
-- product types like @(v, Int)@ for the color-choice construction). Edges are
-- stored normalised so that the smaller endpoint comes first; this keeps the
-- edge set canonical regardless of insertion order.
module UDGColor.Graph
  ( Graph(..)
  , edge
  , empty
  , fromEdges
  , addVertex
  , addEdge
  , order
  , size
  , hasEdge
  , neighbors
  , degree
  , removeVertex
  , removeClosedNeighborhood
  , inducedSubgraph
    -- * Named graph families
  , path
  , cycleGraph
  , complete
  , completeBipartite
  , star
  , emptyGraph
  , bowtie
  , triangleChain
  ) where

import           Data.Set (Set)
import qualified Data.Set as Set

-- | A finite simple undirected graph.
data Graph a = Graph
  { vertices :: Set a
  , edges    :: Set (a, a) -- ^ normalised: for every @(u,v)@ we have @u < v@
  } deriving (Eq, Show)

-- | Build a normalised edge. A self-loop @edge x x@ is degenerate; callers
-- should avoid it (simple graphs have none).
edge :: Ord a => a -> a -> (a, a)
edge u v = if u <= v then (u, v) else (v, u)

empty :: Graph a
empty = Graph Set.empty Set.empty

-- | Construct a graph from an explicit list of edges (endpoints become
-- vertices automatically).
fromEdges :: Ord a => [(a, a)] -> Graph a
fromEdges = foldr (\(u, v) -> addEdge u v) empty

addVertex :: Ord a => a -> Graph a -> Graph a
addVertex v g = g { vertices = Set.insert v (vertices g) }

-- | Insert an edge, adding its endpoints if necessary. Self-loops are ignored.
addEdge :: Ord a => a -> a -> Graph a -> Graph a
addEdge u v g
  | u == v    = addVertex u g
  | otherwise = g { vertices = Set.insert u (Set.insert v (vertices g))
                  , edges    = Set.insert (edge u v) (edges g)
                  }

order :: Graph a -> Int
order = Set.size . vertices

size :: Graph a -> Int
size = Set.size . edges

hasEdge :: Ord a => a -> a -> Graph a -> Bool
hasEdge u v g = Set.member (edge u v) (edges g)

neighbors :: Ord a => a -> Graph a -> Set a
neighbors v g =
  Set.fromList [ if a == v then b else a
               | (a, b) <- Set.toList (edges g), a == v || b == v ]

degree :: Ord a => a -> Graph a -> Int
degree v = Set.size . neighbors v

-- | Delete a vertex and every edge touching it.
removeVertex :: Ord a => a -> Graph a -> Graph a
removeVertex v g = Graph
  { vertices = Set.delete v (vertices g)
  , edges    = Set.filter (\(a, b) -> a /= v && b /= v) (edges g)
  }

-- | Delete a vertex together with all of its neighbors (the closed
-- neighborhood @N[v]@). Used by the branch-and-bound independence routine.
removeClosedNeighborhood :: Ord a => a -> Graph a -> Graph a
removeClosedNeighborhood v g =
  let kill = Set.insert v (neighbors v g)
  in Graph
       { vertices = vertices g `Set.difference` kill
       , edges    = Set.filter (\(a, b) -> not (Set.member a kill || Set.member b kill)) (edges g)
       }

-- | The subgraph induced by a vertex subset.
inducedSubgraph :: Ord a => Set a -> Graph a -> Graph a
inducedSubgraph keep g = Graph
  { vertices = Set.intersection keep (vertices g)
  , edges    = Set.filter (\(a, b) -> Set.member a keep && Set.member b keep) (edges g)
  }

-- ── Named families (vertices are @Int@, 0-indexed) ────────────────────────────

-- | Path on @n@ vertices @0..n-1@.
path :: Int -> Graph Int
path n = fromEdges [ (i, i + 1) | i <- [0 .. n - 2] ] `orVertices` n

-- | Cycle on @n@ vertices (@n >= 3@).
cycleGraph :: Int -> Graph Int
cycleGraph n = fromEdges ((n - 1, 0) : [ (i, i + 1) | i <- [0 .. n - 2] ])

-- | Complete graph @K_n@.
complete :: Int -> Graph Int
complete n = fromEdges [ (i, j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1] ]

-- | Complete bipartite @K_{a,b}@; left part @0..a-1@, right part @a..a+b-1@.
completeBipartite :: Int -> Int -> Graph Int
completeBipartite a b =
  fromEdges [ (i, a + j) | i <- [0 .. a - 1], j <- [0 .. b - 1] ]

-- | Star @K_{1,n}@: center @0@, leaves @1..n@. The impossibility-result graph.
star :: Int -> Graph Int
star n = completeBipartite 1 n

-- | Edgeless graph on @n@ vertices.
emptyGraph :: Int -> Graph Int
emptyGraph n = foldr addVertex empty [0 .. n - 1]

-- | Two triangles sharing the single cut vertex @0@ (decomposition Example A).
-- Vertices: 0 = c, {1,2} and {3,4} are the two triangle wings.
bowtie :: Graph Int
bowtie = fromEdges [(1, 2), (1, 0), (2, 0), (3, 4), (3, 0), (4, 0)]

-- | @t@ triangles glued in a line, sharing one cut vertex each
-- (decomposition Example B). Vertices @0..2t@; triangle @j@ is
-- @{2j, 2j+1, 2j+2}@. @n = 2t+1@ grows but every piece is a triangle.
triangleChain :: Int -> Graph Int
triangleChain t = fromEdges $ concat
  [ [(2 * j, 2 * j + 1), (2 * j + 1, 2 * j + 2), (2 * j, 2 * j + 2)]
  | j <- [0 .. t - 1] ]

-- internal: ensure isolated trailing vertices exist for 'path'
orVertices :: Graph Int -> Int -> Graph Int
orVertices g n = foldr addVertex g [0 .. n - 1]
