-- | Stage 3 (secondary path / heuristic geometry): the __layout optimizer__ of
-- @paper.tex@, Section \"Secondary Path: Heuristic Geometry and the Layout
-- Optimizer\".
--
-- The gadget graph @A@ from "UDGColor.Gadget" fixes the required adjacency
-- /exactly/; this module solves the residual /geometric realization/ problem:
-- place the atoms of @A@ in the plane so that the realized unit-disk graph
-- @UDG(p,r)@ matches the prescribed gadget adjacency, subject to a hardware
-- spacing floor @d_min@. Per Theorem \"Supergraph inflation is unbounded\" the
-- heuristics cannot affect /correctness/ (the gadget structure and weights are
-- fixed); a poor layout can only cost feasibility or analog-solve quality. So
-- the optimizer minimizes an /adjacency-realization/ loss, not a
-- @G@-mimicking loss.
--
-- The seven heuristics of the paper map onto the pipeline here as:
--
--   * __H4__ Laplacian-eigenmap init — 'fiedlerInit': @p0(v)=(phi2(v),phi3(v))@
--     from the two smallest non-trivial Laplacian eigenvectors (power iteration
--     on @cI - L@, deflating the constant vector), giving descent a good basin.
--   * __H1__ Geometric-loss minimization — 'descend': fixed-budget gradient
--     descent on the loss @L_layout(p,r)@ of eq. (layoutloss). The budget @T@ is
--     a fixed @poly(|V(A)|)@ (not \"until converged\"), so the @O(T|V(A)|^2)@
--     cost is honest.
--   * __H5__ Monotone local repair — 'repair': fix residual adjacency
--     violations by moves gated on strict decrease of the integer potential
--     @Phi = #violations@, giving a genuine polynomial step bound.
--   * __H6__ Radius sweep — 'minFeasibleRadius': @r* = max_{e in E_A} d_uv@ is
--     the smallest radius realizing every prescribed edge.
--   * __H7__ Quality as evaluation, not objective — 'falseEdges' / 'missingEdges'
--     are piecewise-constant in @(p,r)@ and are /reported/, never differentiated.
--
-- Caveat (matching "UDGColor.Gadget"): this is a generic spring/eigenmap
-- realizer, not the Nguyen copy/crossing-gadget construction that guarantees a
-- /zero-false-edge/ realization exists. On the dense color-choice instances it
-- will generally leave residual false edges; those are reported by 'falseEdges'
-- as the geometric-realization quality, which is the deferred engineering fork.
module UDGColor.Layout
  ( Pt
  , Params(..)
  , defaultParams
  , Layout(..)
  , layoutGadget
    -- * Heuristic components (exposed for the validation harness)
  , fiedlerInit
  , descend
  , repair
  , minFeasibleRadius
  , layoutLoss
    -- * Realized adjacency / quality (H7 evaluation)
  , dist
  , realizedEdges
  , falseEdges
  , missingEdges
  , minSpacing
  ) where

import           Data.List (tails)
import           Data.Map  (Map)
import qualified Data.Map  as Map
import qualified Data.Set  as Set

import           UDGColor.Graph

-- | A point in the layout plane.
type Pt = (Double, Double)

-- | Optimizer parameters. Defaults are tuned for the small validation
-- instances; the iteration budget @pBudget@ is the fixed @poly(n)@ of H1.
data Params = Params
  { pLambda :: Double  -- ^ false-edge penalty weight (lambda in the loss)
  , pEps    :: Double  -- ^ separation margin for non-edges (epsilon)
  , pDmin   :: Double  -- ^ hardware spacing floor (d_min)
  , pMu     :: Double  -- ^ spacing-floor penalty weight (mu)
  , pEta    :: Double  -- ^ gradient-descent step size
  , pBudget :: Int -> Int -- ^ descent iteration budget T as a function of |V(A)|
  , pRepair :: Int     -- ^ cap on H5 local-repair steps
  }

-- | The repair cap 'pRepair' is a flat step budget; 'layoutGadget' overrides it
-- with the @O(|V(A)|^2)@ bound of H5 once it knows the instance size.
defaultParams :: Params
defaultParams = Params
  { pLambda = 1.0
  , pEps    = 0.25
  , pDmin   = 0.5
  , pMu     = 1.0
  , pEta    = 0.05
  , pBudget = \n -> min 150 (10 * n) -- fixed poly(n), capped for the harness
  , pRepair = 0                     -- set per-instance in 'layoutGadget'
  }

-- | The optimizer output: coordinates, the selected (minimum feasible) radius,
-- the per-iteration loss trace (for monotonicity checks), and the number of
-- accepted H5 repair steps.
data Layout a = Layout
  { lPos     :: Map a Pt
  , lRadius  :: Double
  , lTrace   :: [Double]
  , lRepairs :: Int
  } deriving (Show)

-- ── Vector helpers over @Map a Double@ ───────────────────────────────────────────

dotV :: Ord a => Map a Double -> Map a Double -> Double
dotV x y = sum (Map.elems (Map.intersectionWith (*) x y))

axpyV :: Ord a => Double -> Map a Double -> Map a Double -> Map a Double
axpyV a x y = Map.unionWith (+) (Map.map (* a) x) y

normalizeV :: Ord a => Map a Double -> Map a Double
normalizeV x = let nrm = sqrt (dotV x x) in if nrm < 1e-12 then x else Map.map (/ nrm) x

-- | Project @x@ onto the orthogonal complement of the (already orthonormal) set
-- @bs@: @x - sum_b <x,b> b@.
deflate :: Ord a => [Map a Double] -> Map a Double -> Map a Double
deflate bs x = foldr (\b acc -> axpyV (negate (dotV x b)) b acc) x bs

-- ── H4: Laplacian eigenmap initialization ────────────────────────────────────────

-- | Action of @M = cI - L@ on a vector, where @L = D - Adj@ is the graph
-- Laplacian and @c@ shifts @L@'s /smallest/ eigenvalues to @M@'s /largest/, so
-- power iteration recovers the bottom of @L@'s spectrum. Concretely
-- @(M x)(v) = (c - deg v) x(v) + sum_{u ~ v} x(u)@.
applyM :: Ord a => Graph a -> Double -> Map a Double -> Map a Double
applyM g c x = Map.fromList
  [ (v, (c - fromIntegral (degree v g)) * xv
        + sum [ Map.findWithDefault 0 u x | u <- Set.toList (neighbors v g) ])
  | v <- Set.toList (vertices g), let xv = Map.findWithDefault 0 v x ]

-- | One Laplacian eigenvector via deflated power iteration: iterate @M@, keep
-- the result orthogonal to @bs@ (the constant vector plus already-found
-- eigenvectors), normalize. @iters@ is fixed.
powerVec :: Ord a => Graph a -> Double -> Int -> [Map a Double] -> Map a Double -> Map a Double
powerVec g c iters bs = go iters
  where
    go 0 x = x
    go n x = go (n - 1) (normalizeV (deflate bs (applyM g c x)))

-- | H4. Place each atom at @(phi2(v), phi3(v))@ — the Fiedler vector and the
-- next Laplacian eigenvector — then rescale so the mean prescribed-edge length
-- is one. Adjacent atoms land near, well-separated parts far apart.
fiedlerInit :: Ord a => Graph a -> Map a Pt
fiedlerInit g
  | n == 0    = Map.empty
  | otherwise =
      let c       = 2 * fromIntegral (maximum (1 : [ degree v g | v <- verts ]))
          iters   = 60
          ones    = normalizeV (Map.fromList [ (v, 1) | v <- verts ])
          seed k  = Map.fromList [ (v, sin (fromIntegral (i * k + 1)))
                                 | (i, v) <- zip [1 :: Int ..] verts ]
          phi2    = powerVec g c iters [ones]       (normalizeV (deflate [ones] (seed 1)))
          phi3    = powerVec g c iters [ones, phi2] (normalizeV (deflate [ones, phi2] (seed 7)))
          raw     = Map.fromList [ (v, ( Map.findWithDefault 0 v phi2
                                       , Map.findWithDefault 0 v phi3 )) | v <- verts ]
          s       = meanEdgeLen raw
      in Map.map (\(x, y) -> (x / s, y / s)) raw
  where
    verts = Set.toAscList (vertices g)
    n     = length verts
    meanEdgeLen pos =
      case [ dist pos u v | (u, v) <- Set.toList (edges g) ] of
        [] -> 1
        ds -> let m = sum ds / fromIntegral (length ds) in if m < 1e-9 then 1 else m

-- ── Geometry / H7 evaluation ─────────────────────────────────────────────────────

dist :: Ord a => Map a Pt -> a -> a -> Double
dist pos u v =
  let (ux, uy) = Map.findWithDefault (0, 0) u pos
      (vx, vy) = Map.findWithDefault (0, 0) v pos
  in sqrt ((ux - vx) ^ (2 :: Int) + (uy - vy) ^ (2 :: Int))

-- | All vertex pairs.
allPairs :: Ord a => Graph a -> [(a, a)]
allPairs g = [ (u, v) | (u : rest) <- tails (Set.toAscList (vertices g)), v <- rest ]

-- | H6. The minimum feasible radius @r* = max_{e in E_A} d_uv@: the smallest
-- radius under which every prescribed edge is realized.
minFeasibleRadius :: Ord a => Map a Pt -> Graph a -> Double
minFeasibleRadius pos g =
  case [ dist pos u v | (u, v) <- Set.toList (edges g) ] of
    [] -> 0
    ds -> maximum ds

-- | Pairs realized as unit-disk edges at radius @r@ (distance @<= r@).
realizedEdges :: Ord a => Map a Pt -> Double -> Graph a -> [(a, a)]
realizedEdges pos r g = [ (u, v) | (u, v) <- allPairs g, dist pos u v <= r ]

-- | False edges: realized but not prescribed (H7 quality measure).
falseEdges :: Ord a => Map a Pt -> Double -> Graph a -> [(a, a)]
falseEdges pos r g =
  [ (u, v) | (u, v) <- allPairs g, not (hasEdge u v g), dist pos u v <= r ]

-- | Missing edges: prescribed but not realized at @r@. Empty when @r >= r*@.
missingEdges :: Ord a => Map a Pt -> Double -> Graph a -> [(a, a)]
missingEdges pos r g =
  [ (u, v) | (u, v) <- Set.toList (edges g), dist pos u v > r ]

-- | Closest pair distance (checked against the spacing floor @d_min@).
minSpacing :: Ord a => Map a Pt -> Graph a -> Double
minSpacing pos g =
  case [ dist pos u v | (u, v) <- allPairs g ] of
    [] -> 1 / 0
    ds -> minimum ds

-- ── H1: geometric-loss gradient descent ──────────────────────────────────────────

-- | The layout loss of eq. (layoutloss): prescribed edges want @d <= r@,
-- non-edges want @d >= r + eps@, all pairs want @d >= d_min@.
layoutLoss :: Ord a => Params -> Map a Pt -> Double -> Graph a -> Double
layoutLoss pr pos r g =
    sum [ sq (max 0 (dist pos u v - r))            | (u, v) <- Set.toList (edges g) ]
  + pLambda pr * sum [ sq (max 0 (r + pEps pr - d)) | (u, v) <- nonEdges, let d = dist pos u v ]
  + pMu pr     * sum [ sq (max 0 (pDmin pr - d))    | (u, v) <- pairs,    let d = dist pos u v ]
  where
    pairs    = allPairs g
    nonEdges = [ (u, v) | (u, v) <- pairs, not (hasEdge u v g) ]
    sq x     = x * x

-- | One descent step at step size @eta@ and /fixed/ target radius @r@:
-- accumulate the negative gradient of 'layoutLoss' as a force per atom and move.
-- Holding @r@ fixed (H1 optimizes @p@; H6 selects the radius afterwards) keeps
-- the loss landscape smooth, so the backtracking descent actually makes
-- progress instead of stalling on the jumpy adaptive-@r@ objective.
forceStep :: Ord a => Params -> Graph a -> Double -> Double -> Map a Pt -> Map a Pt
forceStep pr g r eta pos =
  let forces = Map.fromListWith add2 (concatMap pairForce (allPairs g))
      add2 (a, b) (c, d) = (a + c, b + d)
  in Map.mapWithKey
       (\v p -> step p (Map.findWithDefault (0, 0) v forces)) pos
  where
    step (x, y) (fx, fy) = (x + eta * fx, y + eta * fy)
    -- Force on (u,v): list of (vertex, force) contributions (Newton's 3rd law).
    pairForce (u, v) =
      let d        = dist pos u v
          (ux, uy) = Map.findWithDefault (0, 0) u pos
          (vx, vy) = Map.findWithDefault (0, 0) v pos
          d'       = max d 1e-9
          ex       = (vx - ux) / d'              -- unit vector u -> v
          ey       = (vy - uy) / d'
          prescribed = hasEdge u v g
          -- magnitude of the attractive(+)/repulsive(-) force along (u->v)
          mag
            | prescribed                = 2 * max 0 (d - r)               -- pull together
            | d < r + pEps pr           = negate (2 * pLambda pr * (r + pEps pr - d)) -- push apart
            | otherwise                 = 0
          floorMag = if d < pDmin pr then negate (2 * pMu pr * (pDmin pr - d)) else 0
          m        = mag + floorMag
          fu       = (m * ex, m * ey)            -- on u, toward v if m>0
          fv       = (negate (m * ex), negate (m * ey))
      in [ (u, fu), (v, fv) ]

-- | H1. Run up to a fixed budget of descent steps with backtracking line
-- search: at each step try @eta, eta/2, eta/4, eta/8@ and accept the first that
-- strictly decreases 'layoutLoss'; if none does, the iterate is a (local)
-- stationary point and we stop early. This makes the loss trace genuinely
-- non-increasing (a real guarantee, not a hope) and converges fast on the small
-- instances. The budget @T = pBudget |V(A)|@ remains a fixed @poly(n)@ cap.
descend :: Ord a => Params -> Graph a -> Map a Pt -> (Map a Pt, [Double])
descend pr g p0 = go (pBudget pr (order g)) p0 [loss p0]
  where
    -- Fixed target radius for the descent: a notch above the typical prescribed
    -- edge length of the (unit-scaled) eigenmap init. H6 reselects r* at the end.
    rTgt   = 1.3 * meanPrescribed p0
    loss p = layoutLoss pr p rTgt g
    etas   = takeWhile (> pEta pr / 16) (iterate (/ 2) (pEta pr))
    go 0 p tr = (p, reverse tr)
    go n p tr =
      let l0    = loss p
          cands = [ (lp, p') | eta <- etas, let p' = forceStep pr g rTgt eta p
                             , let lp = loss p', lp < l0 ]
      in case cands of
           ((lp, p') : _) -> go (n - 1) p' (lp : tr)
           []             -> (p, reverse tr)   -- stationary: stop
    meanPrescribed p =
      case [ dist p u v | (u, v) <- Set.toList (edges g) ] of
        [] -> 1
        ds -> let s = foldr (+) 0 ds / fromIntegral (length ds)
              in if s < 1e-9 then 1 else s

-- ── H5: monotone local repair ────────────────────────────────────────────────────

-- | The integer potential @Phi = #adjacency violations@ at radius @r@: false
-- edges plus missing edges. Repair accepts a move only if @Phi@ strictly
-- decreases, and @Phi >= 0@ is integer, so termination is guaranteed within
-- @Phi_0@ steps.
violations :: Ord a => Map a Pt -> Double -> Graph a -> Int
violations pos r g = length (falseEdges pos r g) + length (missingEdges pos r g)

-- | H5. Greedily nudge the endpoints of the worst violations apart/together
-- along their connecting line, accepting a move only when the integer potential
-- strictly drops. Capped at 'pRepair' steps (a genuine polynomial bound).
repair :: Ord a => Params -> Graph a -> Map a Pt -> (Map a Pt, Int)
repair pr g = go (pRepair pr) 0
  where
    go 0    acc pos = (pos, acc)
    go fuel acc pos =
      let r    = minFeasibleRadius pos g
          phi0 = violations pos r g
      in if phi0 == 0
           then (pos, acc)
           else case [ pos' | (u, v) <- take scan (worstFirst pos r)
                            , pos' <- [ nudge pos u v (hasEdge u v g) ]
                            , violations pos' (minFeasibleRadius pos' g) g < phi0 ] of
                  (pos' : _) -> go (fuel - 1) (acc + 1) pos'
                  []         -> (pos, acc)   -- local optimum within the window: stop
    -- only probe a bounded window of violations per step, so each accepted
    -- repair costs O(scan * |V|^2) rather than O(|violations| * |V|^2).
    scan = 8 :: Int
    -- order candidate violations: false edges (push apart) then missing (pull in)
    worstFirst pos r = falseEdges pos r g ++ missingEdges pos r g
    -- move u and v symmetrically along their line by a small delta; sign chosen
    -- to separate (false edge) or close (missing edge).
    nudge pos u v prescribed =
      let d        = max (dist pos u v) 1e-9
          (ux, uy) = Map.findWithDefault (0, 0) u pos
          (vx, vy) = Map.findWithDefault (0, 0) v pos
          ex       = (vx - ux) / d
          ey       = (vy - uy) / d
          step     = (if prescribed then negate 1 else 1) * 0.5 * pDmin pr
      in Map.insert u (ux - step * ex, uy - step * ey)
       $ Map.insert v (vx + step * ex, vy + step * ey) pos

-- ── Driver ───────────────────────────────────────────────────────────────────────

-- | Run the full layout pipeline on a gadget graph: H4 init, H1 descent, H5
-- repair, H6 radius selection. H5's termination is guaranteed within
-- @Phi_0 = O(|V|^2)@ accepted steps (the integer-potential bound); for the
-- harness we cap further at @6|V|@, since repair is a local touch-up and these
-- gadget instances are not exactly UD-realizable without true Nguyen gadgets.
layoutGadget :: Ord a => Params -> Graph a -> Layout a
layoutGadget pr0 g =
  let pr        = pr0 { pRepair = 6 * order g }
      p0        = fiedlerInit g
      (p1, tr)  = descend pr g p0
      (p2, rps) = repair pr g p1
      r         = minFeasibleRadius p2 g
  in Layout { lPos = p2, lRadius = r, lTrace = tr, lRepairs = rps }
