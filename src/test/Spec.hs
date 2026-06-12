-- | Validation suite: check the polynomial reduction stages against the
-- brute-force oracle, exhaustively on all small graphs.
module Main (main) where

import           Control.Monad    (forM_, unless)
import           Data.Bits        (testBit)
import qualified Data.Map         as Map
import qualified Data.Set         as Set
import           System.Directory (createDirectoryIfMissing)
import           System.Exit      (exitFailure)

import           UDGColor.Gadget
import           UDGColor.Graph
import           UDGColor.Layout
import           UDGColor.Oracle
import           UDGColor.Stage1
import           UDGColor.Viz

-- | All labelled simple graphs on @n@ vertices @0..n-1@, by choosing a subset
-- of the possible edges.
allGraphs :: Int -> [Graph Int]
allGraphs n =
  let pairs = [ (i, j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1] ]
      m     = length pairs
  in [ foldr addVertex
              (fromEdges [ p | (b, p) <- zip [0 ..] pairs, testBit mask b ])
              [0 .. n - 1]
     | mask <- [0 .. (2 ^ m) - 1 :: Int] ]

-- A single named check, returns (description, passed?).
type Check = (String, Bool)

-- | Theorem (Stage-1 exactness): for every graph and every k,
--   alpha(G') = n  <=>  G is k-colorable,  and  alpha(G') <= n always.
-- Plus: when k-colorable, the witnessing MIS decodes to a /proper/ coloring,
-- and the least k with alpha(G')=n equals chromatic(G).
stage1Checks :: Int -> [Check]
stage1Checks n = concatMap perGraph (zip [0 :: Int ..] (allGraphs n))
  where
    perGraph (idx, g) =
      let tag s = "n=" ++ show n ++ " g#" ++ show idx ++ ": " ++ s
          ks    = [1 .. n]
          exact k =
            let gp = colorChoiceGraph k g
                a  = independenceNumber gp
            in ( tag ("alpha(G')=n <=> k-col (k=" ++ show k ++ ")")
               , (a == order g) == isKColorable k g && a <= order g )
          decodes k =
            let gp  = colorChoiceGraph k g
            in if isKColorable k g
                 then let mis = maxIndependentSet gp
                      in case decodeColoring g mis of
                           Just c  -> ( tag ("decode proper (k=" ++ show k ++ ")")
                                      , isProperColoring g c )
                           Nothing -> ( tag ("decode full (k=" ++ show k ++ ")")
                                      , False )
                 else (tag "n/a", True)
          chromMatches =
            let viaStage1 =
                  case [ k | k <- ks, independenceNumber (colorChoiceGraph k g) == order g ] of
                    (k : _) -> k
                    []      -> 0
            in ( tag "chromatic sweep matches oracle"
               , order g == 0 || viaStage1 == chromatic g )
      in chromMatches : concat [ [exact k, decodes k] | k <- ks ]

-- | Theorem (Stage-2 gadget interface): for the gadget A of an instance G'
--   (here G' is taken to be the small graph itself, unit weights),
--   MWIS(A) = alpha(G') + C,  and the logical-atom restriction of an MWIS of A
--   is a maximum independent set of G'.
gadgetChecks :: Int -> [Check]
gadgetChecks n = concatMap perGraph (zip [0 :: Int ..] (allGraphs n))
  where
    perGraph (idx, g) =
      let gad       = gadgetize g
          tag s     = "gadget n=" ++ show n ++ " g#" ++ show idx ++ ": " ++ s
          val       = mwisValue (gWeights gad) (gGraph gad)
          predicted = fromIntegral (independenceNumber g) + gOffset gad
          dec       = decodeLogical (maxWeightIS (gWeights gad) (gGraph gad))
      in [ ( tag "MWIS(A) = alpha(G') + C", val == predicted )
         , ( tag "decode is a max IS of G'"
           , isIndependent dec g && Set.size dec == independenceNumber g ) ]

-- | Theorem-adjacent invariants of the heuristic layout layer (Stage 3). The
-- layout cannot affect correctness, so these check the two things it must
-- guarantee: H6's minimum feasible radius realizes /every/ prescribed edge
-- (no missing edges), and H1's fixed-budget descent does not increase the loss
-- over its eigenmap initialization.
layoutChecks :: Int -> [Check]
layoutChecks n = concatMap perGraph (zip [0 :: Int ..] (allGraphs n))
  where
    perGraph (idx, g) =
      let ag    = gGraph (gadgetize g)
          lay   = layoutGadget defaultParams ag
          pos   = lPos lay
          r     = lRadius lay
          tag s = "layout n=" ++ show n ++ " g#" ++ show idx ++ ": " ++ s
          (l0, lN) = traceEnds (lTrace lay)
      in [ ( tag "r* realizes all prescribed edges (missing = 0)"
           , null (missingEdges pos r ag) )
         , ( tag "descent does not increase loss"
           , lN <= l0 + 1e-6 )
         ]

-- | First and last of a (possibly empty) loss trace, total and partial-free.
traceEnds :: [Double] -> (Double, Double)
traceEnds []          = (0, 0)
traceEnds xs@(x0 : _) = (x0, foldl (\_ y -> y) x0 xs)

-- | Spot-check known chromatic numbers, independent of the reduction.
namedChecks :: [Check]
namedChecks =
  [ ("chi(P4)=2",            chromatic (path 4) == 2)
  , ("chi(C5)=3",            chromatic (cycleGraph 5) == 3)
  , ("chi(C6)=2",            chromatic (cycleGraph 6) == 2)
  , ("chi(K4)=4",            chromatic (complete 4) == 4)
  , ("chi(K3,3)=2",          chromatic (completeBipartite 3 3) == 2)
  , ("chi(star K1,6)=2",     chromatic (star 6) == 2)
  , ("alpha(K5)=1",          independenceNumber (complete 5) == 1)
  , ("alpha(empty 5)=5",     independenceNumber (emptyGraph 5) == 5)
  , ("chi(bowtie)=3",        chromatic bowtie == 3)
  , ("chi(triangleChain 4)=3", chromatic (triangleChain 4) == 3)
  ]

-- | Precolored encoding sanity (decomposition Prop. 4.2 shape):
-- on the bowtie with cut vertex 0 pinned, the second triangle still 3-colors.
precolorChecks :: [Check]
precolorChecks =
  let g   = bowtie
      -- pin the cut vertex 0 to color 1; alpha should still equal n=5 at k=3
      beta = Map.fromList [(0, 1)]
      gp   = colorChoiceGraphPrecolored 3 g beta
      a    = independenceNumber gp
  in [ ("bowtie precolored(0=1) k=3: alpha=n", a == order g)
     , ("bowtie precolored(0=1) k=2: infeasible",
        independenceNumber (colorChoiceGraphPrecolored 2 g beta) < order g)
     ]

-- ── Per-example stage dump ──────────────────────────────────────────────────────
--
-- For each example we write one SVG per pipeline stage into viz/test_N/, so the
-- effect of every transformation can be inspected on its own. info.txt lists the
-- numbers to validate the stage against.

vizRoot :: FilePath
vizRoot = "viz"

-- | An example instance: a name, a palette size k, and the input graph.
data Example = Example String Int (Graph Int)

examples :: [Example]
examples =
  [ Example "path4"          2 (path 4)
  , Example "cycle4"         2 (cycleGraph 4)
  , Example "cycle5"         3 (cycleGraph 5)
  , Example "triangle"       3 (complete 3)
  , Example "complete4"      4 (complete 4)
  , Example "bipartite33"    2 (completeBipartite 3 3)
  , Example "star6"          2 (star 6)
  , Example "bowtie"         3 bowtie
  , Example "triangleChain3" 3 (triangleChain 3)
  , Example "path3"          2 (path 3)
  ]

-- | Schematic drawing of the gadget graph A: logical atoms (labelled) on a
-- circle, the two gadget atoms of each edge drawn along the chord between its
-- endpoints. (This is the combinatorial structure, not a metric UD layout.)
gadgetStageSvg :: Gadget (Slot Int) -> String
gadgetStageSvg gad = toSvgWith lbl allPos rad (gGraph gad)
  where
    logs  = gLogical gad
    n     = length logs
    r     = max 170 (fromIntegral n * 24) :: Double
    ang i = 2 * pi * fromIntegral i / fromIntegral (max 1 n)
    logPos = Map.fromList
      [ (s, (r * cos (ang i), r * sin (ang i))) | (i, s) <- zip [0 :: Int ..] logs ]
    look s = Map.findWithDefault (0, 0) s logPos
    lerp (ax, ay) (bx, by) t = (ax + (bx - ax) * t, ay + (by - ay) * t)
    -- bow each gadget chain outward (away from the circle centre) so chords
    -- that would otherwise pile up through the middle separate visually.
    bow (ax, ay) (bx, by) t =
      let (mx, my) = lerp (ax, ay) (bx, by) t
          (cx, cy) = lerp (ax, ay) (bx, by) 0.5
          len      = sqrt (cx * cx + cy * cy)
          (ox, oy) = if len < 1e-6 then (0, 0) else (cx / len, cy / len)
          amt      = 0.16 * r
      in (mx + ox * amt, my + oy * amt)
    posOf v = case v of
      Logical s   -> look s
      EdgeA u w 1 -> bow (look u) (look w) 0.34
      EdgeA u w _ -> bow (look u) (look w) 0.66
    allPos = Map.fromList [ (v, posOf v) | v <- Set.toList (vertices (gGraph gad)) ]
    lbl v  = case v of Logical s -> labelSlot s; _ -> ""
    rad v  = case v of Logical _ -> 14; _ -> 7

-- | Stage 3 (heuristic layout optimizer): the gadget atoms placed at the
-- coordinates the optimizer found, with the blockade radius @r*@ and the
-- realized/false/missing edge classification drawn.
layoutStageSvg :: Gadget (Slot Int) -> Layout (GVert (Slot Int)) -> String
layoutStageSvg gad lay =
  toSvgLayout lbl (lPos lay) rad (lRadius lay) solid missing false_ verts
  where
    ag      = gGraph gad
    r       = lRadius lay
    pos     = lPos lay
    verts   = Set.toList (vertices ag)
    missing = missingEdges pos r ag
    missSet = Set.fromList missing
    solid   = [ e | e <- Set.toList (edges ag), Set.notMember e missSet ]
    false_  = falseEdges pos r ag
    lbl v   = case v of Logical s -> labelSlot s; _ -> ""
    rad v   = case v of Logical _ -> 9; _ -> 4

-- | Dump every stage of one example to viz/test_N/.
writeExample :: Int -> Example -> IO ()
writeExample idx (Example nm k g) = do
  let dir = vizRoot ++ "/test_" ++ show idx
  createDirectoryIfMissing True dir
  -- Stage 0: the input graph G.
  writeFile (dir ++ "/0_input.svg") (toSvg labelInt Nothing g)
  -- Stage 1: the color-choice graph G' (color -> independent set).
  let gp = colorChoiceGraph k g
  writeFile (dir ++ "/1_colorchoice.svg") (toSvg labelSlot Nothing gp)
  -- Stage 2: the gadget graph A (independent set -> MWIS instance).
  let gad = gadgetize gp
      ag  = gGraph gad
      c   = round (gOffset gad) :: Int
  writeFile (dir ++ "/2_gadget.svg") (gadgetStageSvg gad)
  -- Stage 3: the heuristic layout optimizer (atom coordinates + blockade r*).
  let lay     = layoutGadget defaultParams ag
      pos     = lPos lay
      r       = lRadius lay
      nMiss   = length (missingEdges pos r ag)
      nFalse  = length (falseEdges pos r ag)
      nReal   = size ag - nMiss
      spacing = minSpacing pos ag
      (loss0, lossN) = traceEnds (lTrace lay)
      r2 x    = fromIntegral (round (x * 100) :: Int) / 100 :: Double
  writeFile (dir ++ "/3_layout.svg") (layoutStageSvg gad lay)
  -- Numbers to validate the transformations.
  writeFile (dir ++ "/info.txt") $ unlines
    [ "example test_" ++ show idx ++ ": " ++ nm
    , "k = " ++ show k
    , ""
    , "stage 0  input G        : |V|=" ++ show (order g) ++ "  |E|=" ++ show (size g)
    , "stage 1  color-choice G': |V'|=" ++ show (order gp) ++ "  |E'|=" ++ show (size gp)
    , "         expected |V'| = n*k = " ++ show (order g) ++ "*" ++ show k
                                        ++ " = " ++ show (order g * k)
    , "stage 2  gadget A       : |V(A)|=" ++ show (order ag) ++ "  |E(A)|=" ++ show (size ag)
    , "         logical atoms = " ++ show (length (gLogical gad))
                                  ++ " ; gadget atoms = " ++ show (order ag - length (gLogical gad))
    , "         offset C = 2|E'| = " ++ show c
    , "stage 3  layout (H4->H1->H5->H6) : r* = " ++ show (r2 r)
    , "         prescribed realized = " ++ show nReal ++ "/" ++ show (size ag)
                                        ++ " ; missing = " ++ show nMiss
                                        ++ " ; false edges = " ++ show nFalse
    , "         loss " ++ show (r2 loss0) ++ " -> " ++ show (r2 lossN)
                       ++ " (" ++ show (length (lTrace lay) - 1) ++ " steps) ; "
                       ++ "repair steps = " ++ show (lRepairs lay)
                       ++ " ; min spacing = " ++ show (r2 spacing)
                       ++ " (floor " ++ show (pDmin defaultParams) ++ ")"
    , ""
    , "validation:"
    , "  alpha(G') = " ++ show (independenceNumber gp)
                       ++ "   (theorem: = n iff k-colorable; n = " ++ show (order g) ++ ")"
    , "  predicted MWIS(A) = alpha(G') + C = " ++ show (independenceNumber gp)
                       ++ " + " ++ show c ++ " = " ++ show (independenceNumber gp + c)
    , "  G is " ++ show k ++ "-colorable: " ++ show (isKColorable k g)
    , "  layout: missing=0 (r* realizes every prescribed edge): " ++ show (nMiss == 0)
    , "  layout: descent non-increasing: " ++ show (lossN <= loss0)
    ]

main :: IO ()
main = do
  createDirectoryIfMissing True vizRoot
  forM_ (zip [1 ..] examples) (uncurry writeExample)
  putStrLn $ "wrote " ++ show (length examples)
                      ++ " examples (one folder per case) to " ++ vizRoot ++ "/test_N/"
  let checks = namedChecks
            ++ precolorChecks
            ++ concatMap stage1Checks [0, 1, 2, 3, 4, 5]
            ++ concatMap gadgetChecks [0, 1, 2, 3, 4]
            ++ concatMap layoutChecks [0, 1, 2, 3, 4]
      failures = [ d | (d, ok) <- checks, not ok ]
      total    = length checks
  putStrLn $ "ran " ++ show total ++ " checks"
  mapM_ (\d -> putStrLn ("FAIL: " ++ d)) failures
  unless (null failures) $ do
    putStrLn $ show (length failures) ++ " failures"
    exitFailure
  putStrLn "all checks passed"
