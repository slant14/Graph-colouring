-- | Lightweight, dependency-free graph rendering for eyeballing the
-- constructions: standalone SVG (circular layout, viewable in any browser),
-- Graphviz DOT (render with @dot -Tsvg@ if Graphviz is installed), and a plain
-- ASCII adjacency matrix for terminal output.
--
-- All renderers take a labelling function @a -> String@ (so they work for plain
-- @Int@ graphs and for @(v, Int)@ color-choice slots alike) and an optional
-- coloring @Map a Int@ that fills nodes by color class.
module UDGColor.Viz
  ( -- * Renderers
    toSvg
  , toSvgWith
  , toSvgLayout
  , toDot
  , toAscii
    -- * Labellers
  , labelInt
  , labelSlot
    -- * Palette
  , palette
  ) where

import           Data.List (intercalate)
import           Data.Map  (Map)
import qualified Data.Map  as Map
import qualified Data.Set  as Set

import           UDGColor.Graph

-- | A distinct fill color per color class (1-indexed). Wraps if exceeded.
palette :: Int -> String
palette i = cycle cols !! max 0 (i - 1)
  where
    cols = [ "#e57373", "#64b5f6", "#fff176", "#81c784", "#ba68c8"
           , "#ffb74d", "#4db6ac", "#f06292", "#a1887f", "#90a4ae" ]

labelInt :: Int -> String
labelInt = show

-- | Label a color-choice slot @(v, i)@ as @"v=i"@.
labelSlot :: Show a => (a, Int) -> String
labelSlot (v, i) = show v ++ "=" ++ show i

-- ── SVG (circular layout) ───────────────────────────────────────────────────────

-- | A standalone SVG document: vertices equally spaced on a circle, edges as
-- straight lines, nodes filled by the optional coloring. Self-contained and
-- immediately viewable.
toSvg :: Ord a => (a -> String) -> Maybe (Map a Int) -> Graph a -> String
toSvg lbl mcol g = unlines $
  [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"" ++ show w
      ++ "\" height=\"" ++ show w ++ "\" viewBox=\"0 0 " ++ show w ++ " " ++ show w ++ "\">"
  , "  <rect width=\"100%\" height=\"100%\" fill=\"white\"/>"
  ]
  ++ edgeLines
  ++ concatMap node verts
  ++ [ "</svg>" ]
  where
    verts = Set.toAscList (vertices g)
    n     = length verts
    r     = max 130 (n * 16)         -- layout radius
    pad   = 40
    w     = 2 * (r + pad)
    cx    = r + pad
    cy    = r + pad
    pos   = Map.fromList
              [ (v, ( round (fromIntegral cx + fromIntegral r * cos (theta k))
                    , round (fromIntegral cy + fromIntegral r * sin (theta k)) ))
              | (k, v) <- zip [0 :: Int ..] verts ]
    theta k = 2 * pi * fromIntegral k / fromIntegral (max 1 n) :: Double

    at v = Map.findWithDefault (cx, cy) v pos :: (Int, Int)

    edgeLines =
      [ "  <line x1=\"" ++ show x1 ++ "\" y1=\"" ++ show y1
          ++ "\" x2=\"" ++ show x2 ++ "\" y2=\"" ++ show y2
          ++ "\" stroke=\"#555\" stroke-width=\"1.5\"/>"
      | (u, v) <- Set.toList (edges g)
      , let (x1, y1) = at u, let (x2, y2) = at v ]

    node v =
      let (x, y) = at v
          fill   = maybe "white" palette (mcol >>= Map.lookup v)
      in [ "  <circle cx=\"" ++ show x ++ "\" cy=\"" ++ show y
             ++ "\" r=\"16\" fill=\"" ++ fill ++ "\" stroke=\"#222\" stroke-width=\"1.5\"/>"
         , "  <text x=\"" ++ show x ++ "\" y=\"" ++ show (y + 4)
             ++ "\" font-size=\"11\" font-family=\"sans-serif\""
             ++ " text-anchor=\"middle\">" ++ xmlEscape (lbl v) ++ "</text>" ]

-- | SVG with caller-supplied coordinates and per-node radii (used to draw the
-- gadget graph: large logical atoms, small gadget atoms, edges as drawn). The
-- view box is fitted to the given positions.
toSvgWith
  :: Ord a
  => (a -> String)            -- ^ node label
  -> Map a (Double, Double)   -- ^ node position
  -> (a -> Double)            -- ^ node radius
  -> Graph a
  -> String
toSvgWith lbl pos rad g = unlines $
  [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"" ++ ii w
      ++ "\" height=\"" ++ ii h ++ "\" viewBox=\"0 0 " ++ ii w ++ " " ++ ii h ++ "\">"
  , "  <rect width=\"100%\" height=\"100%\" fill=\"white\"/>"
  ]
  ++ edgeLines
  ++ concatMap node verts
  ++ [ "</svg>" ]
  where
    verts = Set.toAscList (vertices g)
    at v  = Map.findWithDefault (0, 0) v pos
    xs    = [ fst (at v) | v <- verts ]
    ys    = [ snd (at v) | v <- verts ]
    pad   = 30
    minx  = if null xs then 0 else minimum xs
    miny  = if null ys then 0 else minimum ys
    maxx  = if null xs then 0 else maximum xs
    maxy  = if null ys then 0 else maximum ys
    sx p  = p - minx + pad
    sy p  = p - miny + pad
    w     = maxx - minx + 2 * pad
    h     = maxy - miny + 2 * pad
    ii    = show . (round :: Double -> Int)

    edgeLines =
      [ "  <line x1=\"" ++ ii (sx x1) ++ "\" y1=\"" ++ ii (sy y1)
          ++ "\" x2=\"" ++ ii (sx x2) ++ "\" y2=\"" ++ ii (sy y2)
          ++ "\" stroke=\"#888\" stroke-width=\"1\"/>"
      | (u, v) <- Set.toList (edges g)
      , let (x1, y1) = at u, let (x2, y2) = at v ]

    node v =
      let (x, y) = at v
          r      = rad v
      in [ "  <circle cx=\"" ++ ii (sx x) ++ "\" cy=\"" ++ ii (sy y)
             ++ "\" r=\"" ++ ii r ++ "\" fill=\""
             ++ (if r >= 12 then "white" else "#ddd")
             ++ "\" stroke=\"#222\" stroke-width=\"1\"/>" ]
      ++ [ "  <text x=\"" ++ ii (sx x) ++ "\" y=\"" ++ ii (sy y + 4)
             ++ "\" font-size=\"10\" font-family=\"sans-serif\""
             ++ " text-anchor=\"middle\">" ++ xmlEscape (lbl v) ++ "</text>"
         | not (null (lbl v)) ]

-- | Render an optimized /metric/ layout (stage 3, the heuristic layout
-- optimizer): atoms at their planar coordinates, the blockade radius @r@ drawn
-- as a faint disk around one atom for scale, and edges classified by how the
-- realized unit-disk graph compares to the prescribed gadget adjacency —
-- prescribed-and-realized (grey, solid), prescribed-but-missing (red, dashed),
-- and false edges, i.e. realized non-edges (orange, dashed). A short caption
-- legend reports the radius and the false/missing counts.
toSvgLayout
  :: Ord a
  => (a -> String)            -- ^ node label ("" suppresses text)
  -> Map a (Double, Double)   -- ^ node position (layout units)
  -> (a -> Double)            -- ^ node radius in px
  -> Double                   -- ^ blockade radius r (layout units)
  -> [(a, a)]                 -- ^ prescribed & realized edges (solid grey)
  -> [(a, a)]                 -- ^ prescribed & missing edges (dashed red)
  -> [(a, a)]                 -- ^ false edges / realized non-edges (dashed orange)
  -> [a]                      -- ^ vertices to draw
  -> String
toSvgLayout lbl pos rad r solid missing false_ verts = unlines $
  [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"" ++ ii w
      ++ "\" height=\"" ++ ii h ++ "\" viewBox=\"0 0 " ++ ii w ++ " " ++ ii h ++ "\">"
  , "  <rect width=\"100%\" height=\"100%\" fill=\"white\"/>"
  ]
  ++ blockade
  ++ map (line "#bbb"    (1.0 :: Double) False) solid
  ++ map (line "#e8a33d" (1.0 :: Double) True) (take falseCap false_)
  ++ map (line "#d33"    (1.6 :: Double) True) missing
  ++ concatMap node verts
  ++ legend
  ++ [ "</svg>" ]
  where
    falseCap = 80 :: Int   -- cap drawn false edges; legend reports the true total
    at v  = Map.findWithDefault (0, 0) v pos
    xs    = [ fst (at v) | v <- verts ]
    ys    = [ snd (at v) | v <- verts ]
    pad   = 40 :: Double
    capH  = 34 :: Double      -- room for the caption at the bottom
    minx  = if null xs then 0 else minimum xs
    miny  = if null ys then 0 else minimum ys
    maxx  = if null xs then 1 else maximum xs
    maxy  = if null ys then 1 else maximum ys
    spanx = max 1e-6 (maxx - minx)
    spany = max 1e-6 (maxy - miny)
    target = 660 :: Double
    sc    = target / max spanx spany    -- uniform layout-units -> px
    px p  = (p - minx) * sc + pad
    py p  = (p - miny) * sc + pad
    w     = spanx * sc + 2 * pad
    h     = spany * sc + 2 * pad + capH
    ii    = show . (round :: Double -> Int)
    ff x  = show (fromIntegral (round (x * 100) :: Int) / 100 :: Double)

    line col wid dash (u, v) =
      let (x1, y1) = at u; (x2, y2) = at v
      in "  <line x1=\"" ++ ii (px x1) ++ "\" y1=\"" ++ ii (py y1)
           ++ "\" x2=\"" ++ ii (px x2) ++ "\" y2=\"" ++ ii (py y2)
           ++ "\" stroke=\"" ++ col ++ "\" stroke-width=\"" ++ show wid ++ "\""
           ++ (if dash then " stroke-dasharray=\"4,3\"" else "") ++ "/>"

    -- the blockade disk around the first atom, for visual scale
    blockade = case verts of
      []      -> []
      (v : _) -> let (cx, cy) = at v
                 in [ "  <circle cx=\"" ++ ii (px cx) ++ "\" cy=\"" ++ ii (py cy)
                        ++ "\" r=\"" ++ ii (r * sc) ++ "\" fill=\"#4db6ac\""
                        ++ " fill-opacity=\"0.10\" stroke=\"#4db6ac\""
                        ++ " stroke-dasharray=\"2,3\" stroke-width=\"1\"/>" ]

    node v =
      let (x, y) = at v
          rr     = rad v
      in [ "  <circle cx=\"" ++ ii (px x) ++ "\" cy=\"" ++ ii (py y)
             ++ "\" r=\"" ++ ii rr ++ "\" fill=\""
             ++ (if rr >= 7 then "white" else "#ccc")
             ++ "\" stroke=\"#222\" stroke-width=\"1\"/>" ]
      ++ [ "  <text x=\"" ++ ii (px x) ++ "\" y=\"" ++ ii (py y + 3)
             ++ "\" font-size=\"9\" font-family=\"sans-serif\""
             ++ " text-anchor=\"middle\">" ++ xmlEscape (lbl v) ++ "</text>"
         | not (null (lbl v)) ]

    legend =
      [ "  <text x=\"" ++ ii pad ++ "\" y=\"" ++ ii (h - 12)
          ++ "\" font-size=\"12\" font-family=\"sans-serif\" fill=\"#333\">"
          ++ "r* = " ++ ff r
          ++ "   realized prescribed = " ++ show (length solid)
          ++ "   false edges = " ++ show (length false_)
          ++ (if length false_ > falseCap then " (showing " ++ show falseCap ++ ")" else "")
          ++ "   missing = " ++ show (length missing)
          ++ "</text>" ]

xmlEscape :: String -> String
xmlEscape = concatMap esc
  where
    esc '&' = "&amp;"; esc '<' = "&lt;"; esc '>' = "&gt;"
    esc '"' = "&quot;"; esc c = [c]

-- ── Graphviz DOT ────────────────────────────────────────────────────────────────

-- | An undirected DOT graph; render with e.g. @dot -Tsvg g.dot -o g.svg@.
toDot :: Ord a => (a -> String) -> Maybe (Map a Int) -> Graph a -> String
toDot lbl mcol g = unlines $
  [ "graph G {"
  , "  node [shape=circle, style=filled, fillcolor=white, fontname=\"sans\"];"
  ]
  ++ [ "  " ++ q v ++ fillOf v ++ ";" | v <- Set.toList (vertices g) ]
  ++ [ "  " ++ q u ++ " -- " ++ q w ++ ";" | (u, w) <- Set.toList (edges g) ]
  ++ [ "}" ]
  where
    q v       = show (lbl v)   -- 'show' on String yields a quoted, escaped DOT id
    fillOf v  = case mcol >>= Map.lookup v of
                  Just c  -> " [fillcolor=\"" ++ palette c ++ "\"]"
                  Nothing -> ""

-- ── ASCII adjacency matrix (Int graphs) ─────────────────────────────────────────

-- | Adjacency matrix as text, for quick terminal inspection of small @Int@
-- graphs.
toAscii :: Graph Int -> String
toAscii g =
  let vs  = Set.toAscList (vertices g)
      hdr = "    " ++ intercalate " " [ pad v | v <- vs ]
      row u = pad u ++ " " ++ intercalate " "
                [ if hasEdge u v g then "  1" else "  ." | v <- vs ]
  in unlines (hdr : [ row u | u <- vs ])
  where
    pad x = let s = show x in replicate (3 - length s) ' ' ++ s
