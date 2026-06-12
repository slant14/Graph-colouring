# Certified Compilation of Graph Coloring to Neutral-Atom Hardware

This repository accompanies the paper *Certified Compilation of Graph Coloring to
Neutral-Atom Hardware* (Naderi, Mazzara, Ciancarini). It contains the research
paper, a typed surface language and its compiler (`udg-color`), a machine-checked
soundness proof of the compilation pipeline (Rocq/Coq), a neutral-atom simulation
backend, and an empirical benchmark suite.

## Motivation

Neutral-atom quantum processors (for example QuEra/Bloqade) do not color graphs.
The hardware natively solves **maximum-weight independent set (MWIS) on a unit-disk
graph (UDG)**: atoms placed in the plane interact through a Rydberg blockade whose
adjacency is exactly the unit-disk relation. Any pipeline that targets this hardware
for graph coloring must therefore *reduce* coloring to UDG–MWIS, not merely embed the
input graph geometrically.

The project takes the reduction seriously and makes its correctness **static**. A
small typed language expresses a coloring problem and the chain of transformations
that lower it to a device instance. A *certified-reduction* type-and-effect system
accepts a pipeline only if every stage is answer-preserving and the stages compose in
a valid order, so that the bitstring the device returns is guaranteed to decode to a
correct coloring of the original graph. The end-to-end soundness of that discipline is
proved once, mechanically, and then reused for every program the checker accepts.

Two lowering paths are distinguished throughout:

- **Primary (exact gadget path).** Reduce `k`-colorability to independent set on an
  auxiliary *color-choice graph* of size `nk`, then apply Nguyen-style copy/crossing
  gadgets to obtain a weighted UDG. This path is exact.
- **Secondary (supergraph path).** Place the original vertices in the plane and grow a
  unit-disk supergraph. This is only conditionally safe and is disqualified as a
  general coloring mechanism by an impossibility result (a vertex whose neighborhood
  independence exceeds five, such as the star `K(1,6)`, admits no chromatic-bounded UDG
  supergraph). The language encodes this as a typing side-condition.

## Repository layout

```
.
├── paper.tex            Research paper (Elsevier CAS single-column class)
├── cas-sc.cls           Class and bibliography files required to build paper.tex
├── cas-common.sty
├── cas-model2-names.bst
├── references.bib
├── thumbnails/          Front-matter icons required by the CAS class
│
├── src/                 The udg-color compiler (Haskell) and simulation backend
│   ├── udg-color.cabal
│   ├── lib/UDGColor/     Library modules (parser, type checker, elaborator, stages)
│   ├── app/Main.hs       The udgc command-line driver
│   ├── examples/         Example programs (*.udgc)
│   ├── test/             Test suites (spec, langspec)
│   └── sim/              Neutral-atom simulation backend (Python)
│
├── proof/               Rocq/Coq mechanization of pipeline soundness
├── benchmarks/          Expected (oracle) vs. actual (simulation) experiments
└── docs/                Drafts and companion write-ups
```

## The `udg-color` language

A program is a sequence of top-level bindings describing graphs, palettes,
restrictions, transformation pipelines, coloring instances, and queries. The compiler
(`udgc`) parses a program, type-checks it under the certified-reduction discipline, and
elaborates each instance down to the device instance the simulator consumes, stopping
before any simulation is run.

### Declarations

The language provides six kinds of declaration.

| Keyword form        | Purpose                                                        |
|---------------------|---------------------------------------------------------------|
| `graph`             | A graph literal, a `udg` literal, or `apply T to G`           |
| `palette`           | A set of colors (`colors [...]`) or a size (`size n`)         |
| `restrictions`      | A block of coloring constraints                               |
| `transform`         | A transformation, possibly a `>>>` pipeline                   |
| `instance`          | `color G using P subjectTo R via T`                           |
| `compute`           | A query, currently `chromaticNumber(G)`                       |

Each declaration may be written in an **explicit keyword form**, where the keyword
fixes the kind:

```
graph gK3 = graph { vertices = [a, b, c], edges = [(a,b), (b,c), (a,c)] }
palette pRGB = colors [red, green, blue]
```

or in a **signature-driven form**, where the head of the right-hand side fixes the kind
and an optional Haskell-style signature records the intended type:

```
encodeK3 :: Coloring 3 3 ~> Dev 45
encodeK3 = colorChoice 3 >>> gadgetize >>> layout opts >>> emit
```

A graph or unit-disk literal:

```
graph gInput = graph { vertices = [1, 2, 3, 4, 5]
                     , edges    = [(1,2), (2,3), (3,1), (1,4), (3,5)] }

graph gU = udg { radius = 1.0, edges = [(1,2), (2,3), (1,3)] }
```

A restriction block (semicolon-separated):

```
restrictions rMain = { precolor 1 : red
                     ; differentColor (1, 2)
                     ; useAtMost 3 }
```

The available restrictions are `precolor v : c`, `allow v : [...]`, `forbid v : [...]`,
`sameColor(u, v)`, `differentColor(u, v)`, `useAtMost n`, `useExactly n`, and
`distinctOn [...]`.

### Problem-types and the reduction arrow

The type system works over *problem-types*, the sorts of the compilation. A transform
is typed as a certified reduction `A ~> B ! e` from problem-type `A` to problem-type
`B`, carrying a safety effect `e`.

| Sort          | Surface syntax      | Meaning                                          |
|---------------|---------------------|--------------------------------------------------|
| `Col`         | `Coloring n k`      | `k`-coloring instance on `n` vertices            |
| `IS`          | `IS N`              | Independent-set instance on `N` vertices         |
| `WIS`         | `WIS N C`           | Weighted independent set with offset constant `C`|
| `UDG`         | `UDG N`             | Independent set on a unit-disk graph             |
| `Dev`         | `Dev N`             | A device instance of `N` atoms                   |

The base types `Graph`, `Palette`, `Restrictions`, `Instance`, `Result`, and `Int`
classify the domain declarations and queries.

The safety effect `e` is either `safe` (poly-time and chromatic-number preserving) or
`asafe k` (almost-safe: never lowers the chromatic number and increases it by at most
the constant `k`). The effect is `safe` by default and may be written explicitly after
`!`, as in `Coloring 5 3 ~> Coloring 5 4 ! asafe 1`.

### Transform combinators

A pipeline is built from stage primitives and combined with `>>>` (left-to-right
composition). The primary path is the four-stage chain:

| Combinator            | Reduction                          | Role                          |
|-----------------------|------------------------------------|-------------------------------|
| `colorChoice k`       | `Coloring n k ~> IS (n·k)`         | Stage 1: color-choice graph   |
| `gadgetize`           | `IS ~> WIS`                        | Stage 2: gadget encoding      |
| `layout [opts]`       | `WIS ~> UDG`                       | Stage 3: geometric layout     |
| `emit`                | `UDG ~> Dev`                       | Device lowering + budget check|

Additional combinators:

- `encodeColoring k` — the exact gadget encoding `Col ~> WIS`, fusing Stages 1 and 2.
- `superUDG` — the secondary same-vertex supergraph path `Coloring n k ~> Coloring n k'`,
  which carries a safety effect and is gated by the impossibility side-condition.
- `toUDG(exact | preserve P, opts...)` — a UDG realization, exact or property-preserving,
  with options `radius`, `keep`, `drop`, `trackOrigin`. The preserved property `P` is one
  of `kColorable(n)`, `chromatic`, or `bipartite`.
- `compose [t1, t2, ...]` — composition of named transforms.

### What the type checker enforces

The checker runs two layers.

1. **Static well-formedness** (the `errors.tex` catalogue). Scope and kind checks,
   palette and vertex membership, restriction validity, and signature agreement. A
   sample of the catalogue numbers reported in diagnostics: `#2` a restriction names a
   vertex absent from the graph; `#3` an edge endpoint is not a declared vertex; `#4` a
   color is not in the palette; `#5` `useExactly` exceeds the palette size; `#6` a
   restriction belongs to the wrong set; `#8` `keep` and `drop` overlap; `#9` an `exact`
   transform tries to drop vertices.

2. **The certified-reduction discipline.** Composition `>>>` is checked at the sort
   granularity: a stage producing sort `S` may only feed a stage that expects `S`, so a
   misordered pipeline (for example `emit` after `colorChoice`) is rejected. The `emit`
   stage enforces the device budget `N <= Nmax`, with `Nmax = 256` by default; an
   estimate of the gadget atom count is compared against it. The supergraph path is gated
   by the impossibility side-condition `sigma(G) <= 5`, where `sigma(G)` is the maximum
   over vertices of the independence number of the neighborhood; when it fails, the
   safety effect is unavailable and the checker directs the user to the exact path.

## Examples

The programs in `src/examples/` exercise the language end to end. Run them with `udgc`
(see the next section).

### `triangle.udgc` — smallest end-to-end pipeline

A 3-coloring of the triangle `K3` through the exact gadget path. It also shows both
binding forms.

```
graph gK3 = graph { vertices = [a, b, c]
                  , edges    = [(a,b), (b,c), (a,c)] }

palette pRGB = colors [red, green, blue]

encodeK3 :: Coloring 3 3 ~> Dev 45
encodeK3 = colorChoice 3 >>> gadgetize >>> layout opts >>> emit

solveK3 :: Result
solveK3 = color gK3 using pRGB via encodeK3

chiK3 :: Int
chiK3 = chromaticNumber (gK3)
```

### `paper_example.udgc` — primary and secondary paths together

The five-vertex example from the paper. The exact pipeline `encode3` is fully typed as
a chain of certified reductions; the `super` binding shows the supergraph path carrying
an `asafe 1` effect.

```
encode3 :: Coloring 5 3 ~> Dev 75
encode3 = colorChoice 3 >>> gadgetize >>> layout opts >>> emit

super :: Coloring 5 3 ~> Coloring 5 4 ! asafe 1
super = superUDG
```

### `supergraph_star.udgc` — the impossibility result as a type error

The star `K(1,6)` has chromatic number 2, but `sigma(G) = 6 > 5`, so no UDG supergraph
can bound its chromatic inflation. The `superUDG` transform therefore does **not**
type-check on this graph: the checker rejects the supergraph path and points to the
exact path instead.

### `errors.udgc` — a catalogue of static errors

A program that deliberately triggers the static-well-formedness catalogue (out-of-scope
edge endpoints, undeclared vertices and colors, `useExactly` against a too-small palette,
`keep`/`drop` overlap, an `exact` transform dropping vertices, and a misordered
pipeline). Running the checker reports each with its catalogue number.

## The `udgc` command-line driver

```
udgc FILE.udgc              parse, type-check, and elaborate (default)
udgc --check FILE.udgc      parse and type-check only (no elaboration)
udgc --emit-sim FILE.udgc [OUTDIR]
                            type-check, then write one <instance>.sim.json per
                            instance for the simulator (default OUTDIR: sim/instances)
```

The default mode prints the inferred type of every binding, all diagnostics (with
`errors.tex` numbers where applicable), and, when there are no errors, the elaborated
pre-simulation device instance for each coloring instance: the color-choice graph size,
the gadget atom count and offset constant, the layout radius and edge-realization
quality, and the oracle's colorability verdict. The `--emit-sim` mode refuses to write
anything if the program has type errors.

## Building and running

### The compiler (Haskell)

Requires GHC and Cabal (developed against GHC 9.12.2 and cabal-install 3.12).

```sh
cd src
cabal build all
cabal test                                  # spec + langspec (exhaustive oracle checks)
cabal run udgc -- examples/triangle.udgc    # run an example
cabal run udgc -- --check examples/errors.udgc
```

The library has no non-boot dependencies beyond `parsec` and `containers`; the parser
uses `parsec` deliberately so the project builds in an offline environment.

### The simulation backend (Python)

The `src/sim/` backend runs the neutral-atom simulation on the emitted
`*.sim.json` instances, decodes the recovered independent set into a coloring, and
verifies that the independent-set size equals the vertex count exactly when the graph is
colorable. It provides two engines: a faithful CPU Rydberg MWIS simulation, and the
genuine `bloqade-analog` geometric emulator (run as an end-to-end protocol check on a
clean unit-disk layout). It depends on `numpy`, `scipy`, and `bloqade-analog`.

```sh
cd src
cabal run udgc -- --emit-sim examples/triangle.udgc   # writes sim/instances/solveK3.sim.json
python sim/run_sim.py                                 # run all instances, default engine
python sim/run_sim.py --bloqade-check                 # also run the genuine emulator
```

### The proofs (Rocq/Coq)

The `proof/` directory mechanizes the certified-reduction calculus and the end-to-end
soundness theorem (the measured device bitstring decodes to a correct coloring), with no
axioms and no admitted lemmas. Requires `coqc` (tested on The Rocq Prover 9.0.0); no
external libraries. See `proof/README.md`.

```sh
cd proof
make
```

### The benchmarks

The `benchmarks/` suite runs well-known small graphs end to end and compares the
oracle-expected partial coloring against the simulation's result, in both the colorable
and non-colorable regimes. See `benchmarks/README.md`.

### The paper

```sh
latexmk -pdf paper.tex
```

`paper.tex` is self-contained given the `cas-*` class and bibliography files and the
`thumbnails/` directory in the repository root.

## Component map

| Module (`src/lib/UDGColor/`) | Responsibility                                              |
|------------------------------|-------------------------------------------------------------|
| `Ast`                        | Surface syntax, problem-types, effects, sorts               |
| `Parser`                     | `parsec` front end for `.udgc` programs                     |
| `TypeCheck`                  | Static catalogue + certified-reduction discipline           |
| `Elaborate`                  | Lowering of a well-typed instance to a device instance      |
| `Emit`                       | Device-instance JSON for the simulator                      |
| `Graph`, `Oracle`            | Graph type and brute-force chromatic/independence oracle    |
| `Stage1`                     | Color-choice graph construction and coloring decode         |
| `Gadget`                     | Combinatorial gadget contract and logical decode            |
| `Layout`                     | Stage-3 geometric layout optimizer                          |
| `Viz`                        | SVG, DOT, and ASCII visualizations of each stage            |

## Status and limitations

The compiler, the simulation backend, and the mechanized soundness proof are
implemented and pass their checks. The contribution is the **certified compilation
discipline and its type system**, not near-term quantum advantage: the exact gadget
reduction multiplies the instance size, so the device budget (`Nmax`) is reached on
modest inputs. The size wall is a known and openly stated limitation; the
decomposition front end (block/clique-separator and tree-decomposition based) is the
route to larger instances by replacing the vertex count with a bounded decomposition
width.
