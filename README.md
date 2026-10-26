# Certifying Compilation of Graph Coloring to Neutral-Atom Hardware

This repository is the artifact for the paper *Certifying Compilation of Graph Coloring
to Neutral-Atom Hardware: Typed Exact Reductions with Verified Verdicts* by Mahmoud
Naderi, Manuel Mazzara and Paolo Ciancarini. It contains the
paper source, the Rocq mechanization and its extracted certificate checker, the
Haskell front end `udg-color`, a Rydberg-blockade simulator, and every benchmark
script and recorded result that the paper reports. The version described in the paper
is release [v1.0](https://github.com/slant14/Graph-colouring/releases/tag/v1.0)
(commit `cb71118`).

## Overview

In their analog mode, neutral-atom processors solve maximum-weight independent set
(MWIS) on unit-disk graphs (UDGs); they do not color graphs. To decide whether a graph
`G` with `n` vertices is `k`-colorable on such hardware, we reduce the question in two
exact stages:

1. **Stage 1.** `G` becomes the *color-choice graph* `G'_k` on `nk` slots `(v, i)`
   ("vertex `v` takes color `i`"). `G` is `k`-colorable if and only if
   `α(G'_k) = n`, and the size-`n` independent sets of `G'_k` are in bijection with
   the proper `k`-colorings of `G`.
2. **Stage 2.** `G'_k` is embedded into a weighted UDG with the copy/crossing gadgets
   of Nguyen et al. (PRX Quantum 4, 010316, 2023), so that
   `MWIS(A) = α(G'_k) + C` for a known offset `C`.

The device returns an independent set of the gadget instance `A`, and the decoder maps
it back through both stages. A readout is accepted only if it selects exactly one slot
per vertex and the resulting coloring is proper on every edge of `G`.

On top of this reduction, the paper contributes:

- **A certified-reduction type system.** Each stage is typed as a reduction that
  carries its decoder, so end-to-end soundness and the legal order of stages follow
  from typing. Ill-ordered pipelines have no typing derivation.
- **Robustness to imperfect solves.** For `k`-colorable `G`, a solve of the
  combinatorial gadget instance that misses the optimum by `ε` decodes to a proper
  coloring with at most `k + ε` colors. This end-to-end theorem is mechanized in
  Rocq.
- **Certificates in both directions.** The device is used only to find colorings.
  Every non-colorability verdict of the separator decomposition comes with a
  refutation tree, which a checker proved sound in Rocq and extracted to OCaml
  accepts.
- **A pathwidth size bound.** For graphs of pathwidth `p`, the gadget instance needs
  `O(nk²(p+1))` atoms, which is linear in `n`, against `O((nk)²)` in general.
- **An impossibility result for the geometric alternative.** Placing the vertices of
  `G` directly as a UDG supergraph cannot preserve the chromatic number in general:
  the star `K(1,n)` has `χ = 2`, yet every UDG supergraph of it has
  `χ ≥ ⌈n/5⌉ + 1`. The seven geometric heuristics are therefore used only as a layout
  optimizer for the gadget instance, where they cannot affect correctness.

The main limitation is size. On a 256-atom device, only the smallest instances fit
(Section 9.5 of the paper); the separator decomposition keeps every simulated solve at
13 logical slots or fewer while the whole instance reaches `nk = 192`.

## Repository layout

```
.
├── paper.tex, references.bib   The paper (Elsevier CAS single-column class)
├── paper.pdf                   The built paper
├── cas-sc.cls, cas-common.sty, cas-model2-names.bst, thumbnails/
│                               Class files needed to build paper.tex
├── proof/                      Rocq mechanization (seven modules, no axioms)
│   └── checker/                Extraction of the certificate checker to OCaml
├── src/                        The udg-color front end (Haskell) and simulator
│   ├── lib/UDGColor/           Parser, type checker, elaborator, stages, emitter
│   ├── app/Main.hs             The udgc command-line driver
│   ├── examples/               Example programs (*.udgc)
│   ├── test/                   Test suites (spec, langspec)
│   └── sim/                    Rydberg-blockade simulator (Python)
├── benchmarks/                 Experiment scripts (Python, Julia)
│   └── results/                Recorded outputs and certificates
└── docs/                       Design notes and early drafts
```

## Requirements

The versions are the ones used for the paper.

| Component | Tools |
|---|---|
| Proofs | Rocq Prover 9.0.0 (`coqc`, `coq_makefile`); no external libraries |
| Certificate checker | OCaml 5.3 with `ocamlfind` |
| Front end | GHC 9.12.2 and cabal-install 3.12; dependencies `base`, `containers`, `parsec`, `directory` only |
| Simulator and benchmarks | Python 3.10 with `numpy`, `scipy` and `networkx`; optionally `bloqade-analog` (emulator check) and `plotext` (terminal plots) |
| Metric layouts | Julia 1.11 with UnitDiskMapping.jl 0.5.1 and Graphs.jl |
| Paper | A TeX distribution with `latexmk`, `pgfplots` and `listings` |

## Building

```sh
# Proofs, then the verified certificate checker (the decomposition benchmarks call it)
cd proof
coq_makefile -f _CoqProject -o Makefile
make
cd checker && make          # writes proof/checker/certcheck
cd ../..

# Front end and its test suites
cd src
cabal build all
cabal test                  # 4 language checks and 15,334 oracle checks
cd ..

# Python environment used by all benchmark scripts
python3 -m venv src/.venv
src/.venv/bin/pip install numpy scipy networkx      # add bloqade-analog for the emulator check

# Julia packages for the metric layouts
julia -e 'using Pkg; Pkg.add(name="UnitDiskMapping", version="0.5.1"); Pkg.add("Graphs")'

# The paper
latexmk -pdf paper.tex
```

Every head theorem of the Rocq development is closed under the global context: the
development uses no axioms and contains no `Admitted`. `proof/README.md` lists the
theorems and how each corresponds to a result in the paper (Table 1 of the paper).

## Reproducing the results

Run the commands from the repository root after building. Each script writes its
output to `benchmarks/results/`, where the recorded outputs used in the paper are
already present.

| Paper | Command | Output |
|---|---|---|
| Section 9.3: ten named graphs, 18 runs | `src/.venv/bin/python benchmarks/run_benchmarks.py` | `results.{csv,json}`, `bars.svg`, `scatter.svg` |
| Section 9.3, Table 2: random `G(n,p)`, 286 runs | `src/.venv/bin/python benchmarks/run_random.py --workers 5` (about 17 min on 5 cores) | `random.{csv,json}` |
| Section 9.4, Table 3: imperfect solves, 14,835 shots | `src/.venv/bin/python benchmarks/run_robust.py` | `robust.{csv,json}` |
| Section 9.5, Table 4: metric gadget instances | `julia benchmarks/run_layout.jl` (about 15 min) | `layout.{csv,json}` |
| Section 9.5: exact MWIS check of the mapped instances, 24 checks | `julia benchmarks/verify_layout.jl` | `verify_layout.txt` |
| Section 9.5: direct simulation of the combinatorial gadget | `src/.venv/bin/python src/sim/run_gadget.py` | printed |
| Section 9.5: geometric emulator check | `cd src && .venv/bin/python sim/run_sim.py --bloqade-check` | printed |
| Figure 3(c): the `C4` instance | `julia benchmarks/export_c4_layout.jl` | `c4_layout.tex` |
| Section 9.6, Figure 6: scaling with pathwidth | `julia benchmarks/run_scaling.jl` | `scaling.csv` |
| Section 9.7, Table 5, first two groups | `src/.venv/bin/python benchmarks/run_largenk.py` | `largenk.{csv,json,svg}` |
| Section 9.7, Table 5, third group | `src/.venv/bin/python benchmarks/run_decomp.py` | `decomp.{csv,json,svg}` |
| Section 9.7, Table 5, Mycielski graphs | `src/.venv/bin/python benchmarks/run_dimacs.py` | `dimacs.{csv,json,svg}` |
| Section 9.8: certificates | written by the three decomposition scripts | `certs/*.cert` |

The three decomposition scripts write a certificate for each of the 26 runs and check
it with `proof/checker/certcheck` when it is written; a run passes only if its
certificate is accepted (column `cert_valid` in the CSV files). The directory holds 24
files because two instances, Petersen and the dodecahedral graph at `k = 3`, are run
by both `run_decomp.py` and `run_largenk.py` and share a file name. Any certificate can
be checked again directly:

```sh
proof/checker/certcheck benchmarks/results/certs/myciel3_k3.cert
# VALID: no proper 3-coloring exists (n=11, m=20)
```

`benchmarks/README.md` describes each experiment in more detail.

## The `udg-color` language

A program declares graphs, palettes, restrictions, transforms, instances and queries.
The checker accepts a pipeline only if every stage is a certified reduction and the
stages are composed in a legal order. The program below is
`src/examples/paper_figure.udgc`, shown in Figure 5 of the paper:

```
graph gInput = graph { vertices=[1,2,3,4,5],
                       edges=[(1,2),(2,3),(3,1),(1,4),(3,5)] }
palette pNamed = colors [red, blue, green]
restrictions rMain = { precolor 1 : red; differentColor(1,2); useAtMost 3 }
transform tExact   = colorChoice 3 >>> gadgetize >>> layout >>> emit
transform tBounded = toUDG(boundedChi chromatic, keep=[1,2,3], trackOrigin=true)
instance inst1 = color gInput using pNamed subjectTo rMain via tExact
instance inst2 = color gInput using pNamed subjectTo rMain via tBounded
compute  chiInput = chromaticNumber(gInput)
```

`tExact` is the exact path, typed `Col ~> Dev`. `tBounded` is the supergraph path,
typed `Col ~> Col` with the effect `mono` (the chromatic number is never lowered, but
its increase is not bounded).

The stages of the exact path are:

| Stage | Typed as | Role |
|---|---|---|
| `colorChoice k` | `Coloring n k ~> IS (n·k)` | Stage 1: color-choice graph |
| `gadgetize` | `IS ~> WIS` | Stage 2: gadget instance with offset `C` |
| `layout [opts]` | `WIS ~> UDG` | Stage 3: geometric layout |
| `emit` | `UDG ~> Dev` | Device instance and atom-budget check |

The checker enforces two layers. The first is static well-formedness: scope, palette
and vertex membership, restriction validity, and signature agreement, with diagnostics
numbered as in the error list of Section 9.2 of the paper. Restrictions on single
vertices and pairs (`precolor`, `allow`, `forbid`, `sameColor`, `differentColor`,
`distinctOn`) are compiled into the color-choice graph (Proposition 4.3); the
counting restrictions `useExactly`, and `useAtMost j` with `j < k`, are rejected on
the exact path (#13). The second is the
certified-reduction discipline. A stage that produces sort `S` can feed only a stage
that expects `S`, so a misordered pipeline is rejected. The supergraph path is
rejected when `σ(G) > 5`, where `σ(G)` is the largest independence number of a
neighborhood. The `emit` stage checks the atom budget: it reports an error when the
`nk` logical atoms alone exceed `Nmax`, and reports that an instance fits only when
the bound `4(nk)²` is within `Nmax`; otherwise device fit must be decided from the
metric layout. Section 9.2 of the paper lists what the prototype checks and what it
does not check yet.

Other examples in `src/examples/`:

- `triangle.udgc`: the smallest end-to-end pipeline, a 3-coloring of `K3`.
- `paper_example.udgc`: the exact path and the supergraph path on the same graph.
- `supergraph_star.udgc`: the star `K(1,6)`, on which the supergraph path is rejected.
- `errors.udgc`: a program that triggers the static error catalogue.

The command-line driver:

```
udgc FILE.udgc                    parse, type-check and elaborate (default)
udgc --check FILE.udgc            parse and type-check only
udgc --emit-sim FILE.udgc [DIR]   type-check, then write <instance>.sim.json files
                                  for the simulator (default DIR: sim/instances)
```

For example, from `src/`: `cabal run udgc -- examples/paper_figure.udgc`.

## Citation

If you use this artifact, please cite the paper:

```bibtex
@misc{NaderiMazzaraCiancarini2026,
  author = {Naderi, Mahmoud and Mazzara, Manuel and Ciancarini, Paolo},
  title  = {Certifying Compilation of Graph Coloring to Neutral-Atom Hardware:
            Typed Exact Reductions with Verified Verdicts},
  year   = {2026},
  note   = {Manuscript},
  url    = {https://github.com/slant14/Graph-colouring}
}
```

## Contact

Mahmoud Naderi, Innopolis University (m.naderi@innopolis.university).
