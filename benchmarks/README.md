# Graph-colouring benchmarks: expected (oracle) vs actual (Rydberg sim)

Well-known small graphs run end-to-end through the neutral-atom pipeline. For
each graph `G` and palette size `k` we build the Stage-1 colour-choice graph
`G'` (the `option`-encoded MWIS instance the [Coq proofs](../proof) and the
[Haskell harness](../src) use), solve it on the abstract adiabatic Rydberg
engine (`src/sim/rydberg_sim.mwis_graph`), and decode a colouring.

- **expected** = `α(G')`, the maximum-size partial proper `k`-colouring, by
  brute-force oracle. By Stage-1 exactness `α(G') = n` **iff** `G` is
  `k`-colourable.
- **actual** = `|MWIS|`, the independent set the simulation returns.

Each graph is run at `k = χ(G)` (colourable regime, expected `= n`) **and** at
`k = χ(G)-1` (non-colourable regime, expected `< n`), so both regimes appear.

## Run

```sh
python benchmarks/run_benchmarks.py        # solve + write results + plots
python benchmarks/plot.py                  # re-plot from results/results.json only
```

Uses the project venv (`src/.venv`): `src/.venv/bin/python benchmarks/run_benchmarks.py`.
Needs numpy/scipy (already installed); plotting needs nothing (hand-rolled SVG)
plus optional `plotext` for the terminal chart.

## Benchmarks

| graph | n | m | χ | note |
|-------|---|---|---|------|
| P4 (path) | 4 | 3 | 2 | bipartite |
| C4 (cycle) | 4 | 4 | 2 | even cycle |
| C5 (cycle) | 5 | 5 | 3 | odd cycle |
| K3 (triangle) | 3 | 3 | 3 | smallest odd clique |
| K4 (complete) | 4 | 6 | 4 | χ=4, the 2¹⁶ worst case |
| K2,3 | 5 | 6 | 2 | complete bipartite |
| K1,4 (star) | 5 | 4 | 2 | the σ>5 supergraph obstruction lives here |
| Bull | 5 | 5 | 3 | triangle + 2 pendants |
| W5 (wheel) | 5 | 8 | 3 | C4 + hub |
| Petersen | 10 | 15 | 3 | **skipped** — n·k=30 slots > size wall |

## Results

All 18 simulated instances recover the optimum exactly (`actual = expected`),
and every colourable case decodes to a verified-proper colouring — see
`results/results.csv`. Petersen is skipped because the engine evolves a
`2^(n·k)` state vector and `n·k = 30` exceeds the `NK_MAX = 16` wall of the
classical simulator.

Outputs in `results/`:

- `bars.svg` — grouped bar chart, expected (blue) vs actual (green=match,
  red=mismatch) per `(graph, k)`.
- `scatter.svg` — actual vs expected with the `y = x` agreement line; every
  point sits on the line.
- `results.json`, `results.csv` — the raw table (n, m, χ, k, slots, expected,
  actual, match, proper, seconds).

## Decomposition — breaking the 16 wall

`NK_MAX = 16` is a **classical-simulator** cap (the engine evolves a `2^(n·k)`
state vector), *not* the device atom budget (`Nmax = 256` in `TypeCheck.hs`) and
not fundamental. The Split/Stitch path (`type-system.tex` Refinement C) makes
peak device size `O((w·k)²)` in the separator width `w`, **independent of `n`**:
a separator is precoloured, each piece is solved on a *small* Rydberg array, and
the pieces are stitched (they agree on the separator by construction).

`decompose.py` implements this (exact nested-precolouring dissection: separator →
boundary-table enumeration → per-piece `mwis_graph` solve → stitch);
`run_decomp.py` drives it. Run:

```sh
src/.venv/bin/python benchmarks/run_decomp.py
```

Result — whole-graph `n·k` from 28 to **90**, every actual device solve ≤ 12 slots:

| graph | k | whole n·k | max piece slots | device calls | result |
|-------|---|-----------|-----------------|--------------|--------|
| Petersen | 3 | 30 | 10 | 4 | proper ✓ |
| Frucht | 3 | 36 | 9 | 4 | proper ✓ |
| Heawood | 2 | 28 | 11 | 4 | proper ✓ |
| Pappus | 2 | 36 | 11 | 6 | proper ✓ |
| Desargues | 2 | 40 | 11 | 7 | proper ✓ |
| Dodecahedral | 3 | 60 | 10 | 25 | proper ✓ |
| C30 (cycle) | 3 | 90 | 11 | 8 | proper ✓ |
| C21 (odd) | 2 | 42 | 12 | 17 | not 2-colourable ✓ |

**Certificates.** A colouring returned by the device is a witness and is checked
classically. A device solve that returns no colouring is *not* a proof that the
piece is infeasible, so every such leaf is decided by an exact classical search
(`decompose.exact_extension`; leaves are ≤ 13 slots). A "not colourable" verdict
is therefore a classical certificate (exhaustive boundary enumeration + exact
leaf checks); the CSVs record `device_witnesses`, `classical_checks` and
`device_misses` (colourable leaves the device missed — 0 in every run).
`run_largenk.py` also runs each graph at `k = χ` and `k = χ-1`.

Output: `results/decomp.svg` (whole `n·k` vs max simulated piece, with the wall
line at 16), `results/decomp.{json,csv}`. Cliques have no separator, so `K_m`
stays irreducible — decomposition helps sparse / bounded-width graphs, exactly as
the theory predicts.

## Random G(n,p) instances

`run_random.py` repeats the oracle comparison on Erdős–Rényi graphs drawn from a
fixed seed (20 per cell, none discarded), running each instance at `k = χ` and
`k = χ-1` wherever `n·k ≤ 16`. Result: **286/286 runs match the oracle, 130/130
colourable runs decode to proper colourings** (160 instances).

```sh
src/.venv/bin/python benchmarks/run_random.py --workers 5   # ~17 min on 5 cores
```

Output: `results/random.{json,csv}`.

## Metric gadget layouts (Julia)

`run_layout.jl` maps each colour-choice graph `G'_k` to the weighted unit-disk
instance of Nguyen et al. (PRX Quantum 4, 010316) with
[UnitDiskMapping.jl](https://github.com/QuEraComputing/UnitDiskMapping.jl) 0.5.1
under three copy-line orders — naive input order, our optimized order (Fiedler
vector + monotone adjacent-swap repair on the atom count), and the library's own
path-decomposition order — and records atoms, crossing gadgets and bounding box.
`verify_layout.jl` solves MWIS on the small mapped instances exactly and checks
`MWIS(A) = MWIS(G'_k, w) + overhead` for uniform and random weights (24/24 pass).
`export_c4_layout.jl` writes the atom coordinates used in the paper's C4 figure.
Shared definitions are in `layout_common.jl`.

```sh
julia -e 'using Pkg; Pkg.add(["UnitDiskMapping", "Graphs"])'
julia benchmarks/run_layout.jl        # ~15 min, dominated by myciel3
julia benchmarks/verify_layout.jl
```

Output: `results/layout.{csv,json}`, `results/verify_layout.txt`,
`results/c4_layout.tex`. Only the two smallest instances (n·k ≤ 8) fit a
256-atom device.

## Verified certificates

Every run of `run_decomp.py`, `run_largenk.py` and `run_dimacs.py` writes a
certificate to `results/certs/` — the colouring, or a refutation tree (see
`proof/Certificate.v`) — and checks it with the verified checker
`proof/checker/certcheck` (build it with `cd proof && make && cd checker && make`).
All 26 certificates are accepted; the largest refutation (myciel3, k=3) has 794
nodes. A run only PASSes if its certificate is accepted. The directory holds 24
files for the 26 runs: Petersen and Dodecahedral at k=3 are run by both
`run_decomp.py` and `run_largenk.py` and share a file name.

## Imperfect solves and pathwidth scaling

`run_robust.py` shortens the adiabatic sweep (T = 1.2) so shots often miss the
optimum, and decodes every shot with the robust decoders (fresh colour per
unselected vertex; on `A_4`, drop one end of each internal edge first): all
14,835 decoded shots are proper and within `k + d + ε` colours.
`run_scaling.jl` (Julia, UnitDiskMapping.jl) maps paths, cycles, ladders and
3×m grids up to n = 40 at k = 3 under the lifted slot order: atom counts grow
linearly in n (paths 54.75 n − 34, cycles 90.75 n − 49), complete graphs
quadratically. Outputs: `results/robust.{json,csv}`, `results/scaling.csv`.

## Notes

- This benchmarks the **logical** MWIS the gadget array realizes (the abstract
  Rydberg engine), not the geometric `bloqade-analog` layout — same split as
  `src/sim/run_sim.py`. The genuine emulator is validated separately there.
- The `α(G')` oracle enumerates `(k+1)^n` partial colourings (one colour-or-none
  per vertex = the choice-clique `option` encoding), so it is exact, not a
  heuristic colouring.
- Runtime is dominated by the two 16-slot / 15-slot instances; the adiabatic
  step count is scaled down for the largest state vectors (`steps_for`).
