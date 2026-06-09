# Graph-colouring benchmarks: expected (oracle) vs actual (Rydberg sim)

Well-known small graphs run end-to-end through the neutral-atom pipeline. For
each graph `G` and palette size `k` we build the Stage-1 colour-choice graph
`G'` (the `option`-encoded MWIS instance the [Coq proofs](../proof) and the
[Haskell harness](../code) use), solve it on the abstract adiabatic Rydberg
engine (`code/sim/rydberg_sim.mwis_graph`), and decode a colouring.

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

Uses the project venv (`code/.venv`): `code/.venv/bin/python benchmarks/run_benchmarks.py`.
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
`2^(n·k)` state vector and `n·k = 30` exceeds the `NK_MAX = 16` wall; this is
the same finite-size limitation noted in the thesis framing, made concrete.

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
code/.venv/bin/python benchmarks/run_decomp.py
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

Output: `results/decomp.svg` (whole `n·k` vs max simulated piece, with the wall
line at 16), `results/decomp.{json,csv}`. Cliques have no separator, so `K_m`
stays irreducible — decomposition helps sparse / bounded-width graphs, exactly as
the theory predicts.

## Notes

- This benchmarks the **logical** MWIS the gadget array realizes (the abstract
  Rydberg engine), not the geometric `bloqade-analog` layout — same split as
  `code/sim/run_sim.py`. The genuine emulator is validated separately there.
- The `α(G')` oracle enumerates `(k+1)^n` partial colourings (one colour-or-none
  per vertex = the choice-clique `option` encoding), so it is exact, not a
  heuristic colouring.
- Runtime is dominated by the two 16-slot / 15-slot instances; the adiabatic
  step count is scaled down for the largest state vectors (`steps_for`).
