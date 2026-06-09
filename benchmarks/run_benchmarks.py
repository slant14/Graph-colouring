"""Run well-known small graph-colouring benchmarks through the neutral-atom
pipeline and compare the *expected* optimum (brute-force oracle) against the
*actual* value the adiabatic Rydberg simulation recovers.

For a graph G and palette size k we build the Stage-1 colour-choice graph G'
(the `option`-encoded MWIS instance the Coq proofs and the Haskell harness use),
solve it on the abstract Rydberg engine (`code/sim/rydberg_sim.mwis_graph`), and
decode a colouring.  The figure of merit is

    expected = alpha(G')   (max-size partial proper k-colouring, brute force)
    actual   = |MWIS|      (independent set the simulation returns)

By the Stage-1 exactness theorem expected = n  iff  G is k-colourable, so each
benchmark is run at k = chi(G) (expected = n, colourable) and at k = chi-1
(expected < n, not colourable) — giving both regimes to plot.

Outputs: results/results.json, results/results.csv, and (via plot.py) the SVG
and terminal plots.  Run:  python benchmarks/run_benchmarks.py
"""

from __future__ import annotations

import csv
import itertools
import json
import os
import sys
import time
from typing import Dict, List, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "code", "sim"))
from rydberg_sim import mwis_graph  # noqa: E402

# largest colour-choice instance (n*k slots) we are willing to simulate: the
# engine evolves a 2^(n*k) state vector, so this is the size wall.
NK_MAX = 16

Edge = Tuple[int, int]


# ── well-known small benchmark graphs (0-indexed) ────────────────────────────

def complete(n: int) -> List[Edge]:
    return [(u, v) for u in range(n) for v in range(u + 1, n)]

def cycle(n: int) -> List[Edge]:
    return [(i, (i + 1) % n) for i in range(n)]

def path(n: int) -> List[Edge]:
    return [(i, i + 1) for i in range(n - 1)]

def complete_bipartite(a: int, b: int) -> List[Edge]:
    return [(u, a + w) for u in range(a) for w in range(b)]

def star(n_leaves: int) -> List[Edge]:
    return [(0, i + 1) for i in range(n_leaves)]

# bull: triangle 0-1-2 with pendants 0-3 and 1-4
BULL = [(0, 1), (1, 2), (2, 0), (0, 3), (1, 4)]
# wheel W5: hub 4 joined to a 4-cycle 0-1-2-3
WHEEL5 = cycle(4) + [(4, i) for i in range(4)]
# Petersen graph (outer 5-cycle, inner pentagram, spokes) — chi = 3
PETERSEN = (
    [(i, (i + 1) % 5) for i in range(5)]                      # outer C5
    + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]            # inner pentagram
    + [(i, 5 + i) for i in range(5)]                          # spokes
)

# (name, n, edges, known chi) — known chi is asserted against the oracle.
BENCHMARKS: List[Tuple[str, int, List[Edge], int]] = [
    ("P4 (path)",          4, path(4),                 2),
    ("C4 (cycle)",         4, cycle(4),                2),
    ("C5 (cycle)",         5, cycle(5),                3),
    ("K3 (triangle)",      3, complete(3),             3),
    ("K4 (complete)",      4, complete(4),             4),
    ("K2,3 (bipartite)",   5, complete_bipartite(2, 3), 2),
    ("K1,4 (star)",        5, star(4),                 2),
    ("Bull",               5, BULL,                    3),
    ("W5 (wheel)",         5, WHEEL5,                  3),
    ("Petersen",          10, PETERSEN,                3),
]


# ── brute-force oracle (expected values) ─────────────────────────────────────

def proper_partial(assign: Tuple[int, ...], edges: List[Edge]) -> bool:
    """assign[v] = 0 means uncoloured; >0 is a colour.  Proper iff no edge joins
    two equally-coloured (coloured) endpoints."""
    return all(not (assign[u] and assign[u] == assign[v]) for (u, v) in edges)

def alpha_gprime(n: int, k: int, edges: List[Edge]) -> int:
    """alpha(G') = the maximum number of vertices in a proper partial
    k-colouring = the maximum independent set of the colour-choice graph.
    Enumerates (k+1)^n partial colourings (one colour-or-none per vertex —
    exactly the `option` encoding of the choice clique)."""
    best = 0
    for assign in itertools.product(range(k + 1), repeat=n):
        if proper_partial(assign, edges):
            cnt = sum(1 for c in assign if c)
            if cnt > best:
                best = cnt
                if best == n:
                    return n
    return best

def chromatic(n: int, edges: List[Edge]) -> int:
    k = 1
    while alpha_gprime(n, k, edges) != n:
        k += 1
    return k


# ── Stage-1 colour-choice graph builder (mirrors Stage1.hs / Sorts.v) ─────────

def color_choice(n: int, k: int, edges: List[Edge]):
    slots = [(v, c) for v in range(n) for c in range(1, k + 1)]
    idx = {s: i for i, s in enumerate(slots)}
    E: List[Edge] = []
    for v in range(n):                       # choice clique per vertex
        sv = [idx[(v, c)] for c in range(1, k + 1)]
        for a in range(len(sv)):
            for b in range(a + 1, len(sv)):
                E.append((sv[a], sv[b]))
    for (u, w) in edges:                     # conflict edges (same colour)
        for c in range(1, k + 1):
            E.append((idx[(u, c)], idx[(w, c)]))
    return len(slots), E, slots


def steps_for(nslots: int) -> int:
    """Fewer adiabatic steps for the largest state vectors, to bound runtime."""
    if nslots <= 12:
        return 160
    if nslots <= 14:
        return 130
    if nslots == 15:
        return 120
    return 90


def decode(slots, selected) -> Dict[int, int] | None:
    by_vertex: Dict[int, List[int]] = {}
    for i in selected:
        v, c = slots[i]
        by_vertex.setdefault(v, []).append(c)
    coloring = {}
    for v, cs in by_vertex.items():
        if len(cs) != 1:
            return None
        coloring[v] = cs[0]
    return coloring

def is_proper(n: int, edges: List[Edge], coloring: Dict[int, int]) -> bool:
    if set(coloring) != set(range(n)):
        return False
    return all(coloring[u] != coloring[v] for (u, v) in edges)


# ── driver ───────────────────────────────────────────────────────────────────

def run() -> List[dict]:
    rows: List[dict] = []
    for name, n, edges, known_chi in BENCHMARKS:
        chi = chromatic(n, edges)
        assert chi == known_chi, f"{name}: oracle chi={chi} != known {known_chi}"
        ks = [chi] + ([chi - 1] if chi - 1 >= 1 else [])
        for k in ks:
            nslots, E, slots = color_choice(n, k, edges)
            expected = alpha_gprime(n, k, edges)   # = n iff k-colourable
            colorable = (expected == n)
            row = {
                "name": name, "n": n, "m": len(edges), "chi": chi, "k": k,
                "nslots": nslots, "expected": expected, "colorable": colorable,
            }
            if nslots <= NK_MAX:
                t0 = time.time()
                sel, _ = mwis_graph(nslots, E, steps=steps_for(nslots))
                dt = time.time() - t0
                coloring = decode(slots, sel)
                proper = (coloring is not None and is_proper(n, edges, coloring)
                          if colorable else None)
                row.update({
                    "actual": len(sel), "match": len(sel) == expected,
                    "proper": proper, "seconds": round(dt, 1), "simulated": True,
                })
                tag = "match" if row["match"] else "MISMATCH"
                pr = "" if proper is None else (" proper" if proper else " IMPROPER")
                print(f"  {name:18} k={k}  slots={nslots:2}  "
                      f"expected={expected}  actual={len(sel)}  [{tag}]{pr}"
                      f"  ({dt:.0f}s)")
            else:
                row.update({"actual": None, "match": None, "proper": None,
                            "seconds": None, "simulated": False})
                print(f"  {name:18} k={k}  slots={nslots:2}  "
                      f"expected={expected}  actual=--  [skipped: > {NK_MAX}]")
            rows.append(row)
    return rows


def save(rows: List[dict]) -> None:
    outdir = os.path.join(HERE, "results")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "results.json"), "w") as fh:
        json.dump(rows, fh, indent=2)
    cols = ["name", "n", "m", "chi", "k", "nslots", "expected", "actual",
            "colorable", "match", "proper", "seconds", "simulated"]
    with open(os.path.join(outdir, "results.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c) for c in cols})
    print(f"\nwrote {outdir}/results.json and results.csv")


if __name__ == "__main__":
    print("== graph-colouring benchmarks: expected (oracle) vs actual (Rydberg sim) ==")
    rows = run()
    save(rows)
    # plots
    try:
        import plot
        plot.make_all(rows, os.path.join(HERE, "results"))
    except Exception as e:  # plotting is best-effort
        print(f"(plotting skipped: {e})")
