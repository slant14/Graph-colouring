"""Decomposition where it *means* something: relatively large n AND large k at
the same time, actually simulated on the Rydberg engine.

Monolithically each of these is a 2^(n*k) state vector — e.g. P30 at k=10 is
2^300, utterly impossible. Split/Stitch keeps every device solve to a single
free vertex's choice clique plus its (small) precoloured boundary, so the peak
simulated piece stays around k+boundary ≲ 12 slots while the whole-graph n*k
runs into the hundreds. The point of decomposition, made concrete.

Graphs are chosen with small separators (bounded treewidth: cycles, paths,
ladders tw≤2; the cubic graphs need width-3 separators) so the boundary table
k^|S| stays small and the first feasible boundary colouring extends.

Run:  src/.venv/bin/python benchmarks/run_largenk.py
"""

from __future__ import annotations

import csv
import json
import os
import sys
import time
from typing import List

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import decompose as D  # noqa: E402


def edges_of(G) -> tuple:
    G = nx.convert_node_labels_to_integers(G)
    return G.number_of_nodes(), [tuple(sorted(e)) for e in G.edges()]


# (name, networkx graph, k, chi, expected colourable, note)
# k=8 on the structural graphs (pieces ≈ k+boundary ≤ 11 slots), plus a star at
# k=10 — pinning the hub keeps every piece to k+1 = 11 slots, the clean way to
# push k high without stiff large cliques.
SUITE = [
    ("C24 (cycle)",   nx.cycle_graph(24),         8, 2, True, "n·k=192, 2^192 monolithic"),
    ("Ladder 2x10",   nx.grid_2d_graph(2, 10),    8, 2, True, "tw 2, n·k=160"),
    ("Petersen",      nx.petersen_graph(),        8, 3, True, "cubic, n·k=80"),
    ("Dodecahedral",  nx.dodecahedral_graph(),    8, 3, True, "cubic, n·k=160"),
    ("Star K1,12",    nx.star_graph(12),         10, 2, True, "k=10, n·k=130"),
]


def run() -> List[dict]:
    rows = []
    for name, G, k, chi, exp_col, note in SUITE:
        n, edges = edges_of(G)
        adj = D.adjacency(n, edges)
        st = D.Stats()
        t0 = time.time()
        col = D.solve(set(range(n)), k, {}, adj, st)
        dt = time.time() - t0
        colorable = col is not None
        proper = D.is_proper_full(n, edges, col, k) if col else None
        ncolors = len(set(col.values())) if col else 0
        ok = (colorable == exp_col) and (not exp_col or proper)
        whole = n * k
        rows.append({
            "name": name, "n": n, "m": len(edges), "chi": chi, "k": k,
            "whole_slots": whole, "max_piece_slots": st.max_piece_slots,
            "device_calls": st.device_calls, "colors_used": ncolors,
            "colorable": colorable, "expected_colorable": exp_col,
            "proper": proper, "seconds": round(dt, 1), "ok": ok, "note": note,
        })
        verdict = "PASS" if ok else "FAIL"
        print(f"  {name:14} n={n:2} k={k:2}  n·k={whole:3}  "
              f"max piece={st.max_piece_slots:2}  calls={st.device_calls:3}  "
              f"colours used={ncolors:2}  "
              f"{'proper' if proper else 'IMPROPER'}  [{verdict}]  ({dt:.0f}s)")
    return rows


def save(rows):
    outdir = os.path.join(HERE, "results")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "largenk.json"), "w") as fh:
        json.dump(rows, fh, indent=2)
    cols = ["name", "n", "m", "chi", "k", "whole_slots", "max_piece_slots",
            "device_calls", "colors_used", "colorable", "expected_colorable",
            "proper", "seconds", "ok", "note"]
    with open(os.path.join(outdir, "largenk.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c) for c in cols})
    print(f"\nwrote {outdir}/largenk.json and largenk.csv")


if __name__ == "__main__":
    print("== large n AND k via decomposition (monolithic = 2^(n·k), impossible) ==")
    print("   every device solve stays ~k+boundary slots; whole n·k in the hundreds\n")
    rows = run()
    save(rows)
    try:
        import plot
        plot.make_decomp(rows, os.path.join(HERE, "results"), fname="largenk.svg")
    except Exception as e:
        print(f"(plotting skipped: {e})")
