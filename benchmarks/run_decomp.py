"""Decomposed benchmarks: graphs whose whole colour-choice instance (n*k slots)
is far past the monolithic 2^(n*k) wall (NK_MAX = 16), solved by Split/Stitch so
every actual Rydberg solve stays small.

For each graph we report the would-be monolithic size (n*k) versus the *max
piece slots* actually simulated, the number of device calls, and verify the
stitched colouring is proper (or, for the negative case, that no colouring
exists).  Run:  code/.venv/bin/python benchmarks/run_decomp.py
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

NK_MONO = 16  # the monolithic wall the decomposition is beating


def edges_of(G) -> tuple:
    """Relabel a networkx graph to 0..n-1 and return (n, edge list)."""
    G = nx.convert_node_labels_to_integers(G)
    return G.number_of_nodes(), [tuple(sorted(e)) for e in G.edges()]


# (name, networkx-graph, k, known chi, expected colourable, note)
def cycle(n):
    return nx.cycle_graph(n)

SUITE = [
    ("Petersen",      nx.petersen_graph(),     3, 3, True,  "cubic, χ=3"),
    ("Frucht",        nx.frucht_graph(),       3, 3, True,  "cubic, χ=3"),
    ("Heawood",       nx.heawood_graph(),      2, 2, True,  "bipartite"),
    ("Pappus",        nx.pappus_graph(),       2, 2, True,  "bipartite"),
    ("Desargues",     nx.desargues_graph(),    2, 2, True,  "bipartite"),
    ("Dodecahedral",  nx.dodecahedral_graph(), 3, 3, True,  "cubic, χ=3"),
    ("C30 (cycle)",   cycle(30),               3, 2, True,  "n·k=90, trivial seps"),
    ("C21 (odd)",     cycle(21),               2, 3, False, "odd cycle, NOT 2-col"),
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
        ok = (colorable == exp_col) and (not exp_col or proper)
        whole = n * k
        rows.append({
            "name": name, "n": n, "m": len(edges), "chi": chi, "k": k,
            "whole_slots": whole, "max_piece_slots": st.max_piece_slots,
            "device_calls": st.device_calls, "colorable": colorable,
            "expected_colorable": exp_col, "proper": proper,
            "seconds": round(dt, 1), "ok": ok, "note": note,
        })
        verdict = "PASS" if ok else "FAIL"
        shrink = f"{whole}→{st.max_piece_slots}" if st.max_piece_slots else f"{whole}"
        print(f"  {name:14} k={k}  n·k={whole:3}  "
              f"max piece={st.max_piece_slots:2}  calls={st.device_calls:3}  "
              f"colorable={colorable!s:5}  "
              f"{'proper' if proper else ('—' if proper is None else 'IMPROPER')}"
              f"  [{verdict}]  ({dt:.0f}s)")
    return rows


def save(rows):
    outdir = os.path.join(HERE, "results")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "decomp.json"), "w") as fh:
        json.dump(rows, fh, indent=2)
    cols = ["name", "n", "m", "chi", "k", "whole_slots", "max_piece_slots",
            "device_calls", "colorable", "expected_colorable", "proper",
            "seconds", "ok", "note"]
    with open(os.path.join(outdir, "decomp.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c) for c in cols})
    print(f"\nwrote {outdir}/decomp.json and decomp.csv")


if __name__ == "__main__":
    print("== decomposed benchmarks: whole n·k (would skip) vs max piece slots (simulated) ==")
    print(f"   monolithic wall NK_MAX = {NK_MONO};  base-case piece budget NK_PIECE = 12\n")
    rows = run()
    save(rows)
    try:
        import plot
        plot.make_decomp(rows, os.path.join(HERE, "results"))
    except Exception as e:
        print(f"(plotting skipped: {e})")
