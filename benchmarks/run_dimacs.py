"""DIMACS Mycielski benchmark: the canonical hard graph-colouring family, run
end-to-end through the certified decomposition + Rydberg-MWIS pipeline.

The Mycielskians ``myciel3..myciel6`` are the standard DIMACS colouring instances
(triangle-free yet with chromatic number growing without bound -- the textbook
"hard to colour" family, since greedy/clique bounds are useless on them).  Here
``myciel_k`` is the Mycielskian of order ``k+1`` in ``networkx``:

    myciel3 : n=11  m= 20  chi=4
    myciel4 : n=23  m= 71  chi=5
    myciel5 : n=47  m=236  chi=6   (beyond the device reach: dense, large
    myciel6 : n=95  m=755  chi=7    separators -- listed but skipped by default)

For each instance we exercise the pipeline in BOTH directions, which together
*certify the chromatic number exactly*:

  * feasible    : k = chi  -- the engine must find a proper colouring,
  * infeasible  : k = chi-1 -- the engine must prove NO colouring exists
                  (full backtracking over the boundary table; this is the
                  expensive direction and the real correctness test).

Monolithically each instance is a 2^(n*chi) state vector (myciel3 alone is
2^44, already hopeless); decomposition keeps every Rydberg solve to ~k+boundary
slots.  Whole n*chi vs max simulated piece is reported and plotted.

Run:
    code/.venv/bin/python benchmarks/run_dimacs.py            # default suite
    code/.venv/bin/python benchmarks/run_dimacs.py --feasible-only   # skip the
                                                   # slow infeasible proofs
    code/.venv/bin/python benchmarks/run_dimacs.py --full     # add myciel4 k=4
                                                   # (very slow infeasible proof)
"""

from __future__ import annotations

import argparse
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


# (label, mycielski order, chi) -- the DIMACS myciel family within device reach.
FAMILY = [
    ("myciel3", 4, 4),
    ("myciel4", 5, 5),
]

# Cells to run: (label, mycielski_order, k, expected_colorable, chi, note).
# Both directions per instance certify chi exactly.  The infeasible (k=chi-1)
# proofs exhaust the boundary backtracking and are the slow, decisive test.
def build_suite(full: bool) -> List[tuple]:
    suite: List[tuple] = []
    for label, order, chi in FAMILY:
        suite.append((label, order, chi, True, chi,
                      f"k=chi={chi}: proper colouring exists"))
        # the exact-chi witness: not (chi-1)-colourable.  myciel4 k=4 is very
        # slow (deep infeasible backtracking) so it is gated behind --full.
        if label == "myciel3" or full:
            suite.append((label, order, chi - 1, False, chi,
                          f"k=chi-1={chi-1}: certifies chi (no colouring)"))
    return suite


def run(suite: List[tuple]) -> List[dict]:
    rows = []
    for label, order, k, exp_col, chi, note in suite:
        G = nx.mycielski_graph(order)
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
            "name": label, "n": n, "m": len(edges), "chi": chi, "k": k,
            "direction": "feasible" if exp_col else "infeasible",
            "whole_slots": whole, "max_piece_slots": st.max_piece_slots,
            "device_calls": st.device_calls, "colors_used": ncolors,
            "colorable": colorable, "expected_colorable": exp_col,
            "proper": proper, "seconds": round(dt, 1), "ok": ok, "note": note,
        })
        verdict = "PASS" if ok else "FAIL"
        dirn = "feasible  " if exp_col else "infeasible"
        print(f"  {label:8} chi={chi} k={k} [{dirn}]  n={n:2} m={len(edges):3}  "
              f"n·k={whole:3}  max piece={st.max_piece_slots:2}  "
              f"calls={st.device_calls:3}  colourable={str(colorable):5}  "
              f"(exp {str(exp_col):5})  [{verdict}]  ({dt:.0f}s)")
    return rows


def save(rows):
    outdir = os.path.join(HERE, "results")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "dimacs.json"), "w") as fh:
        json.dump(rows, fh, indent=2)
    cols = ["name", "n", "m", "chi", "k", "direction", "whole_slots",
            "max_piece_slots", "device_calls", "colors_used", "colorable",
            "expected_colorable", "proper", "seconds", "ok", "note"]
    with open(os.path.join(outdir, "dimacs.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c) for c in cols})
    print(f"\nwrote {outdir}/dimacs.json and dimacs.csv")


def main(argv) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--feasible-only", action="store_true",
                    help="run only the k=chi feasible direction (skip the slow "
                         "infeasible chi-certifying proofs)")
    ap.add_argument("--full", action="store_true",
                    help="also run myciel4 at k=4 (very slow infeasible proof)")
    args = ap.parse_args(argv)

    suite = build_suite(args.full)
    if args.feasible_only:
        suite = [c for c in suite if c[3]]  # exp_col == True

    print("== DIMACS Mycielski family via decomposition (monolithic = 2^(n·chi),"
          " impossible) ==")
    print("   feasible k=chi finds a colouring; infeasible k=chi-1 certifies chi"
          " exactly\n")
    rows = run(suite)
    save(rows)

    all_ok = all(r["ok"] for r in rows)
    print(f"\n{'ALL PASS' if all_ok else 'SOME FAILED'}  "
          f"({sum(r['ok'] for r in rows)}/{len(rows)})")
    try:
        import plot
        plot.make_decomp(rows, os.path.join(HERE, "results"), fname="dimacs.svg")
    except Exception as e:
        print(f"(plotting skipped: {e})")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
