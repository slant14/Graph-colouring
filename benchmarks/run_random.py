"""Random Erdos-Renyi G(n,p) instances through the Stage-1 pipeline, compared
against the brute-force oracle -- the randomized companion of run_benchmarks.py
(paper, Table "Random G(n,p) instances").

Protocol (fixed before running, identical to run_benchmarks.py otherwise):

  * for each (n, p) cell draw INSTANCES graphs G(n,p) from a fixed seed and
    discard none;
  * compute chi(G) with the oracle, then run the Stage-1 colour-choice graph G'_k
    on the abstract Rydberg engine at every k in {chi, chi-1} (k >= 1) with
    n*k <= NK_MAX, i.e. in both directions wherever the classical-simulation
    wall permits;
  * an instance for which neither direction fits under the wall (chi-1 > NK_MAX//n)
    is run once at the largest palette k = NK_MAX//n, which is then necessarily a
    non-colourable run, so that every drawn instance contributes;
  * agreement means |IS returned by the simulation| == alpha(G'_k) (oracle), and
    every colourable run must decode to a verified-proper colouring.

Densities straddle the colourability threshold of the palettes the wall admits
(k <= 3 at n = 5, k <= 2 for n >= 6), so both verdicts occur.

Run:  src/.venv/bin/python benchmarks/run_random.py  [--workers W]
Writes results/random.{json,csv}.
"""

from __future__ import annotations

import os

# Pin BLAS to one thread *before* numpy loads (as rydberg_sim.py does); with
# several worker processes a per-process BLAS pool oversubscribes the CPU.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse  # noqa: E402
import csv  # noqa: E402
import json  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402
from multiprocessing import Pool  # noqa: E402
from typing import List, Tuple  # noqa: E402

import numpy as np  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from run_benchmarks import (NK_MAX, alpha_gprime, chromatic, color_choice,  # noqa: E402
                            decode, is_proper, steps_for)
from rydberg_sim import mwis_graph  # noqa: E402  (path set by run_benchmarks)

SEED = 20260901
INSTANCES = 20
# (n, p) cells; n*k <= 16 admits k <= 4 (n = 4), k <= 3 (n = 5), k <= 2 (n >= 6)
CELLS: List[Tuple[int, float]] = [
    (4, 0.5),
    (5, 0.3), (5, 0.5), (5, 0.7),
    (6, 0.2), (6, 0.35),
    (7, 0.2),
    (8, 0.15),
]

Edge = Tuple[int, int]


def gnp(rng: np.random.Generator, n: int, p: float) -> List[Edge]:
    return [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < p]


def draw_all() -> List[dict]:
    """All instances, deterministically from SEED (one sub-stream per cell)."""
    jobs = []
    for ci, (n, p) in enumerate(CELLS):
        rng = np.random.default_rng([SEED, ci])
        for i in range(INSTANCES):
            edges = gnp(rng, n, p)
            jobs.append({"n": n, "p": p, "idx": i, "edges": edges})
    return jobs


def palettes(n: int, chi: int) -> List[int]:
    kmax = NK_MAX // n
    ks = [k for k in (chi, chi - 1) if 1 <= k <= kmax]
    if not ks:
        ks = [kmax]               # chi-1 > kmax: the largest admissible k is < chi
    return ks


def run_instance(job: dict) -> List[dict]:
    n, edges = job["n"], job["edges"]
    chi = chromatic(n, edges)
    rows = []
    for k in palettes(n, chi):
        nslots, E, slots = color_choice(n, k, edges)
        expected = alpha_gprime(n, k, edges)
        colorable = expected == n
        t0 = time.time()
        sel, _ = mwis_graph(nslots, E, steps=steps_for(nslots))
        dt = time.time() - t0
        coloring = decode(slots, sel)
        proper = (coloring is not None and is_proper(n, edges, coloring)) if colorable else None
        rows.append({
            "n": n, "p": job["p"], "idx": job["idx"], "m": len(edges), "chi": chi,
            "k": k, "nslots": nslots, "expected": expected, "actual": len(sel),
            "match": len(sel) == expected, "colorable": colorable,
            "proper": proper, "seconds": round(dt, 1),
            "edges": edges,
        })
    return rows


def summarize(rows: List[dict]) -> List[dict]:
    out = []
    for (n, p) in CELLS:
        rs = [r for r in rows if r["n"] == n and r["p"] == p]
        col = [r for r in rs if r["colorable"]]
        out.append({
            "n": n, "p": p,
            "instances": len({r["idx"] for r in rs}),
            "ks": sorted({r["k"] for r in rs}),
            "chis": sorted({r["chi"] for r in rs}),
            "runs": len(rs),
            "colorable_runs": len(col),
            "noncolorable_runs": len(rs) - len(col),
            "matches": sum(r["match"] for r in rs),
            "proper": sum(bool(r["proper"]) for r in col),
        })
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 2) - 2))
    args = ap.parse_args()

    jobs = draw_all()
    print(f"== random G(n,p): {len(jobs)} instances, seed {SEED}, "
          f"{args.workers} workers ==")
    t0 = time.time()
    rows: List[dict] = []
    with Pool(args.workers) as pool:
        for rs in pool.imap_unordered(run_instance, jobs):
            for r in rs:
                tag = "match" if r["match"] else "MISMATCH"
                pr = "" if r["proper"] is None else (" proper" if r["proper"] else " IMPROPER")
                print(f"  n={r['n']} p={r['p']:<4} #{r['idx']:<2} m={r['m']:<2} chi={r['chi']} "
                      f"k={r['k']} slots={r['nslots']:<2} expected={r['expected']} "
                      f"actual={r['actual']} [{tag}]{pr} ({r['seconds']}s)", flush=True)
            rows.extend(rs)
    rows.sort(key=lambda r: (CELLS.index((r["n"], r["p"])), r["idx"], -r["k"]))
    summary = summarize(rows)

    outdir = os.path.join(HERE, "results")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "random.json"), "w") as fh:
        json.dump({"seed": SEED, "instances_per_cell": INSTANCES, "nk_max": NK_MAX,
                   "summary": summary, "runs": rows}, fh, indent=1)
    cols = ["n", "p", "idx", "m", "chi", "k", "nslots", "expected", "actual",
            "match", "colorable", "proper", "seconds"]
    with open(os.path.join(outdir, "random.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c) for c in cols})

    print(f"\n{'n':>2} {'p':>5} {'inst':>4} {'k':>6} {'col/not':>8} {'match':>7} {'proper':>7}")
    for s in summary:
        print(f"{s['n']:>2} {s['p']:>5} {s['instances']:>4} {str(s['ks']):>6} "
              f"{s['colorable_runs']:>3}/{s['noncolorable_runs']:<4} "
              f"{s['matches']:>3}/{s['runs']:<3} {s['proper']:>3}/{s['colorable_runs']:<3}")
    tot_runs = sum(s["runs"] for s in summary)
    print(f"total: {sum(s['matches'] for s in summary)}/{tot_runs} match, "
          f"{sum(s['proper'] for s in summary)}/{sum(s['colorable_runs'] for s in summary)} proper"
          f"  ({time.time() - t0:.0f}s)")
    print(f"wrote {outdir}/random.json and random.csv")


if __name__ == "__main__":
    main()
