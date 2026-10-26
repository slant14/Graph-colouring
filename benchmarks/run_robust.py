"""Imperfect solves and the robust decoder (paper, Section "Robustness").

The exactness theorems assume the device returns an optimum.  Here we make it
fail on purpose -- an adiabatic sweep much shorter than the one used elsewhere --
and decode *every* shot with the robust decoders:

  * Stage 1 (colour-choice graph G'_k): a shot is an independent set S of G'_k
    with gap  eps = alpha(G'_k) - |S|.  The robust decoder gives every vertex
    without a selected slot a fresh colour, so it returns a proper colouring with
    at most  k + (n - alpha(G'_k)) + eps  colours (Theorem "Robust decoding"; the
    middle term is 0 when G is k-colourable).  We also report a greedy variant
    that first tries the k palette colours.

  * Stage 2 (combinatorial gadget A_4(G'_k)): a shot is an independent set S_A of
    A_4 with weight gap  eps_w = MWIS(A_4) - w(S_A).  Dropping one end of every
    internal edge gives an independent set of G'_k of size >= alpha - eps_w
    (Lemma "Robust edge-path gadget"), which then decodes as above.

Shots are sampled from the final state; bitstrings violating the blockade are
discarded, as on hardware.  Every decoded colouring is checked for properness
and against the bound.

Run:  src/.venv/bin/python benchmarks/run_robust.py
Writes results/robust.{json,csv}.
"""

from __future__ import annotations

import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import csv  # noqa: E402
import json  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402
from collections import Counter  # noqa: E402
from typing import Dict, List, Tuple  # noqa: E402

import numpy as np  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from run_benchmarks import (BENCHMARKS, alpha_gprime, chromatic,  # noqa: E402
                            color_choice, BULL, WHEEL5)
from rydberg_sim import mwis_graph  # noqa: E402

SEED = 20261002
SHOTS = 1000
FAST_T, FAST_STEPS = 1.2, 40          # vs. total_time 4.0, 90-160 steps elsewhere

Edge = Tuple[int, int]


def sample_shots(probs: np.ndarray, rng, shots: int) -> np.ndarray:
    p = probs / probs.sum()
    return rng.choice(len(p), size=shots, p=p)


def is_independent(b: int, edges: List[Edge]) -> bool:
    return not any((b >> u) & 1 and (b >> v) & 1 for (u, v) in edges)


def decode_robust(n: int, k: int, slots, chosen: List[int], edges_g: List[Edge],
                  greedy: bool) -> Dict[int, int]:
    col: Dict[int, int] = {}
    for i in chosen:
        v, c = slots[i]
        col[v] = c                       # at most one slot per vertex (choice clique)
    fresh = k
    nbrs = {v: set() for v in range(n)}
    for (u, v) in edges_g:
        nbrs[u].add(v)
        nbrs[v].add(u)
    for v in range(n):
        if v in col:
            continue
        if greedy:
            used = {col[w] for w in nbrs[v] if w in col}
            free = [c for c in range(1, k + 1) if c not in used]
            if free:
                col[v] = free[0]
                continue
        fresh += 1
        col[v] = fresh
    return col


def proper(col: Dict[int, int], edges_g: List[Edge]) -> bool:
    return all(col[u] != col[v] for (u, v) in edges_g)


# ── Stage 1: shots on the colour-choice graph ─────────────────────────────────

def stage1_case(name: str, n: int, edges_g: List[Edge], k: int, rng) -> dict:
    nslots, E, slots = color_choice(n, k, edges_g)
    alpha = alpha_gprime(n, k, edges_g)
    d = n - alpha
    t0 = time.time()
    _, probs = mwis_graph(nslots, E, total_time=FAST_T, steps=FAST_STEPS)
    shots = sample_shots(probs, rng, SHOTS)
    kept, gaps, ok_bound, ok_proper, k_colourings, greedy_k = 0, Counter(), 0, 0, 0, 0
    for b in shots:
        b = int(b)
        if not is_independent(b, E):
            continue
        kept += 1
        chosen = [i for i in range(nslots) if (b >> i) & 1]
        eps = alpha - len(chosen)
        gaps[eps] += 1
        col = decode_robust(n, k, slots, chosen, edges_g, greedy=False)
        ncol = len(set(col.values()))
        ok_proper += proper(col, edges_g)
        ok_bound += ncol <= k + d + eps
        k_colourings += ncol <= k
        gcol = decode_robust(n, k, slots, chosen, edges_g, greedy=True)
        greedy_k += proper(gcol, edges_g) and len(set(gcol.values())) <= k
    return {"level": "G'_k", "name": name, "n": n, "k": k, "atoms": nslots,
            "alpha": alpha, "d": d, "shots": SHOTS, "independent": kept,
            "gap0": gaps[0], "gap1": gaps[1], "gap2": gaps[2],
            "gap3plus": sum(v for g, v in gaps.items() if g >= 3),
            "proper": ok_proper, "within_bound": ok_bound,
            "k_colourings": k_colourings, "greedy_k_colourings": greedy_k,
            "seconds": round(time.time() - t0, 1)}


# ── Stage 2: shots on the combinatorial gadget A_4(G'_k) ──────────────────────

def a4(nslots: int, E: List[Edge]):
    """A_4: logical atoms 0..nslots-1 (weight 1); edge j=(u,v) -> a_j, b_j."""
    atoms = nslots + 2 * len(E)
    edges, weights = [], [1.0] * nslots + [2.0] * (2 * len(E))
    for j, (u, v) in enumerate(E):
        a, b = nslots + 2 * j, nslots + 2 * j + 1
        edges += [(u, a), (a, b), (b, v)]
    return atoms, edges, weights


def drop_decode(chosen_logical: set, E: List[Edge]) -> set:
    S = set(chosen_logical)
    for (u, v) in E:                    # the decoder of Lemma "Edge-path gadget"
        if u in S and v in S:
            S.discard(u)
    return S


def stage2_case(name: str, n: int, edges_g: List[Edge], k: int, rng) -> dict:
    nslots, E, slots = color_choice(n, k, edges_g)
    alpha = alpha_gprime(n, k, edges_g)
    d = n - alpha
    atoms, EA, w = a4(nslots, E)
    opt = alpha + 2 * len(E)
    t0 = time.time()
    _, probs = mwis_graph(atoms, EA, weights=w, total_time=FAST_T, steps=FAST_STEPS)
    shots = sample_shots(probs, rng, SHOTS)
    kept, gaps, ok_s1, ok_bound, ok_proper = 0, Counter(), 0, 0, 0
    for b in shots:
        b = int(b)
        if not is_independent(b, EA):
            continue
        kept += 1
        sel = [i for i in range(atoms) if (b >> i) & 1]
        eps_w = opt - sum(w[i] for i in sel)
        gaps[int(round(eps_w))] += 1
        S1 = drop_decode({i for i in sel if i < nslots}, E)
        ok_s1 += len(S1) >= alpha - eps_w and all(not (u in S1 and v in S1) for (u, v) in E)
        col = decode_robust(n, k, slots, sorted(S1), edges_g, greedy=False)
        ok_proper += proper(col, edges_g)
        ok_bound += len(set(col.values())) <= k + d + eps_w
    return {"level": "A_4", "name": name, "n": n, "k": k, "atoms": atoms,
            "alpha": alpha, "d": d, "shots": SHOTS, "independent": kept,
            "gap0": gaps[0], "gap1": gaps[1], "gap2": gaps[2],
            "gap3plus": sum(v for g, v in gaps.items() if g >= 3),
            "stage2_bound": ok_s1, "proper": ok_proper, "within_bound": ok_bound,
            "seconds": round(time.time() - t0, 1)}


def main() -> None:
    rng = np.random.default_rng(SEED)
    rows = []
    print(f"== imperfect solves: sweep T={FAST_T}, {FAST_STEPS} steps, {SHOTS} shots ==")
    for name, n, edges, chi in BENCHMARKS:
        if name.startswith("Petersen"):
            continue
        r = stage1_case(name, n, edges, chi, rng)
        rows.append(r)
        print(f"  G'_k {name:18} k={chi} slots={r['atoms']:2}  IS shots={r['independent']:4}"
              f"  gap0/1/2/3+={r['gap0']}/{r['gap1']}/{r['gap2']}/{r['gap3plus']}"
              f"  proper={r['proper']}  bound={r['within_bound']}"
              f"  k-col(fresh/greedy)={r['k_colourings']}/{r['greedy_k_colourings']}"
              f"  ({r['seconds']}s)", flush=True)
    for name, n, edges, k in [("K2", 2, [(0, 1)], 2), ("K2", 2, [(0, 1)], 1),
                              ("P3", 3, [(0, 1), (1, 2)], 1),
                              ("K3", 3, [(0, 1), (1, 2), (0, 2)], 1),
                              ("P4", 4, [(0, 1), (1, 2), (2, 3)], 1),
                              ("C4", 4, [(0, 1), (1, 2), (2, 3), (3, 0)], 1)]:
        r = stage2_case(name, n, edges, k, rng)
        rows.append(r)
        print(f"  A_4  {name:18} k={k} atoms={r['atoms']:2}  IS shots={r['independent']:4}"
              f"  gap0/1/2/3+={r['gap0']}/{r['gap1']}/{r['gap2']}/{r['gap3plus']}"
              f"  stage2-bound={r['stage2_bound']}  proper={r['proper']}"
              f"  bound={r['within_bound']}  ({r['seconds']}s)", flush=True)

    out = os.path.join(HERE, "results")
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "robust.json"), "w") as fh:
        json.dump({"seed": SEED, "shots": SHOTS, "total_time": FAST_T,
                   "steps": FAST_STEPS, "rows": rows}, fh, indent=1)
    cols = sorted({c for r in rows for c in r}, key=lambda c: list(rows[0]).index(c)
                  if c in rows[0] else 100)
    with open(os.path.join(out, "robust.csv"), "w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=cols)
        wr.writeheader()
        for r in rows:
            wr.writerow(r)
    allok = all(r["proper"] == r["independent"] and r["within_bound"] == r["independent"]
                and r.get("stage2_bound", r["independent"]) == r["independent"] for r in rows)
    print("ALL decoded shots proper and within the bound" if allok else "BOUND VIOLATED")
    print(f"wrote {out}/robust.json and robust.csv")


if __name__ == "__main__":
    main()
