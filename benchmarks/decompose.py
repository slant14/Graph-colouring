"""Decomposed compilation (type-system.tex, Refinement C: Split / Stitch).

The monolithic benchmark simulates the whole colour-choice graph, so it is
capped by a 2^(n*k) state vector (NK_MAX = 16).  Decomposition breaks that wall:
a separator S splits G, we *precolour* S and solve each piece independently on a
*small* device, then stitch the pieces (they agree on S by construction).  Peak
device size is O((w*k)^2) in the separator width w, **independent of n**, so the
whole-graph n*k can grow without bound while every Rydberg solve stays tiny.

Algorithm (exact, nested precolouring dissection):

    solve(V, k, pinned):
      if (#pinned + k*#free) <= NK_PIECE:      # small enough for the device
          return device_solve(V, k, pinned)    # Rydberg MWIS base case
      S := balanced separator of the free part
      for each proper colouring betaS of S (consistent with pinned):
          for each component C of (free \ S):
              boundary := (pinned u S) adjacent to C        # only real neighbours
              sub := solve(C u boundary, k, pinned u betaS restricted to boundary)
              if sub is None: this betaS fails
          if all components solved: stitch -> full colouring
      return None  (no betaS extends)  ==> G not k-colourable

The device is the genuine adiabatic Rydberg engine
(`src/sim/rydberg_sim.mwis_graph`); only the boundary table and the stitch are
classical, exactly as the note prescribes ("bounded search over the boundary
table, at most k^|S| candidate beta").
"""

from __future__ import annotations

import itertools
import os
import sys
from typing import Dict, List, Optional, Set

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "src", "sim"))
from rydberg_sim import mwis_graph  # noqa: E402

Adj = Dict[int, Set[int]]


class Stats:
    def __init__(self) -> None:
        self.device_calls = 0
        self.max_piece_slots = 0
        self.piece_slot_hist: List[int] = []


# ── graph helpers ─────────────────────────────────────────────────────────────

def adjacency(n_or_verts, edges) -> Adj:
    verts = range(n_or_verts) if isinstance(n_or_verts, int) else n_or_verts
    adj: Adj = {v: set() for v in verts}
    for u, w in edges:
        adj[u].add(w)
        adj[w].add(u)
    return adj

def components(verts: Set[int], adj: Adj) -> List[Set[int]]:
    """Connected components of the subgraph induced on `verts`."""
    seen: Set[int] = set()
    out: List[Set[int]] = []
    for s in verts:
        if s in seen:
            continue
        comp = {s}
        stack = [s]
        seen.add(s)
        while stack:
            x = stack.pop()
            for y in adj[x] & verts:
                if y not in seen:
                    seen.add(y)
                    comp.add(y)
                    stack.append(y)
        out.append(comp)
    return out


def find_separator(free: Set[int], adj: Adj, maxsep: int) -> Optional[Set[int]]:
    """A balanced vertex separator of the *free* subgraph: the smallest set whose
    removal disconnects it, minimising the largest remaining component."""
    free = set(free)
    if not components_connected(free, adj):
        return set()  # already disconnected: separate with empty S
    flist = sorted(free)
    upper = min(maxsep, len(flist) - 1)
    for s in range(1, upper + 1):
        best: Optional[Set[int]] = None
        best_score = None
        for S in itertools.combinations(flist, s):
            Sset = set(S)
            rest = free - Sset
            comps = components(rest, adj)
            if len(comps) >= 2:
                score = max(len(c) for c in comps)
                if best_score is None or score < best_score:
                    best_score = score
                    best = Sset
        if best is not None:
            return best
    return None

def components_connected(verts: Set[int], adj: Adj) -> bool:
    return len(components(verts, adj)) <= 1


# ── proper colourings of a separator (the boundary table) ────────────────────

def proper_colorings(S: List[int], adj: Adj, k: int,
                     pinned: Dict[int, int]):
    """All colourings of S in 1..k that are proper on edges inside S and against
    already-pinned neighbours.  Yields dicts; backtracking keeps it to the
    feasible k^|S| frontier."""
    S = list(S)

    def rec(i: int, cur: Dict[int, int]):
        if i == len(S):
            yield dict(cur)
            return
        v = S[i]
        forbidden = {pinned[w] for w in adj[v] if w in pinned}
        forbidden |= {cur[w] for w in adj[v] if w in cur}
        for c in range(1, k + 1):
            if c not in forbidden:
                cur[v] = c
                yield from rec(i + 1, cur)
                del cur[v]
    yield from rec(0, {})


# ── device base case: precoloured Rydberg MWIS solve ─────────────────────────

def device_solve(verts: Set[int], k: int, pinned: Dict[int, int],
                 adj: Adj, stats: Stats) -> Optional[Dict[int, int]]:
    """Build the precoloured colour-choice graph of the piece, solve it on the
    Rydberg engine, and decode a colouring extending `pinned` (or None)."""
    verts = sorted(verts)
    # slots: pinned vertex -> its single colour; free vertex -> k colour slots
    slot_of: Dict[tuple, int] = {}
    slots: List[tuple] = []
    for v in verts:
        if v in pinned:
            slots.append((v, pinned[v]))
        else:
            for c in range(1, k + 1):
                slots.append((v, c))
    for i, s in enumerate(slots):
        slot_of[s] = i
    nslots = len(slots)

    E: List[tuple] = []
    for v in verts:                                  # choice clique (free only)
        if v in pinned:
            continue
        sv = [slot_of[(v, c)] for c in range(1, k + 1)]
        for a in range(len(sv)):
            for b in range(a + 1, len(sv)):
                E.append((sv[a], sv[b]))
    vset = set(verts)
    for v in verts:                                  # conflict edges
        for w in adj[v] & vset:
            if v < w:
                cv = [pinned[v]] if v in pinned else range(1, k + 1)
                cw = set([pinned[w]] if w in pinned else range(1, k + 1))
                for c in cv:
                    if c in cw:
                        E.append((slot_of[(v, c)], slot_of[(w, c)]))

    stats.device_calls += 1
    stats.max_piece_slots = max(stats.max_piece_slots, nslots)
    stats.piece_slot_hist.append(nslots)

    sel, _ = mwis_graph(nslots, E, steps=_steps(nslots))
    chosen = [slots[i] for i in sel]
    coloring: Dict[int, int] = {}
    for (v, c) in chosen:
        if v in coloring:                            # >1 slot per vertex: invalid
            return None
        coloring[v] = c
    if set(coloring) != vset:                        # not a full (alpha=n) IS
        return None
    # honour pins and properness
    for v, c in pinned.items():
        if v in coloring and coloring[v] != c:
            return None
    for v in verts:
        for w in adj[v] & vset:
            if coloring[v] == coloring[w]:
                return None
    return coloring


def _steps(nslots: int) -> int:
    # Reliable schedule (the one under which the decomp suite passed 100%):
    # too few steps makes the adiabatic ramp miss the ground state, the piece
    # spuriously returns infeasible, and the parent backtracks over boundary
    # colourings — a correctness *and* speed disaster.  Keep it conservative.
    if nslots <= 12:
        return 160
    if nslots <= 14:
        return 130
    return 110


# ── recursive solve ───────────────────────────────────────────────────────────

def solve(verts: Set[int], k: int, pinned: Dict[int, int], adj: Adj,
          stats: Stats, nk_piece: int = 12, maxsep: int = 4
          ) -> Optional[Dict[int, int]]:
    verts = set(verts)
    free = {v for v in verts if v not in pinned}
    slots = (len(verts) - len(free)) + k * len(free)
    if slots <= nk_piece or len(free) <= 1:
        return device_solve(verts, k, pinned, adj, stats)

    S = find_separator(free, adj, maxsep)
    if not S:
        # Irreducible free part (a bare edge, a small clique): it cannot be split,
        # yet at large k even two free vertices is 2k slots -- past the device
        # wall.  Pin one free vertex and branch over its colours; `free` shrinks
        # by one each step, so we descend to the len(free)<=1 base case where the
        # device piece is only (boundary + k) slots.  Pinning a vertex is always
        # valid, so this stays exact (nested precolouring dissection).
        if len(free) >= 2:
            v = max(free, key=lambda x: len(adj[x] & verts))
            forbidden = {pinned[w] for w in adj[v] if w in pinned}
            for c in range(1, k + 1):
                if c in forbidden:
                    continue
                sub = solve(verts, k, {**pinned, v: c}, adj, stats, nk_piece, maxsep)
                if sub is not None:
                    return sub
            return None
        return device_solve(verts, k, pinned, adj, stats)  # single free vertex

    rest = free - S
    comps = components(rest, adj)
    Slist = sorted(S)
    for betaS in proper_colorings(Slist, adj, k, pinned):
        full = dict(pinned)
        full.update(betaS)
        ok = True
        for C in comps:
            boundary = set()
            for c in C:
                boundary |= adj[c] & (set(pinned) | S)
            piece_verts = set(C) | boundary
            piece_pinned = {b: full[b] for b in boundary}
            sub = solve(piece_verts, k, piece_pinned, adj, stats, nk_piece, maxsep)
            if sub is None:
                ok = False
                break
            full.update(sub)
        if ok:
            return full
    return None


def is_proper_full(n: int, edges, coloring: Dict[int, int], k: int) -> bool:
    if set(coloring) != set(range(n)):
        return False
    if any(not (1 <= c <= k) for c in coloring.values()):
        return False
    return all(coloring[u] != coloring[w] for (u, w) in edges)
