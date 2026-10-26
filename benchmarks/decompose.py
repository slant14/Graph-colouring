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

The device is the adiabatic Rydberg engine (`src/sim/rydberg_sim.mwis_graph`);
the boundary table and the stitch are classical ("bounded search over the
boundary table, at most k^|S| candidate beta").

Certificates.  A colouring the device returns is a *witness*: it is checked
classically for properness before use.  A device solve that returns no full
independent set is NOT a proof that the piece is infeasible (an imperfect
adiabatic sweep can miss the optimum), so every such leaf is decided exactly by
a classical search over its at most NK_PIECE-ish slots.  A "not k-colourable"
verdict is therefore a classical certificate -- exhaustive boundary enumeration
plus exact leaf checks -- while the device supplies the colourings.  The stats
count how often the device found the witness itself (`device_witnesses`) and
how often a colourable leaf was missed by the device and recovered classically
(`device_misses`).
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
        self.device_witnesses = 0    # leaves solved by the device (verified)
        self.classical_checks = 0    # leaves the device failed on, decided exactly
        self.device_misses = 0       # ... of which were colourable after all


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

def exact_extension(verts: Set[int], k: int, pinned: Dict[int, int],
                    adj: Adj) -> Optional[Dict[int, int]]:
    """Exact classical search: a proper k-colouring of G[verts] extending
    `pinned`, or None if none exists (backtracking; leaves are tiny)."""
    verts = set(verts)
    for v, c in pinned.items():                      # pins must agree already
        if any(w in pinned and pinned[w] == c for w in adj[v] & verts):
            return None
    free = sorted((v for v in verts if v not in pinned),
                  key=lambda x: -len(adj[x] & verts))
    cur = dict(pinned)

    def rec(i: int) -> bool:
        if i == len(free):
            return True
        v = free[i]
        used = {cur[w] for w in adj[v] & verts if w in cur}
        for c in range(1, k + 1):
            if c not in used:
                cur[v] = c
                if rec(i + 1):
                    return True
                del cur[v]
        return False

    return {v: cur[v] for v in verts} if rec(0) else None


def device_solve(verts: Set[int], k: int, pinned: Dict[int, int],
                 adj: Adj, stats: Stats) -> Optional[Dict[int, int]]:
    """Solve one leaf piece: the device proposes a colouring extending `pinned`;
    if it returns none, the leaf is decided exactly by `exact_extension`, so an
    infeasible verdict is a classical certificate, never a device outcome."""
    col = _device_attempt(verts, k, pinned, adj, stats)
    if col is not None:
        stats.device_witnesses += 1
        return col
    stats.classical_checks += 1
    col = exact_extension(set(verts), k, pinned, adj)
    if col is not None:
        stats.device_misses += 1
    return col


def _device_attempt(verts: Set[int], k: int, pinned: Dict[int, int],
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
    """Colouring of G[verts] extending `pinned`, or None (see `solve_cert`)."""
    return solve_cert(verts, k, pinned, adj, stats, nk_piece, maxsep)[0]


# ── certificates (checked by the verified checker of proof/Certificate.v) ─────
#
# A refutation is a tree over colour domains, mirroring Certificate.check_ref:
#   ('E', v)               v has no colour left
#   ('C', u, v)            edge uv with both ends fixed to the same colour
#   ('S', v, c, yes, no)   split on "v gets colour c"
#   ('R', [verts], sub)    restrict to a sub-piece
# Colours are 1..k here and written 0-indexed.  In the context of a node the
# domain of a pinned vertex is the singleton of its colour and every other
# vertex has the full palette; `_branch_chain` reproduces exactly the domains
# check_ref computes (yes: [c]; no: c removed, order kept).

def _branch_chain(v: int, k: int, yes_for):
    """Split v over all k colours: S v 1 (yes 1) (S v 2 (yes 2) ... (yes k))."""
    def chain(c: int):
        if c == k:
            return yes_for(c)
        return ('S', v, c, yes_for(c), chain(c + 1))
    return chain(1)


def refute_leaf(W: Set[int], k: int, pinned: Dict[int, int], adj: Adj):
    """Exhaustive refutation that G[W] has no proper k-colouring extending
    `pinned`, or None if one exists."""
    W = set(W)
    order = sorted(W, key=lambda x: (-len(adj[x] & W), x))
    dom0 = {v: ([pinned[v]] if v in pinned else list(range(1, k + 1))) for v in W}

    def rec(dom):
        for v in order:
            if not dom[v]:
                return ('E', v)
        for u in order:
            if len(dom[u]) == 1:
                for w in adj[u] & W:
                    if dom[w] == dom[u]:
                        return ('C', u, w)
        v = next((x for x in order if len(dom[x]) >= 2), None)
        if v is None:
            return None                      # every domain fixed, no clash
        c = dom[v][0]
        yes = rec({**dom, v: [c]})
        if yes is None:
            return None
        no = rec({**dom, v: [x for x in dom[v] if x != c]})
        if no is None:
            return None
        return ('S', v, c, yes, no)

    return rec(dom0)


def solve_cert(verts: Set[int], k: int, pinned: Dict[int, int], adj: Adj,
               stats: Stats, nk_piece: int = 12, maxsep: int = 4):
    """Returns (colouring, None) or (None, refutation)."""
    verts = set(verts)
    free = {v for v in verts if v not in pinned}
    slots = (len(verts) - len(free)) + k * len(free)
    if slots <= nk_piece or len(free) <= 1:
        col = device_solve(verts, k, pinned, adj, stats)
        if col is not None:
            return col, None
        return None, refute_leaf(verts, k, pinned, adj)

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
            forbidden = {pinned[w]: w for w in adj[v] if w in pinned}
            failing = {}
            for c in range(1, k + 1):
                if c in forbidden:
                    continue
                sub, cert = solve_cert(verts, k, {**pinned, v: c}, adj, stats,
                                       nk_piece, maxsep)
                if sub is not None:
                    return sub, None
                failing[c] = cert
            return None, _branch_chain(
                v, k, lambda c: ('C', v, forbidden[c]) if c in forbidden else failing[c])
        col = device_solve(verts, k, pinned, adj, stats)  # single free vertex
        if col is not None:
            return col, None
        return None, refute_leaf(verts, k, pinned, adj)

    rest = free - S
    comps = components(rest, adj)
    Slist = sorted(S)
    failing = {}
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
            sub, cert = solve_cert(piece_verts, k, piece_pinned, adj, stats,
                                   nk_piece, maxsep)
            if sub is None:
                failing[tuple(sorted(betaS.items()))] = (sorted(piece_verts), cert)
                ok = False
                break
            full.update(sub)
        if ok:
            return full, None

    # every proper boundary colouring failed: split over S, close improper
    # boundary colourings by a clash, restrict the rest to their failing piece
    def gen(i: int, assign: Dict[int, int]):
        if i == len(Slist):
            piece, cert = failing[tuple(sorted(assign.items()))]
            return ('R', piece, cert)
        s_ = Slist[i]

        def yes_for(c: int):
            for w in sorted(adj[s_] & verts):
                if pinned.get(w) == c or assign.get(w) == c:
                    return ('C', s_, w)
            return gen(i + 1, {**assign, s_: c})
        return _branch_chain(s_, k, yes_for)

    return None, gen(0, {})


def cert_nodes(cert) -> int:
    n, stack = 0, [cert]
    while stack:
        node = stack.pop()
        n += 1
        if node[0] == 'S':
            stack += [node[3], node[4]]
        elif node[0] == 'R':
            stack.append(node[2])
    return n


def write_certificate(path: str, n: int, edges, k: int, coloring=None,
                      refutation=None) -> None:
    """Write a certificate in the format read by proof/checker/certcheck."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        fh.write(f"{n} {k} {len(edges)}\n")
        fh.write(" ".join(f"{u} {v}" for (u, v) in edges) + "\n")
        if coloring is not None:
            fh.write("COLORING " + " ".join(str(coloring[v] - 1) for v in range(n)) + "\n")
            return
        fh.write("REFUTATION\n")
        out, stack = [], [refutation]
        while stack:
            node = stack.pop()
            if node[0] == 'E':
                out.append(f"E {node[1]}")
            elif node[0] == 'C':
                out.append(f"C {node[1]} {node[2]}")
            elif node[0] == 'S':
                out.append(f"S {node[1]} {node[2] - 1}")
                stack += [node[4], node[3]]          # pre-order: yes before no
            else:
                out.append(f"R {len(node[1])} " + " ".join(map(str, node[1])))
                stack.append(node[2])
        fh.write("\n".join(out) + "\n")


CHECKER = os.path.join(ROOT, "proof", "checker", "certcheck")


def check_certificate(path: str):
    """Run the extracted verified checker; returns (valid, message, seconds)."""
    import subprocess
    import time
    if not os.path.exists(CHECKER):
        return None, "checker not built (cd proof/checker && make)", 0.0
    t0 = time.time()
    r = subprocess.run([CHECKER, path], capture_output=True, text=True)
    return r.returncode == 0, r.stdout.strip(), round(time.time() - t0, 3)


def is_proper_full(n: int, edges, coloring: Dict[int, int], k: int) -> bool:
    if set(coloring) != set(range(n)):
        return False
    if any(not (1 <= c <= k) for c in coloring.values()):
        return False
    return all(coloring[u] != coloring[w] for (u, w) in edges)
