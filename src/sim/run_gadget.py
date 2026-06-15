"""Driver: run the neutral-atom simulation on the *gadgetised* instance ``A``.

The other drivers (``run_sim.py`` and the ``benchmarks/`` scripts) solve the
abstract Stage-1 color-choice graph ``G'`` directly: they place the blockade on
the edges of ``G'`` and never materialise the Stage-2 gadget array. That
validates the colorability->MWIS reduction (Stage 1) but leaves the gadgetisation
(Stage 2) exercised only by the Coq offset invariant and the Haskell emitter.

This driver closes that loop on the instances small enough to simulate. It runs
the *full* primary pipeline on tiny coloring instances ``(G, k)``:

  1. Stage 1 -- build the color-choice graph ``G'`` (mirrors
     ``UDGColor.Stage1.colorChoiceGraph``);
  2. Stage 2 -- gadgetise ``G'`` into the weighted graph ``A`` (mirrors
     ``UDGColor.Gadget.gadgetize``: each ``G'`` edge becomes a 4-path
     ``logical_u - a1 - a2 - logical_v`` with logical weight 1, gadget-atom
     weight 2, and value offset ``C = 2|E'|``);
  3. run the adiabatic Rydberg *maximum-weight* independent set **on ``A``**
     (blockade on the edges of ``A``, the gadget array itself, not ``G'``);
  4. check the Stage-2 offset invariant ``MWIS(A) = alpha(G') + C`` numerically,
     decode the logical atoms back to a coloring, and verify it is proper.

Because a gadgetised instance uses ``|V'| + 2|E'|`` atoms, only small ``(G, k)``
fit under the classical state-vector wall; full benchmark instances gadgetise to
``O(|V'|^2)`` atoms and are out of classical reach (which is why ``G'`` is solved
directly elsewhere). The cases here are the ones that fit, and they validate the
gadget layer end to end rather than by proof alone.
"""

from __future__ import annotations

import itertools
import os
import sys
from typing import Dict, List, Sequence, Set, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rydberg_sim import mwis_graph  # noqa: E402


# ── Stage 1: color-choice graph G' (mirror of UDGColor.Stage1) ────────────────

Slot = Tuple[str, int]


def color_choice_graph(
    vertices: Sequence[str],
    edges: Sequence[Tuple[str, str]],
    k: int,
) -> Tuple[List[Slot], List[Tuple[int, int]]]:
    """Return ``(slots, choice_edges)`` for ``G'`` as slot-index pairs.

    ``slots[i] = (v, c)`` means "vertex v takes color c"; a k-clique per vertex
    (choose at most one color) plus a conflict edge between equal-color slots of
    adjacent vertices -- exactly ``Stage1.colorChoiceGraph``.
    """
    slots: List[Slot] = [(v, c) for v in vertices for c in range(1, k + 1)]
    idx = {s: i for i, s in enumerate(slots)}
    es: Set[Tuple[int, int]] = set()
    # choice clique per vertex
    for v in vertices:
        cs = list(range(1, k + 1))
        for c1, c2 in itertools.combinations(cs, 2):
            es.add((idx[(v, c1)], idx[(v, c2)]))
    # conflict edges between equal-color slots of adjacent vertices
    for u, w in edges:
        for c in range(1, k + 1):
            es.add((idx[(u, c)], idx[(w, c)]))
    return slots, sorted(es)


# ── Stage 2: gadgetise G' into the weighted graph A (mirror of UDGColor.Gadget)

def gadgetize(
    n_slots: int, choice_edges: Sequence[Tuple[int, int]]
) -> Tuple[int, List[Tuple[int, int]], List[float], float, List[int]]:
    """Mirror of ``UDGColor.Gadget.gadgetize``.

    Each ``G'`` edge ``{u, v}`` becomes a 4-path ``logical_u - a1 - a2 -
    logical_v`` with logical weight 1 and gadget-atom weight 2; the value offset
    is ``C = 2|E'|``. Returns ``(n_atoms, A_edges, weights, offset, logical)``
    where ``logical[i]`` is the atom index of the i-th ``G'`` slot.
    """
    logical = list(range(n_slots))           # atoms 0..n_slots-1 are the logicals
    weights: List[float] = [1.0] * n_slots
    a_edges: List[Tuple[int, int]] = []
    nxt = n_slots
    for (u, v) in choice_edges:
        a1, a2 = nxt, nxt + 1
        nxt += 2
        weights.extend([2.0, 2.0])
        a_edges += [(u, a1), (a1, a2), (a2, v)]
    offset = 2.0 * len(choice_edges)
    return nxt, a_edges, weights, offset, logical


# ── brute-force alpha(G') oracle ──────────────────────────────────────────────

def alpha(n: int, edges: Sequence[Tuple[int, int]]) -> int:
    """Independence number by exhaustive search (n is tiny here)."""
    eset = {frozenset(e) for e in edges}
    best = 0
    for r in range(n, 0, -1):
        for combo in itertools.combinations(range(n), r):
            if all(frozenset((a, b)) not in eset
                   for a, b in itertools.combinations(combo, 2)):
                return r
    return best


# ── one full-pipeline run through the gadget array ────────────────────────────

def run_case(name: str, vertices: Sequence[str],
             edges: Sequence[Tuple[str, str]], k: int, chi: int) -> bool:
    slots, choice_edges = color_choice_graph(vertices, edges, k)
    n = len(vertices)
    a_slot = alpha(len(slots), choice_edges)        # oracle alpha(G')
    colorable_oracle = (a_slot == n)

    n_atoms, a_edges, weights, offset, logical = gadgetize(len(slots), choice_edges)
    expected_mwis = a_slot + offset                 # Stage-2 offset invariant

    # adiabatic Rydberg MWIS on the gadget array A itself
    selected, _ = mwis_graph(n_atoms, a_edges, weights)
    sel_weight = sum(weights[i] for i in selected)
    chosen_slots = {logical.index(i) for i in selected if i in logical}

    # decode logical atoms -> coloring of G
    by_vertex: Dict[str, List[int]] = {}
    for s in chosen_slots:
        v, c = slots[s]
        by_vertex.setdefault(v, []).append(c)
    coloring: Dict[str, int] | None = {}
    for v in vertices:
        cs = by_vertex.get(v, [])
        if len(cs) != 1:
            coloring = None
            break
        coloring[v] = cs[0]
    proper = coloring is not None and all(
        coloring[u] != coloring[w] for u, w in edges)
    found_colorable = (len(chosen_slots) == n)

    invariant_ok = abs(sel_weight - expected_mwis) < 0.5
    agrees_oracle = found_colorable == colorable_oracle
    good = invariant_ok and agrees_oracle and (not colorable_oracle or proper)

    print(f"== {name}  (G: n={n}, m={len(edges)}, chi={chi}; k={k}) ==")
    print(f"   Stage 1: G' slots={len(slots)}  choice-edges={len(choice_edges)}"
          f"  alpha(G')={a_slot}")
    print(f"   Stage 2: gadget A atoms={n_atoms}  offset C={offset:.0f}"
          f"  (logical={len(logical)} + gadget={n_atoms - len(logical)})")
    print(f"   sim on A: |MWIS(A)|_weight={sel_weight:.0f}"
          f"  expect alpha+C={expected_mwis:.0f}"
          f"  -> invariant {'OK' if invariant_ok else 'FAIL'}")
    col = ("(no full witness)" if coloring is None
           else ", ".join(f"{v}->c{coloring[v]}" for v in vertices))
    print(f"   decode  : {col}   ({'proper' if proper else 'improper/none'})")
    print(f"   colorable? sim={found_colorable} oracle={colorable_oracle}"
          f"  -> {'agree' if agrees_oracle else 'DISAGREE'}")
    print(f"   verdict : {'PASS' if good else 'FAIL'}\n")
    return good


def main() -> int:
    # tiny instances whose gadget array A fits under the classical wall.
    cases = [
        # (name, vertices, edges, k, chi)
        ("K2  k=chi  (1 edge)", ["a", "b"], [("a", "b")], 2, 2),
        ("K2  k=chi-1 (1 edge)", ["a", "b"], [("a", "b")], 1, 2),
    ]
    all_good = True
    for name, vs, es, k, chi in cases:
        all_good &= run_case(name, vs, es, k, chi)
    print("ALL PASS" if all_good else "SOME FAILED")
    return 0 if all_good else 1


if __name__ == "__main__":
    raise SystemExit(main())
