"""Driver: run the neutral-atom simulation on the emitted ``*.sim.json``
instances and decode a graph coloring.

The Haskell front end (``udg-color --emit-sim``) lowers each well-typed
``instance`` to a ``<name>.sim.json`` holding the Stage-1 *color-choice graph*
``G'`` — the tractable logical object the Nguyen gadget array physically
realizes — together with the slot |-> (vertex, color) decode map, the original
graph, and the ground-truth ``colorable`` flag.

This script closes the loop:

  1. run the adiabatic Rydberg *maximum-weight independent set* on ``G'``,
  2. decode the recovered independent set into a coloring of the original graph,
  3. verify the coloring is proper and that ``|MWIS| = n`` exactly when ``G`` is
     k-colorable (Stage-1 exactness theorem),
  4. cross-check against the ``colorable`` oracle flag.

Two engines (see ``rydberg_sim``):

  * ``mwis``    (default) — explicit Rydberg Hamiltonian with the blockade placed
    on the *edges* of ``G'``. ``G'`` is not itself unit-disk, so this is the
    faithful CPU simulation of the logical array the gadgets realize.
  * ``bloqade`` — the genuine ``bloqade-analog`` geometric emulator. It needs a
    real unit-disk layout; we run it as an end-to-end protocol check on a clean
    UDG and confirm it reproduces the abstract engine's independent set.

Usage::

    python sim/run_sim.py                       # all instances, mwis engine
    python sim/run_sim.py sim/instances/*.json  # explicit files
    python sim/run_sim.py --bloqade-check       # also run the genuine emulator
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import sys
from typing import Dict, List, Sequence, Set, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rydberg_sim import (  # noqa: E402
    best_mis_from_shots,
    mis_bloqade,
    mwis_graph,
)


# ── instance model ───────────────────────────────────────────────────────────

class Instance:
    """A parsed ``*.sim.json`` color-choice instance."""

    def __init__(self, d: dict) -> None:
        self.name: str = d["instance"]
        self.graph: str = d["graph"]
        self.n: int = d["n"]
        self.k: int = d["k"]
        self.offsetC: float = d["offsetC"]
        self.colorable: bool = d["colorable"]
        self.original_vertices: List[str] = [str(v) for v in d["originalVertices"]]
        self.original_edges: List[Tuple[str, str]] = [
            (str(u), str(v)) for u, v in d["originalEdges"]
        ]
        # slots[i] = (vertex, color): the decode map slot-index -> (v, color)
        self.slots: List[Tuple[str, int]] = [
            (str(v), int(c)) for v, c in d["slots"]
        ]
        self.choice_edges: List[Tuple[int, int]] = [
            (int(a), int(b)) for a, b in d["choiceEdges"]
        ]

    @property
    def n_slots(self) -> int:
        return len(self.slots)


def load(path: str) -> Instance:
    with open(path, "r") as fh:
        return Instance(json.load(fh))


# ── decode + verify ──────────────────────────────────────────────────────────

def decode_coloring(inst: Instance, chosen: Set[int]) -> Dict[str, int] | None:
    """Stage-1 inverse: read a coloring off the chosen slot indices.

    Returns the coloring only if every original vertex is assigned exactly one
    slot (mirrors ``UDGColor.Stage1.decodeColoring``); otherwise ``None``.
    """
    by_vertex: Dict[str, List[int]] = {}
    for idx in chosen:
        v, color = inst.slots[idx]
        by_vertex.setdefault(v, []).append(color)
    coloring: Dict[str, int] = {}
    for v, colors in by_vertex.items():
        if len(colors) != 1:
            return None  # vertex assigned 0 or >1 colors -> not a witness
        coloring[v] = colors[0]
    if set(coloring) != set(inst.original_vertices):
        return None  # some vertex left uncolored
    return coloring


def is_proper(inst: Instance, coloring: Dict[str, int]) -> bool:
    if set(coloring) != set(inst.original_vertices):
        return False
    return all(coloring[u] != coloring[v] for u, v in inst.original_edges)


# ── run one instance through the abstract Rydberg MWIS ────────────────────────

def run_mwis(inst: Instance) -> dict:
    """Solve ``G'`` with the abstract Rydberg engine, decode, verify."""
    selected, _probs = mwis_graph(inst.n_slots, inst.choice_edges)
    mis_size = len(selected)
    coloring = decode_coloring(inst, selected)
    proper = coloring is not None and is_proper(inst, coloring)
    # Stage-1 exactness: alpha(G') = n  <=>  G is k-colorable.
    found_colorable = mis_size == inst.n
    return {
        "selected": sorted(selected),
        "mis_size": mis_size,
        "coloring": coloring,
        "proper": proper,
        "found_colorable": found_colorable,
        "agrees_oracle": found_colorable == inst.colorable,
    }


# ── genuine bloqade-analog protocol check (clean UDG) ─────────────────────────

def bloqade_protocol_check() -> dict:
    """Run the genuine ``bloqade-analog`` emulator on a clean unit-disk graph
    and confirm it reproduces the abstract engine's maximum independent set.

    The color-choice graphs ``G'`` are generally *not* unit-disk, so they belong
    to the abstract engine; here we exercise the literal geometric emulator on a
    UDG whose MIS is known, to validate the analog adiabatic protocol itself.

    Layout: a 5-atom unit-disk "bowtie" — two triangles sharing atom 2 —
    forming a UDG whose maximum independent set is {0, 4} (size 2).
    """
    # positions (in micrometers); blockade radius ~ 9um at these drive params
    coords = [
        (0.0, 0.0),   # 0
        (0.0, 6.0),   # 1
        (5.0, 3.0),   # 2  (shared apex)
        (10.0, 0.0),  # 3
        (10.0, 6.0),  # 4
    ]
    # the unit-disk edges these positions induce (within blockade radius)
    edges = [(0, 1), (0, 2), (1, 2), (2, 3), (2, 4), (3, 4)]

    shots = mis_bloqade(coords, shots=200)
    bloqade_mis = best_mis_from_shots(shots, edges)

    abstract_sel, _ = mwis_graph(len(coords), edges)

    return {
        "edges": edges,
        "bloqade_mis": sorted(bloqade_mis),
        "abstract_mis": sorted(abstract_sel),
        "sizes_match": len(bloqade_mis) == len(abstract_sel),
        "expected_size": 2,
    }


# ── reporting ────────────────────────────────────────────────────────────────

def fmt_coloring(coloring: Dict[str, int] | None) -> str:
    if coloring is None:
        return "(no full witness)"
    return ", ".join(f"{v}->c{coloring[v]}" for v in sorted(coloring))


def report_instance(inst: Instance, res: dict) -> bool:
    print(f"== instance {inst.name}  (graph {inst.graph}, n={inst.n}, k={inst.k}) ==")
    print(f"   G' slots = {inst.n_slots}  choice-edges = {len(inst.choice_edges)}"
          f"  offset C = {inst.offsetC}")
    print(f"   Rydberg MWIS |IS| = {res['mis_size']}  (theorem: = n={inst.n}"
          f" iff {inst.k}-colorable)")
    print(f"   decoded coloring : {fmt_coloring(res['coloring'])}")
    ok_proper = "proper" if res["proper"] else "IMPROPER/incomplete"
    print(f"   coloring check   : {ok_proper}")
    print(f"   colorable?  sim={res['found_colorable']}  oracle={inst.colorable}"
          f"  -> {'agree' if res['agrees_oracle'] else 'DISAGREE'}")
    # a run is good if the simulated colorability verdict matches the oracle and,
    # when colorable, the decoded coloring is actually proper.
    good = res["agrees_oracle"] and (not inst.colorable or res["proper"])
    print(f"   verdict          : {'PASS' if good else 'FAIL'}\n")
    return good


# ── main ─────────────────────────────────────────────────────────────────────

def main(argv: Sequence[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="*", help="*.sim.json files (default: all in "
                    "sim/instances/)")
    ap.add_argument("--bloqade-check", action="store_true",
                    help="also run the genuine bloqade-analog emulator on a clean "
                         "UDG to validate the analog protocol")
    args = ap.parse_args(argv)

    here = os.path.dirname(os.path.abspath(__file__))
    paths = args.paths or sorted(glob.glob(os.path.join(here, "instances", "*.sim.json")))
    if not paths:
        print("no *.sim.json instances found", file=sys.stderr)
        return 2

    all_good = True
    for path in paths:
        inst = load(path)
        res = run_mwis(inst)
        all_good &= report_instance(inst, res)

    if args.bloqade_check:
        print("== genuine bloqade-analog protocol check (clean UDG) ==")
        bc = bloqade_protocol_check()
        print(f"   UDG edges        : {bc['edges']}")
        print(f"   bloqade MIS      : {bc['bloqade_mis']}  (expect size "
              f"{bc['expected_size']})")
        print(f"   abstract MIS     : {bc['abstract_mis']}")
        match = bc["sizes_match"] and len(bc["bloqade_mis"]) == bc["expected_size"]
        print(f"   verdict          : {'PASS' if match else 'FAIL'}\n")
        all_good &= match

    print("ALL PASS" if all_good else "SOME FAILED")
    return 0 if all_good else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
