"""Neutral-atom (Rydberg) analog simulation backends for the coloring pipeline.

Two engines, both implementing the *same* QuEra-style adiabatic protocol
(ramp the Rabi drive Omega up then down while sweeping the detuning Delta from
negative to positive), differing only in how the blockade is defined:

  * ``mis_bloqade``  -- the genuine ``bloqade-analog`` emulator. The blockade is
    *geometric* (the Rydberg C6/r^6 interaction from real atom positions). This
    is the literal neutral-atom simulation; it solves MIS on a unit-disk graph.

  * ``mwis_graph``   -- an explicit Rydberg Hamiltonian whose blockade is placed
    on the edges of an *abstract* graph. This is the logical object the Nguyen
    copy/crossing gadget array physically realizes, and it lets us simulate the
    color-choice graph G' (which is not itself unit-disk) on the CPU for the
    small instances the pipeline produces.

Measurement convention follows Bloqade: a bit == 0 means the atom is
Rydberg-excited (i.e. *in* the independent set); == 1 means ground.
"""

from __future__ import annotations

import os

# The engine issues many small dense/sparse kernels (Krylov mat-vecs, tiny
# expm's).  Letting BLAS spawn a thread pool per call causes severe
# oversubscription -- wall time blows up while threads fight.  Pin the math
# libraries to a single thread *before* numpy/scipy load their backends.  Set
# these in the environment beforehand to override.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

from typing import Iterable, List, Sequence, Set, Tuple

import numpy as np
import scipy.sparse as sp
from scipy.linalg import expm


# ── adiabatic schedule ───────────────────────────────────────────────────────

def _omega(t: float, T: float, omega_max: float) -> float:
    """Rabi amplitude: linear ramp up over the first 15%, hold, ramp down."""
    up, dn = 0.15 * T, 0.85 * T
    if t < up:
        return omega_max * t / up
    if t > dn:
        return omega_max * (T - t) / (T - dn)
    return omega_max


def _delta(t: float, T: float, delta_max: float) -> float:
    """Detuning swept linearly from -delta_max to +delta_max."""
    return -delta_max + 2 * delta_max * (t / T)


# ── short-time Krylov propagator ──────────────────────────────────────────────

def _propagate(matvec, psi: np.ndarray, dt: float,
               m_max: int = 30, tol: float = 1e-9) -> np.ndarray:
    """Apply ``exp(-1j * dt * H) psi`` for a Hermitian ``H`` given only its
    action ``matvec(v) = H @ v``.

    Builds a Lanczos (Krylov) subspace with full reorthogonalization, growing it
    one vector at a time and stopping as soon as the exponential of the small
    tridiagonal block has converged (the trailing coefficient falls below
    ``tol``).  For the short adiabatic time steps used here this converges in a
    handful of vectors, so each step costs only a few matrix-vector products --
    far cheaper than the per-step operator-norm estimation that ``scipy``'s
    ``expm_multiply`` redoes on every call, which was the source of the slowdown.
    """
    dim = psi.shape[0]
    m_max = min(m_max, dim)
    beta0 = float(np.linalg.norm(psi))
    if beta0 == 0.0:
        return psi

    Q = np.zeros((dim, m_max), dtype=complex)
    alpha: List[float] = []
    beta: List[float] = []
    Q[:, 0] = psi / beta0
    r = matvec(Q[:, 0])
    a = float(np.real(np.vdot(Q[:, 0], r)))
    alpha.append(a)
    r = r - a * Q[:, 0]

    coeffs = np.array([np.exp(-1j * dt * a) * beta0], dtype=complex)
    for j in range(1, m_max):
        b = float(np.linalg.norm(r))
        if b < tol:
            break
        q = r / b
        # full reorthogonalization keeps the small basis numerically clean;
        # conj(q) @ Q avoids conjugating the whole (dim x j) basis block.
        h = np.conj(np.conj(q) @ Q[:, :j])
        q = q - Q[:, :j] @ h
        nrm = float(np.linalg.norm(q))
        if nrm < tol:
            break
        q /= nrm
        Q[:, j] = q
        beta.append(b)
        r = matvec(q)
        a = float(np.real(np.vdot(q, r)))
        alpha.append(a)
        r = r - a * q - b * Q[:, j - 1]

        # exponential of the (j+1)x(j+1) tridiagonal block; stop when converged
        T = (np.diag(alpha) + np.diag(beta, 1) + np.diag(beta, -1))
        coeffs = expm(-1j * dt * T)[:, 0] * beta0
        if abs(coeffs[-1]) < tol:
            break

    return Q[:, :coeffs.shape[0]] @ coeffs


# ── abstract-graph Rydberg MWIS (the logical array the gadgets realize) ───────

def _drive_operator(n: int) -> sp.csr_matrix:
    """sum_i X_i over n qubits, as a sparse 2^n x 2^n matrix."""
    dim = 1 << n
    rows = np.repeat(np.arange(dim), n)
    cols = np.empty(dim * n, dtype=np.int64)
    for i in range(n):
        cols[i::n] = np.arange(dim) ^ (1 << i)
    data = np.ones(dim * n)
    return sp.csr_matrix((data, (rows, cols)), shape=(dim, dim))


def _diagonals(n: int, edges: Sequence[Tuple[int, int]],
               weights: Sequence[float]) -> Tuple[np.ndarray, np.ndarray]:
    """Per-basis-state weighted occupation sum and blockade-violation count."""
    dim = 1 << n
    bits = ((np.arange(dim)[:, None] >> np.arange(n)) & 1).astype(np.int64)
    wcount = bits @ np.asarray(weights, dtype=float)
    penalty = np.zeros(dim)
    for (u, v) in edges:
        penalty += bits[:, u] * bits[:, v]
    return wcount, penalty


def mwis_graph(n: int,
               edges: Sequence[Tuple[int, int]],
               weights: Sequence[float] | None = None,
               *,
               omega_max: float = 8.0,
               delta_max: float = 14.0,
               penalty: float = 40.0,
               total_time: float = 4.0,
               steps: int = 160,
               topk: int = 128) -> Tuple[Set[int], np.ndarray]:
    """Simulate the adiabatic Rydberg MWIS of an abstract weighted graph.

    Returns ``(selected, probs)`` where ``selected`` is the recovered
    maximum-weight independent set (atom indices) and ``probs`` are the final
    state populations. We evolve the time-dependent Hamiltonian

        H(t) = -Delta(t) sum_i w_i n_i + U sum_{(i,j) in E} n_i n_j
               + (Omega(t)/2) sum_i X_i

    from the all-ground state, then read out: among the most populated basis
    states we keep the genuine independent sets and pick the maximum weight
    (exactly what hardware does by repeating shots and post-selecting).
    """
    if weights is None:
        weights = [1.0] * n
    dim = 1 << n
    xsum = _drive_operator(n)
    wcount, pen = _diagonals(n, edges, weights)

    psi = np.zeros(dim, dtype=complex)
    psi[0] = 1.0  # all atoms in the ground state
    dt = total_time / steps
    for s in range(steps):
        t = (s + 0.5) * dt
        diag = -_delta(t, total_time, delta_max) * wcount + penalty * pen
        om = _omega(t, total_time, omega_max) / 2.0
        # H(t) @ v, applied matrix-free so no sparse matrix is rebuilt per step
        def matvec(v: np.ndarray, _diag=diag, _om=om) -> np.ndarray:
            return _diag * v + _om * (xsum @ v)
        psi = _propagate(matvec, psi, dt)

    probs = np.abs(psi) ** 2
    order = np.argsort(probs)[::-1][:topk]
    best: Set[int] = set()
    best_w = -1.0
    for b in order:
        sel = {i for i in range(n) if (b >> i) & 1}
        if any((b >> u) & 1 and (b >> v) & 1 for (u, v) in edges):
            continue  # not independent
        w = sum(weights[i] for i in sel)
        if w > best_w:
            best_w, best = w, sel
    return best, probs


# ── genuine bloqade-analog geometric MIS ─────────────────────────────────────

def mis_bloqade(coords: Sequence[Tuple[float, float]],
                *,
                omega_max: float = 15.0,
                delta_max: float = 25.0,
                t_ramp: float = 0.2,
                t_hold: float = 1.6,
                shots: int = 200) -> List[Tuple[int, ...]]:
    """Run the bloqade-analog emulator on atom positions; return measured
    bitstrings as tuples (Bloqade convention: 0 = Rydberg/selected)."""
    from bloqade.analog import start

    prog = start.add_position([(float(x), float(y)) for (x, y) in coords])
    prog = (
        prog.rydberg.rabi.amplitude.uniform.piecewise_linear(
            [t_ramp, t_hold, t_ramp], [0.0, omega_max, omega_max, 0.0])
        .rydberg.detuning.uniform.piecewise_linear(
            [t_ramp, t_hold, t_ramp], [-delta_max, -delta_max, delta_max, delta_max])
    )
    result = prog.bloqade.python().run(shots)
    bitstrings = result.report().bitstrings()[0]
    return [tuple(int(b) for b in row) for row in bitstrings]


def best_mis_from_shots(bitstrings: Iterable[Tuple[int, ...]],
                        edges: Sequence[Tuple[int, int]]) -> Set[int]:
    """Pick the largest independent set (in ``edges``) among measured shots.
    Selected atoms are those with bit == 0 (Rydberg)."""
    eset = {frozenset(e) for e in edges}
    best: Set[int] = set()
    for row in bitstrings:
        sel = {i for i, b in enumerate(row) if b == 0}
        if any(frozenset((u, v)) in eset for u in sel for v in sel if u < v):
            continue
        if len(sel) > len(best):
            best = sel
    return best


# ── self-test ────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    # triangle K3: alpha = 1
    sel, _ = mwis_graph(3, [(0, 1), (0, 2), (1, 2)])
    print("K3  MWIS:", sorted(sel), "(expect one vertex)")
    assert len(sel) == 1

    # path P3 (0-1-2): alpha = 2 = {0,2}
    sel, _ = mwis_graph(3, [(0, 1), (1, 2)])
    print("P3  MWIS:", sorted(sel), "(expect {0, 2})")
    assert sel == {0, 2}

    # a 4-cycle 0-1-2-3-0: alpha = 2 = {0,2} or {1,3}
    sel, _ = mwis_graph(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
    print("C4  MWIS:", sorted(sel), "(expect 2 opposite vertices)")
    assert len(sel) == 2
    print("rydberg_sim self-test OK")
