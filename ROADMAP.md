# Research Roadmap

Typed language for certified compilation of graph-coloring problems to neutral-atom (QuEra / Bloqade.jl) hardware.

This document captures the scope evaluation, the foundational design decisions, and a goal-by-goal roadmap. It is a living planning doc, not a paper section.

---

## Foundational design decisions (2026-05-28)

1. **Hardware target = gadgetized UD-MWIS.** The neutral-atom device solves (max-weight) independent set on a unit-disk graph, *not* coloring. So `k`-colorability is reduced to a single UD-MWIS instance via copy/crossing gadgets (QuEra / Nguyen et al., PRX Quantum 2023, style). The transformation adds atoms; decoding runs the gadget logic in reverse.
2. **Two transform kinds, typed differently.**
   - *Same-vertex UDG supergraph*: `E(G) ⊆ E(H)` on identical `V`; decode = restriction.
   - *Vertex-adding gadget encoding*: `H` introduces auxiliary atoms with an explicit decoder.
3. **"Preserve chromatic number" as a strength hierarchy.** Witness-relative safety (`χ(H) ≤ |κ|` for a carried coloring `κ`, poly-time checkable) is the default certificate level; true-`χ` equality is a stronger, proof-only level.
4. **Hybrid type checking.** Static decidable checks (kinds, provenance, stage-ordering, degree bounds) PLUS poly-time runtime certificate validation at transform boundaries for the geometric/coloring guarantees.

---

## The key reframing

Choosing gadgetized UD-MWIS is a strict upgrade in rigor and relocates where "heuristic" lives:

- **Main-path correctness becomes exact and polynomial.** The reduction `k`-colorability → UD-MWIS is an exact poly-time reduction — no χ-inflation, no "usually safe." Correctness is a once-proved meta-theorem, not a per-instance gamble. *Goal 1's hardest sub-goal largely dissolves on the main path.*
- **The genuine heuristic uncertainty moves elsewhere**, and is no longer a correctness question:
  - (a) **placement/routing cost** — atom count, area, crossing number vs. hardware limits (`d_min`, max radius, lattice geometry);
  - (b) **analog-solve quality** — whether the Rydberg dynamics actually reaches the MWIS ground state.
- **The seven supergraph heuristics change job.** They are no longer the main coloring-preservation mechanism. They become either (i) the *secondary* "color-a-UDG-supergraph" path (kept alive by decision #2), or — preferred — (ii) the **layout optimizer** for the gadgetized instance (geometric loss / Laplacian init / radius sweep minimize crossings and gadget-chain length under hardware spacing).

### Driving impossibility result (justifies decision #2)

A same-vertex UDG supergraph cannot bound χ-inflation in general. In any UDG the open neighborhood of a vertex has independence number ≤ 5 (six points within radius `r` of a center force two within `r` of each other — 60° pigeonhole). Hence the star `K_{1,n}` has `χ = 2`, but *any* UDG supergraph on the same vertices needs `χ(H) ≥ ⌈n/5⌉ → ∞`. So "almost-safe for all graphs" is impossible under supergraph-only; gadgets are required for hard graphs.

---

## Primary pipeline

```
G ─[color→IS reduction, ×k]→ G' ─[UD-MWIS gadgetize]→ A ─[Rydberg MWIS]→ σ ─[decode]→ k-coloring of G
   exact, poly                   exact, poly (Nguyen)    analog solve       exact inverse
```

**Color → IS reduction** (first theorem to pin down): vertices `V × [k]`; a *choice-clique* on the `k` slots of each vertex (≤ 1 color per vertex); a *conflict edge* `{(u,i),(v,i)}` for every `{u,v} ∈ E` and color `i`. Then `α(G') = |V|` iff `G` is `k`-colorable. Size `nk`.

Then Nguyen-style copy/crossing gadgets map `MWIS(G')` → **weighted** MWIS on a UDG (weighted — that is what the blockade ground state encodes).

Grammar hooks: `kColorable(k)` = one fixed-`k` encoding; `chromatic` = sweep `k`.

**Practical bottleneck = size.** `nk` vertices → up to `O((nk)²)` atoms after gadgetization, against a few-hundred-atom device. Layout and preprocessing are where the project's effort pays off.

---

## Goal-by-goal roadmap

### Goal 1 — verify heuristics are poly-time and safe / almost-safe (split along the two paths)

**Gadget path (primary):**
- Prove (1) color→IS correctness, (2) the UD-MWIS gadget reduction preserves the MWIS value (cite + re-prove for the chosen gadget set), (3) both are poly-time and the decoder is an exact inverse. All achievable, all exact.
- Separately, **bound the size** (atom count / area as a function of `n`, `k`, crossing number) — the real theorem to optimize.

**Supergraph path (secondary):**
- Keep `χ(G) ≤ χ(H)` (one-line, unconditional) and the witness-relative `χ(H) ≤ |κ|` conditional theorem.
- Fix the `T = poly(n)` iteration budget; prove `Φ`-monotonicity termination (`Φ` = weighted false-edge count, integer, bounded by `M·n²`, decreases ≥ 1 per accepted step ⇒ poly steps).
- Scope any "almost-safe" claim to a graph class; candidate precondition `σ(G) = max_v α(G[N(v)]) ≤ 5`.

### Goal 2 — make preconditions precise

- **Gadget path:** preconditions are *feasibility*, not safety — gadgetized atom count ≤ device capacity, area ≤ array size. Poly-time checkable ⇒ belongs in the static layer.
- **Supergraph path:** precondition is "a coloring witness `κ` exists with geometrically separable color classes," gated by the `σ(G) ≤ 5` necessary condition. Make class-membership a checkable type refinement.

The anchor theorem for the supergraph path:

> **Color-class separation.** If the placement keeps every color class of `κ` pairwise at distance `> r`, then `χ(H) ≤ |κ|`.

The hypothesis is a poly-time-checkable postcondition ⇒ it becomes a certificate. Precondition decomposes into a combinatorial part (is `κ` optimal? NP-hard ⇒ carry as witness, don't recompute) and a geometric part (separability, governed by `σ`).

### Goal 3 — type system for static precondition checks (hybrid)

Two transform constructors, distinct types:
- `superUDG : Graph[Gen] → Graph[UDG]{⊇ G, witness κ}`
- `encodeColoring(k) : Graph[Gen] → UDMWIS{encodes kColorable(k) of G, decoder δ}`

**Static / decidable layer** (the `errors.tex` catalogue lives here): kinds, provenance (`Coloring[from=G]`; MWIS solution decoded against the instance it came from), pipeline-stage ordering (no solve-before-lower, no decode-against-wrong-source — errors #6/#10), `keep`/`drop` disjointness, palette/restriction consistency, and that `k` in `encodeColoring(k)` matches the palette size.

**Certificate layer** (poly-time validators at transform boundaries):
- supergraph → verify `E(G) ⊆ E(H)` and `κ` proper on `H`;
- gadget → structural check that `A` is the spec-conformant gadgetization of `G'`, and that `δ` inverts it.

**Guarantee lattice** (decision #3): two chains joined at the provenance node —
- supergraph: `Exact ⊑ PreserveChromatic-true ⊑ WitnessSafe(κ) ⊑ NeverLowers`
- gadget: `EncodesKColorable(k)` (exact)

Subsumption: a stronger certificate may stand in where a weaker one is required, never the reverse (formalizes error #10).

### Goal 4 — does transformation order affect safety?

- **Correctness composes** by threading decoders (reverse order) and provenance — provable and order-independent, because the gadget reduction is exact and the supergraph decoder is restriction.
- **Cost is strongly order-dependent** (preprocessing/simplifying `G` before `encodeColoring` can slash atom count). So `compose` should be typed to chain decoders + provenance; the interesting order question is an *optimization* (cost), not a safety one.

---

## Suggested first deliverables (in order)

1. Write & prove the two-step exact reduction (color→IS, IS→UD-MWIS) with a worked small example (reuse `example.tex`'s `K_5`, but as a *coloring→MWIS* encoding, not a supergraph).
2. State the size / feasibility bounds and identify the preprocessing knobs.
3. Re-cast `main.tex`'s `K_{3,3}→C_6` / Petersen→`C_5` examples as the *secondary* supergraph path, clearly labeled, so the two paths do not read as one.
4. Formalize the two-constructor type system + guarantee lattice.

---

## Specific technical fixes (independent of the above)

- **"Trees achieve ρ = 1" (`heuristics.tex:614`) is false.** `K_{1,6}` is a tree that is not a UDG; a DFS-line layout at distance `1 = r` both creates false edges and drops true edges. Replace with caterpillars / proper-interval trees.
- **"Interval graphs are 1D UDGs" (`heuristics.tex:621`) is false.** 1D UDGs are exactly *unit / proper interval* graphs; the claw `K_{1,3}` is interval but not unit-interval. Restrict the claim.
- **"Bipartite UDGs achieve ρ = 1" (`heuristics.tex:628`) is vacuous** — it assumes the embedding it is meant to produce. Make it constructive or drop it.
- **`T` is not a complexity bound.** "Iterate until loss converges" must become a fixed `poly(n)` budget (or a proven convergence rate) for the `O(T·n²)` claim to hold.

---

## Open forks (resolve before writing the formal development)

- **Which gadget set** — adopt Nguyen et al.'s copy/crossing gadgets verbatim, or design a custom set (affects what must be re-proved)?
- **Weighted vs unweighted** — confirm the target is *max-weight* IS (the gadget reduction needs weights); does the grammar's `udg` literal need a weight field?
- **Is the supergraph path a real second backend** (color the UDG by iterated MIS) **or kept only for theory/comparison**? Decides how much to invest in its safety theorems vs. repurposing it for layout.
