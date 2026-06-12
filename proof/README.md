# Coq proofs for the certified-reduction type system

A mechanisation (Rocq / Coq 9.0) of the type discipline in
[`../type-system/type-system.tex`]: the *certified-reduction calculus* that makes
the correctness of the compilation **stages** static. Each compiler stage is
typed as an answer-preserving morphism carrying an executable decoder, and a
single composition rule yields the end-to-end soundness theorem
("the measured device bitstring decodes to a correct colouring").

Everything is proved **with no axioms and no `Admitted`** (`Print Assumptions`
reports *Closed under the global context* for every head theorem).

## Build

```sh
coq_makefile -f _CoqProject -o Makefile   # already generated; regenerate if needed
make                                       # compiles all five modules
```

Requires `coqc` (tested on The Rocq Prover 9.0.0). No external libraries.

## What is formalised

| File | Contents |
|------|----------|
| `Problem.v` | The abstract calculus: a *problem-type* (`Sol` + `IsOpt`), a *decoder* `B ⇀ A`, the **total-on-optima** certificate `tot_opt`, certified reductions `CRed A B`, identity, **composition** (rule `Comp`) with the proof that `tot_opt` composes, associativity, and the generic soundness lemma `cred_sound`. |
| `Sorts.v` | The concrete sorts on graph data: `Pcol` (k-colouring), `Pis` (Stage-1 colour-choice IS), `Pwis` (gadget weighted IS), and `Pudg`/`Pdev`. The colour-choice graph's *choice clique* ("≤1 slot per vertex") is encoded **exactly** by an `option`-valued selection, eliminating all pigeonhole counting. |
| `Stages.v` | The per-stage certified reductions `S1`, `gadgetize`, `layout_exact`, `emit`, each discharging its proof obligation — including the genuine **Stage-1 exactness theorem** `stage1_exact` (`α = n ⟺ k-colourable`) and the gadget offset invariant `gadget_mwis` (`MWIS = α + C`). |
| `Pipeline.v` | The composed compiler `Col ⇝ IS ⇝ WIS ⇝ UDG ⇝ Dev`; **Theorem 5.2** `pipeline_sound` (optimal device measurement decodes to a proper colouring); the decision theorem `pipeline_decision` (device optimum exists ⟺ colourable); and **Corollary 5.3** — a syntactic step relation whose shape *is* the legal stage order, so the three ill-ordered pipelines (`no_gadget_before_choice`, `no_emit_before_layout`, `no_exit_from_udga`) have no derivation, and the device is reachable only through the exact `UDG` sort (`dev_only_via_udg`). |
| `Effect.v` | Refinement A: the certificate-**grade** lattice `w ⊑ χ` (partial order, bottom `w`). Refinement B: the **safety-effect** algebra `{safe, asafe c}` proved a commutative monoid under `⊕`, with the accumulated χ-bound `bound (a ⊕ b) = bound a + bound b`. |

## Head theorems

- `Problem.cred_sound` — a certified reduction maps any target optimum to a
  decoded source optimum (the engine of soundness).
- `Stages.stage1_exact` — `colorable k g ↔ ∃ optimum of (Pis k g)`.
- `Pipeline.pipeline_sound` — an optimal `Dev` measurement decodes through the
  whole chain to a `proper k g` colouring.
- `Pipeline.pipeline_decision` — `(∃ device optimum) ↔ colorable k g`.

## Modelling notes (faithfulness vs. the Haskell harness in `../src`)

- `IsOpt (Pis k g)` is "a *maximum-size* (`= n`) independent selection", i.e. the
  α = n witness; its existence is `colorable`, matching
  `src/lib/UDGColor/Stage1.hs` and the brute-force oracle.
- Stage 2's ancilla atoms are abstracted to a logical-vs-ancilla product so
  `decodeLogical = fst`; the offset `C` is carried as a value index
  (`gWeight`), per the note's "subtract C is type-directed".
- Stages 3-exact and Emit carry **identity** decoders; their geometric
  realisability / device-budget premises gate *derivability* only — the formal
  statement of "heuristics affect feasibility, never the answer". The lossy
  `UDGa` (false-edged) layout deliberately has **no** certified decoder out,
  only `Repair` back to `WIS`.
