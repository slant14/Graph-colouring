# Coq proofs for the certified-reduction type system

A mechanisation (Rocq / Coq 9.0) of the type discipline in
[`../docs/type-system/type-system.tex`]: the *certified-reduction calculus* that makes
the correctness of the compilation **stages** static. Each compiler stage is
typed as an answer-preserving morphism carrying an executable decoder, and a
single composition rule yields the end-to-end soundness theorem
("the measured device bitstring decodes to a correct colouring").

Everything is proved **with no axioms and no `Admitted`** (`Print Assumptions`
reports *Closed under the global context* for every head theorem).

## Build

```sh
coq_makefile -f _CoqProject -o Makefile   # generate the Makefile (not committed)
make                                       # compiles all seven modules
cd checker && make                         # extract + compile the certificate checker
```

Requires `coqc` (tested on The Rocq Prover 9.0.0); the checker additionally needs
OCaml (`ocamlfind ocamlopt`, tested with OCaml 5.3). No external libraries.

## What is formalised

| File | Contents |
|------|----------|
| `Problem.v` | The abstract calculus: a *problem-type* (`Sol` + `IsOpt`), a *decoder* `B ⇀ A`, the **total-on-optima** certificate `tot_opt`, certified reductions `CRed A B`, identity, **composition** (rule `Comp`) with the proof that `tot_opt` composes, associativity, and the generic soundness lemma `cred_sound`. |
| `Sorts.v` | The concrete sorts on graph data: `Pcol` (a colouring or the answer "not k-colourable"), `Pis` (Stage-1 colour-choice IS, whose optima are maximum independent selections in the standard sense), and `Pwis`/`Pudg`/`Pdev` (gadget, unit-disk and device instances, indexed by the atom count `N` and the offset `C`, with distinct solution types). The colour-choice graph's *choice clique* ("≤1 slot per vertex") is encoded by an `option`-valued selection. |
| `Stages.v` | The per-stage certified reductions `S1`, `gadgetize`, `layout_exact`, `emit` (premise: atom count `N <= Nmax`). The Stage-1 decoder performs the readout check (one slot per vertex, proper on every edge). **Stage-1 exactness** `stage1_opt`: a maximum independent selection has size `n` iff the graph is k-colourable; the gadget invariant `gadget_mwis`: an optimum has the largest weight, `n + C` iff colourable. |
| `Pipeline.v` | The composed compiler `Col ⇝ IS ⇝ WIS ⇝ UDG ⇝ Dev`. Pipeline soundness: `pipeline_accept_sound` (every accepted readout of *any* measurement is a proper colouring) and `pipeline_sound` (an optimal measurement decodes to a proper colouring, or to "not k-colourable" when none exists); `pipeline_decision` (at an optimum, `n` logical atoms are selected iff colourable). Ordering: `Fail` commands show that compositions in a wrong order, or with mismatched atom counts, do not type-check; a step relation on sorts has no transition for the illegal orders (`no_gadget_before_choice`, `no_emit_before_layout`, `no_exit_from_udga`, `dev_only_via_udg`). |
| `Robust.v` | Imperfect solves. Graded problems and **robust decoders** with slack transfer `g`, composing as `g1 ∘ g2` (`robust_comp`). The combinatorial **edge-path gadget** `A_4(F)` on an arbitrary edge list: `MWIS(A_4(F)) = α(F) + 2|E|` (`gadget_mwis_value`), every optimum restricts to a maximum IS of `F` (`gadget_optimum_restricts`), and the robust bound — `ε` below the optimum decodes (drop one end of each internal edge) to an IS within `ε` of `α(F)` (`gadget_robust`). The robust Stage-1 decoder with fresh colours (`stage1_robust`: proper, excess over `k` = number of unselected vertices). The explicit colour-choice graph (`Gk_edges`: choice cliques and conflict edges) and the **end-to-end robustness theorem** `robust_end_to_end`: a solve of `A_4(G'_k)` that is `ε` below the optimum decodes to a proper colouring with at most `n - α(G'_k) + ε` fresh colours. |
| `Certificate.v` | Certificates. `check_coloring` and `check_refutation` (refutation trees of `Empty`/`Clash`/`Split`/`Restrict` nodes over colour domains), with `check_coloring_sound` and `check_refutation_sound` (acceptance ⇒ no proper `k`-colouring). Extracted to OCaml in `checker/` (`Extract.v`, `main.ml`); the decomposition driver in `../benchmarks` emits a certificate for every run and calls `checker/certcheck`. |
| `Effect.v` | Refinement A: the certificate-**grade** lattice `w ⊑ χ` (partial order, bottom `w`). Refinement B: the **safety-effect** algebra `{safe, asafe c, mono}` proved a commutative monoid under `⊕`; its meaning over chromatic numbers (`respects`) composes along `⊕` (`respects_comp`), and `asafe (u - l)` is introduced soundly from a colouring/clique witness pair (`asafe_intro`). |

## Head theorems

- `Problem.cred_sound` — a certified reduction maps any target optimum to a
  decoded source optimum (the engine of soundness).
- `Stages.stage1_opt` — a maximum independent selection has size `n` iff
  `colorable k g`.
- `Pipeline.pipeline_accept_sound` — any measurement whose readout is accepted
  decodes to a `proper k g` colouring.
- `Pipeline.pipeline_sound` — an optimal `Dev` measurement decodes to a correct
  answer: a proper colouring, or "not k-colourable" when none exists.
- `Pipeline.pipeline_decision` — at an optimum, `colorable k g` iff `n` logical
  atoms are selected.
- `Robust.gadget_mwis_value`, `Robust.gadget_robust`, `Robust.stage1_robust`,
  `Robust.robust_comp` — the edge-path gadget and robust decoding.
- `Robust.robust_end_to_end` — the end-to-end robustness theorem on the explicit
  colour-choice graph.
- `Certificate.check_refutation_sound` — an accepted refutation proves
  non-colourability; `Certificate.check_coloring_sound` likewise for colourings.

## Modelling notes (faithfulness vs. the Haskell harness in `../src`)

- `IsOpt (Pis k g)` is a maximum independent selection in the standard sense (no
  independent selection is larger); `stage1_opt` shows its size is `n` exactly when
  the graph is colourable, matching `src/lib/UDGColor/Stage1.hs` and the
  brute-force oracle.
- Stage 2's ancilla atoms are abstracted to a logical-vs-ancilla product so
  `decodeLogical = fst`; the offset `C` is carried as a value index
  (`gWeight`), per the note's "subtract C is type-directed".
- Stages 3-exact and Emit only unwrap solutions; their geometric realisability
  and atom-count premises gate *derivability* only, which formalises
  "heuristics affect feasibility, never the answer". The lossy `UDGa`
  (false-edged) layout deliberately has **no** certified decoder out, only
  `Repair` back to `WIS`.
- Restrictions (precolor, allow/forbid, sameColor, differentColor, distinctOn)
  are not mechanized; the Haskell property suite checks their encoding.
