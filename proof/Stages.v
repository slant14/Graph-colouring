(** * Stages.v — the per-stage certified reductions (note, Sec. 4).

    Each rule of [type-system/type-system.tex] Sec. 4 becomes a [CRed] between
    the concrete problem-types of [Sorts.v], with its "proof obligation"
    (the premises above the line) discharged here once and for all:

      [S1]       colorChoice : Col ⇝[decodeColoring] IS     + Stage-1 exactness
      [S2]       gadgetize   : IS  ⇝[decodeLogical]  WIS    + offset C
      [S3-exact] layout      : WIS ⇝[id]             UDG    (premise: realizes)
      [Fit]      emit        : UDG ⇝[id]             Dev    (premise: N ≤ Nmax)

    The geometric premise of [S3-exact] and the budget premise of [Fit] gate
    *derivability* only; their decoders are the identity, formalising the note's
    "heuristics affect feasibility, never the answer." *)

From Stdlib Require Import PeanoNat Lia.
From CertCol Require Import Problem Sorts.

(** ** Stage 1 — colour-choice. *)

(** Read a colouring off a selection (undefined slots default to colour 0; on
    optima every slot is defined, so the default is never reached). *)
Definition selColor (sel : Sel) : Coloring :=
  fun v => match sel v with Some i => i | None => 0 end.

(** A decidable "every vertex < n is slotted" test, so the decoder is genuinely
    partial off the optima (note: [decodeColoring] is total on size-n IS, partial
    elsewhere). *)
Fixpoint all_some (sel : Sel) (n : nat) : bool :=
  match n with
  | 0   => true
  | S m => match sel m with Some _ => all_some sel m | None => false end
  end.

Lemma all_some_full : forall n sel,
  (forall v, v < n -> sel v <> None) -> all_some sel n = true.
Proof.
  induction n; intros sel H; simpl.
  - reflexivity.
  - destruct (sel n) eqn:E.
    + apply IHn. intros v Hv; apply H; lia.
    + exfalso. apply (H n (Nat.lt_succ_diag_r n)). exact E.
Qed.

Definition decodeColoring (k : nat) (g : Graph) : decoder (Pis k g) (Pcol k g) :=
  fun sel => if all_some sel (gN g) then Some (selColor sel) else None.

(** The Stage-1 obligation: a maximum-size independent selection decodes to a
    proper colouring. *)
Lemma decodeColoring_tot_opt (k : nat) (g : Graph) :
  tot_opt (decodeColoring k g).
Proof.
  intros sel [ [Hwf Hind] Hcount ]. simpl in *.
  assert (Hfull : forall v, v < gN g -> sel v <> None)
    by (apply count_full; exact Hcount).
  exists (selColor sel). split.
  - unfold decodeColoring. rewrite (all_some_full _ _ Hfull). reflexivity.
  - simpl. unfold proper. split.
    + (* colour range *)
      intros v Hv. unfold selColor. specialize (Hwf v Hv).
      destruct (sel v) as [i|] eqn:E;
        [exact Hwf | exfalso; apply (Hfull v Hv); exact E].
    + (* no monochromatic edge *)
      intros u v Hu Hv Hadj Heq. unfold selColor in Heq.
      destruct (sel u) as [iu|] eqn:Eu; [| exfalso; apply (Hfull u Hu); exact Eu].
      destruct (sel v) as [iv|] eqn:Ev; [| exfalso; apply (Hfull v Hv); exact Ev].
      (* Heq : iu = iv, but the conflict edge forbids equal-colour slots *)
      apply (Hind u v iu Hu Hv Hadj Eu). rewrite Ev, Heq. reflexivity.
Qed.

(** Rule [S1] as a certified reduction. *)
Definition S1 (k : nat) (g : Graph) : CRed (Pcol k g) (Pis k g) :=
  {| dec := decodeColoring k g; cert := decodeColoring_tot_opt k g |}.

(** Stage-1 *exactness* (the refinement [P_s1], α = n ⟺ k-colourable): the
    [IS] problem has an optimum iff [G] is k-colourable, and optima are in
    bijection with proper colourings.  This is the genuine reduction theorem,
    not a definitional artefact. *)
Theorem stage1_exact (k : nat) (g : Graph) :
  colorable k g <-> exists sel, IsOpt (Pis k g) sel.
Proof.
  split.
  - intros [c [Hrange Hmono]].
    exists (fun v => Some (c v)). simpl. split; [split | ].
    + intros v Hv. apply Hrange; exact Hv.
    + intros u v i Hu Hv Hadj Hu' Hv'.
      injection Hu' as Hu'. injection Hv' as Hv'.
      apply (Hmono u v Hu Hv Hadj). rewrite Hu', Hv'. reflexivity.
    + apply full_count. intros v Hv. discriminate.
  - intros [sel Hopt].
    destruct (decodeColoring_tot_opt k g sel Hopt) as [c [_ Hc]].
    exists c. exact Hc.
Qed.

(** ** Stage 2 — gadget. *)

(** Keep the logical atoms (drop the ancilla): the note's [decodeLogical]. *)
Definition decodeLogical (k : nat) (g : Graph) : decoder (Pwis k g) (Pis k g) :=
  fun s => Some (fst s).

Lemma decodeLogical_tot_opt (k : nat) (g : Graph) :
  tot_opt (decodeLogical k g).
Proof.
  intros s Hs. exists (fst s). split; [reflexivity | exact Hs].
Qed.

Definition gadgetize (k : nat) (g : Graph) : CRed (Pis k g) (Pwis k g) :=
  {| dec := decodeLogical k g; cert := decodeLogical_tot_opt k g |}.

(** The static offset [C] is carried alongside the type so "subtract C" is
    type-directed; at an optimum the gadget weight is [α + C = n + C], the note's
    invariant [MWIS(A) = α + C]. *)
Definition gWeight (C n : nat) (s : WSel) : nat := count_some (fst s) n + C.

Lemma gadget_mwis (k : nat) (g : Graph) (C : nat) (s : WSel) :
  IsOpt (Pwis k g) s -> gWeight C (gN g) s = gN g + C.
Proof.
  intros [_ Hcount]. unfold gWeight. rewrite Hcount. reflexivity.
Qed.

(** ** Stage 3 (exact) — layout, and Emit — device budget.

    Both carry the identity decoder; the geometric realisability premise
    [Realizes] and the budget premise [N ≤ Nmax] gate derivability only. *)

Definition layout_exact (k : nat) (g : Graph) (Realizes : Prop) (H : Realizes)
  : CRed (Pwis k g) (Pudg k g) := cred_id (Pwis k g).

Definition emit (k : nat) (g : Graph) (Nmax : nat) (H : gN g <= Nmax)
  : CRed (Pudg k g) (Pdev k g) := cred_id (Pwis k g).
