(** * Stages.v — the per-stage certified reductions (note, Sec. 4).

    Each rule of [type-system/type-system.tex] Sec. 4 becomes a [CRed] between
    the concrete problem-types of [Sorts.v], with its "proof obligation"
    (the premises above the line) discharged here once and for all:

      [S1]       colorChoice : Col     ⇝[decodeColoring] IS
      [S2]       gadgetize   : IS      ⇝[decodeLogical]  WIS⟨N,C⟩
      [S3-exact] layout      : WIS⟨N,C⟩ ⇝[unwrap]       UDG⟨N⟩  (premise: realizes)
      [Fit]      emit        : UDG⟨N⟩  ⇝[unwrap]         Dev⟨N⟩  (premise: N ≤ Nmax)

    The geometric premise of [S3-exact] and the atom-count premise of [Fit] gate
    *derivability* only; their decoders only unwrap, formalising the note's
    "heuristics affect feasibility, never the answer." *)

From Stdlib Require Import PeanoNat Lia List Bool.
From CertCol Require Import Problem Sorts.
Import ListNotations.

(** ** Stage 1 — colour-choice. *)

(** Read a colouring off a selection (unselected vertices default to colour 0;
    the readout check below rejects such selections). *)
Definition selColor (sel : Sel) : Coloring :=
  fun v => match sel v with Some i => i | None => 0 end.

(** A decidable "every vertex < n is slotted" test. *)
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

(** A decidable properness test: colours in range and no monochromatic edge. *)
Definition proper_b (k : nat) (g : Graph) (c : Coloring) : bool :=
  forallb (fun u => Nat.ltb (c u) k &&
             forallb (fun v => negb (gAdj g u v) || negb (Nat.eqb (c u) (c v)))
                     (seq 0 (gN g)))
          (seq 0 (gN g)).

Lemma proper_b_spec (k : nat) (g : Graph) (c : Coloring) :
  proper_b k g c = true <-> proper k g c.
Proof.
  unfold proper_b, proper. rewrite forallb_forall. split.
  - intros H. split.
    + intros v Hv. assert (Hin : In v (seq 0 (gN g))) by (apply in_seq; lia).
      specialize (H v Hin). apply andb_true_iff in H as [H _].
      apply Nat.ltb_lt; exact H.
    + intros u v Hu Hv Hadj Heq.
      assert (Hin : In u (seq 0 (gN g))) by (apply in_seq; lia).
      specialize (H u Hin). apply andb_true_iff in H as [_ H].
      rewrite forallb_forall in H.
      assert (Hin' : In v (seq 0 (gN g))) by (apply in_seq; lia).
      specialize (H v Hin'). rewrite Hadj, Heq, Nat.eqb_refl in H. discriminate.
  - intros [Hr He] u Hu. apply in_seq in Hu.
    apply andb_true_iff. split.
    + apply Nat.ltb_lt, Hr; lia.
    + apply forallb_forall. intros v Hv. apply in_seq in Hv.
      destruct (gAdj g u v) eqn:Ea; [|reflexivity]. simpl.
      destruct (Nat.eqb (c u) (c v)) eqn:Ec; [|reflexivity].
      apply Nat.eqb_eq in Ec. exfalso. exact (He u v ltac:(lia) ltac:(lia) Ea Ec).
Qed.

(** The readout check of the paper (Section "Decoding"): accept a selection only
    if it holds exactly one slot for every vertex and the colouring it reads off
    is proper; otherwise answer "no colouring found" ([None]). *)
Definition decodeColoring (k : nat) (g : Graph) : decoder (Pis k g) (Pcol k g) :=
  fun sel => if all_some sel (gN g) && proper_b k g (selColor sel)
             then Some (Some (selColor sel)) else Some None.

(** An accepted readout is a proper colouring, whatever the quality of the
    solve: this needs no optimality assumption. *)
Lemma decodeColoring_accept_sound (k : nat) (g : Graph) (sel : Sel) (c : Coloring) :
  decodeColoring k g sel = Some (Some c) -> proper k g c.
Proof.
  unfold decodeColoring.
  destruct (all_some sel (gN g) && proper_b k g (selColor sel)) eqn:E;
    [|discriminate].
  intros H. injection H as <-. apply andb_true_iff in E as [_ E].
  apply proper_b_spec; exact E.
Qed.

(** An independent selection that covers every vertex reads off a proper
    colouring. *)
Lemma isol_full_proper (k : nat) (g : Graph) (sel : Sel) :
  isol k g sel -> (forall v, v < gN g -> sel v <> None) -> proper k g (selColor sel).
Proof.
  intros [Hwf Hind] Hfull. split.
  - intros v Hv. unfold selColor. specialize (Hwf v Hv).
    destruct (sel v) as [i|] eqn:E; [exact Hwf | exfalso; apply (Hfull v Hv); exact E].
  - intros u v Hu Hv Hadj Heq. unfold selColor in Heq.
    destruct (sel u) as [iu|] eqn:Eu; [| exfalso; apply (Hfull u Hu); exact Eu].
    destruct (sel v) as [iv|] eqn:Ev; [| exfalso; apply (Hfull v Hv); exact Ev].
    apply (Hind u v iu Hu Hv Hadj Eu). rewrite Ev, Heq. reflexivity.
Qed.

(** A proper colouring gives an independent selection of size [n]. *)
Lemma coloring_isol (k : nat) (g : Graph) (c : Coloring) :
  proper k g c ->
  isol k g (fun v => Some (c v)) /\ count_some (fun v => Some (c v)) (gN g) = gN g.
Proof.
  intros [Hrange Hmono]. split; [split|].
  - intros v Hv. apply Hrange; exact Hv.
  - intros u v i Hu Hv Hadj Hu' Hv'.
    injection Hu' as Hu'. injection Hv' as Hv'.
    apply (Hmono u v Hu Hv Hadj). rewrite Hu', Hv'. reflexivity.
  - apply full_count. intros v Hv. discriminate.
Qed.

(** Stage-1 *exactness* over the standard maximum (the refinement [P_s1],
    [α(G'_k) = n ⟺ k-colourable]): a maximum independent selection has size
    [n] if and only if [G] is k-colourable. *)
Theorem stage1_opt (k : nat) (g : Graph) (sel : Sel) :
  IsOpt (Pis k g) sel -> (colorable k g <-> count_some sel (gN g) = gN g).
Proof.
  intros [Hiso Hmax]. split.
  - intros [c Hc]. destruct (coloring_isol k g c Hc) as [Hi Hn].
    specialize (Hmax _ Hi). pose proof (count_some_le sel (gN g)). lia.
  - intros Hn. exists (selColor sel). apply (isol_full_proper k g sel Hiso).
    apply count_full; exact Hn.
Qed.

(** The Stage-1 obligation: on a maximum, the readout decides colourability
    correctly in both directions. *)
Lemma decodeColoring_tot_opt (k : nat) (g : Graph) :
  tot_opt (decodeColoring k g).
Proof.
  intros sel Hopt. unfold decodeColoring.
  destruct (all_some sel (gN g) && proper_b k g (selColor sel)) eqn:E.
  - exists (Some (selColor sel)). split; [reflexivity|].
    simpl. apply andb_true_iff in E as [_ E]. apply proper_b_spec; exact E.
  - exists None. split; [reflexivity|]. simpl. intros Hcol.
    destruct Hopt as [Hiso Hmax].
    assert (Hn : count_some sel (gN g) = gN g)
      by (apply (stage1_opt k g sel (conj Hiso Hmax)); exact Hcol).
    assert (Hfull : forall v, v < gN g -> sel v <> None) by (apply count_full; exact Hn).
    rewrite (all_some_full _ _ Hfull) in E. simpl in E.
    assert (Hp : proper_b k g (selColor sel) = true)
      by (apply proper_b_spec; exact (isol_full_proper k g sel Hiso Hfull)).
    rewrite Hp in E. discriminate.
Qed.

(** Rule [S1] as a certified reduction. *)
Definition S1 (k : nat) (g : Graph) : CRed (Pcol k g) (Pis k g) :=
  {| dec := decodeColoring k g; cert := decodeColoring_tot_opt k g |}.

(** Stage-1 exactness as an existence statement. *)
Theorem stage1_exact (k : nat) (g : Graph) :
  colorable k g <-> exists sel, IsOpt (Pis k g) sel /\ count_some sel (gN g) = gN g.
Proof.
  split.
  - intros [c Hc]. destruct (coloring_isol k g c Hc) as [Hi Hn].
    exists (fun v => Some (c v)). split; [split|exact Hn].
    + exact Hi.
    + intros sel' _. rewrite Hn. apply count_some_le.
  - intros [sel [Hopt Hn]]. apply (stage1_opt k g sel Hopt). exact Hn.
Qed.

(** ** Stage 2 — gadget. *)

(** Keep the logical atoms (drop the ancilla): the note's [decodeLogical]. *)
Definition decodeLogical (k : nat) (g : Graph) (N C : nat)
  : decoder (Pwis k g N C) (Pis k g) :=
  fun (s : WSol N C) => Some (fst (unW s)).

Lemma decodeLogical_tot_opt (k : nat) (g : Graph) (N C : nat) :
  tot_opt (decodeLogical k g N C).
Proof.
  intros s Hs. exists (fst (unW s)). split; [reflexivity | exact Hs].
Qed.

Definition gadgetize (k : nat) (g : Graph) (N C : nat)
  : CRed (Pis k g) (Pwis k g N C) :=
  {| dec := decodeLogical k g N C; cert := decodeLogical_tot_opt k g N C |}.

(** The static offset [C] is carried as an index so "subtract C" is
    type-directed: the gadget weight of a solution is its logical count plus
    [C], an optimum has the largest weight, and that weight is [n + C] exactly
    when [G] is k-colourable (the invariant [MWIS(A) = α + C]). *)
Definition gWeight (C n : nat) (s : WSel) : nat := count_some (fst s) n + C.

Lemma gadget_mwis (k : nat) (g : Graph) (N C : nat) (s : WSol N C) :
  IsOpt (Pwis k g N C) s ->
  (forall w, isol k g (fst w) -> gWeight C (gN g) w <= gWeight C (gN g) (unW s)) /\
  (colorable k g <-> gWeight C (gN g) (unW s) = gN g + C).
Proof.
  intros Hs. split.
  - intros w Hw. unfold gWeight. destruct Hs as [_ Hmax].
    specialize (Hmax _ Hw). lia.
  - unfold gWeight. rewrite (stage1_opt k g (fst (unW s)) Hs). lia.
Qed.

(** ** Stage 3 (exact) — layout, and Fit — the atom budget.

    Both decoders only unwrap the solution; the geometric realisability premise
    [Realizes] and the atom-count premise [N ≤ Nmax] gate derivability only. *)

Lemma unwrapU_tot_opt (k : nat) (g : Graph) (N C : nat) :
  @tot_opt (Pudg k g N) (Pwis k g N C) (fun (u : USol N) => Some (mkW (unU u))).
Proof. intros s Hs. exists (mkW (unU s)). split; [reflexivity | exact Hs]. Qed.

Definition layout_exact (k : nat) (g : Graph) (N C : nat)
           (Realizes : Prop) (H : Realizes)
  : CRed (Pwis k g N C) (Pudg k g N) :=
  Build_CRed (Pwis k g N C) (Pudg k g N) (fun (u : USol N) => Some (mkW (unU u)))
             (unwrapU_tot_opt k g N C).

Lemma unwrapD_tot_opt (k : nat) (g : Graph) (N : nat) :
  @tot_opt (Pdev k g N) (Pudg k g N) (fun (d : DSol N) => Some (mkU (unD d))).
Proof. intros s Hs. exists (mkU (unD s)). split; [reflexivity | exact Hs]. Qed.

Definition emit (k : nat) (g : Graph) (N Nmax : nat) (H : N <= Nmax)
  : CRed (Pudg k g N) (Pdev k g N) :=
  Build_CRed (Pudg k g N) (Pdev k g N) (fun (d : DSol N) => Some (mkU (unD d)))
             (unwrapD_tot_opt k g N).
