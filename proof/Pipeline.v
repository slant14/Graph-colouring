(** * Pipeline.v — composition, end-to-end soundness, and ordering.

    This file assembles the per-stage reductions of [Stages.v] into the whole
    compiler [Col ⇝ IS ⇝ WIS⟨N,C⟩ ⇝ UDG⟨N⟩ ⇝ Dev⟨N⟩] and proves the head
    theorems of [type-system/type-system.tex]:

      - Pipeline soundness ([pipeline_sound]): an optimal device measurement
        decodes to a correct answer, a proper k-colouring if [G] is
        k-colourable and the answer "not k-colourable" otherwise;
      - acceptance soundness ([pipeline_accept_sound]): *any* measurement whose
        readout is accepted decodes to a proper k-colouring, optimal or not;
      - the decision content ([pipeline_decision]): an optimal measurement has
        [n] logical atoms selected exactly when [G] is k-colourable.

    It also mechanises the ordering corollary twice: compositions in a wrong
    stage order do not type-check ([Fail] commands below), and a syntactic step
    relation on sorts has no transition for the illegal orders. *)

From Stdlib Require Import PeanoNat Lia.
From CertCol Require Import Problem Sorts Stages.

(** ** The composed pipeline and its soundness. *)

Section Pipeline.
  Variable k : nat.
  Variable g : Graph.
  Variable N : nat.                 (* atom count of the device instance (index) *)
  Variable C : nat.                 (* the gadget offset (index) *)
  Variable Realizes : Prop.         (* Stage-3 geometric realisability premise *)
  Variable HR : Realizes.
  Variable Nmax : nat.              (* device budget *)
  Variable HN : N <= Nmax.          (* [Fit] premise: the atom count fits *)

  (** [Col ⇝ IS ⇝ WIS ⇝ UDG ⇝ Dev], built by [Comp] from the four stage rules. *)
  Definition pipeline : CRed (Pcol k g) (Pdev k g N) :=
    cred_comp (S1 k g)
      (cred_comp (gadgetize k g N C)
        (cred_comp (layout_exact k g N C Realizes HR)
                   (emit k g N Nmax HN))).

  (** The composed decoder is the Stage-1 readout of the logical atoms. *)
  Lemma pipeline_dec (m : DSol N) : dec pipeline m = decodeColoring k g (fst (unD m)).
  Proof. reflexivity. Qed.

  (** Pipeline soundness.  Any device measurement of optimal value decodes,
      through the whole chain of total-on-optima decoders, to a correct answer:
      a proper k-colouring, or "not k-colourable" when none exists. *)
  Theorem pipeline_sound :
    forall m, IsOpt (Pdev k g N) m ->
      exists a, dec pipeline m = Some a /\ IsOpt (Pcol k g) a.
  Proof. exact (cred_sound pipeline). Qed.

  Corollary pipeline_sound_colorable :
    forall m, IsOpt (Pdev k g N) m -> colorable k g ->
      exists c, dec pipeline m = Some (Some c) /\ proper k g c.
  Proof.
    intros m Hm Hcol. destruct (pipeline_sound m Hm) as [[c|] [Hd Ha]].
    - exists c. split; assumption.
    - exfalso. exact (Ha Hcol).
  Qed.

  (** Acceptance soundness: a readout that passes the check is a proper
      k-colouring for *every* measurement.  Only the rejection of a readout
      depends on optimality, which cannot be checked (Remark 4.6). *)
  Theorem pipeline_accept_sound :
    forall m c, dec pipeline m = Some (Some c) -> proper k g c.
  Proof.
    intros m c H. rewrite pipeline_dec in H.
    exact (decodeColoring_accept_sound k g _ c H).
  Qed.

End Pipeline.

(** ** The decision theorem.

    At an optimal measurement, [n] logical atoms are selected exactly when [G]
    is k-colourable: the Stage-1 exactness refinement [P_s1] survives
    composition to the device. *)
Theorem pipeline_decision (k : nat) (g : Graph) (N : nat) (m : DSol N) :
  IsOpt (Pdev k g N) m ->
  (colorable k g <-> count_some (fst (unD m)) (gN g) = gN g).
Proof. intros Hm. exact (stage1_opt k g (fst (unD m)) Hm). Qed.

(** ** Ill-ordered compositions do not type-check.

    The sorts [Pwis], [Pudg] and [Pdev] have distinct solution types, so the
    stage reductions compose only in the legal order, and the atom count [N]
    must agree from the gadget stage to the device.  Each [Fail] below succeeds
    only because the composition it contains is rejected by Rocq. *)

(* "emit before layout": [Fit] expects UDG, is given WIS. *)
Fail Definition emit_before_layout (k : nat) (g : Graph) (N C Nmax : nat)
     (H : N <= Nmax) :=
  cred_comp (gadgetize k g N C) (emit k g N Nmax H).

(* "gadgetize before colorChoice": [S2] expects IS, is given Col. *)
Fail Definition gadgetize_before_choice (k : nat) (g : Graph) (N C : nat) :=
  cred_comp (gadgetize k g N C) (S1 k g).

(* The atom count checked by [Fit] must be the one the gadget stage produced. *)
Fail Definition mismatched_atom_count (k : nat) (g : Graph) (N C Nmax : nat)
     (R : Prop) (HR : R) (H : S N <= Nmax) :=
  cred_comp (layout_exact k g N C R HR) (emit k g (S N) Nmax H).

(** ** Corollary 5.3 — ill-ordered pipelines are ill-typed.

    A syntactic sort for each problem-type, and the legal one-step transitions.
    The constructors *are* the per-stage rules; an illegal stage order is simply
    a transition with no constructor. *)
Inductive Ty := TCol | TIS | TWIS | TUDG | TUDGa | TDev.

Inductive Step : Ty -> Ty -> Prop :=
| St_S1      : Step TCol  TIS      (* colorChoice *)
| St_S2      : Step TIS   TWIS     (* gadgetize *)
| St_S3exact : Step TWIS  TUDG     (* layout, realizes *)
| St_S3approx: Step TWIS  TUDGa    (* layout, leaves false edges *)
| St_Repair  : Step TUDGa TWIS     (* nguyen copy/crossing repair *)
| St_Fit     : Step TUDG  TDev.    (* emit, N ≤ Nmax *)

(** "gadgetize before colorChoice" : [S2] expects IS, is given Col. *)
Lemma no_gadget_before_choice : ~ Step TCol TWIS.
Proof. intro H; inversion H. Qed.

(** "emit before layout" : [Fit] expects UDG, is given WIS. *)
Lemma no_emit_before_layout : ~ Step TWIS TDev.
Proof. intro H; inversion H. Qed.

(** No certified decoder leaves a false-edged layout [UDGa]: the only way out is
    [Repair], back to WIS — never forward to UDG or the device. *)
Lemma no_exit_from_udga :
  (~ Step TUDGa TUDG) /\ (~ Step TUDGa TDev).
Proof. split; intro H; inversion H. Qed.

(** The reachability closure, and the fact that the *only* route to the device
    runs through the exact [UDG] sort (never through [UDGa]). *)
Inductive Path : Ty -> Ty -> Prop :=
| P_refl : forall a, Path a a
| P_step : forall a b c, Step a b -> Path b c -> Path a c.

(** The legal pipeline is a path. *)
Example legal_pipeline : Path TCol TDev.
Proof.
  eapply P_step. apply St_S1.
  eapply P_step. apply St_S2.
  eapply P_step. apply St_S3exact.
  eapply P_step. apply St_Fit.
  apply P_refl.
Qed.

(** Every path into [TDev] takes the [Fit] step from [TUDG] last: the device is
    reached only through the exact unit-disk sort. *)
Lemma dev_only_via_udg :
  forall a, Step a TDev -> a = TUDG.
Proof. intros a H; inversion H; reflexivity. Qed.
