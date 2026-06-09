(** * Pipeline.v — composition, end-to-end soundness, and ordering.

    This file assembles the per-stage reductions of [Stages.v] into the whole
    compiler [Col ⇝ IS ⇝ WIS ⇝ UDG ⇝ Dev] and proves the two head theorems of
    [type-system/type-system.tex]:

      - Theorem 5.2 (Pipeline soundness): an optimal device measurement decodes
        back to a *proper k-colouring* — [pipeline_sound];
      - the decision content (α = n ⟺ k-colourable lifted to the device):
        the device has an optimum iff [G] is colourable — [pipeline_decision].

    It also mechanises Corollary 5.3 (ill-ordered pipelines are ill-typed): a
    syntactic step relation on sorts whose shape *is* the legal ordering, so the
    three illegal pipelines simply have no derivation. *)

From Stdlib Require Import PeanoNat Lia.
From CertCol Require Import Problem Sorts Stages.

(** ** The composed pipeline and its soundness. *)

Section Pipeline.
  Variable k : nat.
  Variable g : Graph.
  Variable C : nat.                 (* the gadget offset (carried index) *)
  Variable Realizes : Prop.         (* Stage-3 geometric realisability premise *)
  Variable HR : Realizes.
  Variable Nmax : nat.              (* device budget *)
  Variable HN : gN g <= Nmax.       (* [Fit] premise *)

  (** [Col ⇝ IS ⇝ WIS ⇝ UDG ⇝ Dev], built by [Comp] from the four stage rules. *)
  Definition pipeline : CRed (Pcol k g) (Pdev k g) :=
    cred_comp (S1 k g)
      (cred_comp (gadgetize k g)
        (cred_comp (layout_exact k g Realizes HR)
                   (emit k g Nmax HN))).

  (** Theorem 5.2.  Any device measurement of optimal value decodes, through the
      whole chain of total-on-optima decoders, to a proper k-colouring of G. *)
  Theorem pipeline_sound :
    forall m, IsOpt (Pdev k g) m ->
      exists c, dec pipeline m = Some c /\ proper k g c.
  Proof.
    intros m Hm.
    destruct (cred_sound pipeline m Hm) as [c [Hdec Hopt]].
    exists c. split; [exact Hdec | exact Hopt].
  Qed.

End Pipeline.

(** ** The decision theorem.

    Reaching a device optimum is possible exactly when G is k-colourable: the
    Stage-1 exactness refinement [P_s1] survives composition to the device. *)
Theorem pipeline_decision (k : nat) (g : Graph) :
  (exists m, IsOpt (Pdev k g) m) <-> colorable k g.
Proof.
  split.
  - intros [m [Hiso Hcount]].
    apply (stage1_exact k g).
    exists (fst m). split; [exact Hiso | exact Hcount].
  - intros Hcol.
    apply (stage1_exact k g) in Hcol. destruct Hcol as [sel [Hiso Hcount]].
    exists (sel, fun _ => false). simpl. split; [exact Hiso | exact Hcount].
Qed.

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
