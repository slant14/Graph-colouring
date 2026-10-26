(** * Certificate.v — checkable certificates for both directions.

    The device only ever proposes colourings.  This module defines what counts
    as a proof in each direction and gives verified checkers for both, which
    are extracted to OCaml ([checker/]) and run on every certificate the
    decomposition driver emits.

      - Colourable direction: a colouring is checked by [check_coloring];
        [check_coloring_sound] proves that acceptance means a proper
        [k]-colouring.

      - Non-colourable direction: a *refutation* is a tree over colour
        domains.  [Split v c yes no] splits on whether [v] gets colour [c];
        [Restrict W' r] restricts attention to a sub-piece [W'] (a component of
        the separator decomposition plus its boundary); the leaves [Empty v]
        (a vertex with no colour left) and [Clash u v] (an edge whose two ends
        are both fixed to the same colour) close a branch.  A separator node of
        the decomposition is a chain of [Split]s over the separator's vertices
        followed, for every boundary colouring, by a [Restrict] to a piece that
        cannot be coloured; leaf pieces are refuted by [Split]s down to clashes.
        [check_refutation_sound] proves that acceptance means no proper
        [k]-colouring exists — the mechanized form of Theorem "Decomposed
        soundness" (ii), exhaustiveness included.

    No axioms. *)

From Stdlib Require Import PeanoNat Lia List Bool.
Import ListNotations.
Open Scope bool_scope.

Section Certificates.

Variable E : list (nat * nat).          (* edges of G *)

Definition adj (u v : nat) : bool :=
  existsb (fun e => (Nat.eqb (fst e) u && Nat.eqb (snd e) v)
                    || (Nat.eqb (fst e) v && Nat.eqb (snd e) u)) E.

Definition memb (x : nat) (l : list nat) : bool := existsb (Nat.eqb x) l.

Lemma memb_In : forall x l, memb x l = true <-> In x l.
Proof.
  intros x l. unfold memb. rewrite existsb_exists. split.
  - intros [y [Hy Hxy]]. apply Nat.eqb_eq in Hxy. subst. exact Hy.
  - intros H. exists x. split; [exact H|apply Nat.eqb_refl].
Qed.

Lemma adj_edge : forall u v, In (u, v) E -> adj u v = true.
Proof.
  intros u v H. unfold adj. apply existsb_exists. exists (u, v). split; [exact H|].
  simpl. rewrite !Nat.eqb_refl. reflexivity.
Qed.

(** ** Colourable direction. *)

Definition check_coloring (V : list nat) (k : nat) (col : nat -> nat) : bool :=
  forallb (fun v => Nat.ltb (col v) k) V &&
  forallb (fun e => negb (Nat.eqb (col (fst e)) (col (snd e)))) E.

Theorem check_coloring_sound : forall V k col,
  check_coloring V k col = true ->
  (forall v, In v V -> col v < k) /\
  (forall u v, In (u, v) E -> col u <> col v).
Proof.
  intros V k col H. unfold check_coloring in H.
  apply andb_true_iff in H as [H1 H2]. split.
  - intros v Hv. rewrite forallb_forall in H1. apply Nat.ltb_lt, H1, Hv.
  - intros u v Hin Heq. rewrite forallb_forall in H2.
    specialize (H2 (u, v) Hin). simpl in H2. rewrite Heq, Nat.eqb_refl in H2.
    discriminate.
Qed.

(** ** Non-colourable direction. *)

Inductive refutation :=
| Empty    (v : nat)
| Clash    (u v : nat)
| Split    (v c : nat) (yes no : refutation)
| Restrict (W : list nat) (r : refutation).

Definition dom_upd (d : nat -> list nat) (v : nat) (l : list nat) : nat -> list nat :=
  fun x => if Nat.eqb x v then l else d x.

Definition singleton_eq (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [a], [b] => Nat.eqb a b
  | _, _ => false
  end.

Fixpoint check_ref (W : list nat) (d : nat -> list nat) (r : refutation) : bool :=
  match r with
  | Empty v => memb v W && (match d v with [] => true | _ => false end)
  | Clash u v => memb u W && memb v W && adj u v && singleton_eq (d u) (d v)
  | Split v c yes no =>
      memb v W && check_ref W (dom_upd d v [c]) yes
               && check_ref W (dom_upd d v (remove Nat.eq_dec c (d v))) no
  | Restrict W' r' => forallb (fun x => memb x W) W' && check_ref W' d r'
  end.

(** A colouring of the piece [W] that respects the domains [d] and is proper on
    the edges inside [W]. *)
Definition respects_dom (W : list nat) (d : nat -> list nat) (col : nat -> nat) : Prop :=
  (forall v, In v W -> In (col v) (d v)) /\
  (forall u v, In u W -> In v W -> adj u v = true -> col u <> col v).

Theorem check_ref_sound : forall r W d col,
  check_ref W d r = true -> respects_dom W d col -> False.
Proof.
  induction r as [v|u v|v c yes IHy no IHn|W' r IH]; intros W d col Hc [Hdom Hprop];
    simpl in Hc.
  - apply andb_true_iff in Hc as [Hv He]. apply memb_In in Hv.
    specialize (Hdom v Hv). destruct (d v); [destruct Hdom|discriminate].
  - repeat rewrite andb_true_iff in Hc. destruct Hc as [[[Hu Hv] Ha] Hs].
    apply memb_In in Hu, Hv.
    pose proof (Hdom u Hu) as Du. pose proof (Hdom v Hv) as Dv.
    destruct (d u) as [|a [|]] eqn:Eu; try discriminate;
    destruct (d v) as [|b [|]] eqn:Ev; try discriminate.
    simpl in Hs. apply Nat.eqb_eq in Hs. subst b.
    destruct Du as [Du|[]]. destruct Dv as [Dv|[]].
    apply (Hprop u v Hu Hv Ha). congruence.
  - repeat rewrite andb_true_iff in Hc. destruct Hc as [[Hv Hy] Hn].
    apply memb_In in Hv.
    destruct (Nat.eq_dec (col v) c) as [Heq|Hne].
    + apply (IHy W (dom_upd d v [c]) col Hy). split; [|exact Hprop].
      intros x Hx. unfold dom_upd. destruct (Nat.eqb x v) eqn:Exv.
      * apply Nat.eqb_eq in Exv. rewrite Exv. left. symmetry. exact Heq.
      * apply Hdom, Hx.
    + apply (IHn W (dom_upd d v (remove Nat.eq_dec c (d v))) col Hn).
      split; [|exact Hprop].
      intros x Hx. unfold dom_upd. destruct (Nat.eqb x v) eqn:Exv.
      * apply Nat.eqb_eq in Exv. rewrite Exv. apply in_in_remove; [exact Hne|].
        apply Hdom, Hv.
      * apply Hdom, Hx.
  - apply andb_true_iff in Hc as [Hsub Hr].
    rewrite forallb_forall in Hsub.
    apply (IH W' d col Hr). split.
    + intros x Hx. apply Hdom. apply memb_In, Hsub, Hx.
    + intros u v Hu Hv Ha. apply Hprop; [apply memb_In, Hsub, Hu|apply memb_In, Hsub, Hv|exact Ha].
Qed.

(** The initial domains: every vertex may take any colour [0 .. k-1]. *)
Definition full_dom (k : nat) : nat -> list nat := fun _ => seq 0 k.

Definition check_refutation (V : list nat) (k : nat) (r : refutation) : bool :=
  check_ref V (full_dom k) r.

(** Acceptance of a refutation proves that [G] has no proper [k]-colouring. *)
Theorem check_refutation_sound : forall V k r,
  check_refutation V k r = true ->
  ~ exists col, (forall v, In v V -> col v < k) /\
                (forall u v, In u V -> In v V -> In (u, v) E -> col u <> col v).
Proof.
  intros V k r Hc [col [Hrange Hprop]].
  apply (check_ref_sound r V (full_dom k) col Hc). split.
  - intros v Hv. unfold full_dom. apply in_seq. specialize (Hrange v Hv). lia.
  - intros u v Hu Hv Ha. unfold adj in Ha. apply existsb_exists in Ha as [[a b] [Hin Hab]].
    simpl in Hab. apply orb_true_iff in Hab as [Hab|Hab];
      apply andb_true_iff in Hab as [H1 H2]; apply Nat.eqb_eq in H1, H2; subst.
    + apply (Hprop u v Hu Hv Hin).
    + intro Heq. apply (Hprop v u Hv Hu Hin). symmetry. exact Heq.
Qed.

End Certificates.

(** Extraction to OCaml: see [checker/Extract.v]. *)
