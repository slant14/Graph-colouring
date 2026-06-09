(** * Effect.v — refinements A and B: certificate grade and the safety effect.

    Two self-contained algebraic refinements from [type-system/type-system.tex]:

      - Sec. 7 (Refinement A): the certificate *grade* lattice
        [w ⊑ χ] (witness-relative ⊑ true-χ), a partial order with bottom [w];
      - Sec. 6 (Refinement B): the *safety effect* [{safe, asafe c}] of the
        secondary supergraph path, with composition [⊕].  We prove it is a
        commutative monoid (the note states the laws; here they are checked),
        which is what makes the [Comp-S] rule's effect accumulation well-defined
        and order-independent in its *bound*. *)

From Stdlib Require Import PeanoNat Lia.

(** ** Refinement A — certificate grade. *)

Inductive Grade := gw | gchi.   (* witness-relative  ⊑  true-χ *)

Definition gle (a b : Grade) : Prop :=
  match a, b with
  | gw,   _    => True          (* w is below everything *)
  | gchi, gchi => True
  | gchi, gw   => False
  end.

Lemma gle_refl : forall a, gle a a.
Proof. destruct a; exact I. Qed.

Lemma gle_trans : forall a b c, gle a b -> gle b c -> gle a c.
Proof. destruct a, b, c; simpl; tauto. Qed.

Lemma gle_antisym : forall a b, gle a b -> gle b a -> a = b.
Proof. destruct a, b; simpl; intros; (reflexivity || contradiction). Qed.

(** [gw] is the bottom grade: soundness already holds at the witness level,
    so nothing requires the true chromatic number. *)
Lemma gw_bottom : forall a, gle gw a.
Proof. intro a; exact I. Qed.

(** ** Refinement B — the safety effect monoid. *)

Inductive Eff :=
| safe                    (* χ preserved *)
| asafe (c : nat).        (* never lowers χ; raises it by at most c *)

Definition eplus (a b : Eff) : Eff :=
  match a, b with
  | safe,     b'        => b'
  | a',       safe      => a'
  | asafe c,  asafe d   => asafe (c + d)
  end.

Lemma eplus_id_l : forall e, eplus safe e = e.
Proof. destruct e; reflexivity. Qed.

Lemma eplus_id_r : forall e, eplus e safe = e.
Proof. destruct e; reflexivity. Qed.

Lemma eplus_assoc : forall a b c, eplus a (eplus b c) = eplus (eplus a b) c.
Proof.
  destruct a as [|ca], b as [|cb], c as [|cc]; simpl;
    try reflexivity. f_equal; lia.
Qed.

Lemma eplus_comm : forall a b, eplus a b = eplus b a.
Proof.
  destruct a as [|ca], b as [|cb]; simpl; try reflexivity. f_equal; lia.
Qed.

(** The accumulated bound is monotone: composing more [asafe] steps can only
    raise the χ-increase budget, never lower it — the note's "order records
    order-sensitivity as a difference in the derived effect." *)
Definition bound (e : Eff) : nat :=
  match e with safe => 0 | asafe c => c end.

Lemma bound_eplus : forall a b, bound (eplus a b) = bound a + bound b.
Proof. destruct a as [|ca], b as [|cb]; simpl; lia. Qed.

(** Composition order is irrelevant to the accumulated *bound* (a corollary of
    commutativity of [+]); the carrier graph may still differ, which is exactly
    where genuine order-sensitivity is recorded. *)
Lemma bound_comm : forall a b, bound (eplus a b) = bound (eplus b a).
Proof. intros; rewrite eplus_comm; reflexivity. Qed.
