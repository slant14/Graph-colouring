(** * Effect.v — refinements A and B: certificate grade and the safety effect.

    Two self-contained algebraic refinements from [type-system/type-system.tex]:

      - Sec. 7 (Refinement A): the certificate *grade* lattice
        [w ⊑ χ] (witness-relative ⊑ true-χ), a partial order with bottom [w];
      - Sec. 6 (Refinement B): the *safety effect* [{safe, asafe c, mono}] of
        the secondary supergraph path, with composition [⊕].  We prove it is a
        commutative monoid, give each effect a meaning over chromatic numbers
        ([respects]), and prove that the meaning composes ([respects_comp]) and
        that the witness-based introduction of [asafe c] is sound
        ([asafe_intro]). *)

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

(** ** Refinement B — the safety effect monoid.

    [safe]      χ preserved (only for a transform that adds no edge);
    [asafe c]   χ does not decrease and rises by at most [c] — introduced only
                with a discharged witness premise (a proper colouring of the new
                graph with [u] colours and a clique of size [l] in the old one,
                [c = u - l]; see [asafe_intro]);
    [mono]      χ does not decrease (Prop. "Safety ⇒ decoder correctness"),
                with no bound — the default for any same-vertex supergraph
                transform whose bound has not been discharged. *)

Inductive Eff :=
| safe
| asafe (c : nat)
| mono.

Definition eplus (a b : Eff) : Eff :=
  match a, b with
  | safe,     b'        => b'
  | a',       safe      => a'
  | mono,     _         => mono
  | _,        mono      => mono
  | asafe c,  asafe d   => asafe (c + d)
  end.

Lemma eplus_id_l : forall e, eplus safe e = e.
Proof. destruct e; reflexivity. Qed.

Lemma eplus_id_r : forall e, eplus e safe = e.
Proof. destruct e; reflexivity. Qed.

Lemma eplus_assoc : forall a b c, eplus a (eplus b c) = eplus (eplus a b) c.
Proof.
  destruct a as [|ca|], b as [|cb|], c as [|cc|]; simpl;
    try reflexivity. f_equal; lia.
Qed.

Lemma eplus_comm : forall a b, eplus a b = eplus b a.
Proof.
  destruct a as [|ca|], b as [|cb|]; simpl; try reflexivity. f_equal; lia.
Qed.

(** *** Meaning of an effect: how χ may move across one transform.

    [respects e x y] says that a transform carrying effect [e] takes a graph of
    chromatic number [x] to one of chromatic number [y] as [e] promises. *)
Definition respects (e : Eff) (x y : nat) : Prop :=
  match e with
  | safe    => y = x
  | asafe c => x <= y /\ y <= x + c
  | mono    => x <= y
  end.

(** Soundness of composition: the meanings compose along [eplus], so the
    accumulated effect of a pipeline is a correct statement about the χ of its
    end points (bounds add, [mono] absorbs). *)
Lemma respects_comp : forall a b x y z,
  respects a x y -> respects b y z -> respects (eplus a b) x z.
Proof.
  destruct a as [|ca|], b as [|cb|]; simpl; intros; lia.
Qed.

(** Introduction rules.  [mono] needs only that χ does not decrease, which
    holds for every same-vertex supergraph.  [asafe] needs witnesses: a lower
    bound [l <= χ(G)] (a clique of size [l] in [G]) and an upper bound
    [χ(H) <= u] (a proper colouring of [H] with [u] colours). *)
Lemma mono_intro : forall x y, x <= y -> respects mono x y.
Proof. simpl; intros; lia. Qed.

Lemma asafe_intro : forall x y l u,
  l <= x -> y <= u -> x <= y -> respects (asafe (u - l)) x y.
Proof. simpl; intros; lia. Qed.

Lemma safe_intro : forall x, respects safe x x.
Proof. reflexivity. Qed.

(** *** The accumulated bound: [None] once any step is unbounded. *)
Definition bound (e : Eff) : option nat :=
  match e with safe => Some 0 | asafe c => Some c | mono => None end.

Definition oadd (a b : option nat) : option nat :=
  match a, b with Some x, Some y => Some (x + y) | _, _ => None end.

Lemma bound_eplus : forall a b, bound (eplus a b) = oadd (bound a) (bound b).
Proof. destruct a as [|ca|], b as [|cb|]; simpl; try reflexivity. f_equal; lia. Qed.

(** Composition order is irrelevant to the accumulated *bound* (a corollary of
    commutativity); the carrier graph may still differ, which is exactly where
    genuine order-sensitivity is recorded. *)
Lemma bound_comm : forall a b, bound (eplus a b) = bound (eplus b a).
Proof. intros; rewrite eplus_comm; reflexivity. Qed.
