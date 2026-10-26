(** * Sorts.v — the concrete problem-types and their solution domains.

    The abstract calculus of [Problem.v] is instantiated here on real graph
    data, giving the sorts of [type-system/type-system.tex] Sec. 2:

      - [Pcol k g]  — the [Col⟨n,k⟩] k-colouring instance,
      - [Pis  k g]  — the Stage-1 colour-choice independent-set instance
                      [IS⟨nk⟩{P_s1}], carrying the exactness refinement,
      - [Pwis k g]  — the gadget weighted-IS instance [WIS⟨N,C⟩].

    The one modelling idea worth stating up front concerns the colour-choice
    graph [G'].  Its vertices are slots [(v,i)] = "vertex v takes colour i", and
    a *choice clique* per [v] forbids picking two slots of the same vertex.  We
    represent an independent set of [G'] directly by an [option]-valued choice
    function [Sel := nat -> option nat]: [sel v = Some i] means slot [(v,i)] is
    chosen, [None] means [v] is unslotted.  The choice clique — "at most one
    slot per vertex" — is then *exactly* the well-typedness of [option], so no
    pigeonhole counting is ever needed.  Independence reduces to the conflict
    edges only.  This is faithful to [src/lib/UDGColor/Stage1.hs]. *)

From Stdlib Require Import PeanoNat Lia.
From CertCol Require Import Problem.

(** A finite simple graph on vertices [0 .. gN-1] with a boolean adjacency. *)
Record Graph := { gN : nat; gAdj : nat -> nat -> bool }.

(** ** Colourings (the [Col] solution domain). *)

Definition Coloring := nat -> nat.

Definition proper (k : nat) (g : Graph) (c : Coloring) : Prop :=
  (forall v, v < gN g -> c v < k) /\
  (forall u v, u < gN g -> v < gN g -> gAdj g u v = true -> c u <> c v).

Definition colorable (k : nat) (g : Graph) : Prop := exists c, proper k g c.

(** The [Col] problem asks for a decision with a witness: a solution is either a
    colouring ([Some c]) or the answer "not k-colourable" ([None]).  [Some c] is
    correct when [c] is proper, and [None] is correct when no proper colouring
    exists. *)
Definition Pcol (k : nat) (g : Graph) : Problem :=
  {| Sol   := option Coloring;
     IsOpt := fun a => match a with
                       | Some c => proper k g c
                       | None   => ~ colorable k g
                       end |}.

(** ** Colour-choice independent sets (the [IS] solution domain). *)

Definition Sel := nat -> option nat.

(** Colours are in range; the choice-clique "≤1 per vertex" is built into [Sel]. *)
Definition sel_wf (k : nat) (g : Graph) (sel : Sel) : Prop :=
  forall v, v < gN g -> match sel v with Some i => i < k | None => True end.

(** Independence in [G']: a conflict edge joins equal-colour slots of adjacent
    vertices, so independence forbids adjacent vertices sharing a colour. *)
Definition indep (g : Graph) (sel : Sel) : Prop :=
  forall u v i, u < gN g -> v < gN g -> gAdj g u v = true ->
                sel u = Some i -> sel v = Some i -> False.

Definition isol (k : nat) (g : Graph) (sel : Sel) : Prop :=
  sel_wf k g sel /\ indep g sel.

(** Size of a selection over the first [n] vertices. *)
Fixpoint count_some (sel : Sel) (n : nat) : nat :=
  match n with
  | 0   => 0
  | S m => (match sel m with Some _ => 1 | None => 0 end) + count_some sel m
  end.

Lemma count_some_le : forall sel n, count_some sel n <= n.
Proof.
  intros sel n. induction n; simpl; [lia | destruct (sel n); lia].
Qed.

(** A selection covering every vertex < n has size n. *)
Lemma full_count : forall n sel,
  (forall v, v < n -> sel v <> None) -> count_some sel n = n.
Proof.
  induction n; intros sel H; simpl.
  - reflexivity.
  - destruct (sel n) eqn:E.
    + assert (Hc : count_some sel n = n) by (apply IHn; intros v Hv; apply H; lia).
      rewrite Hc; lia.
    + exfalso. apply (H n (Nat.lt_succ_diag_r n)). exact E.
Qed.

(** Conversely a maximum-size (= n) selection covers every vertex < n. *)
Lemma count_full : forall n sel,
  count_some sel n = n -> forall v, v < n -> sel v <> None.
Proof.
  induction n; intros sel Hc v Hv; simpl in Hc.
  - lia.
  - assert (Hle := count_some_le sel n).
    destruct (sel n) eqn:E.
    + assert (Hc' : count_some sel n = n) by lia.
      destruct (Nat.eq_dec v n) as [->|Hne].
      * rewrite E; discriminate.
      * apply IHn; [exact Hc' | lia].
    + lia.
Qed.

(** The independent-set problem-type [IS⟨nk⟩{P_s1}].  Its optima are the
    *maximum* independent selections in the standard sense: no independent
    selection is larger.  Stage-1 exactness ([Stages.stage1_opt]) then says that
    a maximum has size [n] exactly when [G] is k-colourable. *)
Definition maximum (k : nat) (g : Graph) (sel : Sel) : Prop :=
  isol k g sel /\
  forall sel', isol k g sel' -> count_some sel' (gN g) <= count_some sel (gN g).

Definition Pis (k : nat) (g : Graph) : Problem :=
  {| Sol := Sel; IsOpt := maximum k g |}.

(** ** Gadget weighted-IS, unit-disk and device sorts.

    Stage 2 is mechanised at its interface: a solution of the gadget instance
    carries the logical selection together with an ancilla occupancy, and its
    optima are those whose logical part is a maximum of [Pis]; the offset [C] and
    the atom count [N] are indices of the sort ([WIS⟨N,C⟩] in the paper).

    The three sorts have the same optima but *distinct* solution types, indexed
    by [N] (and [C]), so no two of them are convertible: composing the stage
    reductions in a wrong order, or with mismatched atom counts, is a type
    error (see [Pipeline.v]). *)
Definition WSel := (Sel * (nat -> bool))%type.

Record WSol (N C : nat) := mkW { unW : WSel }.
Record USol (N : nat) := mkU { unU : WSel }.
Record DSol (N : nat) := mkD { unD : WSel }.
Arguments mkW {N C}. Arguments unW {N C}.
Arguments mkU {N}.   Arguments unU {N}.
Arguments mkD {N}.   Arguments unD {N}.

Definition Pwis (k : nat) (g : Graph) (N C : nat) : Problem :=
  {| Sol := WSol N C; IsOpt := fun s => maximum k g (fst (unW s)) |}.

Definition Pudg (k : nat) (g : Graph) (N : nat) : Problem :=
  {| Sol := USol N; IsOpt := fun s => maximum k g (fst (unU s)) |}.

Definition Pdev (k : nat) (g : Graph) (N : nat) : Problem :=
  {| Sol := DSol N; IsOpt := fun s => maximum k g (fst (unD s)) |}.
