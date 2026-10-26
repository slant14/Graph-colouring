(** * Robust.v — decoding imperfect solves.

    Every other theorem of the development assumes the device returns an
    optimum.  This module proves what happens when it does not.

      - [GProblem], [robust], [robust_comp]: a decoder is *robust with slack
        transfer [g]* if a target solution [eps] away from optimal decodes to a
        source solution at most [g eps] away; robust decoders compose, with the
        slack transfers composing as functions.  This is the graded form of the
        certified-reduction arrow.

      - The combinatorial edge-path gadget [A_4(F)] of the paper (Lemma
        "Edge-path gadget"): every edge [{u,v}] of [F] becomes the path
        [u - a - b - v], logical weight 1, gadget weight 2.  We prove its MWIS is
        [alpha(F) + 2|E|] ([gadget_mwis_value]), that every optimum restricts to
        a maximum independent set of [F] ([gadget_optimum_restricts]), and the
        robust form: an independent set of [A_4(F)] within [eps] of the optimum
        decodes, by dropping one end of every internal edge, to an independent
        set of [F] within [eps] of [alpha(F)] ([gadget_robust]).

      - Stage 1 under slack ([stage1_robust]): an independent selection of the
        colour-choice graph decodes to a proper colouring that uses a fresh
        colour for each unselected vertex, so its excess over [k] colours is
        exactly the number of unselected vertices.

    No axioms. *)

From Stdlib Require Import PeanoNat Lia List Bool.
Open Scope bool_scope.
From CertCol Require Import Sorts.
Import ListNotations.

(** ** Graded problems and robust decoders. *)

Record GProblem := { GSol : Type; gap : GSol -> nat }.

Definition robust {A B : GProblem} (d : GSol B -> GSol A) (g : nat -> nat) : Prop :=
  forall s, gap A (d s) <= g (gap B s).

Definition monotone (g : nat -> nat) : Prop := forall x y, x <= y -> g x <= g y.

Lemma robust_comp {A B C : GProblem} (d1 : GSol B -> GSol A) (d2 : GSol C -> GSol B)
      (g1 g2 : nat -> nat) :
  monotone g1 -> robust d1 g1 -> robust d2 g2 ->
  robust (fun s => d1 (d2 s)) (fun e => g1 (g2 e)).
Proof.
  intros Hm H1 H2 s. eapply Nat.le_trans; [apply H1|]. apply Hm, H2.
Qed.

Lemma robust_id (A : GProblem) : robust (A:=A) (B:=A) (fun s => s) (fun e => e).
Proof. intro s; lia. Qed.

(** ** The edge-path gadget [A_4(F)].

    [F] has vertices [0 .. N-1] and the edge list [E].  A solution of [A_4(F)]
    is a logical set [S] together with one ancilla choice per edge:
    [None] (neither gadget atom), [Some true] (the atom [a] next to the first
    end) or [Some false] (the atom [b] next to the second end); [a] and [b] are
    adjacent, so at most one is chosen, which the encoding builds in. *)

Section EdgePathGadget.

Variable N : nat.
Variable E : list (nat * nat).
Hypothesis E_range : forall u v, In (u, v) E -> u < N /\ v < N.

Fixpoint count_true (S : nat -> bool) (n : nat) : nat :=
  match n with
  | 0 => 0
  | Datatypes.S m => (if S m then 1 else 0) + count_true S m
  end.

Definition card (S : nat -> bool) : nat := count_true S N.

Definition Findep (T : nat -> bool) : Prop :=
  forall u v, In (u, v) E -> T u = true -> T v = true -> False.

Fixpoint indep4 (es : list (nat * nat)) (t : list (option bool)) (S : nat -> bool)
  : Prop :=
  match es, t with
  | [], [] => True
  | (u, v) :: es', o :: t' =>
      (o = Some true -> S u = false) /\ (o = Some false -> S v = false) /\
      indep4 es' t' S
  | _, _ => False
  end.

Definition anc (t : list (option bool)) : nat :=
  length (filter (fun o => match o with Some _ => true | None => false end) t).

Definition weight (S : nat -> bool) (t : list (option bool)) : nat :=
  card S + 2 * anc t.

Definition internal (es : list (nat * nat)) (S : nat -> bool) : nat :=
  length (filter (fun e => S (fst e) && S (snd e)) es).

Definition upd (S : nat -> bool) (x : nat) (b : bool) : nat -> bool :=
  fun y => if Nat.eqb y x then b else S y.

(** Decoder of Stage 2: walk the edges, dropping the first end of every edge
    whose two ends are both still selected. *)
Fixpoint drop (es : list (nat * nat)) (S : nat -> bool) : nat -> bool :=
  match es with
  | [] => S
  | (u, v) :: es' => drop es' (if S u && S v then upd S u false else S)
  end.

(** *** Counting lemmas. *)

Lemma count_true_le_pointwise : forall (S T : nat -> bool) n,
  (forall x, S x = true -> T x = true) -> count_true S n <= count_true T n.
Proof.
  intros S T n H. induction n; simpl; [lia|].
  destruct (S n) eqn:Es; [rewrite (H n Es)|destruct (T n)]; lia.
Qed.

Lemma count_true_upd_below : forall S x b j,
  j <= x -> count_true (upd S x b) j = count_true S j.
Proof.
  intros S x b j. induction j; intros Hj; [reflexivity|]. simpl.
  unfold upd at 1. destruct (Nat.eqb j x) eqn:E1; [apply Nat.eqb_eq in E1; lia|].
  rewrite IHj by lia. reflexivity.
Qed.

Lemma count_true_upd_false : forall S x n,
  x < n -> S x = true -> count_true (upd S x false) n + 1 = count_true S n.
Proof.
  intros S x n. induction n; intros Hx HS; [lia|]. simpl.
  unfold upd at 1. destruct (Nat.eqb n x) eqn:Eq.
  - apply Nat.eqb_eq in Eq; subst. rewrite HS.
    rewrite count_true_upd_below by lia. lia.
  - apply Nat.eqb_neq in Eq.
    assert (Hx' : x < n) by lia. specialize (IHn Hx' HS). lia.
Qed.

Lemma internal_mono : forall es (S T : nat -> bool),
  (forall x, S x = true -> T x = true) -> internal es S <= internal es T.
Proof.
  intros es S T H. unfold internal.
  induction es as [|[u v] es IH]; simpl; [lia|].
  destruct (S u) eqn:Su; destruct (S v) eqn:Sv; simpl.
  - rewrite (H u Su), (H v Sv). simpl. lia.
  - destruct (T u && T v); simpl; lia.
  - destruct (T u && T v); simpl; lia.
  - destruct (T u && T v); simpl; lia.
Qed.

Lemma drop_sub : forall es S x, drop es S x = true -> S x = true.
Proof.
  induction es as [|[u v] es IH]; intros S x H; simpl in H; [exact H|].
  apply IH in H. destruct (S u && S v); [|exact H].
  unfold upd in H. destruct (Nat.eqb x u); [discriminate|exact H].
Qed.

Lemma drop_card : forall es S,
  (forall u v, In (u, v) es -> u < N /\ v < N) ->
  card S <= card (drop es S) + internal es S.
Proof.
  induction es as [|[u v] es IH]; intros S Hr; simpl.
  - unfold internal; simpl; lia.
  - unfold internal at 1; simpl.
    destruct (S u) eqn:Su, (S v) eqn:Sv; simpl.
    + assert (Hu : u < N) by (apply (Hr u v); left; reflexivity).
      pose proof (count_true_upd_false S u N Hu Su) as Hc.
      assert (IH' := IH (upd S u false) (fun a b H => Hr a b (or_intror H))).
      assert (Hm : internal es (upd S u false) <= internal es S).
      { apply internal_mono. intros x Hx. unfold upd in Hx.
        destruct (Nat.eqb x u); [discriminate|exact Hx]. }
      unfold card in *. fold (internal es S). lia.
    + fold (internal es S). apply IH. intros a b H; apply Hr; right; exact H.
    + fold (internal es S). apply IH. intros a b H; apply Hr; right; exact H.
    + fold (internal es S). apply IH. intros a b H; apply Hr; right; exact H.
Qed.

Lemma drop_indep_list : forall es S u v,
  In (u, v) es -> drop es S u = true -> drop es S v = true -> False.
Proof.
  induction es as [|[a b] es IH]; intros S u v Hin Hu Hv; [destruct Hin|].
  simpl in Hu, Hv. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->.
    set (S1 := if S u && S v then upd S u false else S) in *.
    apply drop_sub in Hu. apply drop_sub in Hv. unfold S1 in Hu, Hv.
    destruct (S u) eqn:Su, (S v) eqn:Sv; simpl in Hu, Hv;
      try (unfold upd in Hu; rewrite Nat.eqb_refl in Hu; discriminate);
      congruence.
  - eapply IH; eauto.
Qed.

Lemma anc_internal : forall es t S,
  indep4 es t S -> anc t + internal es S <= length es.
Proof.
  induction es as [|[u v] es IH]; intros t S H; destruct t as [|o t]; simpl in H;
    try contradiction.
  - unfold anc, internal; simpl; lia.
  - destruct H as [Ha [Hb Hrest]]. specialize (IH t S Hrest).
    unfold anc, internal in *; simpl.
    destruct o as [[|]|]; simpl.
    + rewrite (Ha eq_refl); simpl. lia.
    + rewrite (Hb eq_refl). destruct (S u); simpl; lia.
    + destruct (S u && S v); simpl; lia.
Qed.

Lemma internal_zero_indep : forall S, internal E S = 0 -> Findep S.
Proof.
  intros S H u v Hin Hu Hv. unfold internal in H.
  assert (In (u, v) (filter (fun e => S (fst e) && S (snd e)) E)).
  { apply filter_In. split; [exact Hin|]. simpl. rewrite Hu, Hv; reflexivity. }
  destruct (filter (fun e => S (fst e) && S (snd e)) E); [destruct H0|discriminate].
Qed.

(** *** The decoder bound and achievability. *)

Theorem gadget_decode_bound : forall S t,
  indep4 E t S ->
  Findep (drop E S) /\ weight S t + internal E S <= card (drop E S) + 2 * length E.
Proof.
  intros S t H. split.
  - intros u v Hin Hu Hv. eapply drop_indep_list; eauto.
  - pose proof (anc_internal E t S H). pose proof (drop_card E S E_range).
    unfold weight. lia.
Qed.

Theorem gadget_achieve : forall T,
  Findep T -> exists t, indep4 E t T /\ weight T t = card T + 2 * length E.
Proof.
  intros T HT.
  exists (map (fun e => if T (fst e) then Some false else Some true) E).
  assert (Hind : forall es, (forall u v, In (u, v) es -> In (u, v) E) ->
            indep4 es (map (fun e => if T (fst e) then Some false else Some true) es) T
            /\ anc (map (fun e => if T (fst e) then Some false else Some true) es)
               = length es).
  { induction es as [|[u v] es IH]; intros Hsub; simpl; [split; reflexivity|].
    destruct IH as [IH1 IH2]; [intros a b Hin; apply Hsub; right; exact Hin|].
    split.
    - destruct (T u) eqn:Tu; simpl.
      + split; [discriminate|]. split; [|exact IH1].
        intros _. destruct (T v) eqn:Tv; [|reflexivity].
        exfalso. apply (HT u v); [apply Hsub; left; reflexivity|exact Tu|exact Tv].
      + split; [intros _; reflexivity|]. split; [discriminate|exact IH1].
    - unfold anc in *. simpl. destruct (T u); simpl; rewrite IH2; reflexivity. }
  destruct (Hind E (fun u v H => H)) as [H1 H2]. split; [exact H1|].
  unfold weight. rewrite H2. reflexivity.
Qed.

(** *** Lemma "Edge-path gadget", mechanized: with [a = alpha(F)]. *)

Definition is_alpha (a : nat) : Prop :=
  (forall T, Findep T -> card T <= a) /\ (exists T, Findep T /\ card T = a).

Theorem gadget_mwis_value : forall a, is_alpha a ->
  (forall S t, indep4 E t S -> weight S t <= a + 2 * length E) /\
  (exists S t, indep4 E t S /\ weight S t = a + 2 * length E).
Proof.
  intros a [Hmax [T [HT HTa]]]. split.
  - intros S t H. destruct (gadget_decode_bound S t H) as [Hi Hb].
    specialize (Hmax _ Hi). lia.
  - destruct (gadget_achieve T HT) as [t [H1 H2]]. exists T, t. split; [exact H1|lia].
Qed.

Theorem gadget_optimum_restricts : forall a S t, is_alpha a ->
  indep4 E t S -> weight S t = a + 2 * length E -> Findep S /\ card S = a.
Proof.
  intros a S t [Hmax HT] H Hw.
  destruct (gadget_decode_bound S t H) as [Hi Hb].
  pose proof (Hmax _ Hi). pose proof (anc_internal E t S H).
  pose proof (drop_card E S E_range).
  assert (Hint : internal E S = 0) by (unfold weight in *; lia).
  split; [apply internal_zero_indep; exact Hint|].
  unfold weight in *. lia.
Qed.

(** Robustness: [eps] below the optimum of [A_4(F)] decodes to an independent
    set of [F] at most [eps] below [alpha(F)]. *)
Theorem gadget_robust : forall a eps S t, is_alpha a ->
  indep4 E t S -> a + 2 * length E <= weight S t + eps ->
  Findep (drop E S) /\ a <= card (drop E S) + eps.
Proof.
  intros a eps S t Ha H Hw.
  destruct (gadget_decode_bound S t H) as [Hi Hb]. split; [exact Hi|lia].
Qed.

End EdgePathGadget.

(** ** Stage 1 under slack: fresh colours for unselected vertices. *)

Definition decodeRobust (k : nat) (sel : Sel) : Coloring :=
  fun v => match sel v with Some i => i | None => k + v end.

Definition proper_any (g : Graph) (c : Coloring) : Prop :=
  forall u v, u < gN g -> v < gN g -> gAdj g u v = true -> c u <> c v.

(** Number of vertices below [n] carrying a colour [>= k]. *)
Fixpoint excess (k : nat) (c : Coloring) (n : nat) : nat :=
  match n with
  | 0 => 0
  | Datatypes.S m => (if Nat.leb k (c m) then 1 else 0) + excess k c m
  end.

Lemma excess_decodeRobust : forall k g sel n, sel_wf k g sel -> n <= gN g ->
  excess k (decodeRobust k sel) n + count_some sel n = n.
Proof.
  intros k g sel n Hwf. induction n; intros Hn; simpl; [reflexivity|].
  specialize (IHn ltac:(lia)). unfold decodeRobust at 1.
  pose proof (Hwf n ltac:(lia)) as Hn'.
  destruct (sel n) as [i|] eqn:Es.
  - assert (Nat.leb k i = false) by (apply Nat.leb_gt; exact Hn'). rewrite H. lia.
  - assert (Nat.leb k (k + n) = true) by (apply Nat.leb_le; lia). rewrite H. lia.
Qed.

(** The robust Stage-1 decoder: an independent selection of size
    [n - delta] yields a proper colouring in which exactly [delta] vertices
    carry a colour outside [0..k-1], each a distinct fresh colour. *)
Theorem stage1_robust : forall k g sel,
  (forall v, v < gN g -> gAdj g v v = false) ->
  isol k g sel ->
  proper_any g (decodeRobust k sel) /\
  excess k (decodeRobust k sel) (gN g) = gN g - count_some sel (gN g) /\
  (forall u v, u < gN g -> v < gN g -> u <> v ->
     k <= decodeRobust k sel u -> decodeRobust k sel u <> decodeRobust k sel v).
Proof.
  intros k g sel Hloop [Hwf Hind]. split; [|split].
  - intros u v Hu Hv Hadj Heq. unfold decodeRobust in Heq.
    destruct (Nat.eq_dec u v) as [->|Hne]; [rewrite Hloop in Hadj; [discriminate|exact Hv]|].
    pose proof (Hwf u Hu) as Wu. pose proof (Hwf v Hv) as Wv.
    destruct (sel u) as [i|] eqn:Su, (sel v) as [j|] eqn:Sv.
    + subst j. exact (Hind u v i Hu Hv Hadj Su Sv).
    + lia.
    + lia.
    + lia.
  - pose proof (excess_decodeRobust k g sel (gN g) Hwf (le_n _)). lia.
  - intros u v Hu Hv Hne Hk Heq. unfold decodeRobust in *.
    pose proof (Hwf u Hu) as Wu. pose proof (Hwf v Hv) as Wv.
    destruct (sel u) as [i|], (sel v) as [j|]; lia.
Qed.

(** ** Theorem "End-to-end robustness" as one theorem.

    The two robust decoders above are composed on the explicit colour-choice
    graph [G'_k]: its slots [(v,i)] are numbered [v*k + i], its edge list is
    the choice cliques followed by the conflict edges, and an independent set
    [T] of [G'_k] is read as the selection [toSel T] that gives each vertex its
    first selected slot.  A solve of [A_4(G'_k)] that is [eps] below the
    optimum then decodes, by [drop] and the fresh-colour decoder, to a proper
    colouring whose colours beyond [k] number at most [d + eps], with
    [d = n - alpha(G'_k)], each fresh colour used by one vertex only. *)

Section EndToEnd.

Variable k : nat.
Variable g : Graph.
Hypothesis g_loop : forall v, v < gN g -> gAdj g v v = false.
Hypothesis g_sym  : forall u v, gAdj g u v = gAdj g v u.

Definition slot (v i : nat) : nat := v * k + i.

Definition choice_edges : list (nat * nat) :=
  flat_map (fun v => flat_map (fun i => map (fun j => (slot v i, slot v j))
                                            (seq (Datatypes.S i) (k - Datatypes.S i)))
                              (seq 0 k))
           (seq 0 (gN g)).

Definition conflict_edges : list (nat * nat) :=
  flat_map (fun u => flat_map (fun v => if gAdj g u v
                                        then map (fun i => (slot u i, slot v i)) (seq 0 k)
                                        else [])
                              (seq (Datatypes.S u) (gN g - Datatypes.S u)))
           (seq 0 (gN g)).

Definition Gk_edges : list (nat * nat) := choice_edges ++ conflict_edges.

Definition NGk : nat := gN g * k.

Lemma slot_lt : forall v i, v < gN g -> i < k -> slot v i < NGk.
Proof. intros v i Hv Hi. unfold slot, NGk. nia. Qed.

Lemma in_choice : forall v i j, v < gN g -> i < j -> j < k ->
  In (slot v i, slot v j) Gk_edges.
Proof.
  intros v i j Hv Hij Hj. apply in_or_app; left. unfold choice_edges.
  apply in_flat_map. exists v. split; [apply in_seq; lia|].
  apply in_flat_map. exists i. split; [apply in_seq; lia|].
  apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia.
Qed.

Lemma in_conflict : forall u v i, u < v -> v < gN g -> gAdj g u v = true -> i < k ->
  In (slot u i, slot v i) Gk_edges.
Proof.
  intros u v i Huv Hv Hadj Hi. apply in_or_app; right. unfold conflict_edges.
  apply in_flat_map. exists u. split; [apply in_seq; lia|].
  apply in_flat_map. exists v. split; [apply in_seq; lia|].
  rewrite Hadj. apply in_map_iff. exists i. split; [reflexivity|]. apply in_seq. lia.
Qed.

Lemma Gk_range : forall x y, In (x, y) Gk_edges -> x < NGk /\ y < NGk.
Proof.
  intros x y H. apply in_app_or in H as [H|H].
  - unfold choice_edges in H.
    apply in_flat_map in H as [v [Hv H]]. apply in_flat_map in H as [i [Hi H]].
    apply in_map_iff in H as [j [Heq Hj]]. injection Heq as <- <-.
    apply in_seq in Hv, Hi, Hj. split; apply slot_lt; lia.
  - unfold conflict_edges in H.
    apply in_flat_map in H as [u [Hu H]]. apply in_flat_map in H as [v [Hv H]].
    destruct (gAdj g u v); [|destruct H].
    apply in_map_iff in H as [i [Heq Hi]]. injection Heq as <- <-.
    apply in_seq in Hu, Hv, Hi. split; apply slot_lt; lia.
Qed.

(** Read an independent set of [G'_k] as a selection: the first selected slot. *)
Definition toSel (T : nat -> bool) : Sel :=
  fun v => find (fun i => T (slot v i)) (seq 0 k).

Lemma toSel_some : forall T v i, toSel T v = Some i -> i < k /\ T (slot v i) = true.
Proof.
  intros T v i H. apply find_some in H as [Hin HT]. apply in_seq in Hin. split; [lia|exact HT].
Qed.

Lemma toSel_none : forall T v, toSel T v = None -> forall i, i < k -> T (slot v i) = false.
Proof.
  intros T v H i Hi. eapply find_none in H; [exact H|]. apply in_seq; lia.
Qed.

Section Indep.
Variable T : nat -> bool.
Hypothesis HF : Findep Gk_edges T.

(** The choice cliques allow at most one selected slot per vertex. *)
Lemma block_unique : forall v i j, v < gN g -> i < k -> j < k -> i <> j ->
  T (slot v i) = true -> T (slot v j) = false.
Proof.
  intros v i j Hv Hi Hj Hne Ti. destruct (T (slot v j)) eqn:Tj; [|reflexivity].
  exfalso. destruct (Nat.lt_ge_cases i j) as [Hlt|Hge].
  - exact (HF _ _ (in_choice v i j Hv Hlt Hj) Ti Tj).
  - exact (HF _ _ (in_choice v j i Hv ltac:(lia) Hi) Tj Ti).
Qed.

(** The conflict edges make the selection independent in the sense of [Sorts]. *)
Lemma toSel_isol : isol k g (toSel T).
Proof.
  split.
  - intros v Hv. destruct (toSel T v) eqn:E; [apply (toSel_some T v n E)|exact I].
  - intros u v i Hu Hv Hadj Su Sv.
    destruct (toSel_some T u i Su) as [Hi Tu]. destruct (toSel_some T v i Sv) as [_ Tv].
    destruct (Nat.lt_trichotomy u v) as [Huv|[Huv|Huv]].
    + exact (HF _ _ (in_conflict u v i Huv Hv Hadj Hi) Tu Tv).
    + subst v. rewrite (g_loop u Hu) in Hadj. discriminate.
    + rewrite g_sym in Hadj. exact (HF _ _ (in_conflict v u i Huv Hu Hadj Hi) Tv Tu).
Qed.

Fixpoint count_range (a b : nat) : nat :=
  match b with
  | 0 => 0
  | Datatypes.S b' => (if T (a + b') then 1 else 0) + count_range a b'
  end.

Lemma count_true_add : forall a b, count_true T (a + b) = count_true T a + count_range a b.
Proof.
  intros a b. induction b; simpl.
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. simpl. rewrite IHb. lia.
Qed.

Lemma count_range_zero : forall a b, (forall i, i < b -> T (a + i) = false) ->
  count_range a b = 0.
Proof.
  intros a b. induction b; intros H; simpl; [reflexivity|].
  rewrite (H b ltac:(lia)). simpl. apply IHb. intros i Hi; apply H; lia.
Qed.

Lemma count_range_one : forall a b i0, i0 < b -> T (a + i0) = true ->
  (forall j, j < b -> j <> i0 -> T (a + j) = false) -> count_range a b = 1.
Proof.
  intros a b. induction b; intros i0 Hi0 Ht Hf; [lia|]. simpl.
  destruct (Nat.eq_dec i0 b) as [->|Hne].
  - rewrite Ht. rewrite count_range_zero; [lia|]. intros j Hj. apply Hf; lia.
  - rewrite (Hf b ltac:(lia) ltac:(lia)). simpl.
    apply (IHb i0); [lia|exact Ht|]. intros j Hj Hj'. apply Hf; lia.
Qed.

(** With at most one slot per vertex, the size of [T] is the size of the
    selection it encodes. *)
Lemma count_blocks : forall m, m <= gN g -> count_true T (m * k) = count_some (toSel T) m.
Proof.
  induction m; intros Hm; [reflexivity|].
  replace (Datatypes.S m * k) with (m * k + k) by lia.
  rewrite count_true_add, IHm by lia. simpl.
  destruct (toSel T m) as [i|] eqn:Es.
  - destruct (toSel_some T m i Es) as [Hi Ti].
    rewrite (count_range_one (m * k) k i Hi Ti); [lia|].
    intros j Hj Hji. apply (block_unique m i j); [lia|exact Hi|exact Hj|lia|exact Ti].
  - rewrite count_range_zero; [lia|]. intros i Hi. apply (toSel_none T m Es i Hi).
Qed.

End Indep.

(** Theorem "End-to-end robustness", mechanized.  [a] is the independence
    number of the explicit [G'_k]; the decoded colouring is proper, at most
    [(n - a) + eps] vertices carry a colour beyond [k], and each such colour is
    used by one vertex only, so at most [k + (n - a) + eps] colours are used. *)
Theorem robust_end_to_end : forall a eps S t,
  is_alpha NGk Gk_edges a ->
  indep4 Gk_edges t S ->
  a + 2 * length Gk_edges <= weight NGk S t + eps ->
  let c := decodeRobust k (toSel (drop Gk_edges S)) in
  proper_any g c /\
  excess k c (gN g) <= (gN g - a) + eps /\
  (forall u v, u < gN g -> v < gN g -> u <> v -> k <= c u -> c u <> c v).
Proof.
  intros a eps S t Ha Hind Hw c.
  destruct (gadget_robust NGk Gk_edges Gk_range a eps S t Ha Hind Hw) as [HF Hcard].
  set (T := drop Gk_edges S) in *.
  pose proof (toSel_isol T HF) as Hiso.
  destruct (stage1_robust k g (toSel T) g_loop Hiso) as [Hp [Hex Hdist]].
  pose proof (count_blocks T HF (gN g) (le_n _)) as Hcount.
  unfold card, NGk in Hcard. fold NGk in Hcard.
  split; [exact Hp|]. split; [|exact Hdist].
  unfold c. rewrite Hex. unfold NGk in Hcard. lia.
Qed.

End EndToEnd.
