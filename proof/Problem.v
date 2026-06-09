(** * Problem.v — the certified-reduction calculus, abstractly.

    This is the mechanised core of [type-system/type-system.tex]: the
    "certified-reduction judgment" of Sec. 3 and the composition rule [Comp] of
    Sec. 5, with nothing yet about graphs.  A *problem-type* (the note's sorts
    Col, IS, WIS, UDG, Dev) is modelled semantically by its solution domain
    together with the predicate that singles out its optimal solutions; a
    *certified reduction* [A ⇝[δ] B] is a decoder [δ : B ⇀ A] that is
    "total on optima".  The pay-off (the note's "minimal core, steps 1–3") is
    that these reductions form a category: identities and composition exist and
    composition preserves the total-on-optima certificate.  That single fact is
    the engine of the end-to-end soundness theorem in [Pipeline.v]. *)

(** A problem-type: a solution domain [Sol] and a predicate [IsOpt] picking out
    the optimal solutions (the note's [Sol A] and [opt A]). *)
Record Problem : Type := {
  Sol   : Type;
  IsOpt : Sol -> Prop
}.

(** A *decoder* from [B] to [A] is a partial map on solution domains
    (note, Def. "Decoder"). *)
Definition decoder (B A : Problem) := Sol B -> option (Sol A).

(** "Total on optima": defined on every optimum of [B], and landing on an
    optimum of [A] (note, Def. "tot-opt"). *)
Definition tot_opt {B A : Problem} (d : decoder B A) : Prop :=
  forall s, IsOpt B s -> exists a, d s = Some a /\ IsOpt A a.

(** A certified reduction [A ⇝[dec] B] (note, Def. "Certified reduction").
    The transformation runs [A → B]; the decoder runs [B → A] and is the
    answer-preservation certificate. *)
Record CRed (A B : Problem) : Type := {
  dec  : decoder B A;
  cert : tot_opt dec
}.
Arguments dec  {A B}.
Arguments cert {A B}.

(** ** Identity reduction. *)

Definition idDec (A : Problem) : decoder A A := fun s => Some s.

Lemma idDec_tot_opt (A : Problem) : tot_opt (idDec A).
Proof. intros s Hs. exists s. split; [reflexivity | exact Hs]. Qed.

Definition cred_id (A : Problem) : CRed A A :=
  {| dec := idDec A; cert := idDec_tot_opt A |}.

(** ** Composition (rule [Comp]).

    A reduction [A ⇝ B] followed by [B ⇝ C] yields [A ⇝ C]; the composed
    decoder runs [C → B → A]. *)

Definition comp_dec {A B C : Problem}
           (dAB : decoder B A) (dBC : decoder C B) : decoder C A :=
  fun s => match dBC s with
           | Some b => dAB b
           | None   => None
           end.

Lemma comp_tot_opt {A B C : Problem}
      (dAB : decoder B A) (dBC : decoder C B) :
  tot_opt dAB -> tot_opt dBC -> tot_opt (comp_dec dAB dBC).
Proof.
  intros HAB HBC s Hs.
  destruct (HBC s Hs) as [b [Hb Hob]].
  destruct (HAB b Hob) as [a [Ha Hoa]].
  exists a. unfold comp_dec. rewrite Hb. split; [exact Ha | exact Hoa].
Qed.

Definition cred_comp {A B C : Problem}
           (r1 : CRed A B) (r2 : CRed B C) : CRed A C :=
  {| dec  := comp_dec (dec r1) (dec r2);
     cert := comp_tot_opt (dec r1) (dec r2) (cert r1) (cert r2) |}.

(** ** Generic soundness — the kernel of Theorem "Pipeline soundness".

    A certified reduction turns any optimum of the *target* [B] into a decoded
    optimum of the *source* [A]: "solve [B] on the device, apply [δ], read off
    [A]'s answer." *)

Theorem cred_sound {A B : Problem} (r : CRed A B) :
  forall s, IsOpt B s -> exists a, dec r s = Some a /\ IsOpt A a.
Proof. exact (cert r). Qed.

(** Composition is associative on decoders (the category law), so the order in
    which a long pipeline is bracketed is immaterial. *)
Lemma comp_dec_assoc {A B C D : Problem}
      (dAB : decoder B A) (dBC : decoder C B) (dCD : decoder D C) (s : Sol D) :
  comp_dec dAB (comp_dec dBC dCD) s = comp_dec (comp_dec dAB dBC) dCD s.
Proof.
  unfold comp_dec. destruct (dCD s) as [c|]; [destruct (dBC c) as [b|]|]; reflexivity.
Qed.
