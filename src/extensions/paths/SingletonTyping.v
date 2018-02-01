(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)


Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality List.
Require Import Definitions Binding Narrowing PreciseTyping RecordAndInertTypes
               Subenvironments TightTyping.

(** * Singleton typing

      Encodes singleton transitivity rule, which we only allow to be obtained directly
      from the environment. It is like precise typing + following singleton paths *)

Reserved Notation "G '⊢•' p ':' qs '⪼' T" (at level 40, p at level 59).

Inductive ty_path_sngl : ctx -> path -> list path -> typ -> Prop :=

| ty_refl_sngl : forall G p T T',
    G ⊢! p: T ⪼ T' ->
    G ⊢• p: nil ⪼ T'

| ty_trans_sngl : forall G p q qs rs T,
    G ⊢• p: qs ⪼ typ_sngl q ->
    G ⊢• q: rs ⪼ T ->
    G ⊢• p: rs ++ (q :: qs) ⪼ T

where "G '⊢•' p ':' qs ⪼ T" := (ty_path_sngl G p qs T).

Hint Constructors ty_path_sngl.

Lemma sngl_bot : forall G p qs,
    inert G ->
    G ⊢• p: qs ⪼ typ_bot ->
    False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. false* pf_bot.
Qed.

Lemma sngl_and : forall G p qs T U,
    inert G ->
    G ⊢• p : qs ⪼ typ_and T U ->
    G ⊢• p : qs ⪼ T /\ G ⊢• p: qs ⪼ U.
Proof.
  introv Hi Hp. dependent induction Hp.
  - assert (G ⊢! p : T0 ⪼ T /\ G ⊢! p : T0 ⪼ U) as Hpp by constructor*.
    destruct Hpp as [Hp1 Hp2]; constructor*.
  - specialize (IHHp2 _ _ Hi eq_refl). destruct IHHp2 as [Hr1 Hr2]. eauto.
Qed.

Lemma sngl_to_tight: forall G p qs T,
    G ⊢• p : qs ⪼ T ->
    G ⊢# trm_path p: T.
Proof.
  introv Hp. dependent induction Hp. apply* precise_to_tight. eauto.
Qed.

Lemma sngl_precise : forall G p q qs T,
    G ⊢• p : (q :: qs) ⪼ T ->
    exists U, G ⊢! q: U ⪼ T.
Proof.
  introv Hp. dependent induction Hp; eauto.
  destruct rs.
  - simpls. inversions x. inversions Hp2. eauto.
    destruct (app_eq_nil _ _ H). subst. inversion H2.
  - simpls. inversions x. specialize (IHHp2 _ _ eq_refl). destruct IHHp2 as [U Hp]. eauto.
Qed.

Lemma sngl_tight_paths : forall G p q qs T,
    G ⊢• p : (q :: qs) ⪼ T ->
    G ⊢# trm_path p : typ_sngl q.
Proof.
  introv Hp. dependent induction Hp; eauto.
  destruct rs; simpls; inversions x. apply* sngl_to_tight.
  specialize (IHHp2 _ _ eq_refl). apply sngl_to_tight in Hp1. apply ty_sub_t with (T:=typ_sngl q0); auto.
  assert (typ_sngl q = repl_typ q0 q (typ_sngl q0)) as Heq by admit. rewrite* Heq.
Qed.

Lemma sngl_inertsngl : forall G p qs T,
    inert G ->
    G ⊢• p: qs ⪼ T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Hp. induction Hp; eauto. apply* pf_inertsngl.
Qed.
