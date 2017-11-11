Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules:
  (forall G t T, G |- t : T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 |- t : T) /\
  (forall G p T, G |-\||/ p: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 |-\||/ p: T) /\
  (forall G x T d D, G && x ~ T |- d : D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ T) ->
    (G1 & G2 & G3) && x ~ T |- d : D) /\
  (forall G x U ds T, G && x ~ U |- ds :: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ U) ->
    G1 & G2 & G3 && x ~ U |- ds :: T) /\
  (forall G T U, G |- T <: U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 |- T <: U).
Proof.
  apply rules_mutind; eauto 4; intros; subst.
  + eapply ty_var. eapply binds_weaken; eauto.
  + apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 G3). apply* H.
  + apply_fresh ty_let as z.
    - auto.
    - assert (zL: z \notin L) by auto.
      specialize (H0 z zL G1 G2 (G3 & z ~ T)).
      repeat rewrite concat_assoc in H0.
      apply* H0.
  + apply ty_def_trm.
    rewrite <- concat_assoc. apply H;rewrite concat_assoc. reflexivity. assumption.
  + apply ty_def_val. rewrite <- concat_assoc. apply H; rewrite concat_assoc. reflexivity. assumption.
  + apply_fresh subtyp_all as z.
    auto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma weaken_ty_trm:  forall G1 G2 t T,
    G1 |- t : T ->
    ok (G1 & G2) ->
    G1 & G2 |- t : T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp: forall G1 G2 S U,
  G1 |- S <: U ->
  ok (G1 & G2) ->
  G1 & G2 |- S <: U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_rules_p: forall G t T G1 G2 G3,
    G |-! t : T ->
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 |-! t : T.
Proof.
  introv Hp Heq ok. dependent induction Hp; eauto.
  - apply ty_var_p. apply* binds_weaken. subst*.
  - apply_fresh ty_all_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL).
    assert (Hz: G & z ~ T = G1 & G3 & z ~ T) by rewrite* Heq.
    assert(Hok: LibEnv.ok (G1 & G2 & G3 & z ~ T)) by auto.
    rewrite <- concat_assoc.
    apply ((proj41 weaken_rules) (G & z ~ T)).
    + assumption.
    + rewrite concat_assoc. subst*.
    + rewrite concat_assoc. subst*.
  - apply_fresh ty_new_intro_p as z. apply* weaken_rules.
Qed.

Lemma weaken_ty_trm_p: forall G1 G2 t T,
    G1 |-! t : T ->
    ok (G1 & G2) ->
    G1 & G2 |-! t : T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_p.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.
