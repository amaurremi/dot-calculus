Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules_ctx:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm m1 m2 (G1 & G2 & G3) S t T) /\
  (forall G S d D, ty_def G S d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_def (G1 & G2 & G3) S d D) /\
  (forall G S ds T, ty_defs G S ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_defs (G1 & G2 & G3) S ds T) /\
  (forall m1 m2 G S T U, subtyp m1 m2 G S T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m1 m2 (G1 & G2 & G3) S T U).
Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; eauto.
  + intros. subst.
    apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst.
    apply_fresh subtyp_all as z.
    eauto.
    eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.


Lemma weaken_rules_sigma:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_trm m1 m2 G (S1 & S2 & S3) t T) /\
  (forall G S d D, ty_def G S d D -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_def G (S1 & S2 & S3) d D) /\
  (forall G S ds T, ty_defs G S ds T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_defs G (S1 & S2 & S3) ds T) /\
  (forall m1 m2 G S T U, subtyp m1 m2 G S T U -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    subtyp m1 m2 G (S1 & S2 & S3) T U).
Proof.
  apply rules_mutind; try solve [eauto].
  intros. subst.
  eapply ty_loc. eapply binds_weaken; eauto.
Qed.


Lemma weaken_ty_trm_ctx:  forall m1 m2 G1 G2 S t T,
    ty_trm m1 m2 G1 S t T ->
    ok (G1 & G2) ->
    ty_trm m1 m2 (G1 & G2) S t T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_ctx.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_ty_trm_sigma: forall m1 m2 G S1 S2 t T,
  ty_trm m1 m2 G S1 t T ->
  ok (S1 & S2) ->
  ty_trm m1 m2 G (S1 & S2) t T.
Proof.
  intros. assert (S1 & S2 = S1 & S2 & empty) as EqS. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqS. apply* weaken_rules_sigma.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqS. assumption.
Qed.

Lemma weaken_subtyp_ctx: forall m1 m2 G1 G2 S T U,
  subtyp m1 m2 G1 S T U ->
  ok (G1 & G2) ->
  subtyp m1 m2 (G1 & G2) S T U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_ctx.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp_sigma: forall m1 m2 G S1 S2 T U,
  subtyp m1 m2 G S1 T U ->
  ok (S1 & S2) ->
  subtyp m1 m2 G (S1 & S2) T U.
Proof.
  intros.
    assert (S1 & S2 = S1 & S2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_sigma.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.
