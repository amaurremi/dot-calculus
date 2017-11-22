(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.

(** * Weakening Lemma *)
(** Weakening states that typing is preserved in extended environments. *)

(** [G1, G3 ⊢ t: T]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ t: T] #<br># #<br>#

    and

    [G1, G3 ⊢ d: D]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ d: D] #<br># #<br>#

    and

    [G1, G3 ⊢ ds :: T]                 #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ ds :: T] #<br># #<br>#

    and

    [G1, G3 ⊢ T <: U]                  #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ T <: U] #<br># #<br>#

    The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma weaken_rules:
  (forall G Sigma t T, G ⋆ Sigma ⊢ t : T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 ⋆ Sigma ⊢ t : T) /\
  (forall G Sigma d D, G ⋆ Sigma /- d : D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 ⋆ Sigma /- d : D) /\
  (forall G Sigma ds T, G ⋆ Sigma /- ds :: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 ⋆ Sigma /- ds :: T) /\
  (forall G Sigma T U, G ⋆ Sigma ⊢ T <: U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 ⋆ Sigma ⊢ T <: U).
Proof.
  apply rules_mutind; intros; subst;
  eauto 4 using binds_weaken;
  fresh_constructor;
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _,
        Hok: ok (?G1 & ?G2 & ?G3)
        |- context [?z ~ ?T] ] =>
      assert (zL : z \notin L) by auto;
      specialize (H z zL G1 G2 (G3 & z ~ T));
      rewrite? concat_assoc in H;
      apply~ H
    end.
Qed.

Lemma weaken_rules_sigma:
  (forall G Sigma t T, G ⋆ Sigma ⊢ t : T -> forall Sigma1 Sigma2 Sigma3,
    Sigma = Sigma1 & Sigma3 ->
    ok (Sigma1 & Sigma2 & Sigma3) ->
    G ⋆ (Sigma1 & Sigma2 & Sigma3) ⊢ t : T) /\
  (forall G Sigma d D, G ⋆ Sigma /- d : D -> forall Sigma1 Sigma2 Sigma3,
    Sigma = Sigma1 & Sigma3 ->
    ok (Sigma1 & Sigma2 & Sigma3) ->
    G ⋆ (Sigma1 & Sigma2 & Sigma3) /- d : D) /\
  (forall G Sigma ds T, G ⋆ Sigma /- ds :: T -> forall Sigma1 Sigma2 Sigma3,
    Sigma = Sigma1 & Sigma3 ->
    ok (Sigma1 & Sigma2 & Sigma3) ->
    G ⋆ (Sigma1 & Sigma2 & Sigma3) /- ds :: T) /\
  (forall G Sigma T U, G ⋆ Sigma ⊢ T <: U -> forall Sigma1 Sigma2 Sigma3,
    Sigma = Sigma1 & Sigma3 ->
    ok (Sigma1 & Sigma2 & Sigma3) ->
    G ⋆ (Sigma1 & Sigma2 & Sigma3) ⊢ T <: U).
Proof.
  apply rules_mutind; try solve [eauto].
  intros. subst.
  eapply ty_loc. eapply binds_weaken; eauto.
Qed.

Ltac weaken_specialize :=
  intros;
  match goal with
  | [ Hok: ok (?G1 & ?G2) |- _ ] =>
    assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r;
    rewrite EqG; apply~ weaken_rules;
    (rewrite concat_empty_r || rewrite <- EqG); assumption
  end.

Ltac weaken_specialize_sigma :=
  intros;
  match goal with
  | [ Hok: ok (?G1 & ?G2) |- _ ] =>
    assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r;
    rewrite EqG; apply~ weaken_rules_sigma;
    (rewrite concat_empty_r || rewrite <- EqG); assumption
  end.

(** Weakening lemma specialized to term typing. *)
Lemma weaken_ty_trm: forall G1 G2 Sigma t T,
    G1 ⋆ Sigma ⊢ t : T ->
    ok (G1 & G2) ->
    G1 & G2 ⋆ Sigma ⊢ t : T.
Proof.
  weaken_specialize.
Qed.

Lemma weaken_ty_trm_sigma: forall G Sigma1 Sigma2 t T,
  G ⋆ Sigma1 ⊢ t : T ->
  ok (Sigma1 & Sigma2) ->
  G ⋆ (Sigma1 & Sigma2) ⊢ t : T.
Proof.
  weaken_specialize_sigma.
Qed.

(** Weakening lemma specialized to subtyping. *)
Lemma weaken_subtyp: forall G1 G2 Sigma T U,
  G1 ⋆ Sigma ⊢ T <: U ->
  ok (G1 & G2) ->
  G1 & G2 ⋆ Sigma ⊢ T <: U.
Proof.
  weaken_specialize.
Qed.

Lemma weaken_subtyp_sigma: forall G Sigma1 Sigma2 T U,
  G ⋆ Sigma1 ⊢ T <: U ->
  ok (Sigma1 & Sigma2) ->
  G ⋆ (Sigma1 & Sigma2) ⊢ T <: U.
Proof.
  weaken_specialize_sigma.
Qed.
