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
  (forall G t T, G ⊢ t : T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 ⊢ t : T) /\
  (forall G d D, G /- d : D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 /- d : D) /\
  (forall G ds T, G /- ds :: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 /- ds :: T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 ⊢ T <: U).
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

Ltac weaken_specialize :=
  intros;
  match goal with
  | [ Hok: ok (?G1 & ?G2) |- _ ] =>
    assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r;
    rewrite EqG; apply~ weaken_rules;
    (rewrite concat_empty_r || rewrite <- EqG); assumption
  end.

(** Weakening lemma specialized to term typing. *)
Lemma weaken_ty_trm: forall G1 G2 t T,
    G1 ⊢ t : T ->
    ok (G1 & G2) ->
    G1 & G2 ⊢ t : T.
Proof.
  weaken_specialize.
Qed.

(** Weakening lemma specialized to subtyping. *)
Lemma weaken_subtyp: forall G1 G2 S U,
  G1 ⊢ S <: U ->
  ok (G1 & G2) ->
  G1 & G2 ⊢ S <: U.
Proof.
  weaken_specialize.
Qed.
