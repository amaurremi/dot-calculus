(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Weakening.


(** [G1] is a subenvironment of [G2], denoted [G1 subG G2],
     if for each [x] s.t. [G2(x)=T2],
    [G1(x) = T1] and [G1 |- T1 <: T2]. *)
Definition subenv(G1 G2: ctx) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ G1 ⊢ T1 <: T2.

(** [G' subG G]              #<br>#
    [ok(G', x: T)]               #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T]  #<br>#
    Note: [ok(G)] means that [G]'s domain consists of distinct variables.
    [ok] is defined in [TLC.LibEnv.v]. *)
Lemma subenv_push: forall G G' x T,
  subenv G' G ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T).
Proof.
  intros.
  unfold subenv. intros xb Tb Bi. apply binds_push_inv in Bi.
  destruct Bi as [Bi | Bi].
  + destruct Bi as [Bi1 Bi2]. subst.
    left. eauto.
  + destruct Bi as [Bi1 Bi2].
    unfold subenv in H. specialize (H xb Tb Bi2). destruct H as [Bi' | Bi'].
    * left. eauto.
    * right. destruct Bi' as [T' [Bi1' Bi2']].
      exists T'. split. eauto. apply weaken_subtyp. assumption. eauto.
Qed.

(** [G ⊢ S <: U]                      #<br>#
    [ok(G, x: S)] (see [subenv_push]) #<br>#
    [――――――――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T] *)
Lemma subenv_last: forall G x S U,
  G ⊢ S <: U ->
  ok (G & x ~ S) ->
  subenv (G & x ~ S) (G & x ~ U).
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists S. split; eauto using weaken_subtyp.
  - destruct Bi. left. eauto.
Qed.

Lemma subenv_concat: forall G G' G'',
    subenv G' G ->
    ok (G & G'') ->
    ok (G' & G'') ->
    subenv (G' & G'') (G & G'').
Proof.
  intros. unfold subenv in *. intros y T Bi. apply binds_concat_inv in Bi.
  destruct~ Bi. destruct H2. specialize (H y T H3). destruct~ H.
  destruct H as [T' [Bi Hs]]. right. exists T'. split~.
  apply~ weaken_subtyp.
Qed.

(** * Narrowing Lemma *)
(** The narrowing lemma states that typing is preserved under subenvironments.
    The lemma corresponds to Lemma 3.11 in the paper.
    The proof is by mutual induction on term typing, definition typing,
    and subtyping. *)

(** [G ⊢ t: T]                 #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ t: T]

    and

    [G ⊢ d: D]                 #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ d: D]

    and

    [G ⊢ ds :: T]              #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ ds :: T]

    and

    [G ⊢ S <: U]               #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ S <: U]              #<br>#

Note: for simplicity, the definition typing judgements and [ok] conditions
      are omitted from the paper formulation. *)
Lemma narrow_rules:
  (forall G t T, G ⊢ t : T -> forall G',
    ok G' ->
    subenv G' G ->
    G' ⊢ t : T)
/\ (forall x bs P G d D, x; bs; P; G ⊢ d : D -> forall G',
    ok G' ->
    subenv G' G ->
    x; bs; P; G' ⊢ d : D)
/\ (forall x bs P G ds T, x; bs; P; G ⊢ ds :: T -> forall G',
    ok G' ->
    subenv G' G ->
    x; bs; P; G' ⊢ ds :: T)
/\ (forall G S U, G ⊢ S <: U -> forall G',
    ok G' ->
    subenv G' G ->
    G' ⊢ S <: U).
Proof.
  apply rules_mutind; intros; eauto 4;
    try solve [fresh_constructor; auto using subenv_push].
  Case "ty_var".
  match goal with
  | [ Hs: subenv _ _, Hb: binds ?x ?T _ |- _ ] =>
    specialize (Hs x T Hb);
    destruct_all; eauto
  end.
Qed.

(** The narrowing lemma, formulated only for term typing. *)
Lemma narrow_typing: forall G G' t T,
  G ⊢ t : T ->
  subenv G' G -> ok G' ->
  G' ⊢ t : T.
Proof.
  intros. apply* narrow_rules.
Qed.

(** The narrowing lemma, formulated only for subtyping. *)
Lemma narrow_subtyping: forall G G' S U,
  G ⊢ S <: U ->
  subenv G' G -> ok G' ->
  G' ⊢ S <: U.
Proof.
  intros. apply* narrow_rules.
Qed.
