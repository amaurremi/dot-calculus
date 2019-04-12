(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality String.
Require Import Definitions Subenvironments Weakening.

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
    G' ⪯ G ->
    G' ⊢ t : T)
/\ (forall G d D, G /- d : D -> forall G',
    G' ⪯ G ->
    G' /- d : D)
/\ (forall G ds T, G /- ds :: T -> forall G',
    G' ⪯ G ->
    G' /- ds :: T)
/\ (forall G S U, G ⊢ S <: U -> forall G',
    G' ⪯ G ->
    G' ⊢ S <: U).
Proof.
  apply rules_mutind; intros; eauto 4;
    try solve [
          match goal with
          | [ H : _ ⪯ _ |- _ ] => destruct (subenv_implies_ok H)
          end;
          fresh_constructor].

  Case "ty_var"%string.
  induction H; auto;
  match goal with
  | [ H : binds _ _ (_ & _) |- _ ] =>
    apply binds_push_inv in H; destruct_all; subst
  end;
  [ eapply ty_sub; [eauto 2 | apply weaken_subtyp; trivial]
  | apply weaken_ty_trm; auto].
Qed.


(** The narrowing lemma, formulated only for term typing. *)
Lemma narrow_typing: forall G G' t T,
  G ⊢ t : T ->
  G' ⪯ G ->
  G' ⊢ t : T.
Proof.
  intros. apply* narrow_rules.
Qed.

(** The narrowing lemma, formulated only for subtyping. *)
Lemma narrow_subtyping: forall G G' S U,
  G ⊢ S <: U ->
  G' ⪯ G ->
  G' ⊢ S <: U.
Proof.
  intros. apply* narrow_rules.
Qed.
