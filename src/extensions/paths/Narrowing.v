(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Narrowing Lemma *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions Subenvironments Weakening.

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
/\ (forall z bs G d D, z; bs; G ⊢ d : D -> forall G',
    G' ⪯ G ->
    z; bs; G' ⊢ d : D)
/\ (forall z bs G ds T, z; bs; G ⊢ ds :: T -> forall G',
    G' ⪯ G ->
    z; bs; G' ⊢ ds :: T)
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
    induction H; auto. apply binds_push_inv in b; destruct_all; subst.
    apply ty_sub with (T:=T0); auto. apply* weaken_subtyp.
    apply* weaken_ty_trm.
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

Lemma narrow_defs: forall G G' ds T z bs,
    z; bs; G ⊢ ds :: T ->
    G' ⪯ G ->
    z; bs; G' ⊢ ds :: T.
Proof.
  intros. apply* narrow_rules.
Qed.
