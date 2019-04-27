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
    apply rules_mutind; intros;
    match goal with
    | [ B: binds _ _ _, H : ?G' ⪯ _ |- _ ⊢ trm_var (avar_f _) : _ ] =>
      induction H; [auto | apply binds_push_inv in B];
        destruct_all; [ subst; eapply ty_sub | idtac];
          eauto using ty_var, weaken_subtyp, weaken_ty_trm
    | _ => try fresh_constructor; eauto
    end.
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
