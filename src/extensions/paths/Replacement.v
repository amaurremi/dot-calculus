(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Path Replacement [T[q/p,n]] *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Sequences.
Require Import Definitions Binding.

Hint Constructors star.


(** If [T[q/p] = U] then [U[p/q] = T] *)
Lemma repl_swap:
  (forall p q T T',
      repl_typ p q T T' ->
      repl_typ q p T' T) /\
  (forall p q D D',
      repl_dec p q D D' ->
      repl_dec q p D' D).
Proof.
  apply repl_mutind; intros; eauto.
Qed.

(** Replacing the whole path of a singleton type *)
Lemma repl_intro_sngl: forall p q,
    repl_typ p q {{ p }} {{ q }}.
Proof.
  intros p q.
  replace {{ p }} with {{ p •• nil }}.
  replace {{ q }} with {{ q •• nil }}.
  - auto.
  - destruct* q.
  - destruct* p.
Qed.

(** As long as named paths are replaced with named paths, opening
    preserves the replacement relationship between types and declarations *)
Lemma repl_open_rec:
  (forall p q T T',
      repl_typ p q T T' -> forall n r,
      named_path p ->
      named_path q ->
      repl_typ p q (open_rec_typ_p n r T) (open_rec_typ_p n r T')) /\
  (forall p q D D',
      repl_dec p q D D' -> forall r n,
      named_path p ->
      named_path q ->
      repl_dec p q (open_rec_dec_p n r D) (open_rec_dec_p n r D')).
Proof.
  apply repl_mutind; intros;
    try solve [unfolds open_typ_p, open_dec_p; simpls; eauto].
  - Case "rpath"%string.
    simpl. repeat rewrite field_sel_open. repeat rewrite open_named_path; auto.
  - Case "rsngl"%string.
    simpl. repeat rewrite field_sel_open. repeat rewrite open_named_path; auto.
Qed.

(** ...for types only *)
Lemma repl_open: forall p q T T' r,
    repl_typ p q T T' ->
    named_path p ->
    named_path q ->
    repl_typ p q (open_typ_p r T) (open_typ_p r T').
Proof.
  unfold open_typ_p. intros. apply* repl_open_rec.
Qed.

(** ... for opening with variables only*)
Lemma repl_open_var: forall p q T T' x,
    repl_typ p q T T' ->
    named_path p ->
    named_path q ->
    repl_typ p q (open_typ x T) (open_typ x T').
Proof.
  introv Hr. repeat rewrite open_var_typ_eq. apply* repl_open.
Qed.

(** Equivalent types (multiple replacements) *)
Notation repl_repeat_typ p q := (star (repl_typ p q)).
Notation repl_repeat_dec p q := (star (repl_dec p q)).

(** The following lemmas construct equivalent types out of simpler equivalent types*)

(** For example, equivalent declarations yield equivalent types *)
Lemma repl_star_rcd: forall p q d1 d2,
  repl_repeat_dec p q d1 d2 ->
  repl_repeat_typ p q (typ_rcd d1) (typ_rcd d2).
Proof.
  introv Hs. dependent induction Hs. 
  apply star_refl. eapply star_trans. apply star_one.
  constructor*. eauto.
Qed.

Ltac solve_repl_star :=
  introv Hs;
  match goal with
  | [ H : repl_repeat_typ _ _ _ _ |- _ ] =>
    dependent induction H
  end;
  eauto.

(** ...and intersecting equivalent types yields equivalent types *)
Lemma repl_star_and1: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (T1 ∧ U) (T2 ∧ U).
Proof.
  solve_repl_star.
Qed.

Lemma repl_star_and2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (U ∧ T1) (U ∧ T2).
Proof.
  solve_repl_star.
Qed.

Lemma repl_star_bnd : forall T1 T2 p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (μ T1) (μ T2).
Proof.
  solve_repl_star.
Qed.

Lemma repl_star_all1: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (∀(T1) U) (∀(T2) U).
Proof.
  solve_repl_star.
Qed.

Lemma repl_star_all2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (∀(U) T1) (∀(U) T2).
Proof.
  solve_repl_star.
Qed.

Lemma repl_star_typ1: forall T1 T2 U A p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {A >: T1 <: U} {A >: T2 <: U}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  constructor*. eauto.
Qed.

Lemma repl_star_typ2: forall T1 T2 U A p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {A >: U <: T1} {A >: U <: T2}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:={A >: U <: b}). apply star_one.
  constructor*. eauto.
Qed.

Lemma repl_star_trm: forall T1 T2 a p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {a ⦂ T1} {a ⦂ T2}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  constructor*. eauto.
Qed.

(** Opening a type (or declaration) with different paths yields two equivalent types (or declarations) *)
Lemma repl_comp_open_rec:
  (forall T p q n,
      repl_repeat_typ p q (open_rec_typ_p n p T) (open_rec_typ_p n q T)) /\
  (forall D p q n,
      repl_repeat_dec p q (open_rec_dec_p n p D) (open_rec_dec_p n q D)).
Proof.
  apply typ_mutind; intros;
    simpl; try solve [apply star_refl]; eauto.
  - apply* repl_star_rcd.
  - eapply star_trans.
    apply* repl_star_and1.
    apply* repl_star_and2.
  - destruct p as [[pn | px] pbs]; destruct p0 as [p0x p0bs]; simpl.
    case_if; destruct q as [qx qbs]; subst. apply star_one. 
    repeat rewrite proj_rewrite_mult. eauto.
    apply star_refl.
    destruct q as [qx qbs]. apply star_refl.
  - apply* repl_star_bnd.
  - eapply star_trans. apply repl_star_all1. apply* H. apply repl_star_all2. apply* H0.
  - destruct p as [[pn | px] pbs]; destruct p0 as [p0x p0bs]; simpl.
    case_if; destruct q as [qx qbs]; subst. apply star_one. 
    repeat rewrite proj_rewrite_mult. eauto.
    apply star_refl.
    destruct q as [qx qbs]. apply star_refl.
  - eapply star_trans. apply repl_star_typ1. apply* H. apply repl_star_typ2. apply* H0.
  - apply* repl_star_trm.
Qed.

(** ...for types only *)
Lemma repl_comp_open: forall p q T,
    repl_repeat_typ p q (open_typ_p p T) (open_typ_p q T).
Proof.
  unfold open_typ_p. intros. apply* repl_comp_open_rec.
Qed.

(** Further properties of path replacement *)

Lemma repl_insert_mutind:
  (forall p q T U,
      repl_typ p q T U ->
      forall r, exists V, repl_typ p r T V /\ repl_typ r q V U) /\
  (forall p q T U,
      repl_dec p q T U ->
      forall r, exists V, repl_dec p r T V /\ repl_dec r q V U).
Proof.
  apply repl_mutind; intros;
  try (destruct (H r0) as [v [H0 H1]]); eauto.
Qed.

Lemma repl_insert: forall p q T U r,
    repl_typ p q T U ->
    exists V, repl_typ p r T V /\ repl_typ r q V U.
Proof.
  destruct repl_insert_mutind. eauto.
Qed.

Lemma repl_field_elim_mutind:
  (forall p q T U,
      repl_typ p q T U ->
      forall p0 q0 a,
      p = p0•a -> q = q0•a ->
      repl_typ p0 q0 T U) /\
  (forall p q T U,
      repl_dec p q T U ->
      forall p0 q0 a,
      p = p0•a -> q = q0•a ->
      repl_dec p0 q0 T U).
Proof.
  apply repl_mutind; intros; subst;
  try (subst; repeat (rewrite sel_field_to_fields));
  eauto.
Qed.

Lemma repl_field_elim : forall p q a T U,
    repl_typ p•a q•a T U ->
    repl_typ p q T U.
Proof.
  destruct repl_field_elim_mutind. eauto.
Qed.

Lemma repl_prefixes_sngl: forall p q p' q',
    repl_typ p q {{ p' }} {{ q' }} ->
    exists bs, p' = p •• bs /\ q' = q •• bs.
Proof.
  introv Hr. inversions Hr. eauto.
Qed.

Lemma repl_prefixes_sel: forall p q p' q' A,
    repl_typ p q (p' ↓ A) (q' ↓ A) ->
    exists bs, p' = p •• bs /\ q' = q •• bs.
Proof.
  introv Hr. inversions Hr. eauto.
Qed.

Lemma sel_fieldss_subst: forall x y p ds,
  subst_path x y p •• ds = (subst_path x y p) •• ds.
Proof.
  intros. destruct p. simpl.
  rewrite app_sel_fields. auto.
Qed.

Lemma repl_typ_subst_mutind:
  (forall p q T U,
    repl_typ p q T U ->
    forall x y,
    repl_typ (subst_path x y p) (subst_path x y q) (subst_typ x y T) (subst_typ x y U)) /\
  (forall p q T U,
    repl_dec p q T U ->
    forall x y,
    repl_dec (subst_path x y p) (subst_path x y q) (subst_dec x y T) (subst_dec x y U)).
Proof.
  apply repl_mutind; intros; simpl; try (constructor); eauto.
  - rewrite* sel_fieldss_subst.
    rewrite* sel_fieldss_subst.
  - rewrite* sel_fieldss_subst.
    rewrite* sel_fieldss_subst.
Qed.

Lemma repl_typ_subst: forall p q T U,
  repl_typ p q T U ->
  forall x y,
  repl_typ (subst_path x y p) (subst_path x y q) (subst_typ x y T) (subst_typ x y U).
Proof.
  destruct repl_typ_subst_mutind; eauto.
Qed.
