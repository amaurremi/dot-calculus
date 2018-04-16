(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Sequences.
Require Import Definitions Binding.

(** * Lemmas about Replacement *)

Lemma repl_swap:
  (forall n p q T T',
      repl_typ n p q T T' ->
      repl_typ n q p T' T) /\
  (forall n p q D D',
      repl_dec n p q D D' ->
      repl_dec n q p D' D).
Proof.
  apply repl_mutind; intros; eauto.
Qed.

Lemma numpaths_open:
  (forall U n p,
      numpaths U = numpaths (open_rec_typ_p n p U)) /\
  (forall D n p,
      numpathsD D = numpathsD (open_rec_dec_p n p D)).
Proof.
  apply typ_mutind; intros; simpl; eauto.
Qed.

Lemma repl_open_rec:
  (forall m p q T T',
      repl_typ m p q T T' -> forall r n,
      named_path p ->
      named_path q ->
      repl_typ m p q (open_rec_typ_p n r T) (open_rec_typ_p n r T')) /\
  (forall m p q D D',
      repl_dec m p q D D' -> forall r n,
      named_path p ->
      named_path q ->
      repl_dec m p q (open_rec_dec_p n r D) (open_rec_dec_p n r D')).
Proof.
  apply repl_mutind; intros;
    try solve [unfolds open_typ_p, open_dec_p; simpls; eauto];
    try solve [simpl; assert (numpaths U = numpaths (open_rec_typ_p n0 r0 U))
                 as Hn by apply* numpaths_open;
               rewrite* Hn].
  - Case "rpath".
    subst. inversions H. destruct H1 as [bs' Heq]. inversions Heq.
    inversions H0. destruct H as [bs'' Heq]. inversions Heq. simpl. destruct r.
    apply* rpath.
  - Case "rsngl".
    subst. inversions H. destruct H1 as [bs' Heq]. inversions Heq.
    inversions H0. destruct H as [bs'' Heq]. inversions Heq. simpl. destruct r.
    apply* rsngl.
Qed.

Lemma repl_open: forall p q T T' r n,
    repl_typ n p q T T' ->
    named_path p ->
    named_path q ->
    repl_typ n p q (open_typ_p r T) (open_typ_p r T').
Proof.
  unfold open_typ_p. intros. apply* repl_open_rec.
Qed.

Lemma repl_open_var: forall n p q T T' x,
    repl_typ n p q T T' ->
    named_path p ->
    named_path q ->
    repl_typ n p q (open_typ x T) (open_typ x T').
Proof.
  introv Hr. repeat rewrite open_var_typ_eq. apply* repl_open.
Qed.

Definition repl_some_typ p q T T' := exists n, repl_typ n p q T T'.
Definition repl_some_dec p q D D' := exists n, repl_dec n p q D D'.

Definition repl_repeat_typ p q := star (repl_some_typ p q).
Definition repl_repeat_dec p q := star (repl_some_dec p q).

Lemma repl_star_rcd: forall p q d1 d2,
  repl_repeat_dec p q d1 d2 ->
  repl_repeat_typ p q (typ_rcd d1) (typ_rcd d2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_dec.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_and1: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_and T1 U) (typ_and T2 U).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_and2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_and U T1) (typ_and U T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:=typ_and U b). apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_bnd : forall T1 T2 p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_bnd T1) (typ_bnd T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_all1: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_all T1 U) (typ_all T2 U).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_all2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_all U T1) (typ_all U T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:=typ_all U b). apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_typ1: forall T1 T2 U A p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {A >: T1 <: U} {A >: T2 <: U}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_typ2: forall T1 T2 U A p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {A >: U <: T1} {A >: U <: T2}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:={A >: U <: b}). apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_trm: forall T1 T2 a p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {a ⦂ T1} {a ⦂ T2}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_comp_open_rec:
  (forall T p q n,
      repl_repeat_typ p q (open_rec_typ_p n p T) (open_rec_typ_p n q T)) /\
  (forall D p q n,
      repl_repeat_dec p q (open_rec_dec_p n p D) (open_rec_dec_p n q D)).
Proof.
  apply typ_mutind; intros; unfolds repl_repeat_typ, repl_repeat_dec;
    simpl; try solve [apply star_refl]; eauto.
  - apply* repl_star_rcd. unfold repl_repeat_dec. eauto.
  - eapply star_trans.
    apply* repl_star_and1. apply* H.
    apply* repl_star_and2. apply* H0.
  - destruct p as [[pn | px] pbs]; destruct p0 as [p0x p0bs]; simpl.
    case_if; destruct q as [qx qbs]; subst. apply star_one. eexists. eauto.
    apply star_refl.
    destruct q as [qx qbs]. apply star_refl.
  - apply* repl_star_bnd. unfolds repl_repeat_typ. eauto.
  - eapply star_trans. apply repl_star_all1. apply* H. apply repl_star_all2. apply* H0.
  - destruct p as [[pn | px] pbs]; destruct p0 as [p0x p0bs]; simpl.
    case_if; destruct q as [qx qbs]; subst. apply star_one. eexists. eauto.
    apply star_refl.
    destruct q as [qx qbs]. apply star_refl.
  - eapply star_trans. apply repl_star_typ1. apply* H. apply repl_star_typ2. apply* H0.
  - apply* repl_star_trm. unfolds repl_repeat_typ. eauto.
Qed.

Lemma repl_comp_open: forall p q T,
    repl_repeat_typ p q (open_typ_p p T) (open_typ_p q T).
Proof.
  unfold open_typ_p. intros. apply* repl_comp_open_rec.
Qed.

Fixpoint ith_path T i : option path :=
  match T with
  | typ_rcd D =>
    ith_path_dec D i
  | typ_and T1 T2 =>
    let n := numpaths T1 in
    If i < n then ith_path T1 i else ith_path T2 (n - i)
  | typ_path p _ =>
    match i with
    | 0 => Some p
    | _ => None
    end
  | typ_bnd T =>
    ith_path T i
  | typ_all T U =>
    let n := numpaths T in
    If i < n then ith_path T i else ith_path U (n - i)
  | typ_sngl p =>
    match i with
    | 0 => Some p
    | _ => None
    end
  | _ => None
  end
with ith_path_dec D i :=
  match D with
  | { _ >: T <: U } =>
    let n := numpaths T in
    If i < n then ith_path T i else ith_path U (n - i)
  | { _ ⦂ T } =>
    ith_path T i
  end.

Notation "T '⚬' i" := (ith_path T i) (at level 50).

Lemma repl_insert: forall n p q T U r,
    repl_typ n p q T U ->
    exists V, repl_typ n p r T V /\ repl_typ n r q V U.
Proof.
  introv Hr. Admitted.

Lemma repl_field_elim : forall n p q a T U,
    repl_typ n p•a q•a T U ->
    repl_typ n p q T U.
Proof. Admitted.

(* if n <> m then
   T[q1 / p1,n][q2 / p2,m] = T[q2 / p2,m][q1 / p1,n] *)
Lemma repl_order_swap: forall n p1 q1 T U V m p2 q2 U' V',
    repl_typ n p1 q1 T U ->
    repl_typ m p2 q2 U V ->
    n <> m ->
    repl_typ m p2 q2 T U' ->
    repl_typ n p1 q1 U' V' ->
    V = V'.
Proof.
  Admitted.

Lemma repl_preserved1 : forall n p q T U V m r s,
        repl_typ n p q T U ->
        repl_typ m r s U V ->
        n <> m ->
        exists V', repl_typ m r s T V'.
Proof.
Admitted.

Lemma repl_preserved2 : forall n p q T U1 U2 m r s,
        repl_typ n p q T U1 ->
        repl_typ m r s T U2 ->
        n <> m ->
        exists V, repl_typ m r s U1 V.
Proof.
  Admitted.
