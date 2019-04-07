(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
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
  - Case "rpath"%string.
    simpl. repeat rewrite field_sel_open. repeat rewrite open_named_path; auto.
  - Case "rsngl"%string.
    simpl. repeat rewrite field_sel_open. repeat rewrite open_named_path; auto.
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
    repl_repeat_typ p q (T1 ∧ U) (T2 ∧ U).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_and2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (U ∧ T1) (U ∧ T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:=U ∧ b). apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_bnd : forall T1 T2 p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (μ T1) (μ T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_all1: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (∀(T1) U) (∀(T2) U).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  unfolds repl_some_typ.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_all2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (∀(U) T1) (∀(U) T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:=∀(U) b). apply star_one.
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
    case_if; destruct q as [qx qbs]; subst. apply star_one. eexists.
    repeat rewrite proj_rewrite_mult. eauto.
    apply star_refl.
    destruct q as [qx qbs]. apply star_refl.
  - apply* repl_star_bnd. unfolds repl_repeat_typ. eauto.
  - eapply star_trans. apply repl_star_all1. apply* H. apply repl_star_all2. apply* H0.
  - destruct p as [[pn | px] pbs]; destruct p0 as [p0x p0bs]; simpl.
    case_if; destruct q as [qx qbs]; subst. apply star_one. eexists.
    repeat rewrite proj_rewrite_mult. eauto.
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

Lemma repl_numpaths_relation_mutind:
  (forall n p q T U,
    repl_typ n p q T U ->
    (n < numpaths T) /\ (n < numpaths U)) /\
  (forall n p q T U,
    repl_dec n p q T U ->
    (n < numpathsD T) /\ (n < numpathsD U)).
Proof.
  apply repl_mutind; simpl; intros; omega.
Qed.

Lemma repl_numpaths_relation: forall n p q T U,
  repl_typ n p q T U ->
  (n < numpaths T) /\ (n < numpaths U).
Proof.
  destruct repl_numpaths_relation_mutind; eauto.
Qed.

Lemma repl_numpaths_equal_mutind:
  (forall n p q T U,
    repl_typ n p q T U ->
    numpaths T = numpaths U) /\
  (forall n p q T U,
    repl_dec n p q T U ->
    numpathsD T = numpathsD U).
Proof.
  apply repl_mutind; simpl; intros; omega.
Qed.

Lemma repl_numpaths_equal: forall n p q T U,
  repl_typ n p q T U ->
  numpaths T = numpaths U.
Proof.
  destruct repl_numpaths_equal_mutind; eauto.
Qed.

Lemma sel_field_to_fields: forall p a bs,
  (p • a) •• bs = p •• (bs ++ (a :: nil)).
Proof.
  intros p a bs. destruct p eqn:Hp.
  simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma sel_fields_equal: forall p bs cs,
  p •• bs = p •• cs -> bs = cs.
Proof.
  intros p bs cs H. destruct p.
  unfold sel_fields. inversions H.  simpl.
  eapply app_inv_tail. apply H1.
Qed.

Lemma app_inv_right: forall T (m n x y : list T),
  m ++ x = n ++ y ->
  exists l, x = l ++ y \/ y = l ++ x.
Proof.
  intros. generalize dependent n.
  generalize dependent x.
  generalize dependent y.
  induction m as [| a m IHm]; eauto.
  intros. destruct n.
  * exists (a :: m). right. auto.
  * inversions H. eauto.
Qed.

Lemma sel_sub_fields: forall p bs0 q bs1,
  p •• bs0 = q •• bs1 ->
  exists bs, p = q •• bs \/ q = p •• bs.
Proof.
  unfold sel_fields. intros.
  destruct p. destruct q. inversions H.
  destruct (app_inv_right bs0 bs1 f f0 H2) as [cs [H2l | H2r]];
  exists cs; subst; eauto.
Qed.
(* Lemmas End*)

Lemma repl_insert_mutind:
  (forall n p q T U,
      repl_typ n p q T U ->
      forall r, exists V, repl_typ n p r T V /\ repl_typ n r q V U) /\
  (forall n p q T U,
      repl_dec n p q T U ->
      forall r, exists V, repl_dec n p r T V /\ repl_dec n r q V U).
Proof.
  apply repl_mutind; intros;
  try (destruct (H r0) as [v [H0 H1]]); eauto.
Qed.

Lemma repl_insert: forall n p q T U r,
    repl_typ n p q T U ->
    exists V, repl_typ n p r T V /\ repl_typ n r q V U.
Proof.
  destruct repl_insert_mutind. eauto.
Qed.

Lemma repl_field_elim_mutind:
  (forall n p q T U,
      repl_typ n p q T U ->
      forall p0 q0 a,
      p = p0•a -> q = q0•a ->
      repl_typ n p0 q0 T U) /\
  (forall n p q T U,
      repl_dec n p q T U ->
      forall p0 q0 a,
      p = p0•a -> q = q0•a ->
      repl_dec n p0 q0 T U).
Proof.
  apply repl_mutind; intros; subst;
  try (subst; repeat (rewrite sel_field_to_fields));
  eauto.
Qed.

Lemma repl_field_elim : forall n p q a T U,
    repl_typ n p•a q•a T U ->
    repl_typ n p q T U.
Proof.
  destruct repl_field_elim_mutind. eauto.
Qed.

Lemma repl_unique_mutind:
  (forall n p q T T1,
      repl_typ n p q T T1 ->
      forall T2,
      repl_typ n p q T T2 ->
      T1 = T2) /\
  (forall n p q T T1,
      repl_dec n p q T T1 ->
      forall T2,
      repl_dec n p q T T2 ->
      T1 = T2).
Proof.
  apply repl_mutind; intros; try (inversions H0); simpl; eauto.
  - rewrite (H D3 H5). reflexivity.
  - rewrite (H T4 H7). reflexivity.
  - destruct (repl_numpaths_relation r). omega.
  - destruct (repl_numpaths_relation H7). omega.
  - apply f_equal.
    assert (Hn : n0 = n). { omega. }
    rewrite Hn in H7. eauto.
  - inversions H. inversions H0.
    rewrite (sel_fields_equal p bs0 bs H1). reflexivity.
  - apply f_equal. eauto.
  - replace T4 with T2; eauto.
  - destruct (repl_numpaths_relation r). omega.
  - destruct (repl_numpaths_relation H7). omega.
  - apply f_equal.
    assert (Hn : n0 = n). { omega. }
    rewrite Hn in H7. eauto.
  - inversions H. rewrite (sel_fields_equal p bs0 bs H0).
    reflexivity.
  - rewrite (H T4 H8). reflexivity.
  - destruct (repl_numpaths_relation r). omega.
  - destruct (repl_numpaths_relation H8). omega.
  - assert (Hn : n0 = n). { omega. } subst.
    rewrite (H T4 H8). reflexivity.
  - rewrite (H T4 H7). reflexivity.
Qed.

Lemma repl_unique: forall n p q T T1 T2,
    repl_typ n p q T T1 ->
    repl_typ n p q T T2 ->
    T1 = T2.
Proof.
  destruct repl_unique_mutind; eauto.
Qed.

Lemma repl_order_swap_mutind':
  (forall n p1 q1 T U,
    repl_typ n p1 q1 T U ->
    forall V m p2 q2,
    repl_typ m p2 q2 U V ->
    n <> m ->
    exists U',
    (repl_typ m p2 q2 T U') /\
    (repl_typ n p1 q1 U' V)) /\
  (forall n p1 q1 T U,
    repl_dec n p1 q1 T U ->
    forall V m p2 q2,
    repl_dec m p2 q2 U V ->
    n <> m ->
    exists U',
    (repl_dec m p2 q2 T U') /\
    (repl_dec n p1 q1 U' V)).
Proof.
  apply repl_mutind; intros; eauto.
  - inversions H0.
    destruct (H D3 m p2 q2) as [U' [Hl Hr]]; eauto.
  - inversions H0.
    * destruct (H T3 m p2 q2) as [U' [Hl Hr]]; eauto.
    * rewrite <- (repl_numpaths_equal r). eauto.
  - inversions H0.
    * rewrite (repl_numpaths_equal H8). eauto.
    * destruct (H T3 n0 p2 q2) as [U' [Hl Hr]]; eauto.
  - inversions H. destruct H0. reflexivity.
  - inversions H0.
    destruct (H T3 m p2 q2) as [U' [Hl Hr]]; eauto.
  - inversions H0.
    * destruct (H T3 m p2 q2) as [U' [Hl Hr]]; eauto.
    * rewrite <- (repl_numpaths_equal r). eauto.
  - inversions H0.
    * rewrite (repl_numpaths_equal H8). eauto.
    * destruct (H T3 n0 p2 q2) as [U' [Hl Hr]]; eauto.
  - inversions H. destruct H0. reflexivity.
  - inversions H0.
    * destruct (H T3 m p2 q2) as [U' [Hl Hr]]; eauto.
    * rewrite <- (repl_numpaths_equal r). eauto.
  - inversions H0.
    * rewrite (repl_numpaths_equal H9). eauto.
    * destruct (H T3 n0 p2 q2) as [U' [Hl Hr]]; eauto.
  - inversions H0.
    destruct (H T3 m p2 q2) as [U' [Hl Hr]]; eauto.
Qed.

Lemma repl_order_swap':
  forall n p1 q1 T U V m p2 q2,
    repl_typ n p1 q1 T U ->
    repl_typ m p2 q2 U V ->
    n <> m ->
    exists U',
    (repl_typ m p2 q2 T U') /\
    (repl_typ n p1 q1 U' V).
Proof.
  destruct repl_order_swap_mutind'; eauto.
Qed.

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
  intros.
  destruct (repl_order_swap' H H0 H1) as [W [Hl Hr]].
  rewrite <- (repl_unique H2 Hl) in Hr.
  rewrite <- (repl_unique H3 Hr).
  reflexivity.
Qed.

Lemma repl_preserved1 : forall n p q T U V m r s,
        repl_typ n p q T U ->
        repl_typ m r s U V ->
        n <> m ->
        exists V', repl_typ m r s T V'.
Proof.
  intros.
  destruct (repl_order_swap' H H0 H1) as [W [Hl Hr]].
  eauto.
Qed.

Lemma repl_preserved2_mutind:
  (forall n p q T U1,
      repl_typ n p q T U1 ->
      forall U2 m r s,
      repl_typ m r s T U2 ->
      n <> m ->
      exists V, repl_typ m r s U1 V) /\
  (forall n p q T U1,
      repl_dec n p q T U1 ->
      forall U2 m r s,
      repl_dec m r s T U2 ->
      n <> m ->
      exists V, repl_dec m r s U1 V).
Proof.
  apply repl_mutind; intros;
  eauto.
  - inversions H0. destruct (H D3 m r0 s); eauto.
  - inversions H0.
    * destruct (H T3 m r0 s); eauto.
    * rewrite (repl_numpaths_equal r). eauto.
  - inversions H0; eauto.
    destruct (H T3 n0 r0 s); eauto.
  - inversions H. destruct H0. reflexivity.
  - inversions H0. destruct (H T3 m r0 s); eauto.
  - inversions H0; eauto.
    * destruct (H T3 m r0 s); eauto.
    * rewrite (repl_numpaths_equal r). eauto.
  - inversions H0; eauto.
    destruct (H T3 n0 r0 s); eauto.
  - inversions H. destruct H0. reflexivity.
  - inversions H0.
    * destruct (H T3 m r0 s); eauto.
    * rewrite (repl_numpaths_equal r). eauto.
  - inversions H0; eauto.
    destruct (H T3 n0 r0 s); eauto.
  - inversions H0.
    destruct (H T3 m r0 s); eauto.
Qed.

Lemma repl_preserved2 : forall n p q T U1 U2 m r s,
        repl_typ n p q T U1 ->
        repl_typ m r s T U2 ->
        n <> m ->
        exists V, repl_typ m r s U1 V.
Proof.
  destruct repl_preserved2_mutind; eauto.
Qed.

Lemma repl_prefixes_sngl: forall n p q p' q',
    repl_typ n p q {{ p' }} {{ q' }} ->
    exists bs, p' = p •• bs /\ q' = q •• bs.
Proof.
  introv Hr. inversions Hr. eauto.
Qed.

Lemma repl_prefixes_sel: forall n p q p' q' A,
    repl_typ n p q (p' ↓ A) (q' ↓ A) ->
    exists bs, p' = p •• bs /\ q' = q •• bs.
Proof.
  introv Hr. inversions Hr. eauto.
Qed.

Lemma repl_prefixes_mutind:
  (forall n q1 p1 T T1,
      repl_typ n q1 p1 T T1 ->
      forall q2 p2 T2,
      repl_typ n p2 q2 T1 T2 ->
      exists bs, p1 = p2 •• bs \/ p2 = p1 •• bs) /\
  (forall n q1 p1 T T1,
      repl_dec n q1 p1 T T1 ->
      forall q2 p2 T2,
      repl_dec n p2 q2 T1 T2 ->
      exists bs, p1 = p2 •• bs \/ p2 = p1 •• bs).
Proof.
  apply repl_mutind; intros;
  try (inversions H);
  try (inversions H0);
  try (destruct (repl_numpaths_relation r));
  try (destruct (repl_numpaths_relation H7));
  try (destruct (repl_numpaths_relation H8));
  try (omega);
  eauto.
  - eapply H. assert (Hn : n0 = n). { omega. }
    rewrite Hn in H7. apply H7.
  - eapply sel_sub_fields. eauto.
  - assert (Hn : n0 = n). { omega. }
    rewrite Hn in H7. eauto.
  - eapply sel_sub_fields. eauto.
  - assert (Hn : n0 = n). { omega. }
    rewrite Hn in H8. eauto.
Qed.

Lemma repl_prefixes: forall n q1 p1 q2 p2 T T1 T2,
 repl_typ n q1 p1 T T1 ->
 repl_typ n p2 q2 T1 T2 ->
 exists bs, p1 = p2 •• bs \/ p2 = p1 •• bs.
Proof.
  destruct repl_prefixes_mutind; eauto.
Qed.

Lemma repl_intro_sngl: forall p q,
    repl_typ 0 p q {{ p }} {{ q }}.
Proof.
  intros p q.
  replace {{ p }} with {{ p •• nil }}.
  replace {{ q }} with {{ q •• nil }}.
  - auto.
  - destruct q. reflexivity.
  - destruct p. reflexivity.
Qed.

Lemma numpaths_subst_typ_mutind:
  (forall T x y,
    numpaths T = numpaths (subst_typ x y T)) /\
  (forall T x y,
    numpathsD T = numpathsD (subst_dec x y T)).
Proof.
  apply typ_mutind; intros; simpl; eauto.
Qed.

Lemma numpaths_subst_typ: forall x y T,
  numpaths (subst_typ x y T) = numpaths T.
Proof.
  destruct numpaths_subst_typ_mutind.
  eauto.
Qed.

Lemma app_sel_fields: forall p xs ys,
  (p •• xs) •• ys = p •• (ys ++ xs).
Proof.
  intros. destruct p. simpl. rewrite app_assoc.
  reflexivity.
Qed.

Lemma sel_fieldss_subst: forall x y p ds,
  subst_path x y p •• ds = (subst_path x y p) •• ds.
Proof.
  intros. destruct p. simpl.
  rewrite app_sel_fields. reflexivity.
Qed.

Lemma repl_typ_subst_mulind:
  (forall n p q T U,
    repl_typ n p q T U ->
    forall x y,
    repl_typ n (subst_path x y p) (subst_path x y q) (subst_typ x y T) (subst_typ x y U)) /\
  (forall n p q T U,
    repl_dec n p q T U ->
    forall x y,
    repl_dec n (subst_path x y p) (subst_path x y q) (subst_dec x y T) (subst_dec x y U)).
Proof.
  apply repl_mutind; intros; simpl; try (constructor); eauto.
  - erewrite <- numpaths_subst_typ. eapply rand2. eauto.
  - rewrite* sel_fieldss_subst.
    rewrite* sel_fieldss_subst.
  - erewrite <- numpaths_subst_typ. eauto.
  - rewrite* sel_fieldss_subst.
    rewrite* sel_fieldss_subst.
  - erewrite <- numpaths_subst_typ. eauto.
Qed.

Lemma repl_typ_subst: forall n p q T U,
  repl_typ n p q T U ->
  forall x y,
  repl_typ n (subst_path x y p) (subst_path x y q) (subst_typ x y T) (subst_typ x y U).
Proof.
  destruct repl_typ_subst_mulind; eauto.
Qed.
