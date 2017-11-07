Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.

Lemma open_var_eq_p_typ_dec_path: forall x,
    (forall T : typ, forall n : nat,
          open_rec_typ n x T = open_rec_typ_p n (p_var (avar_f x)) T) /\
    (forall D : dec, forall n : nat,
          open_rec_dec n x D = open_rec_dec_p n (p_var (avar_f x)) D) /\
    (forall P : path, forall n : nat,
          open_rec_path n x P = open_rec_path_p n (p_var (avar_f x)) P).
Proof.
  intros. apply typ_mutind; unfold open_typ, open_typ_p; simpl; intros; auto;
            try solve [rewrite* H; rewrite* H0].
  unfold open_rec_avar, open_rec_avar_p. destruct a; simpl. case_if*. f_equal*.
Qed.

Lemma open_var_path_typ_eq: forall x T,
  T ||^ x = open_typ_p (p_var (avar_f x)) T.
Proof.
  intros. apply open_var_eq_p_typ_dec_path.
Qed.

Lemma open_var_path_dec_eq: forall x D,
  open_dec x D = open_dec_p (p_var (avar_f x)) D.
Proof.
  intros. apply open_var_eq_p_typ_dec_path.
Qed.

(* ###################################################################### *)
(** *** Lemmas about Record types *)

Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec_p i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record_dec_p: forall D p,
  record_dec D -> record_dec (open_dec_p p D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. rewrite open_var_path_dec_eq. apply* open_record_dec_p.
Qed.

Lemma open_record_typ_p: forall T p ls,
  record_typ T ls -> record_typ (open_typ_p p T) ls.
Proof.
  intros. induction H.
  - unfold open_typ_p. simpl.
    apply rt_one.
    apply open_record_dec_p. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec_p. assumption.
    rewrite <- open_dec_preserves_label. assumption.
Qed.

Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (T ||^ x) ls.
Proof.
  introv Hr. rewrite open_var_path_typ_eq. apply* open_record_typ_p.
Qed.

Lemma open_record_type_p: forall T p,
  record_type T -> record_type (open_typ_p p T).
Proof.
  intros. destruct H as [ls H]. exists ls. apply* open_record_typ_p.
Qed.

Lemma open_record_type: forall T x,
  record_type T -> record_type (T ||^ x).
Proof.
  introv Hr. rewrite open_var_path_typ_eq. apply* open_record_type_p.
Qed.

Lemma open_fresh_avar_injective : forall x y k z,
    z \notin fv_avar x ->
    z \notin fv_avar y ->
    open_rec_avar k z x = open_rec_avar k z y ->
    x = y.
Proof.
  intros. destruct x, y; inversion H1.
  - case_if.
    + case_if. subst. reflexivity.
    + case_if. assumption.
  - case_if. simpl in H0. inversions H3. false* notin_same.
  - case_if. simpl in H. inversions H3. false* notin_same.
  - reflexivity.
Qed.

Lemma open_fresh_typ_dec_injective:
  (forall T T' k x,
    x \notin fv_typ T ->
    x \notin fv_typ T' ->
    open_rec_typ k x T = open_rec_typ k x T' ->
    T = T') /\
  (forall D D' k x,
    x \notin fv_dec D ->
    x \notin fv_dec D' ->
    open_rec_dec k x D = open_rec_dec k x D' ->
    D = D') /\
  (forall p p' k x,
      x \notin fv_path p ->
      x \notin fv_path p' ->
      open_rec_path k x p = open_rec_path k x p' ->
      p = p').
Proof.
  apply typ_mutind; intros.
  - destruct T'; inversions H1. reflexivity.
  - destruct T'; inversions H1. reflexivity.
  - destruct T'; inversions H2. apply f_equal. apply* (H d0 k x).
  - destruct T'; inversions H3.
    assert (t = T'1). {
      apply (H T'1 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    assert (t0 = T'2). {
      apply (H0 T'2 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    subst*.
  - destruct T'; inversions H2. simpls. specialize (H _ _ _ H0 H1 H4). subst*.
  - destruct T'; inversions H2.
    apply f_equal. apply (H T' (Datatypes.S k) x).
    + simpl in H. assumption.
    + simpl in H0. assumption.
    + assumption.
  - destruct T'; inversions H3.
    assert (t = T'1). {
      apply (H T'1 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    assert (t0 = T'2). {
      apply (H0 T'2 (S k) x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    subst*.
  - destruct T'; inversions H2. specialize (H _ _ _ H0 H1 H4). subst*.
  - destruct D'; inversions H3.
    assert (t0 = t3). {
      apply (H t3 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    assert (t1 = t4). {
      apply (H0 t4 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    subst*.
  - destruct D'; inversions H2.
    apply f_equal. apply (H t2 k x).
    + simpl in H0. assumption.
    + simpl in H1. assumption.
    + assumption.
  - destruct p'; inversions H1.
    lets Hx: (open_fresh_avar_injective _ _ _ H H0 H3). subst*.
  - destruct p'; inversions H2.
    simpls. specialize (H _ _ _ H0 H1 H4). subst*.
Qed.

Lemma opening_preserves_labels : forall z T ls ls',
    record_typ T ls ->
    record_typ (open_typ z T) ls' ->
    ls = ls'.
Proof.
  introv Ht Hopen. gen ls'.
  dependent induction Ht; intros.
  - inversions Hopen. rewrite open_var_path_dec_eq.
    rewrite open_dec_preserves_label with (x:=p_var (avar_f z)) (i:=0).
    unfold open_dec_p. reflexivity.
  - inversions Hopen. rewrite open_var_path_dec_eq.
    rewrite open_dec_preserves_label with (x:=p_var (avar_f z)) (i:=0).
    specialize (IHHt ls0 H4). rewrite* IHHt.
Qed.

Lemma record_type_open : forall z T,
    z \notin fv_typ T ->
    record_type (open_typ z T) ->
    record_type T.
Proof.
  introv Hz H. destruct H. dependent induction H.
  - exists \{ l }. destruct T; inversions x. constructor.
    + destruct d; inversions H.
      * apply (proj21 open_fresh_typ_dec_injective) in H3.
        subst. constructor. simpls*. simpls*.
      * constructor.
    + destruct d; inversions H.
      * apply (proj21 open_fresh_typ_dec_injective) in H3.
        subst. constructor. simpls*. simpls*.
      * constructor.
  - destruct T; inversions x. simpl in Hz.
    assert (Hz': z \notin fv_typ T1) by auto.
    destruct (IHrecord_typ T1 z Hz' eq_refl) as [ls' ?]. clear Hz'.
    destruct T2; inversions H5.
    destruct d; inversions H0.
    + exists (ls' \u \{ label_typ t }).
      apply (proj21 open_fresh_typ_dec_injective) in H6; simpls*.
      subst. constructor*. constructor.
      simpl in H2. pose proof (opening_preserves_labels z H1 H). rewrite* H0.
    + exists (ls' \u \{ label_trm t }). constructor*. constructor.
      simpl in H2. pose proof (opening_preserves_labels z H1 H).
      rewrite* H0.
Qed.

(* ###################################################################### *)
(** *** Lemmas about Record has *)

Lemma record_typ_has_label_in: forall T D ls,
  record_typ T ls ->
  record_has T D ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Has. generalize dependent D. induction Htyp; intros.
  - inversion Has. subst. apply in_singleton_self.
  - inversion Has; subst; rewrite in_union.
    + left. apply* IHHtyp.
    + right. inversions H5. apply in_singleton_self.
Qed.

Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_has T { A >: T1 <: T1 } ->
  record_has T { A >: T2 <: T2 } ->
  T1 = T2.
Proof.
  Proof.
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:={ A >: T1 <: T1 })in Htyp.
    + inversions H9. unfold "\notin" in H1. unfold not in H1. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:={ A >: T2 <: T2 }) in Htyp.
    + inversions H5. unfold "\notin" in H1. unfold not in H1. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

Lemma unique_rcd_trm: forall T a m1 m2 U1 U2,
    record_type T ->
    record_has T { a [m1] U1 } ->
    record_has T { a [m2] U2 } ->
    m1 = m2 /\ U1 = U2.
Proof.
  introv Htype Has1 Has2.
  gen U1 U2 m1 m2 a.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:={ a [m1]  U1 }) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:={ a [m1]  U2 }) in Htyp.
    + inversions H5. false* H1.
    + inversions H5. lets Hr: (record_typ_has_label_in Htyp H9).
      false* H1.
  - inversions H5. inversions* H9.
Qed.

Lemma precise_to_path_typing: forall G p T,
    G |-! trm_path p: T ->
    G |-\||/ p: T.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma tight_to_general:
  (forall G t T,
     G |-# t : T ->
     G |- t : T) /\
  (forall G p T,
     G |-#\||/ p: T ->
     G |-\||/ p: T) /\
  (forall G S U,
     G |-# S <: U ->
     G |- S <: U).
Proof.
  apply ts_mutind_ts; intros; subst; eauto.
  - apply* subtyp_sel2. apply* precise_to_path_typing.
  - apply* subtyp_sel1. apply* precise_to_path_typing.
  - apply* subtyp_sngl_sel1. apply* precise_to_path_typing.
  - apply* subtyp_sngl_sel2. apply* precise_to_path_typing.
Qed.

Lemma typing_implies_bound: forall G x T,
  G |- trm_path (p_var (avar_f x)) : T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_path (p_var (avar_f x))) as t.
  induction H; inversion Heqt;
    try solve [apply* IHty_trm];
    try solve [apply* IHty_trm1]; subst*.
Qed.

Lemma typing_implies_bound_p: forall G x T,
  G |-! trm_path (p_var (avar_f x)) : T ->
  exists S, binds x S G.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

(* ###################################################################### *)
(** *** Misc Lemmas *)

Lemma var_typing_implies_avar_f: forall G a T,
  G |- trm_path (p_var a) : T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply* IHty_trm.
Qed.

Lemma val_typing: forall G v T,
  G |- trm_val v : T ->
  exists T', G |-! trm_val v : T' /\
             G |- T' <: T.
Proof.
  intros. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro_p with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro_p with (L:=L); eauto. apply subtyp_refl.
  - specialize (IHty_trm v eq_refl). destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

Lemma binds_destruct: forall {A} x (v:A) E,
  binds x v E ->
  exists E' E'', E = E' & x ~ v & E''.
Proof.
  introv Hb. induction E using env_ind. false* binds_empty_inv.
  destruct (binds_push_inv Hb) as [[Hx HT] | [Hn Hbx]]; subst.
  - exists E (@empty A). rewrite concat_empty_r. reflexivity.
  - apply binds_push_neq_inv in Hb. destruct (IHE Hb) as [E' [E'' HE]]. subst.
    exists E' (E'' & x0 ~ v0). rewrite concat_assoc. reflexivity. assumption.
Qed.

Lemma hasnt_notin : forall G z T ds ls t U,
    G && z ~ T |- ds :: U ->
    record_typ U ls ->
    defs_hasnt ds t ->
    t \notin ls.
Proof.
  introv Hds Hrec Hhasnt.
  inversions Hhasnt. gen ds. induction Hrec; intros.
  - inversions Hds. inversions H7; simpl in *; case_if; apply* notin_singleton.
  - apply notin_union; split.
    + inversions Hds. apply (IHHrec ds0 H5). simpl in *. case_if*.
    + inversions Hds. inversions H10; simpl in *; case_if; apply* notin_singleton.
Qed.

Lemma ty_defs_record_type : forall G z U ds T,
    G && z ~ U |- ds :: T ->
    record_type T.
Proof.
  intros.
  dependent induction H.
  - destruct D.
    + inversions H. exists \{ label_typ t }. constructor*. constructor.
    + exists \{ label_trm t }. constructor*. constructor.
  - destruct IHty_defs. destruct D.
    + unfold record_type. exists (x \u \{ label_typ t }). constructor*.
      * inversions H0. constructor.
      * inversions H0. simpl in H1. apply (hasnt_notin H H2 H1).
    + exists (x \u \{ label_trm t }). constructor*.
      * constructor.
      * inversions H0; simpl in H1; apply (hasnt_notin H H2 H1).
Qed.
