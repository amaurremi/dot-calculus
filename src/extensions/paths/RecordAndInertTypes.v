(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions Binding.

(** * Record Types *)

(** ** Lemmas About Records and Record Types *)

(** [G |- ds :: U]                          #<br>#
    [U] is a record type with labels [ls]  #<br>#
    [ds] are definitions with label [ls']  #<br>#
    [l \notin ls']                          #<br>#
    [―――――――――――――――――――――――――――――――――――]  #<br>#
    [l \notin ls] *)
Lemma hasnt_notin : forall x bs P G ds ls l U,
    x; bs; P; G ⊢ ds :: U ->
    record_typ U ls ->
    defs_hasnt ds l ->
    l \notin ls.
Proof.

Lemma defs_has_open ds d p :
  defs_has ds d ->
  defs_has (open_defs_p p ds) (open_def_p p d).
Proof.
  introv Hd. gen d p; induction ds; introv Hd; introv; inversions Hd.
  case_if.
  - inversions H0. unfold open_defs_p. simpl. unfold open_def_p. unfold defs_has. simpl.
    case_if*.
  - specialize (IHds _ H0). unfold defs_has. simpl. case_if.
    * destruct d, d0; false* C.
    * apply* IHds.
Qed.

  Ltac inversion_def_typ :=
    match goal with
    | H: _; _; _; _ ⊢ _ : _ |- _ => inversions H
    end.

  introv Hds Hrec Hhasnt.
  inversions Hhasnt. gen ds. induction Hrec; intros; inversions Hds.
  - inversion_def_typ; simpl in *; case_if; apply* notin_singleton.
  - apply notin_union; split; simpl in *.
    + apply* IHHrec. case_if*.
    + inversion_def_typ; case_if; apply* notin_singleton.
Qed.

(** [labels(D) = labels(D^x)] *)
Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; reflexivity.
Qed.

Lemma open_dec_preserves_label_p: forall D p i,
  label_of_dec D = label_of_dec (open_rec_dec_p i p D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record:
  (forall D, record_dec D ->
        forall x k, record_dec (open_rec_dec k x D)) /\
  (forall T ls , record_typ T ls ->
        forall x k, record_typ (open_rec_typ k x T) ls) /\
  (forall T, inert_typ T ->
        forall x k, inert_typ (open_rec_typ k x T)).
Proof.
  apply rcd_mutind; intros; try solve [constructor; auto;
    try solve [erewrite open_dec_preserves_label in e; eauto]].
  unfold open_typ. simpl. eauto.
Qed.

Lemma open_record_p:
  (forall D, record_dec D ->
        forall p k, record_dec (open_rec_dec_p k p D)) /\
  (forall T ls , record_typ T ls ->
        forall p k, record_typ (open_rec_typ_p k p T) ls) /\
  (forall T, inert_typ T ->
        forall p k, inert_typ (open_rec_typ_p k p T)).
Proof.
  apply rcd_mutind; intros; try solve [constructor; auto;
    try solve [erewrite open_dec_preserves_label_p in e; eauto]].
  unfold open_typ. simpl. eauto.
Qed.

(** [record_dec D]   #<br>#
    [――――――――――――――] #<br>#
    [record_dec D^x] *)
Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. apply* open_record.
Qed.

Lemma open_record_dec_p: forall D x,
  record_dec D -> record_dec (open_dec_p x D).
Proof.
  intros. apply* open_record_p.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. apply* open_record.
Qed.

Lemma open_record_typ_p: forall T p ls,
  record_typ T ls -> record_typ (open_typ_p p T) ls.
Proof.
  intros. apply* open_record_p.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

Lemma open_record_type_p: forall T p,
  record_type T -> record_type (open_typ_p p T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ_p.
  eassumption.
Qed.

(** The type of definitions is a record type. *)
Lemma ty_defs_record_type : forall z bs P G ds T,
    z; bs; P; G ⊢ ds :: T ->
    record_type T.
Proof.
  intros. induction H; destruct D;
    repeat match goal with
        | [ H: record_type _ |- _ ] =>
          destruct H
        | [ Hd: _; _; _; _ ⊢ _ : { _ >: _ <: _ } |- _ ] =>
          inversions Hd
        | [ Hd: _; _; _; _ ⊢ _ : { _ ⦂ _ } |- _ ] =>
          inversions Hd
    end;
    match goal with
    | [ ls: fset label,
        t: trm_label |- _ ] =>
      exists (ls \u \{ label_trm t })
    | [ ls: fset label,
        t: typ_label |- _ ] =>
      exists (ls \u \{ label_typ t })
    | [ t: trm_label |- _ ] =>
      exists \{ label_trm t }
    | [ t: typ_label |- _ ] =>
      exists \{ label_typ t }
    end;
    constructor*; try constructor; apply (hasnt_notin H); eauto.
Qed.

(** Opening does not affect the labels of a [record_typ]. *)
Lemma opening_preserves_labels : forall z T ls ls',
    record_typ T ls ->
    record_typ (open_typ z T) ls' ->
    ls = ls'.
Proof.
  introv Ht Hopen. gen ls'.
  dependent induction Ht; intros.
  - inversions Hopen. rewrite* <- open_dec_preserves_label.
  - inversions Hopen. rewrite* <- open_dec_preserves_label.
    specialize (IHHt ls0 H4). rewrite* IHHt.
Qed.

 Ltac invert_open :=
    match goal with
    | [ H: _ = open_rec_typ _ _ ?T' |- _ ] =>
       destruct T'; inversions* H
    | [ H: _ = open_rec_dec _ _ ?D' |- _ ] =>
       destruct D'; inversions* H
    end.

Lemma record_open:
  (forall D, record_dec D ->
        forall x k D',
          x \notin fv_dec D' ->
          D = open_rec_dec k x D' ->
          record_dec D') /\
  (forall T ls , record_typ T ls ->
            forall x k T',
              x \notin fv_typ T' ->
              T = open_rec_typ k x T' ->
              record_typ T' ls) /\
  (forall T, inert_typ T ->
        forall x k T',
          x \notin fv_typ T' ->
          T = open_rec_typ k x T' ->
          inert_typ T').
Proof.
  apply rcd_mutind; intros; invert_open; simpls.
  - apply open_fresh_typ_dec_injective in H4; auto. subst. constructor.
  - destruct t0; inversions H3. eauto.
  - constructor*. rewrite* <- open_dec_preserves_label.
  - invert_open. simpls. destruct_notin. constructor*. eauto. rewrite* <- open_dec_preserves_label.
Qed.

(** If [T] is a record type with labels [ls], and [T = ... /\ D /\ ...],
    then [label(D) isin ls]. *)
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

(** [T = ... /\ {A: T1..T1} /\ ...] #<br>#
    [T = ... /\ {A: T2..T2} /\ ...] #<br>#
    [―――――――――――――――――――――――――――] #<br>#
    [T1 = T2] *)
Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_has T {A >: T1 <: T1} ->
  record_has T {A >: T2 <: T2} ->
  T1 = T2.
Proof.
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:={A >: T1 <: T1}) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:={A >: T2 <: T2}) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

Lemma unique_rcd_trm: forall T a U1 U2,
    record_type T ->
    record_has T {a ⦂ U1} ->
    record_has T {a ⦂ U2} ->
    U1 = U2.
Proof.
  introv Htype Has1 Has2.
  gen U1 U2 a.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - eapply record_typ_has_label_in with (D:={a ⦂ U1}) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:={a ⦂ U2}) in Htyp.
    + inversions H5. false* H1.
    + inversions H5. lets Hr: (record_typ_has_label_in Htyp H9).
      false* H1.
  - inversions H5. inversions* H9.
Qed.

Lemma record_has_open T a U p :
  record_has T { a ⦂ U } ->
  exists V, record_has (open_typ_p p T) { a ⦂ V }.
Proof.
  intros Hr. dependent induction Hr.
  - eexists. econstructor.
  - specialize (IHHr _ _ eq_refl) as [V Hrh]. eexists. unfold open_typ_p in *. simpl. eauto.
  - specialize (IHHr _ _ eq_refl) as [V Hrh]. eexists. unfold open_typ_p in *. simpl. eauto.
Qed.

Lemma record_has_close T a U p :
  record_has (open_typ_p p T) { a ⦂ U } ->
  exists V, record_has T { a ⦂ V }.
Proof.
  intros Hr. dependent induction Hr; destruct T; inversions x.
  - destruct d; inversions H0. eexists. econstructor.
  - specialize (IHHr _ _ _ _ eq_refl eq_refl) as [V Hrh]. eexists. unfold open_typ_p in *. simpl. eauto.
  - specialize (IHHr _ _ _ _ eq_refl eq_refl) as [V Hrh]. eexists. unfold open_typ_p in *. simpl. eauto.
Qed.

Lemma record_has_sel_typ: forall G p T a U,
    G ⊢ trm_path p : T ->
    record_has T {a ⦂ U} ->
    G ⊢ trm_path (p • a) : U.
Proof.
  introv Hp Hr. dependent induction Hr; eauto.
Qed.

Lemma inert_concat: forall G' G,
    inert G ->
    inert G' ->
    ok (G & G') ->
    inert (G & G').
Proof.
  induction G' using env_ind; introv Hg Hg' Hok.
  - rewrite* concat_empty_r.
  - rewrite concat_assoc.
    inversions Hg'; inversions Hok;
      rewrite concat_assoc in *; try solve [false* empty_push_inv].
    destruct (eq_push_inv H) as [Heq1 [Heq2 Heq3]]; subst.
    destruct (eq_push_inv H3) as [Heq1 [Heq2 Heq3]]; subst.
    eauto.
Qed.

Lemma inert_prefix_one: forall G x T,
    inert (G & x ~ T) ->
    inert G.
Proof.
  introv Hi. inversions Hi. false* empty_push_inv. lets Heq: (eq_push_inv H); destruct_all; subst*.
Qed.

Lemma inert_last G x T :
  inert (G & x ~ T) ->
  inert_typ T.
Proof.
  intros Hi. inversions Hi. false* empty_push_inv. apply eq_push_inv in H as [-> [-> _]]. auto.
Qed.

Lemma inert_prefix G G' :
  inert (G & G') ->
  inert G.
Proof.
  induction G' using env_ind; intros Hi.
  - rewrite concat_empty_r in Hi; auto.
  - rewrite concat_assoc in Hi. apply inert_prefix_one in Hi. eauto.
Qed.
