(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas used throughout the proof. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(** [G ⊢ ds :: U]                          #<br>#
    [U] is a record type with labels [ls]  #<br>#
    [ds] are definitions with label [ls']  #<br>#
    [l \notin ls']                          #<br>#
    [―――――――――――――――――――――――――――――――――――]  #<br>#
    [l \notin ls] *)
Lemma hasnt_notin : forall G ds ls l U,
    G /- ds :: U ->
    record_typ U ls ->
    defs_hasnt ds l ->
    l \notin ls.
Proof.

  Ltac inversion_def_typ :=
    match goal with
    | [ H: _ /- _ : _ |- _ ] => inversions H
    end.

  introv Hds Hrec Hhasnt.
  inversions Hhasnt. gen ds. induction Hrec; intros; inversions Hds.
  - inversion_def_typ; simpl in *; case_if; apply* notin_singleton.
  - apply notin_union; split; simpl in *.
    + apply* IHHrec. case_if*.
    + inversion_def_typ; case_if; apply* notin_singleton.
Qed.

(** * Lemmas About Opening *)

Ltac avar_solve :=
  repeat match goal with
  | [ a: avar |- _ ] =>
    destruct a; simpl; auto; repeat case_if; subst; simpls; repeat case_if*;
    subst; simpls; repeat case_if*
  end.

(** The following [open_fresh_XYZ_injective] lemmas state that given two
    symbols (variables, types, terms, etc.) [X] and [Y] and a variable [z],
    if [z \notin fv(X)] and [z \notin fv(Y)], then [X^z = Y^z] implies [X = Y]. *)

(** - variables *)
Lemma open_fresh_avar_injective : forall x y k z,
    z \notin fv_avar x ->
    z \notin fv_avar y ->
    open_rec_avar k z x = open_rec_avar k z y ->
    x = y.
Proof.
  intros. avar_solve; inversion* H1; try (inversions H3; false* notin_same).
Qed.

(** - types and declarations *)
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
    D = D').
Proof.

  Ltac invert_open :=
    match goal with
    | [ H: open_rec_typ _ _ _ = open_rec_typ _ _ ?T' |- _ ] =>
       destruct T'; inversions* H
    | [ H: open_rec_dec _ _ _ = open_rec_dec _ _ ?D' |- _ ] =>
       destruct D'; inversions* H
    end.

  apply typ_mutind; intros; invert_open; simpl in *;
    f_equal; eauto using open_fresh_avar_injective.
Qed.

Lemma open_fresh_trm_val_def_defs_injective:
  (forall t t' k x,
      x \notin fv_trm t ->
      x \notin fv_trm t' ->
      open_rec_trm k x t = open_rec_trm k x t' ->
      t = t') /\
  (forall v v' k x,
      x \notin fv_val v ->
      x \notin fv_val v' ->
      open_rec_val k x v = open_rec_val k x v' ->
      v = v') /\
  (forall d d' k x,
      x \notin fv_def d ->
      x \notin fv_def d' ->
      open_rec_def k x d = open_rec_def k x d' ->
      d = d') /\
  (forall ds ds' k x,
      x \notin fv_defs ds ->
      x \notin fv_defs ds' ->
      open_rec_defs k x ds = open_rec_defs k x ds' ->
      ds = ds').
Proof.

  Ltac injective_solver :=
    match goal with
    | [ H: _ = open_rec_trm _ _ ?t |- _ ] =>
      destruct t; inversions H;
      try (f_equal; simpl in *);
      try apply* open_fresh_avar_injective;
        match goal with
        | [ Ho: open_rec_avar _ _ _ = open_rec_avar _ _ _ |- _ ] =>
          apply open_fresh_avar_injective in Ho; subst*
        | [ Heq: forall _ _ _, _ -> _ -> _ -> ?u = _ |- ?u = _ ] =>
          apply* Heq
        end
     | [ H: _ = open_rec_val _ _ ?v |- _ ] =>
       destruct v; inversions H; f_equal; simpl in *;
       try apply* open_fresh_typ_dec_injective; eauto
     | [ H: _ = open_rec_def _ _ ?d |- _ ] =>
       destruct d; inversions H; f_equal;
       try apply* open_fresh_typ_dec_injective; eauto
     | [ H: _ = open_rec_defs _ _ ?ds |- _ ] =>
       destruct ds; inversions H; f_equal; simpl in *; eauto
    end.

  apply trm_mutind; intros; try solve [injective_solver].
Qed.

(** The following [open_comm_XYZ] lemmas state that opening two
    symbols (variables, types, terms, etc.) at different indices commute. *)

(** - types and declarations *)
Lemma open_comm_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) =
        open_rec_typ m y (open_rec_typ n x T)) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) =
        open_rec_dec m y (open_rec_dec n x D)).
Proof.
  intros. apply typ_mutind; intros; subst*; simpl; try solve [rewrite* H; rewrite* H0].
  avar_solve.
Qed.

(** - terms, values, definitions, and lists of definitions *)
Lemma open_comm_trm_val_def_defs : forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) =
        open_rec_trm m y (open_rec_trm n x t)) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) =
        open_rec_val m y (open_rec_val n x v)) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) =
        open_rec_def m y (open_rec_def n x d)) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) =
        open_rec_defs m y (open_rec_defs n x ds)).
Proof.
  intros. apply trm_mutind; intros; subst; simpl; auto; avar_solve;
            try solve [try rewrite* H; rewrite* H0
                                       || rewrite* (proj21 (open_comm_typ_dec x y))].
Qed.

(** The following [lc_open_rec_open_XYZ] lemmas state that if opening
    a symbol (variables, types, terms, etc.) at index [n] that is
    already opened at index [m] results in the same opened symbol,
    opening the symbol itself at index [n] results in the same symbol. *)


(** - types and declarations *)
Lemma lc_open_rec_open_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) = open_rec_typ m y T ->
        open_rec_typ n x T = T) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) = open_rec_dec m y D ->
        open_rec_dec n x D = D).
Proof.
  introv. apply typ_mutind; intros; simpls; auto; avar_solve;
            try solve [(inversions H1; erewrite H; eauto)
                      || (inversions H2; erewrite H; eauto; erewrite H0; eauto)].
  - inversions H1. rewrite H with (m:=S m); auto.
  - inversions H2. erewrite H; eauto. rewrite H0 with (m:=S m); auto.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma lc_open_rec_open_trm_val_def_defs: forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) = open_rec_trm m y t ->
        open_rec_trm n x t = t) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) = open_rec_val m y v ->
        open_rec_val n x v = v) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) = open_rec_def m y d ->
        open_rec_def n x d = d) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) = open_rec_defs m y ds ->
        open_rec_defs n x ds = ds).
Proof.
  introv. apply trm_mutind; intros; simpls; auto.
  - destruct a; simpl; auto.
    case_if; simpl in *; case_if; simpl in *; auto; case_if.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H0.
    destruct a; simpl; auto.
    case_if; simpl in *; case_if; simpl in *; auto; case_if.
  - inversions H0. destruct a; destruct a0; simpl; auto; repeat case_if~; simpls; repeat case_if; simpl in *; repeat case_if~.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=S m); auto.
  - inversions H1. rewrite H with (m:=S m); auto.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=S m); auto.
  - inversions H1. rewrite H with (m:=S m); auto.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=m); auto.
  - inversions H0.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=m); auto.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=m); auto.
Qed.


(** * Lemmas About Records and Record Types *)

(** [labels(D) = labels(D^x)] *)
Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

(** [record_dec D]   #<br>#
    [――――――――――――――] #<br>#
    [record_dec D^x] *)
Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. induction H.
  - unfold open_typ. simpl.
    apply rt_one.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
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

(** The type of definitions is a record type. *)
Lemma ty_defs_record_type : forall G ds T,
    G /- ds :: T ->
    record_type T.
Proof.


 intros. induction H; destruct D;
    repeat match goal with
        | [ H: record_type _ |- _ ] =>
          destruct H
        | [ Hd: _ /- _ : dec_typ _ _ _ |- _ ] =>
          inversions Hd
        | [ Hd: _ /- _ : dec_trm _ _ |- _ ] =>
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

(** Opening does not affect the labels of a [record_type]. *)
Lemma record_type_open : forall z T,
    z \notin fv_typ T ->
    record_type (open_typ z T) ->
    record_type T.
Proof.
  introv Hz H. destruct H. dependent induction H.
  - exists \{ l }. destruct T; inversions x. constructor.
    + destruct d; inversions H.
      * apply (proj21 open_fresh_typ_dec_injective) in H3.
        { subst. constructor. }
        { simpl in Hz; auto. }
        { simpl in Hz; auto. }
      * constructor.
    + destruct d; inversions H.
      * apply (proj21 open_fresh_typ_dec_injective) in H3.
        { subst. constructor. }
        { simpl in Hz; auto. }
        { simpl in Hz; auto. }
      * constructor.
  - destruct T; inversions x. simpl in Hz.
    assert (Hz': z \notin fv_typ T1) by auto.
    destruct (IHrecord_typ T1 z Hz' eq_refl) as [ls' ?]. clear Hz'.
    destruct T2; inversions H5.
    destruct d; inversions H0.
    + exists (ls' \u \{ label_typ t }). apply (proj21 open_fresh_typ_dec_injective) in H6.
      * subst. constructor*.
        { constructor. }
        {
          simpl in H2. pose proof (opening_preserves_labels z H1 H).
          rewrite* H0.
        }
      * simpl in Hz; auto.
      * simpl in Hz; auto.
    + exists (ls' \u \{ label_trm t }). constructor*.
      * constructor.
      * simpl in H2. pose proof (opening_preserves_labels z H1 H).
        rewrite* H0.
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
  record_has T (dec_typ A T1 T1) ->
  record_has T (dec_typ A T2 T2) ->
  T1 = T2.
Proof.
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_typ A T1 T1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_typ A T2 T2) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

(** [ds = ... /\ {a = t} /\ ...]  #<br>#
    [ds = ... /\ {a = t'} /\ ...] #<br>#
    [―――――――――――――――――――――――――] #<br>#
    [t = t'] *)
Lemma defs_has_inv: forall ds a t t',
    defs_has ds (def_trm a t) ->
    defs_has ds (def_trm a t') ->
    t = t'.
Proof.
  intros. unfold defs_has in *.
  inversions H. inversions H0.
  rewrite H1 in H2. inversions H2.
  reflexivity.
Qed.

(** * Conversion into General Typing *)

(** Precise typing implies general typing. *)
Lemma precise_to_general: forall G t T,
    G ⊢! t : T ->
    G ⊢ t : T.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.

(** Tight typing implies general typing. *)
Lemma tight_to_general:
  (forall G t T,
     G ⊢# t : T ->
     G ⊢ t : T) /\
  (forall G S U,
     G ⊢# S <: U ->
     G ⊢ S <: U).
Proof.
  apply ts_mutind_t; intros; subst; eauto using precise_to_general.
Qed.

(** * Well-formedness *)

(** If [G ~~ s] and [x \notin dom(s)], then [x \notin dom(G)]. *)
Lemma wf_sto_notin_dom: forall G s x,
    G ~~ s ->
    x # s -> x # G.
Proof.
  intros. induction H; auto.
Qed.

(** If [G ~~ s], the variables in the domain of [s] are distinct. *)
Lemma wf_sto_to_ok_G: forall s G,
    G ~~ s -> ok G.
Proof.
  intros. induction H; jauto.
Qed.
Hint Resolve wf_sto_to_ok_G.

(** * Other Lemmas *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.13 in the paper. *)
Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢! trm_val v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl) as [T' [Hty Hsub]]. eauto.
Qed.

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G ⊢ trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
Qed.

Lemma var_typing_implies_avar_f: forall G a T,
  G ⊢ trm_var a : T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; eauto.
Qed.
