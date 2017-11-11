(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Binding.

(** The following typing relations are not part of the DOT calculus, but are used
    in the proof of DOT's safety theorems. *)

(** * Record Types *)

(** A record declaration is either a type declaration with equal bounds,
    or a field declaration.*)
Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T).

(** Given a record declaration, a [record_typ] keeps track of the declaration's
    field member labels (i.e. names of fields) and type member labels
    (i.e. names of abstract type members). [record_typ] also requires that the
    labels are distinct.  *)
Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l}).

(** A [record_type] is a [record_typ] with an unspecified set of labels. The meaning
    of [record_type] is an intersection of type/field declarations with distinct labels. *)
Definition record_type T := exists ls, record_typ T ls.

(** Given a type [T = D1 /\ D2 /\ ... /\ Dn] and member declaration [D], [record_has T D] tells whether
    [D] is contained in the intersection of [Di]'s. *)
Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

Hint Constructors record_typ record_has.

(** ** Lemmas About Records and Record Types *)

(** [G ⊢ ds :: U]                          #<br>#
    [U] is a record type with labels [ls]  #<br>#
    [ds] are definitions with label [ls']  #<br>#
    [l \notin ls']                          #<br>#
    [―――――――――――――――――――――――――――――――――――]  #<br>#
    [l \notin ls] *)
Lemma hasnt_notin : forall G S ds ls l U,
    G ⋆ S /- ds :: U ->
    record_typ U ls ->
    defs_hasnt ds l ->
    l \notin ls.
Proof.

  Ltac inversion_def_typ :=
    match goal with
    | [ H: _ ⋆ _ /- _ : _ |- _ ] => inversions H
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
  label_of_dec (open_rec_dec i x D) = label_of_dec D.
Proof.
  intros. induction D; reflexivity.
Qed.

(** [record_dec D]   #<br>#
    [――――――――――――――] #<br>#
    [record_dec D^x] *)
Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. inversion H; unfold open_dec; constructor.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  introv H.
  induction H; unfold open_typ; simpl;
    [apply rt_one | apply rt_cons];
    try apply open_record_dec ; try rewrite open_dec_preserves_label;
    assumption.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  introv [ls H]. exists ls. apply open_record_typ.
  assumption.
Qed.

(** The type of definitions is a record type. *)
Lemma ty_defs_record_type : forall G S ds T,
    G ⋆ S /- ds :: T ->
    record_type T.
Proof.


 intros. induction H; destruct D;
    repeat match goal with
        | [ H: record_type _ |- _ ] =>
          destruct H
        | [ Hd: _ ⋆ _ /- _ : dec_typ _ _ _ |- _ ] =>
          inversions Hd
        | [ Hd: _ ⋆ _ /- _ : dec_trm _ _ |- _ ] =>
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
  - inversions Hopen. rewrite* open_dec_preserves_label.
  - inversions Hopen. rewrite* open_dec_preserves_label.
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


(** * Inert types
       A type is inert if it is either a dependent function type, or a recursive type
       whose type declarations have equal bounds (enforced through [record_type]). #<br>#
       For example, the following types are inert:
       - [lambda(x: S)T]
       - [mu(x: {a: T} /\ {B: U..U})]
       - [mu(x: {C: {A: T..U}..{A: T..U}})]
       And the following types are not inert:
       - [{a: T}]
       - [{B: U..U}]
       - [top]
       - [x.A]
       - [mu(x: {B: S..T})], where [S <> T]. *)
Inductive inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (typ_all S T)
  | inert_typ_bnd : forall T,
      record_type T ->
      inert_typ (typ_bnd T)
  | inert_typ_ref : forall T, inert_typ (typ_ref T).

(** An inert context is a typing context whose range consists only of inert types. *)
Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_all : forall G x T,
      inert G ->
      inert_typ T ->
      x # G ->
      inert (G & x ~ T).

(** In the proof, it is useful to be able to distinguish record types from
    other types. A record type is a concatenation of type declarations with equal
    bounds [{A: T..T}] and field declarations [{a: T}]. *)

Hint Constructors inert_typ inert.

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
    apply inert_all; auto.
Qed.
