(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions.
Require Import Operational_semantics.
Require Import Weakening Narrowing Helper_lemmas Precise_types Substitution Canonical_forms.

(** Reduction in an empty context *)
Notation "t '|->' u" := (empty [t |-> u]) (at level 50).

(** Typing in an empty context *)
Notation "'|-' t ':' T" := (empty |- t: T) (at level 40, t at level 59).

(** * Progress *)

Lemma val_typing_inert: forall G v T,
    inert G ->
    G |- trm_val v: T ->
    inert_typ T.
Proof.
  introv Hi Hv. dependent induction Hv; auto.
  - pick_fresh y. assert (y \notin L) as Hy by auto. specialize (H y Hy).
    Admitted.

(** todo: doc*)
Lemma progress_ec: forall G e t T,
    G ~~ e ->
    inert G ->
    G |- t: T ->
    (normal_form t \/ exists t', e[t |-> t']).
Proof.
  introv Hwf Hi Ht. gen e. induction Ht; eauto; intros.
  - Case "ty_all_elim".
    destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. repeat eexists. apply* red_apply.
  - Case "ty_new_elim".
    destruct (canonical_forms_obj Hi Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. repeat eexists. apply* red_project.
  - Case "ty_let".
    destruct t.
    * SCase "t = trm_var a".
      destruct (var_typing_implies_avar_f Ht); subst.
      right. exists (open_trm x u). constructor.
    * SCase "t = trm_val v".
      destruct (val_typing Ht) as [T' [Htp Hs]].
      pick_fresh y. assert (y \notin L) as Hy by auto.
      admit.
    * SCase "t = trm_sel a t".
      right. destruct (IHHt Hi e Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    * SCase "t = trm_app a a0".
      right. destruct (IHHt Hi e Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    * SCase "t = trm_let t1 t2".
      right. eexists. constructor.
Qed.

(** ** Progress Theorem
    If [|- t : T], then either [t] is a normal form,
    or [t]] reduces to some [t']. *)
Theorem progress: forall t T,
    |- t: T ->
    normal_form t \/ (exists t', t |-> t').
Proof.
  intros. apply* progress_ec. constructor.
Qed.

(** * Preservation *)

Lemma preservation_ec: forall G e t t' T,
  G ~~ e ->
  inert G ->
  G |- t: T ->
  e[t |-> t'] ->
  G |- t': T.
Proof.
  introv Hwf Hi Ht Hr. gen e. induction Ht; introv Hwf Hr; try solve [inversions Hr]; eauto.
  - Case "ty_all_elim".
    destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hr.
    apply (binds_func H3) in Bis. inversions Bis.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y); auto.
    rewrite subst_intro_trm with (x:=y); auto.
    eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
  - Case "ty_new_elim".
    destruct (canonical_forms_obj Hi Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    inversions Hr.
    apply (binds_func H2) in Bis. inversions Bis.
    rewrite <- (defs_has_inv Has H4). assumption.
  - Case "ty_let".
    inversions Hr.
    * SCase "red_let_var".
      pick_fresh z. assert (z \notin L) as FrL by auto. specialize (H0 z FrL).
      admit.
    * SCase "red_let_let".
      admit.
    * SCase "red_let_trm".
      admit.
    * SCase "red_let_val".
      admit.
Qed.

(** ** Preservation Theorem
    If [|- t : T] and [t |-> t'], then [|- t': T]. *)
Theorem preservation: forall (t t' : trm) T,
  |- t: T ->
  t |-> t' ->
  |- t' : T.
Proof.
  intros. apply* preservation_ec. constructor.
Qed.
