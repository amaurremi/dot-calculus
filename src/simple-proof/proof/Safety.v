(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
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
Notation "'⊢' t ':' T" := (empty ⊢ t: T) (at level 40, t at level 59).

(** * Progress *)

Lemma open_rec_preserve_normal_form: forall k x t,
    x \notin fv_trm t ->
    normal_form (open_rec_trm k x t) ->
    normal_form t.
Proof.
  intros. generalize dependent x.
  generalize dependent k.
  induction t; auto; intros;
    try (solve [
    unfold open_trm in H0; unfold open_rec_trm in H0;
    inversion H0]).
  unfold open_trm in H0. unfold open_rec_trm in H0.  
  inversion H0. fold open_rec_trm in *.
  unfold fv_trm in H. fold fv_trm in H.
  assert (x \notin fv_trm t2); auto.
  specialize (IHt2 _ _ H4 H2).

  destruct t1; simpl; inversion H1.
  constructor. auto.
Qed.

Corollary open_preserve_normal_form : forall x t,
    x \notin fv_trm t ->
    normal_form (open_trm x t) ->
    normal_form t.
Proof. apply open_rec_preserve_normal_form. Qed.


(* terms in opened definitions must be opened terms *)
Lemma open_rec_defs_has_open_rec_trm: forall k x ds a t',
    defs_has (open_rec_defs k x ds) (def_trm a t') ->
    exists f, t' = open_rec_trm k x f.
Proof with auto.
  intros k x ds. generalize dependent k. generalize dependent x.
  induction ds; intros; simpl in *.
  - inversion H.
  - unfold defs_has in H. unfold get_def in *. fold get_def in H.
    case_if.
    + inversion H. destruct d; simpl in *; inversion H1.
      exists t0...
    + specialize (IHds x k a t'). unfold defs_has in IHds.
      apply IHds...
Qed.


Lemma open_rec_eval_to_open_rec : forall k e x t t' L,
  x \notin L ->
  e[ open_rec_trm k x t |-> t'] ->
  exists f, (x \notin (fv_trm f)) /\ t' = open_rec_trm k x f.
Proof.
  intros. generalize dependent k.
  generalize dependent e. generalize dependent x.
  generalize dependent t'. generalize dependent L.
  induction t; intros; try (solve [inversion H0]).
Admitted.

Lemma empty_is_top : forall G, subenv G empty.
Proof.
  unfold subenv. intros.
  unfold binds in H. rewrite get_empty in H.
  inversion H.
Qed.

(* Lemma empty_env_inv : forall G, subenv empty G -> G = empty. *)
(* Proof. *)
(*   intros. unfold subenv in *. induction G using env_ind. *)
(*   trivial. *)
(*   unfold subenv2 in *. *)

(* Lemma empty_subenv_inv : forall G, subenv empty G -> G = empty. *)
(* Proof. *)
(*   intros. induction G using env_ind. *)
  
Lemma subenv_trans : forall G1 G2 G3,
    subenv G1 G2 -> subenv G2 G3 -> subenv G1 G3.
Proof.
  induction G1 using env_ind; intros.
  - unfold subenv in *. intros.
    destruct (H x T2); auto.
    destruct (H0 x T2); auto.
    destruct H2 as [T1 [Hb1 Hsub]].
Admitted.
(* Qed. *)


Lemma tryit: forall x y e t t1 t2,
    x \notin (dom e) \u (fv_val t) \u (fv_trm t1) \u (fv_trm t2) ->
    (e & x ~ t)[ open_trm x t1 |-> open_trm x t2 ] ->
    y \notin (dom e) \u (fv_val t) \u (fv_trm t1) \u (fv_trm t2) ->
    (e & y ~ t)[ open_trm y t1 |-> open_trm y t2 ].
Proof. Admitted.

Lemma progress_ec: forall G' G e t T,
    subenv G' G ->
    inert G' ->
    G' ~~ e ->
    G ⊢ t: T ->
    (normal_form t \/ exists t', e[t |-> t']).
Proof.
  introv Hsenv Hig Hwf Ht. gen G' e.
  induction Ht; eauto; intros.
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    destruct (canonical_forms_fun Hig Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. repeat eexists. apply* red_apply.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hig Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. repeat eexists. apply* red_project.
  - Case "ty_let".
    destruct t.
    + SCase "t = trm_var a".
      apply narrow_typing with (G':=G') in Ht; auto.
      destruct (var_typing_implies_avar_f Ht); subst.
      right. exists (open_trm x u). constructor.
    + apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pick_fresh x.
      destruct H0 with (x:=x) (G' := G' & x ~ T') (e := e & x ~ v); auto.
      * admit.
      * apply precise_to_general in H1.
        constructor; auto. eapply narrow_typing in H1; eauto.
      * left.
        destruct u; auto; apply open_preserve_normal_form in H3; auto.
      * right. destruct H3.
        pose proof H3.
        apply (open_rec_eval_to_open_rec _ _ Fr) in H3.
        destruct H3. destruct H3. subst.
        eexists. eapply red_let_val.
        intros. 
        eapply tryit with (x:=x); eauto.
    + SCase "t = trm_sel a t".
      right. destruct (IHHt G' Hsenv Hig e Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_app a a0".
      right. destruct (IHHt G' Hsenv Hig e Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_let t1 t2".
      right. eexists. constructor.
Qed.  


(** ** Progress Theorem
    If [⊢ t : T], then either [t] is a normal form,
    or [t]] reduces to some [t']. *)
Theorem progress: forall t T,
    ⊢ t: T ->
    normal_form t \/ (exists t', t |-> t').
Proof.
  intros. apply* progress_ec; constructor; auto.  
Qed.

(** * Preservation *)

Lemma preservation_ec: forall G e t t' T,
  G ~~ e ->
  inert G ->
  G ⊢ t: T ->
  e[t |-> t'] ->
  G ⊢ t': T.
Proof.
  introv Hwf Hi Ht Hr. gen e. induction Ht; introv Hwf Hr; try solve [inversions Hr]; eauto.
  - Case "ty_all_elim".
    destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hr.
    apply (binds_func H3) in Bis. inversions Bis.
    pick_fresh y. apply* renaming_typ.
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
    If [⊢ t : T] and [t |-> t'], then [⊢ t': T]. *)
Theorem preservation: forall (t t' : trm) T,
  ⊢ t: T ->
  t |-> t' ->
  ⊢ t' : T.
Proof.
  intros. apply* preservation_ec. constructor.
Qed.
