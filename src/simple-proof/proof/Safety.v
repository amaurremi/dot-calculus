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
Require Import LocalClosure.
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


Lemma open_bound_lc_trm : forall k x t,
    rlc_trm (open_trm x t) ->
    open_rec_trm (S k) x t = t.
Proof.
  intros. 
  apply lc_at_opening with (n:=S k) (x:=x) in H.
  eapply (proj1 (lc_open_rec_open_trm_val_def_defs x _)).
  - instantiate (1 := 0). auto.
  - eassumption.
Qed.


Lemma close_rec_typ_dec_no_capture : forall x,
    (forall T k, x \notin fv_typ (close_rec_typ k x T)) /\
    (forall D k, x \notin fv_dec (close_rec_dec k x D)).
Proof.
  intros x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a
    end; simpl;
      try case_if; unfold fv_avar; auto.
Qed.


Lemma close_rec_trm_val_def_defs_no_capture: forall x,
    (forall t k, x \notin fv_trm (close_rec_trm k x t)) /\
    (forall v k, x \notin fv_val (close_rec_val k x v)) /\
    (forall d k, x \notin fv_def (close_rec_def k x d)) /\
    (forall ds k, x \notin fv_defs (close_rec_defs k x ds)).
Proof.
  intro x.
  apply trm_mutind; intros; simpl; auto;
    try apply notin_union; 
    repeat split;
    try applys close_rec_typ_dec_no_capture;
    repeat
      match goal with
      | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a; simpl
      end;
    repeat case_if; unfold fv_avar; auto.
Qed.


Lemma open_rec_eval_to_open_rec : forall e x t t' v,
    x \notin dom e \u fv_trm t \u fv_val v ->
    rlc_sto e -> rlc_val v ->
    e & x ~ v[ open_trm x t |-> t'] ->
    exists f, (x \notin (fv_trm f)) /\ t' = open_trm x f.
Proof.
  intros. exists (close_trm x t'). remember (close_trm x t') as ct. split.
  - subst ct. applys close_rec_trm_val_def_defs_no_capture.
  - symmetry. rewrite Heqct. applys open_left_inverse_close_trm_val_def_defs.
    eapply lc_env_eval_to_lc_trm.
    + apply rlc_sto_cons; eassumption.
    + eassumption.
Qed.


Lemma subenv_empty_supremum : forall G, subenv G empty.
Proof.
  unfold subenv. intros.
  unfold binds in H. rewrite get_empty in H.
  inversion H.
Qed.

Inductive indc_subenv: ctx -> ctx -> Prop :=
| new_subenv_empty : indc_subenv empty empty
| new_subenv_push: forall G G' x T T',
    indc_subenv G G' ->
    ok G ->
    ok G' ->
    x # G ->
    x # G' ->
    G ⊢ T <: T' ->
    indc_subenv (G & x ~ T) (G' & x ~ T').
Hint Constructors indc_subenv.

Lemma indc_subenv_implies_subenv : forall G1 G2,
    indc_subenv G1 G2 -> subenv G1 G2.
Proof.
  introv H. induction H.
  - apply subenv_empty_supremum.
  - unfold subenv. intros y Tb Bi. apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
    + destruct Bi. subst. right. exists T. split.
      * apply binds_push_eq.
      * apply weaken_subtyp; auto.
    + destruct Bi. unfold subenv in IHindc_subenv.
      destruct (IHindc_subenv _ _ H6).
      * left. apply binds_push_neq; trivial.
      * destruct H7 as [T1 [Hb Hs]]. right.
        exists T1. split.
        -- apply binds_push_neq; trivial.
        -- apply weaken_subtyp; auto. 
Qed.
Hint Resolve indc_subenv_implies_subenv.

Lemma indc_subenv_empty_inv : forall G, indc_subenv empty G -> G = empty.
Proof.
  intros. dependent induction H.
  - trivial.
  - renames x to H5. symmetry in H5. apply empty_push_inv in H5. contradiction.
Qed.

Lemma indc_subenv_refl : forall G, ok G -> indc_subenv G G.
Proof.
  intros G H. induction H; auto.
Qed.
Hint Resolve indc_subenv_refl.

Lemma indc_subenv_trans : forall G1 G2 G3,
    indc_subenv G1 G2 ->
    indc_subenv G2 G3 ->
    indc_subenv G1 G3.
Proof.
  introv H. gen G3. induction H; intros; auto.
  dependent induction H5.
  - apply empty_push_inv in x. contradiction.
  - rename x into He. apply eq_push_inv in He. destruct_all.
    subst.
    apply IHindc_subenv in H5.
    constructor; auto.
    apply indc_subenv_implies_subenv in H.
    apply narrow_subtyping with (G':=G) in H10; auto.
    eapply subtyp_trans; eauto.
Qed.
Hint Resolve indc_subenv_trans.

Lemma indc_subenv_push : forall G1 G2 x T,
    indc_subenv G1 G2 ->
    ok (G1 & x ~ T) -> ok (G2 & x ~ T) ->
    indc_subenv (G1 & x ~ T) (G2 & x ~ T).
Proof.
  intros. induction H; intros; auto.
  constructor; auto;
    repeat
      match goal with
      | H : empty = _ & _ |- _ => destruct (empty_push_inv H)
      | H : _ & _ ~ _ = _ & _ ~ _ & _ ~ _ |- _ => apply eq_push_inv in H; destruct_all; subst; trivial
      | H : ok (?G & ?x ~ ?T & _ ~ _) |- x # ?G & ?x ~ ?T => inversion H
      end.
Qed.
Hint Resolve indc_subenv_push.


Lemma eval_renaming_subst : forall x y e1 e2 v t1 t2,
    x \notin dom e1 ->
    y \notin dom e1 \u fv_sto_vals e1 \u fv_val v \u fv_trm t1 ->
    (e1 & x ~ v & e2)[t1 |-> t2] ->
    (e1 & y ~ subst_val x y v & e2)[subst_trm x y t1 |-> subst_trm x y t2].
Proof.
  intros. dependent induction H1.
  (* - apply binds_concat_inv in H1. *)

  (*   apply binds_push_inv in H1. rewrite subst_open_commut_trm. *)
  (*   unfold subst_fvar. simpl in *. *)
  (*   (* destruct_all. *) *)
  (*   (* case_if. case_if. subst. *) *)
  (*   (* econstructor. auto. unfold subst_val. fold subst_trm. auto. *) *)
  (*   destruct_all; repeat case_if; subst; *)
  (*     econstructor; auto; *)
  (*       try solve [unfold subst_val; fold subst_trm; auto]. *)
  (*   all: instantiate (1 := T). Focus 2. *)
    (* not enough! values in e cannot capture x! *)
Admitted.

Lemma eval_renaming: forall x y e1 v t1 t2,
    x \notin (dom e1) \u (fv_val v) \u (fv_trm t1) \u (fv_trm t2) ->
    (e1 & x ~ v)[ open_trm x t1 |-> open_trm x t2 ] ->
    y \notin (dom e1) \u (fv_val v) \u (fv_trm t1) \u (fv_trm t2) ->
    (e1 & y ~ v)[ open_trm y t1 |-> open_trm y t2 ].
Proof.
  intros. dependent induction H0; intros.
  - destruct t1; inversion x2.


Admitted.
 

Lemma progress_ec: forall G' G e t T,
    rlc_sto e ->
    rlc_trm t ->
    indc_subenv G' G ->
    inert G' ->
    G' ~~ e ->
    G ⊢ t: T ->
    ok G ->
    (normal_form t \/ exists t', e[t |-> t']).
Proof with auto.
  introv Hlce Hlc Hsenv Hig Hwf Ht Hokg. gen G' e.
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
      right. exists (open_trm x u). constructor...      
    + SCase "t = trm_val v".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pick_fresh x.
      destruct H0 with (x:=x) (G' := G' & x ~ T') (e := e & x ~ v); auto.
      * inversion Hlc. trivial. applys lc_at_to_open_trm_val_def_defs...
      * intros. eapply indc_subenv_trans; econstructor; eauto.
      * constructor; auto. inversion Hlc. inversion H5. trivial.
      * intros. apply precise_to_general in H1.
        constructor; auto. eapply narrow_typing in H1; eauto.
      * left.
        destruct u; auto; apply open_preserve_normal_form in H3; auto.
      * right. destruct H3.

        (* exists. eapply red_let_val; auto. *)
        (* intros. *)
        
        
        pose proof H3.
        apply open_rec_eval_to_open_rec in H3; auto.
        destruct_all. subst.
        eexists. eapply red_let_val; auto.
        intros.
        eapply eval_renaming with (x:=x); eauto.
        inversion Hlc. inversion H7. trivial.
    + SCase "t = trm_sel a t".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_app a a0".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_let t1 t2".
      right. eexists. constructor. inversion Hlc. trivial.
Qed.  

(** ** Progress Theorem
    If [⊢ t : T], then either [t] is a normal form,
    or [t]] reduces to some [t']. *)
Theorem progress: forall t T,
    rlc_trm t ->
    ⊢ t: T ->
    normal_form t \/ (exists t', t |-> t').
Proof.
  intros. apply* progress_ec; constructor; auto.  
Qed.

(** * Preservation *)

Lemma preservation_ec: forall G G' e t t' T,
    rlc_trm t ->
    indc_subenv G' G ->
    G' ~~ e ->
    inert G' ->
    G ⊢ t: T ->
    e[t |-> t'] ->
    ok G ->
    G' ⊢ t': T.
Proof.
  Local Hint Resolve open_bound_lc_trm.
  introv Hlc Hsenv Hwf Hi Ht Hr Hok. gen e t'. gen G'.
  induction Ht; introv Hsenv Hi Hwf Hr; try solve [inversions Hr]; eauto.
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    apply narrow_typing with (G':=G') in Ht2; auto.
    destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hr.
    apply (binds_func H4) in Bis. inversions Bis.
    pick_fresh y. apply* renaming_typ.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hi Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    inversions Hr.
    apply (binds_func H3) in Bis. inversions Bis.
    rewrite <- (defs_has_inv Has H5). assumption.
  - Case "ty_let".
    inversions Hr.
    * SCase "red_let_var".
      pick_fresh x. assert (x \notin L); auto. specialize (H x H1).
      apply subst_ty_trm with (y:=y) in H; auto.
      -- assert (subst_typ x y U = U). {
           apply subst_fresh_typ_dec. auto.
         }
         rewrite H2 in H.
         assert (open_trm y u = subst_trm x y (open_trm x u)). {
           apply subst_intro_trm. auto.
         }
         rewrite <- H3 in H.
         apply narrow_typing with (G':=G') in H; auto.
      -- assert (subst_typ x y T = T). {
           apply subst_fresh_typ_dec. auto.
         }
         rewrite H2. trivial.
    * SCase "red_let_let".
      clear H0 IHHt.
      assert (forall x, x \notin (L \u dom G) -> G & x ~ T ⊢ open_trm x u : U). {
        intros. assert (x \notin L); auto.
      }
      clear H.
      dependent induction Ht.
      -- apply narrow_typing with (G' := G') in Ht; eauto.
         remember ((((((((((((L \u L0) \u dom G) \u fv_ctx_types G) \u dom G')
                            \u fv_ctx_types G') \u dom e) \u fv_trm u) \u fv_trm s)
                        \u fv_trm t0) \u fv_typ U) \u fv_typ T) \u fv_typ U0) as bigL.
         econstructor; eauto. intros.
         instantiate (1 := bigL) in H2.
         unfold open_trm, open_rec_trm. fold open_rec_trm.

         assert (open_rec_trm 1 x u = u). {
           inversion H5. apply open_bound_lc_trm.
           applys lc_at_to_open_trm_val_def_defs. trivial.
         }
         rewrite H3. clear H3.
         
         rewrite HeqbigL in H2.
         assert (x \notin L0); auto.
         specialize (H _ H3). 
         assert (subenv (G' & x ~ T) (G & x ~ T)). {
           apply subenv_push; auto.
         }
         apply narrow_typing with (G' := G' & x ~ T) in H; auto.
         rewrite <- HeqbigL in H2.         
         econstructor; eauto.
         intros. instantiate (1 := bigL \u \{ x }) in H6.
         subst bigL.
         assert (x0 \notin L \u dom G); auto.
         specialize (H1 _ H7).
         assert (G' & x0 ~ U0 ⊢ open_trm x0 u : U). {
           eapply narrow_typing; [eassumption | |]; auto.
         }
         eapply (proj1 weaken_rules); eauto.
      -- eapply IHHt; eauto; intros.
         specialize (H0 _ H1).
         eapply narrow_typing; eauto.
    * SCase "red_let_trm".
      inversion Hlc.
      specialize (IHHt H3 Hok _ Hsenv Hi _ Hwf t'0 H6).
      eapply ty_let; eauto. intros.
      instantiate (1 := (((((((((L \u dom G) \u fv_ctx_types G) \u dom G')
                                \u fv_ctx_types G') \u dom e) \u fv_trm t) \u fv_trm u)
                            \u fv_trm t'0) \u fv_typ T) \u fv_typ U) in H7.
      assert (x \notin L); auto.
      specialize (H _ H8).
      apply narrow_typing with (G':=G' & x ~ T) in H; auto.
    * SCase "red_let_val".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pose proof H1 as Htt.
      apply precise_to_general in Htt.
      apply narrow_typing with (G':=G') in Htt; auto.
      pick_fresh x. assert (x \notin L); auto.
      assert (ok (G & x ~ T)); auto.
      assert (indc_subenv (G' & x ~ T') (G & x ~ T)). {
        apply indc_subenv_trans with (G & x ~ T'); auto. }
      assert (inert (G' & x ~ T')); auto.
      assert (G' & x ~ T' ~~ e & x ~ v). {
        constructor; auto.
      }
      assert (x \notin L0); auto.
      inversion Hlc.
      
      apply (proj1 (lc_at_to_open_trm_val_def_defs x)) in H14.
      specialize (H0 _ H3 H14 H5 (G' & x ~ T') H7 H8 (e & x ~ v) H9 _ (H6 _ H10)).
      apply_fresh ty_let as y; eauto.

      apply weaken_ty_trm with (G2:=(y ~ T')) in H0; auto.
      
      pose proof (proj1 (subst_rules y T')) as Hsubst.
      specialize (Hsubst _ _ _ H0 G' (y ~ T') x).
      assert (HsubstU : subst_typ x y U = U). {
        apply subst_fresh_typ. auto.
      }
      rewrite HsubstU in Hsubst.

      assert (Hxyt : subst_typ x y T' = T'). {
        apply subst_fresh_typ. auto.
      }
      
      assert (Hopeny : subst_ctx x y (y ~ T') = y ~ T'). {
        unfold subst_ctx. rewrite map_single. rewrite Hxyt. trivial.
      }
      rewrite* Hopeny in Hsubst.

      assert (Hopent : subst_trm x y (open_trm x t'0) = open_trm y t'0). {
        rewrite subst_open_commut_trm.
        rewrite (proj1 (subst_fresh_trm_val_def_defs _ _)); auto.
        unfold subst_fvar. case_if; auto.
      }
      rewrite Hopent in Hsubst.

      apply Hsubst; auto.
      rewrite Hxyt. auto.
      
  - apply narrow_typing with (G' := G') in Ht; auto.
    apply narrow_subtyping with (G' := G') in H; auto.
    eapply ty_sub; eauto.
Qed.

  
(** ** Preservation Theorem
    If [⊢ t : T] and [t |-> t'], then [⊢ t': T]. *)
Theorem preservation: forall (t t' : trm) T,
    rlc_trm t ->
    ⊢ t: T ->
    t |-> t' ->
    ⊢ t' : T.
Proof.
  intros. eapply preservation_ec; eauto. constructor.
Qed.
