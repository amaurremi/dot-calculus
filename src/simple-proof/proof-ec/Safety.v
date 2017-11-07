(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions.
Require Import RecordAndInertTypes.
Require Import Binding.
Require Import OperationalSemantics.
Require Import Weakening SubEnvironments Narrowing PreciseTypes Substitution CanonicalForms.

(** * Progress *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.15 in the paper. *)
Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢! trm_val v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl) as [T' [Hty Hsub]]. eauto.
Qed.

(** [e] and [t] are locally closed          #<br>#
    [G' ⪯ G]                                #<br>#
    inert [G']                              #<br>#
    [e: G']                                 #<br>#
    [G ⊢ t: T]                              #<br>#
    [―――――――――――――――――――――――――――――]         #<br>#
    [t] is in normal form or [e[t] |-> e[t']] *)
Lemma progress_ec: forall G' G e t T,
    lc_ec e ->
    lc_trm t ->
    G' ⪯ G ->
    inert G' ->
    well_typed G' e ->
    G ⊢ t: T ->
    ok G ->
    (normal_form t \/ exists t', e[t |-> t']).
Proof with auto.
  introv Hlce Hlc Hsenv Hig Hwt Ht Hokg. gen G' e.
  induction Ht; eauto; intros.
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    destruct (canonical_forms_fun Hig Hwt Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. repeat eexists. apply* red_apply.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hig Hwt Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. repeat eexists. apply* red_project.
  - Case "ty_let".
    destruct t.
    + SCase "t = trm_var a".
      apply narrow_typing with (G':=G') in Ht; auto.
      right.
      assert (var_typing_implies_avar_f: forall G a T, G ⊢ trm_var a : T -> exists x, a = avar_f x)
        by (introv HGat; dependent induction HGat; eauto).
      destruct (var_typing_implies_avar_f _ _ _ Ht); subst.
      exists (open_trm x u). constructor...
    + SCase "t = trm_val v".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pick_fresh x.
      destruct H0 with (x:=x) (G' := G' & x ~ T') (e := e & x ~ v); auto 2.
      * inversion Hlc. trivial. apply lc_at_to_open_trm_val_def_defs...
      * intros. eapply subenv_trans; econstructor; eauto.
      * constructor; auto. inversion Hlc. inversion H5. trivial.
      * intros. apply precise_to_general in H1.
        constructor; auto. eapply narrow_typing in H1; eauto.
      * left.
        destruct u; auto; apply open_preserve_normal_form in H3; auto.
      * right. destruct H3.
        pose proof H3. inversion Hlc. inversion H7.
        apply open_rec_eval_to_open_rec in H3; auto.
        destruct_all. subst.
        exists (trm_let (trm_val v) x1).

        apply red_let_val with (L \u dom G \u fv_ctx_types G \u dom G
                                  \u fv_ctx_types G \u dom e \u fv_ec_vals e
                                  \u fv_trm (open_trm x u) \u fv_val v \u fv_typ T
                                  \u fv_typ U \u fv_typ T' \u fv_trm x1
                                  \u dom (empty : ec) \u fv_ec_vals empty); auto.
        intros.

        replace (e & x ~ v) with (e & x ~ v & empty) in H4;
          try (rewrite <- concat_empty_r; trivial).


        replace (e & x0 ~ v) with (e & x0 ~ v & empty);
        try (rewrite <- concat_empty_r; trivial).

        assert (Hsubstv : subst_val x x0 v = v). {
          apply subst_fresh_trm_val_def_defs. auto.
        }
        rewrite <- Hsubstv.

        assert (Hleft : open_trm x0 u = subst_trm x x0 (open_trm x u)). {
          apply subst_intro_trm. auto.
        }
        rewrite Hleft.

        assert (Hright : open_trm x0 x1 = subst_trm x x0 (open_trm x x1)). {
          apply subst_intro_trm. auto.
        }
        rewrite Hright.

        replace empty with (subst_env x x0 empty); try apply map_empty; trivial.

        apply eval_renaming_subst; auto.
    + SCase "t = trm_sel a t".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwt) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_app a a0".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwt) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_let t1 t2".
      right. eexists. constructor. inversion Hlc. trivial.
Qed.

(** ** Progress Theorem
    If [⊢ t : T], then either [t] is a normal form,
    or [t]] reduces to some [t']. *)
Theorem progress: forall t T,
    lc_trm t ->
    ⊢ t: T ->
    normal_form t \/ (exists t', t |-> t').
Proof.
  intros. apply* progress_ec.
Qed.

(** * Preservation *)

(** [t] is locally closed   #<br>#
    [G' ⪯ G]                #<br>#
    [e: G']                 #<br>#
    inert [G']              #<br>#
    [G ⊢ t: T]              #<br>#
    [e[t] |-> e[t']]        #<br>#
    [ok G]                  #<br>#
    [―――――――――――――――――――]   #<br>#
    [G' ⊢ t': T]            *)
Lemma preservation_ec: forall G G' e t t' T,
    lc_trm t ->
    G' ⪯ G ->
    well_typed G' e ->
    inert G' ->
    G ⊢ t: T ->
    e[t |-> t'] ->
    ok G ->
    G' ⊢ t': T.
Proof.
  Local Hint Resolve open_bound_lc_trm.
  introv Hlc Hsenv Hwt Hi Ht Hr Hok. gen e t'. gen G'.
  induction Ht; introv Hsenv Hi Hwt Hr; try solve [inversions Hr].
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    destruct (canonical_forms_fun Hi Hwt Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hr.
    apply (binds_func H4) in Bis. inversions Bis.
    pick_fresh y. apply~ renaming_typ.
    apply (narrow_typing Ht2); auto.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hi Hwt Ht) as [S [ds [t [Bis [Has Ty]]]]].
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
           apply lc_at_to_open_trm_val_def_defs. trivial.
         }
         rewrite H3. clear H3.

         rewrite HeqbigL in H2.
         assert (x \notin L0); auto.
         specialize (H _ H3).
         assert (G' & x ~ T ⪯ G & x ~ T); auto.
         apply narrow_typing with (G' := G' & x ~ T) in H; auto.
         rewrite <- HeqbigL in H2.
         econstructor; eauto.
         intros. instantiate (1 := bigL \u \{ x }) in H6.
         subst bigL.
         assert (x0 \notin L \u dom G); auto.
         specialize (H1 _ H7).
         assert (G' & x0 ~ U0 ⊢ open_trm x0 u : U). {
           eapply narrow_typing; [eassumption |]; auto.
         }
         eapply (proj1 weaken_rules); eauto.
      -- eapply IHHt; eauto; intros.
         specialize (H0 _ H1).
         eapply narrow_typing; eauto.
    * SCase "red_let_trm".
      inversion Hlc.
      specialize (IHHt H3 Hok _ Hsenv Hi _ Hwt t'0 H6).
      eapply ty_let; eauto. intros.
      instantiate (1 := (((((((((L \u dom G) \u fv_ctx_types G) \u dom G')
                                \u fv_ctx_types G') \u dom e) \u fv_trm t) \u fv_trm u)
                            \u fv_trm t'0) \u fv_typ T) \u fv_typ U) in H7.
      assert (x \notin L); auto.
      specialize (H _ H8).
      apply (narrow_typing H); auto.
    * SCase "red_let_val".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pose proof H1 as Htt.
      apply precise_to_general in Htt.
      apply narrow_typing with (G':=G') in Htt; auto.
      pick_fresh x. assert (x \notin L); auto.
      assert (ok (G & x ~ T)); auto.
      assert (G' & x ~ T' ⪯ G & x ~ T). {
        apply subenv_trans with (G & x ~ T'); auto.
      }
      assert (inert (G' & x ~ T')) by auto.
      assert (well_typed (G' & x ~ T') (e & x ~ v)) by auto.
      assert (x \notin L0) by auto.
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

      assert (Hxyt : subst_typ x y T' = T'). {
        apply subst_fresh_typ. auto.
      }

      assert (Hopeny : subst_ctx x y (y ~ T') = y ~ T'). {
        unfold subst_ctx. rewrite map_single, Hxyt. trivial.
      }

      assert (Hopent : subst_trm x y (open_trm x t'0) = open_trm y t'0). {
        rewrite subst_open_commut_trm.
        rewrite (proj1 (subst_fresh_trm_val_def_defs _ _)); auto.
        unfold subst_fvar. case_if; auto.
      }
      rewrite HsubstU, Hopeny, Hopent in Hsubst.

      apply Hsubst; auto.
      rewrite Hxyt; auto.

  - apply narrow_typing with (G' := G') in Ht; auto.
    apply narrow_subtyping with (G' := G') in H; auto.
    eauto.
Qed.


(** ** Preservation Theorem
    If [⊢ t : T] and [t |-> t'], then [⊢ t': T]. *)
Theorem preservation: forall (t t' : trm) T,
    lc_trm t ->
    ⊢ t: T ->
    t |-> t' ->
    ⊢ t' : T.
Proof.
  intros. eapply preservation_ec; eauto.
Qed.
