Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Some_lemmas.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Tight_possible_types_val.
Require Import Narrowing.

(* ###################################################################### *)
(** ** Well-formed stack *)

Lemma wf_stack_to_ok_s: forall s G S,
  wf_stack G S s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_stack_to_ok_G: forall s G S,
  wf_stack G S s -> ok G.
Proof. intros. induction H; jauto. Qed.

Lemma wf_stack_to_ok_S: forall s G S,
  wf_stack G S s -> ok S.
Proof. intros. induction H; jauto. Qed.

Lemma wt_store_to_ok_S: forall s G S,
  wt_store G S s -> ok S.
Proof.
  introv Wt. induction Wt; auto.
Qed.

Lemma wt_store_to_ok_G: forall s G S,
  wt_store G S s -> ok G.
Proof.
  introv Wt. induction Wt; auto.
Qed.

Hint Resolve wf_stack_to_ok_s wf_stack_to_ok_G wf_stack_to_ok_S wt_store_to_ok_S wt_store_to_ok_G.

Lemma wt_in_dom: forall G S sto l,
  wt_store G S sto ->
  l \in dom S ->
  index sto l.
Proof.
  introv Wt. gen l. induction Wt; intros.
  - rewrite dom_empty in H. rewrite in_empty in H. false.
  - lets Hind: (IHWt l0 H1).
    lets Hinh: (prove_Inhab x).
    pose proof (classicT (l = l0)) as [H' | H']; unfolds store, addr.
    * pose proof (indom_update sto l l0 x). 
      rewrite index_def. rewrite H2. left. rewrite H'. reflexivity. 
    * pose proof (indom_update sto l l0 x). 
      rewrite index_def. rewrite H2. right. assumption. 
  - lets Hinh: (prove_Inhab x).
    pose proof (classicT (l = l0)) as [H' | H']; unfolds store, addr.
    * rewrite index_def. rewrite indom_update. left. rewrite H'. reflexivity. assumption.
    * rewrite index_def. rewrite indom_update. right.
      assert (l0 \in dom S). {
        simpl_dom. rewrite in_union in H1. destruct H1.
        + rewrite in_singleton in H1. subst. false H'. reflexivity.
        + assumption.
      }
      lets Hin: (IHWt l0 H2). assumption. assumption.
  - apply IHWt in H0. assumption.
Qed.

Lemma wt_notin_dom: forall G S sto l,
  wt_store G S sto ->
  l # S ->
  l \notindom sto.
Proof.
  introv Wt. gen l. induction Wt; intros.
  - unfold store. rewrite LibMap.dom_empty. auto.
  - assert (l <> l0). {
      lets Hdec: (classicT (l = l0)). destruct Hdec.
      * subst. false (binds_fresh_inv H H1).
      * assumption.
    }
    assert (LibBag.dom sto[l := x] = LibBag.dom sto). {
      apply dom_update_index.
      * apply (prove_Inhab x).
      * apply binds_get in H. apply get_some_inv in H.
        lets Hind: (wt_in_dom Wt H). assumption.
    }
    unfolds addr. rewrite H3.
    apply IHWt in H1. assumption.
  - assert (l <> l0). {
      lets Hdec: (classicT (l = l0)). destruct Hdec.
      * subst. rew_env_defs. simpl in H1. apply notin_union in H1. destruct H1.
        false (notin_same H1).
      * assumption.
    }
    unfold LibBag.notin. unfold not. intro His_in.
    assert (l0 \indom sto[l := x]) as Hindom by assumption. clear His_in.
    destruct (indom_update_inv Hindom) as [Hl | Hl].
    * subst. false H2. reflexivity.
    * subst.
      assert (l0 # S) as Hl0. {
        unfolds in H1.
        intro. apply H1. simpl_dom.
        assert (l0 \notin \{l } \u (dom S)) as Hdom by auto.
        apply notin_union in Hdom. destruct Hdom.
        rewrite in_union. right. assumption.
      }
    specialize (IHWt l0 Hl0).  apply IHWt in Hl. false.
    - apply IHWt in H0. assumption.
Qed.

Lemma tpt_to_precise_rec: forall G S v T,
    tight_pt_v G S v (typ_bnd T) ->
    ty_trm ty_precise sub_general G S (trm_val v) (typ_bnd T).
Proof.
  introv Ht.
  inversions Ht. assumption.
Qed.

Lemma tpt_to_precise_lambda: forall G S v V T,
    tight_pt_v G S v (typ_all V T) ->
    inert G ->
    exists L V' T',
      ty_trm ty_precise sub_general G S (trm_val v) (typ_all V' T') /\
      subtyp sub_general G S V V' /\
      (forall y, y \notin L ->
                 subtyp sub_general (G & y ~ V) S (open_typ y T') (open_typ y T)).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) V T. split*.
  - destruct (IHHt V0 T0 eq_refl Hg) as [L' [V1 [T1 [Hp [Hvv Hvt]]]]].
    exists (L \u L' \u dom G) V1 T1. split. assumption. split. apply subtyp_trans with (T:=V0).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ V)) as Hok. {
      apply* ok_push. apply* inert_ok.
    }
    apply subtyp_trans with (T:=open_typ y T0).
    eapply narrow_subtyping. apply* Hvt. apply subenv_last. apply* tight_to_general.
    assumption. assumption.
    apply* H0.
Qed.

Lemma tpt_to_precise_loc: forall G S v T,
    tight_pt_v G S v (typ_ref T) ->
    exists T', 
      ty_trm ty_precise sub_general G S (trm_val v) (typ_ref T') /\
      subtyp sub_general G S T' T /\
      subtyp sub_general G S T T'.
Proof.
  introv Ht. dependent induction Ht.
  - exists* T. 
  - destruct (IHHt T0 eq_refl) as [T' [Hty [Hs1 Hs2]]]. exists T'. repeat split. 
    + assumption.
    + apply subtyp_trans with (T:=T0); auto.
      apply ((proj22 tight_to_general) sub_tight); auto.
    + apply subtyp_trans with (T:=T0); auto.
      apply ((proj22 tight_to_general) sub_tight); auto.
Qed.

Lemma precise_forall_inv : forall G S v V T,
    ty_trm ty_precise sub_general G S (trm_val v) (typ_all V T) ->
    exists t,
      v = val_lambda V t.
Proof.
  introv Ht. inversions Ht. exists* t.
Qed.

Lemma precise_bnd_inv : forall G S v T,
    ty_trm ty_precise sub_general G S (trm_val v) (typ_bnd T) ->
    exists ds,
      v = val_new T ds.
Proof.
  introv Ht. inversions Ht. exists* ds.
Qed.

Lemma precise_ref_inv : forall G S v T,
    ty_trm ty_precise sub_general G S (trm_val v) (typ_ref T) ->
    exists l,
      v = val_loc l.
Proof.
  introv Ht. inversions Ht. exists* l.
Qed.

Lemma precise_obj_typ : forall G S T ds U,
    ty_trm ty_precise sub_general G S (trm_val (val_new T ds)) U ->
    U = typ_bnd T.
Proof.
  introv Hp. dependent induction Hp; auto.
Qed.

Lemma precise_loc_typ : forall G S l T,
    ty_trm ty_precise sub_general G S (trm_val (val_loc l)) T ->
    exists U,
      T = typ_ref U.
Proof.
  introv Hp. dependent induction Hp. exists* T.
Qed.

Lemma tpt_obj_all : forall G S V ds T U,
    tight_pt_v G V (val_new S ds) (typ_all T U) ->
    False.
Proof.
  introv Ht. dependent induction Ht.
  apply precise_obj_typ in H. inversion H.
  apply* IHHt.
Qed.

Lemma tpt_obj_ref : forall G S V ds T,
    tight_pt_v G V (val_new S ds) (typ_ref T) ->
    False.
Proof.
  introv Ht. dependent induction Ht.
  apply precise_obj_typ in H. inversion H.
  apply* IHHt.
Qed.

Lemma corresponding_types: forall G S s x T,
  wf_stack G S s ->
  inert G ->
  binds x T G ->
  ((exists L V U V' U' t, binds x (val_lambda V t) s /\
                     ty_trm ty_precise sub_general G S (trm_val (val_lambda V t)) (typ_all V U) /\
                     T = typ_all V' U' /\
                     subtyp sub_general G S V' V /\
                     (forall y, y \notin L ->
                           subtyp sub_general (G & y ~ V') S (open_typ y U) (open_typ y U'))) \/
   (exists V ds, binds x (val_new V ds) s /\
            ty_trm ty_precise sub_general G S (trm_val (val_new V ds)) (typ_bnd V) /\
            T = typ_bnd V) \/
   (exists V V' l, binds x (val_loc l) s /\
           ty_trm ty_precise sub_general G S (trm_val (val_loc l)) (typ_ref V) /\
           T = typ_ref V' /\
           subtyp sub_general G S V V' /\
           subtyp sub_general G S V' V)).
Proof.
  introv H Hgd Bi. induction H.
  - false* binds_empty_inv.
  - assert (inert G) as Hg. {
      inversions Hgd. false* empty_push_inv. destruct (eq_push_inv H3) as [Hx [Hv HG]]. subst*.
    }
    unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * right. right. exists T0 T0 l. split.
        reflexivity. 
        split. apply* weaken_ty_trm_ctx. split*. 
      * left. exists (L \u dom G) T0 U T0 U t.
        split*. split*.
        apply* weaken_ty_trm_ctx.
      * right. left. exists T0 ds. 
        split. auto. split.
        apply* weaken_ty_trm_ctx. reflexivity.
      * apply general_to_tight_typing in H2.
        lets Hpt: (tight_possible_types_lemma_v Hg H2).
        assert (inert_typ T) as HgT. {
          inversions Hgd. false* empty_push_inv. destruct (eq_push_inv H5) as [Hx [Hv HG]]. subst*.
        }
        inversions HgT.
        { apply tpt_to_precise_lambda in Hpt. destruct Hpt as [L [V' [T' [Hss [Hs1 Hs2]]]]].
          destruct (precise_forall_inv Hss) as [t Heq]. subst. left. 
          exists (L \u dom G \u \{ x0}) V' T' S0 T1 t.
          split. apply* f_equal. split. apply* weaken_ty_trm_ctx. split. reflexivity.
          split. apply* weaken_subtyp_ctx. intros y Hy.
          apply (proj44 weaken_rules_ctx) with (G:=G & y ~ S0). apply* Hs2. reflexivity.
          apply ok_push. apply* inert_ok. simpl_dom. rewrite notin_union. split*.
          assumption.
        }
        { apply tpt_to_precise_rec in Hpt.
          destruct (precise_bnd_inv Hpt) as [ds Heq]. subst. right. left. exists T1 ds.
          split. reflexivity. split. apply* weaken_ty_trm_ctx. reflexivity.
        } 
        { apply tpt_to_precise_loc in Hpt.
          destruct Hpt as [T [Ht [Hs1 Hs2]]].
          destruct (precise_ref_inv Ht) as [l ?].
          subst. right. right. exists T T1 l. 
          split. reflexivity. split. apply* weaken_ty_trm_ctx. split. reflexivity.
          split; apply* weaken_subtyp_ctx.
        }
        assumption.
    + specialize (IHwf_stack Hg Bi).
      destruct IHwf_stack as [[L [V [U [V' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[V [ds [Hv [Ht He]]]] | [V [V' [l [Hv [Ht [He Hs]]]]]]]].
      * left. exists (L \u dom G \u \{x0}) V U V' U' t. split. assumption. split.
        apply* weaken_ty_trm_ctx.
        split. assumption. split. apply* weaken_subtyp_ctx.
        intros y Hy. apply (proj44 (weaken_rules_ctx)) with (G:=G & y ~ V'). apply* Hs2.
        reflexivity. apply ok_push. apply* inert_ok. auto.
      * right. left. exists V ds. split. assumption. split. 
        apply* weaken_ty_trm_ctx. assumption.
      * right. right. exists V V' l. split. assumption. split. apply weaken_ty_trm_ctx; auto.
        apply* inert_ok. split. assumption. split; apply* weaken_subtyp_ctx.
  - specialize (IHwf_stack Hgd Bi).
      destruct IHwf_stack as [[L [V [U [V' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[V [ds [Hv [Ht He]]]] | [V [V' [l' [Hv [Ht [He Hs]]]]]]]].
      * left. exists (L \u dom G \u \{x}) V U V' U' t. split. assumption. split.
        apply* weaken_ty_trm_sigma. split. assumption. split. apply* weaken_subtyp_sigma.
        intros y Hy. apply* weaken_subtyp_sigma.
      * right. left. exists V ds. split. assumption. split. 
        apply* weaken_ty_trm_sigma. assumption.
      * right. right. exists V V' l'. split. assumption. split. apply weaken_ty_trm_sigma; auto.
        apply* ok_push. split. assumption. split; apply* weaken_subtyp_sigma.
Qed.

Lemma stack_binds_to_ctx_binds: forall G S s x v,
  wf_stack G S s -> binds x v s -> exists V, binds x V G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  induction Hwf.
  false* binds_empty_inv.
  destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
  - exists* T.
  - destruct (IHHwf Hb Hwf) as [V HV]. exists V.
    apply* binds_push_neq.
  - auto.
Qed.

Lemma wf_stack_val_new_in_G: forall G S s x T ds,
  wf_stack G S s ->
  inert G ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Hg Bis.
  assert (exists V, binds x V G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [V Bi].
  induction Hwf.
  false* binds_empty_inv.
  assert (inert G /\ inert_typ T0) as HG. {
    inversions Hg. false* empty_push_inv. destruct (eq_push_inv H2) as [Hg [Hx Ht]].
    subst. auto.
  }
  destruct HG as [HG HT].
  destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
  - assert (T0 = typ_bnd T) as Heq. {
      apply binds_push_eq_inv in Bi. subst.
      clear IHHwf Hg Bis H H0 Hwf.
      apply general_to_tight_typing in H1; auto.
      apply tight_possible_types_lemma_v in H1; auto.
      inversions H1; try solve [inversion HT].
      * apply* precise_obj_typ.
      * false* tpt_obj_all.
      * false* tpt_obj_ref.
    }
    subst*.
  - apply binds_push_neq_inv in Bi; auto.
  - auto.
Qed.

Lemma precise_ref_subtyping: forall G S sta sto x l T,
    inert G -> 
    binds x (val_loc l) sta ->
    ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_ref T) ->
    ty_trm ty_general sub_tight G S (trm_val (val_loc l)) (typ_ref T) ->
    wf_stack G S sta ->
    wt_store G S sto ->
    exists U,
      (ty_trm ty_precise sub_general G S (trm_val (val_loc l)) (typ_ref U) /\
       subtyp sub_general G S T U /\
       subtyp sub_general G S U T).
Proof.
  introv Hg Bi Htx Htl Wf Wt.
  pose proof (tight_possible_types_lemma_v Hg Htl).
  dependent induction H.
  - exists T. split*. 
  - pose proof (subtyp_ref H1 H0) as Hs.
    pose proof (ty_sub Htx Hs) as Htx'.
    pose proof (ty_sub Htl Hs) as Htl'.
    specialize (IHtight_pt_v l T0 Hg Bi Htx' Htl' Wf Wt eq_refl eq_refl) as [U [Hx [Hs1 Hs2]]].
    pose proof (typing_implies_bound_loc Htl) as [U' Bi'].
    exists U. repeat split.
    + assumption. 
    + apply subtyp_trans with (T:=T0); auto.
      apply ((proj22 tight_to_general) sub_tight); auto.
    + apply subtyp_trans with (T:=T0); auto.
      apply ((proj22 tight_to_general) sub_tight); auto.
Qed.

Lemma val_new_typing: forall G S s x T ds,
  wf_stack G S s ->
  inert G ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise sub_general G S (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Hg Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Hg Bi) as [Hnew | [Hlambda | Hloc]].
  - destruct Hnew as [_ [V [_ [_ [_ [t [Contra _]]]]]]].
    false.
  - destruct Hlambda as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    pose proof (binds_func Bis Bis') as Heq; inversions Heq.
    assumption.
  - destruct Hloc as [V [l [Bi' [Htyp]]]].
    false.
Qed.
