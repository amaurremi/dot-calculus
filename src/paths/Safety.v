Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Narrowing.
Require Import Some_lemmas.
Require Import Canonical_forms1.
Require Import Canonical_forms2.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Invertible_typing.

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_path (p_var x))
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

Lemma avar_b_typ_false: forall G b T,
    G |- trm_path (p_var (avar_b b)): T -> False.
Proof.
  introv Ht. dependent induction Ht.
  false (IHHt _ eq_refl).
Qed.

Lemma safety: forall G s t T,
    G ~~ s ->
    inert G ->
    G |- t : T ->
        (normal_form t \/
         (exists s' t' G' G'',
             t / s ⇒ t' / s'
           /\ G' = G & G''
           /\ G' |- t' : T
           /\ G' ~~ s'
           /\ inert G')).
Proof.
  introv Hwf Hi H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 Hwf Hi H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (t |^ z) G (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=S).
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. split*.
  - (* Fld-E *) right.
    destruct p as [[b | x] | p].
    + false* avar_b_typ_false.
    + pose proof (canonical_forms_2 Hi Hwf H) as [S [ds [t [Bis [Has Ty]]]]].
      exists s t G (@empty typ). split. apply* red_sel.
      split. rewrite* concat_empty_r. split*.
    + exists s (trm_let (trm_path (p_sel p t))
                   (trm_path (p_sel (p_var (avar_b 0)) a))) G (@empty typ).
      split. apply red_path. split. rewrite* concat_empty_r. split.
      apply ty_let with (L:=dom G) (T:=typ_rcd {a [gen] T}).
      destruct* m. introv Hx.
      unfold open_trm. simpl. case_if. apply* ty_fld_elim. split*.
  - (* Let *) right.
    destruct t.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (s & x ~ v) (u |^ x) (G & x ~ T') (x ~ T').
      split.
      apply red_let. eauto.
      split. reflexivity. split. eapply narrow_typing. eapply H0. apply* subenv_last.
      apply* ok_push. split. apply* wf_sto_push. dependent induction Htyp; eauto.
      constructor*. apply* precise_inert_typ.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi']]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi']]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf Hi). destruct IHty_trm as [IH | IH]; auto. inversions IH.
      * assert (exists y, x = avar_f y) as A. {
          eapply var_typing_implies_avar_f. eassumption.
        }
        destruct A as [y A]. subst.
        exists s (u |^ y) G (@empty typ).
        split.
        apply red_let_var.
        split.
        rewrite concat_empty_r. reflexivity.
        split.
        pick_fresh z. assert (z \notin L) as FrL by auto. specialize (H0 z FrL).
        rewrite subst_intro_trm with (x:=z).
        rewrite <- subst_fresh_typ with (x:=z) (y:=y).
        eapply subst_ty_trm. eapply H0.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
        rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. split*.
      * destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi']]]]]]]].
        exists s' (trm_let t' u) G' G''.
        split. apply red_let_tgt. assumption.
        split. assumption. split.
        apply ty_let with (L:=L \u dom G') (T:=T); eauto.
        intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
        rewrite IH2.
        rewrite <- IH2. eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto.
    right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
    exists s' t' G' G''.
    split; try split; try split; try assumption.
    apply ty_sub with (T:=T).
    assumption.
    rewrite IH2. apply weaken_subtyp. assumption. subst*.
Qed.
