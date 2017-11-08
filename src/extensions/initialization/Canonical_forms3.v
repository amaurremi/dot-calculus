Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Precise_flow.
Require Import Inert_types.
Require Import General_to_tight.

Lemma sigma_binds_to_store_binds_raw: forall sto G S l T,
  wt_store G S sto ->
  binds l T S ->
  exists S1 S2,
    S = S1 & (l ~ T) & S2 /\
    exists x,
    bindsM l x sto /\
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) T.
Proof.
  introv Wt. generalize l T. induction Wt; introv Bi.
  + false* binds_empty_inv.
  + lets OkS: (wt_store_to_ok_S Wt).
    apply IHWt in Bi; clear IHWt.
    destruct Bi as [S1 [S2 [HS [v0 [HBi Hty]]]]].
    exists S1 S2.
    split. assumption.
    lets Hdec: (classicT (l1 = l0)). destruct Hdec as [Hdec | Hdec].
    - subst l1. exists x. split.
      * apply binds_update_eq.
      * assert (binds l0 T1 S) as Hbi. {
          subst S. apply binds_middle_eq.
          apply ok_middle_inv in OkS. destruct OkS as [_ Hl]. assumption.
        }
        subst S. apply binds_middle_eq_inv in H.
        subst. assumption. assumption.
    - exists v0. split.
      * apply binds_update_neq; assumption.
      * assumption.
  + lets OkS: (wt_store_to_ok_S Wt).
    lets Hdec: (classicT (l1 = l0)). destruct Hdec as [Hdec | Hdec].
    - subst l1. exists S (@empty typ).
      apply binds_push_eq_inv in Bi. subst T1.
      split.
      rewrite concat_empty_r. reflexivity.
      exists x. split.
      * apply binds_update_eq.
      * apply weaken_ty_trm_sigma.
        assumption.
        constructor; assumption.
    - apply binds_push_neq_inv in Bi; try assumption.
      destruct (IHWt l1 T1 Bi) as [S1 [S2 [HS [v0 [HBiM Hty]]]]].
      exists S1 (S2 & l0 ~ T0). split.
      subst S. rewrite concat_assoc. reflexivity.
      exists v0. split.
      apply binds_update_neq; assumption.
      apply weaken_ty_trm_sigma. assumption. constructor; assumption.
  + destruct (IHWt l0 T1 Bi) as [S1 [S2 [HS [v [HBi Hty]]]]].
    exists S1 S2. split.
    assumption.
    exists v. split. assumption. apply weaken_ty_trm_ctx.
    assumption. constructor. apply wt_store_to_ok_G in Wt. assumption. assumption.
Qed.

Lemma sigma_binds_to_store_binds_typing: forall G S sto l T,
  wt_store G S sto ->
  binds l T S ->
  exists x, bindsM l x sto /\ ty_trm ty_general sub_general G S (trm_var (avar_f x)) T.
Proof.
  introv Hwf Bi.
  lets A: (sigma_binds_to_store_binds_raw Hwf Bi).
  destruct A as [S1 [S2 [HeqG [x [Bis Hty]]]]].
  exists x. split; eauto.
Qed.

Lemma ref_binds_typ: forall G S l T,
  ty_trm ty_precise sub_general G S (trm_val (val_loc l)) (typ_ref T) ->
  binds l T S.
Proof.
  introv Hty.
  inversion Hty. assumption.
Qed.

(*
Lemma (Canonical forms 3)

If G, S ~ stack, G, S ~ store, G inert, and G, S |- x: Ref T then
  stack(x) = loc l for some address l, such that G, S |- l: Ref T, and
  there exists a value v such that
  store(l) = v and G, S |- v: T.
*)

Lemma canonical_forms_3: forall G S sta sto x T,
  inert G ->
  wf_stack G S sta ->
  wt_store G S sto ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_ref T) ->
  exists l y,
    binds x (val_loc l) sta /\
    ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T) /\
    bindsM l y sto /\
    ty_trm ty_general sub_general G S (trm_var (avar_f y)) T.
Proof.
  introv Hg Hwf Hwt Hty.
  pose proof (typing_implies_bound Hty) as [V Bi].
  pose proof (general_to_tight_typing Hg Hty) as Hty'.
  pose proof (tight_to_precise_typ_ref Hg Hty') as [T' [Hx [Hs1 Hs2]]].
  pose proof (corresponding_types Hwf Hg Bi)
    as [[L [U [W [S1 [W1 [t [Hb [Ht [Heq _]]]]]]]]] | [[U [ds [Hb [Ht Heq]]]] | [[U [U' [l [Hb [Ht [Heq [Hs1' Hs2']]]]]]] | [U [Hb [Ht Heq]]]]]].
  - assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { pose proof (inert_binds Hg Bi) as Hgt.
      induction Hgt.
      - pose proof (precise_flow_lemma Bi Hx) as H.
        apply (precise_flow_all_inv) in H.
        inversion H.
      - exists T0. auto.
      - inversion Heq. 
      - inversion Heq.
    }
    destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V.
    inversion Hsubst.
  - pose proof (inert_binds Hg Bi) as Hgt.
    induction Hgt.
    + inversion Heq.
    + pose proof (precise_flow_lemma Bi Hx) as H'.
      pose proof (precise_flow_bnd_eq_or_record H H'). 
      destruct H0 as [[U' [Heq' Hrec]] | Hrec].
      * inversion Heq'.
      * inversion Hrec. inversion H0.
    + inversion Heq.
    + inversion Heq.
  - subst. 
    pose proof (typing_implies_bound_loc Ht) as [V' Bil].
    pose proof (sigma_binds_to_store_binds_typing Hwt Bil) as [y [Bil' Htyl]].
    pose proof (precise_flow_lemma Bi Hx) as H'.
    exists l y. repeat split; try assumption.
    + apply ty_sub with (T:=typ_ref T'). 
      * apply ty_sub with (T:=typ_ref U). 
        { apply precise_to_general in Ht; auto. }
        { destruct Heq.
          - subst.
          apply precise_flow_ref_inv in H'. rewrite H'.
        apply precise_to_general in Ht; auto. }
      * pose proof (subtyp_ref Hs1 Hs2).
        apply tight_to_general in H; auto.
    + apply precise_flow_ref_inv in H'. inversion H'. subst. 
      apply ty_sub with (T:=U).
      * apply ref_binds_typ in Ht. 
        pose proof (binds_func Ht Bil). subst. assumption.
      * apply subtyp_trans with (T:=U'). 
        { assumption. }
        { apply tight_to_general in Hs1; auto. }
  - assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { pose proof (inert_binds Hg Bi) as Hgt.
      induction Hgt.
      - pose proof (precise_flow_lemma Bi Hx) as H.
        apply (precise_flow_all_inv) in H.
        inversion H.
      - exists T0. auto.
      - inversion Heq. 
    }
    destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V.
    inversion Hsubst.
Qed.
