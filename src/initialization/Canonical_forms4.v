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

Lemma canonical_forms_4: forall G S sta sto x T,
  inert G ->
  wf_stack G S sta ->
  wt_store G S sto ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_nref T) ->
  ((exists l y,
       binds x (val_loc l) sta /\
       ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_nref T) /\
       bindsM l y sto /\
       ty_trm ty_general sub_general G S (trm_var (avar_f y)) T) \/ 
   (binds x val_null sta /\
    ty_trm ty_general sub_general G S (trm_val val_null) (typ_nref T))).
Proof.
  introv Hg Hwf Hwt Hty.
  pose proof (typing_implies_bound Hty) as [V Bi].
  pose proof (general_to_tight_typing Hg Hty) as Hty'.
  (* pose proof (tight_to_precise_typ_ref Hg Hty') as [T' [Hx [Hs1 Hs2]]]. *)
  pose proof (corresponding_types Hwf Hg Bi)
    as [[L [U [W [S1 [W1 [t [Hb [Ht [Heq _]]]]]]]]] | [[U [ds [Hb [Ht Heq]]]] | [[U [l [Hb [Ht Heq]]]] | [U [Hb [Ht Heq]]]]]].
  - assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { admit. (* pose proof (inert_binds Hg Bi) as Hgt. *)
      (* induction Hgt. *)
      (* - pose proof (precise_flow_lemma Bi Hx) as H. *)
      (*   apply (precise_flow_all_inv) in H. *)
      (*   inversion H. *)
      (* - exists T0. auto. *)
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
  - subst. 
    pose proof (typing_implies_bound_loc Ht) as [V Bil].
    pose proof (sigma_binds_to_store_binds_typing Hwt Bil) as [y [Bil' Htyl]].
    pose proof (precise_flow_lemma Bi Hx) as H'.
    exists l y. repeat split; try assumption.
    + apply ty_sub with (T:=typ_ref T').
      * apply precise_flow_ref_inv in H'. rewrite <- H' in Ht. 
        apply precise_to_general in Ht; auto. 
      * pose proof (subtyp_ref Hs1 Hs2).
        apply tight_to_general in H; auto.
    + apply precise_flow_ref_inv in H'. inversion H'. subst. 
      apply ty_sub with (T:=U).
      * apply ref_binds_typ in Ht. 
        pose proof (binds_func Ht Bil). subst. assumption.
      * apply tight_to_general in Hs1; auto.
  - assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { pose proof (inert_binds Hg Bi) as Hgt.
      induction Hgt.
      - pose proof (precise_flow_lemma Bi Hx) as H.
        apply (precise_flow_all_inv) in H.
        inversion H.
      - exists T0. auto.
    }
    destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V.
    inversion Hsubst.
Qed.
