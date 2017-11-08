Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Some_lemmas.
Require Import Precise_flow.

(* ###################################################################### *)
(** ** Inert types *)

(* Definition (Inert types)

A type is inert if it of the form
  all(x: S)T
  rec(x: T), where T is a record type
 *)

Inductive inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (typ_all S T) (* all(x: S)T *)
  | inert_typ_bnd : forall T,
      record_type T ->
      inert_typ (typ_bnd T) (* rec(x:T) *)
  | inert_typ_ref : forall T, inert_typ (typ_ref T).

(* Definition (Inert context)

A context is inert if it is of the form
  {}
  G, x : T where G is a inert context and T is a inert type *)

Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_all : forall pre x T,
      inert pre ->
      inert_typ T ->
      x # pre ->
      inert (pre & x ~ T).

(* Inert contexts bind inert:
If G |- x : T and G is a inert context then T is a inert type. *)

Lemma binds_inert : forall G x T,
    binds x T G ->
    inert G ->
    inert_typ T.
Proof.
  introv Bi Hinert. induction Hinert.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H1. subst. assumption.
    + destruct H1. apply (IHHinert H2).
Qed.

Lemma inert_binds : forall G x T,
    inert G ->
    binds x T G ->
    inert_typ T.
Proof.
  introv Bi Hgd.
  eapply binds_inert; eauto.
Qed.

Lemma inert_typ_bnd_record : forall G x T,
    inert G ->
    binds x (typ_bnd T) G ->
    record_type T.
Proof.
  introv Bi Hgd.
  pose proof (inert_binds Bi Hgd).
  dependent induction H.
  assumption.
Qed.

Lemma inert_unique_tight_bounds' : forall G x T T1 T2 A,
    inert_typ T ->
    precise_flow x G T (typ_rcd (dec_typ A T1 T1)) ->
    precise_flow x G T (typ_rcd (dec_typ A T2 T2)) ->
    T1 = T2.
Proof.
  introv Hgt Hpf1 Hpf2.
  induction Hgt.
  - apply precise_flow_all_inv in Hpf1.
    inversion Hpf1.
  - apply (record_unique_tight_bounds H Hpf1 Hpf2).
  - apply precise_flow_ref_inv in Hpf1.
    inversion Hpf1.
Qed.

Lemma inert_unique_tight_bounds: forall G S x T1 T2 A,
  inert G ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Hgd Hty1 Hty2.
  assert (exists T, binds x T G) as Bi. {
    eapply typing_implies_bound. eassumption.
  }
  destruct Bi as [T Bi].
  pose proof (inert_binds Hgd Bi) as Hgt.
  pose proof (precise_flow_lemma Bi Hty1) as H1.
  pose proof (precise_flow_lemma Bi Hty2) as H2.
  apply (inert_unique_tight_bounds' Hgt H1 H2).
Qed.

Lemma inert_precise_bot : forall T G x,
    inert G ->
    binds x T G ->
    precise_flow x G T typ_bot ->
    False.
Proof.
  intros T G x Hgd Bis Hpf.
  pose proof (binds_inert Bis Hgd) as Hgtyp.
  induction Hgtyp.
  - apply precise_flow_all_inv in Hpf.
    inversion Hpf.
  - pose proof (precise_flow_bnd_eq_or_record H Hpf) as [[U [Contra _]] | [? Contra]];
      inversion Contra.
  - apply precise_flow_ref_inv in Hpf.
    inversion Hpf.
Qed.

Lemma inert_ty_precise_bot : forall G S x,
    inert G ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) typ_bot ->
    False.
Proof.
  intros G S x Hgd Hpt.
  pose proof (typing_implies_bound Hpt) as [T Bi].
  pose proof (precise_flow_lemma Bi Hpt) as Hpf.
  eapply inert_precise_bot; eassumption.
Qed.

Lemma inert_precise_sel_inv : forall G S x y A,
    inert G ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_sel y A) ->
    False.
Proof.
  introv Hgd Hpt.
  pose proof (typing_implies_bound Hpt) as [T Bis].
  pose proof (inert_binds Hgd Bis) as Hgt.
  pose proof (precise_flow_lemma Bis Hpt) as Hpf.
  induction Hgt.
  - apply (precise_flow_all_inv) in Hpf.
    inversion Hpf.
  - pose proof (precise_flow_bnd_eq_or_record H Hpf) as [[U [Contra H1]] | [ls Contra]]; inversion Contra.
  - apply precise_flow_ref_inv in Hpf.
    inversion Hpf.
Qed.

Lemma inert_precise_dec_implies_record_dec : forall G S x D,
    inert G ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd D) ->
    record_dec D.
Proof.
  introv Hgd Hpt.
  pose proof (typing_implies_bound Hpt) as [T' Bis].
  pose proof (inert_binds Hgd Bis) as Hgt.
  pose proof (precise_flow_lemma Bis Hpt) as Hpf.
  induction Hgt.
  - apply (precise_flow_all_inv) in Hpf.
    inversion Hpf.
  - apply (record_precise_dec_implies_record_dec H Hpf).
  - apply precise_flow_ref_inv in Hpf.
    inversion Hpf.
Qed.

Lemma inert_precise_dec_typ_inv : forall G S x A T U,
    inert G ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T U)) ->
    T = U.
Proof.
  introv Hgd Hpt.
  pose proof (inert_precise_dec_implies_record_dec Hgd Hpt) as Hrec.
  inversion Hrec.
  reflexivity.
Qed.

Lemma inert_precise_flow_all_inv : forall x G S T U,
    inert G ->
    precise_flow x G U (typ_all S T) ->
    U = (typ_all S T).
Proof.
  introv Hgd Hpf.
  pose proof (precise_flow_implies_bound Hpf) as Bis.
  pose proof (inert_binds Hgd Bis) as Hgt.
  dependent induction Hgt.
  - symmetry. eapply precise_flow_all_inv. eassumption.
  - pose proof (precise_flow_bnd_eq_or_record H Hpf) as [ [? [Contra _]] | [? Contra]]; inversion Contra.
  - symmetry. eapply precise_flow_ref_inv. eassumption.
Qed.

Lemma inert_precise_all_inv : forall x G S T U,
    inert G ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_all T U) ->
    binds x (typ_all T U) G.
Proof.
  introv Hgd Htyp.
  pose proof (typing_implies_bound Htyp) as [V Bi].
  pose proof (precise_flow_lemma Bi Htyp) as Hpf.
  pose proof (inert_precise_flow_all_inv Hgd Hpf) as H.
  rewrite <- H.
  assumption.
Qed.

Lemma inert_precise_flow_ref_inv : forall x G T U,
    inert G ->
    precise_flow x G U (typ_ref T) ->
    U = (typ_ref T).
Proof.
  introv Hg Hpf.
  pose proof (precise_flow_implies_bound Hpf) as Bis.
  pose proof (inert_binds Hg Bis) as Hgt.
  dependent induction Hgt.
  - symmetry. eapply precise_flow_all_inv. eassumption.
  - pose proof (precise_flow_bnd_eq_or_record H Hpf) as [ [? [Contra _]] | [? Contra]]; inversion Contra.
  - symmetry. eapply precise_flow_ref_inv. eassumption.
Qed.
  

Lemma inert_precise_ref_inv : forall x G S T,
    inert G -> 
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_ref T) ->
    binds x (typ_ref T) G.
Proof.
  introv Hgd Htyp.
  pose proof (typing_implies_bound Htyp) as [V Bi].
  pose proof (precise_flow_lemma Bi Htyp) as Hpf.
  pose proof (inert_precise_flow_ref_inv Hgd Hpf) as H.
  rewrite <- H.
  assumption.
Qed.

Lemma inert_ok : forall G,
    inert G ->
    ok G.
Proof.
  intros G HG. induction G using env_ind.
  auto.
  inversions HG. false* empty_push_inv.
  destruct (eq_push_inv H) as [Hx [HT HG]]. subst.
  apply* ok_push.
Qed.
