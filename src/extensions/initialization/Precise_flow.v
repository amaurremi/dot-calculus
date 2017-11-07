Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Some_lemmas.

(* ###################################################################### *)
(** ** Precise flow *)

(*
Definition (Precise flow of a variable)

For a variable x, environment G, type T, the set Pf(x,G,T) is the set of all
precise types that x can have if G(x)=T. More "precisely":

If G(x)=T, then T is in Pf(x,G,T).
If rec(x:U) is in Pf(x,G,T), then U is in Pf(x,G,T).
If (U1 & U2) is in Pf(x,G,T), then U1 is in Pf(x,G,T).
If (U1 & U2) is in Pf(x,G,T), then U2 is in Pf(x,G,T).

*)

Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=
  | pf_bind : forall x G T,
      binds x T G ->
      precise_flow x G T T
  | pf_open : forall x G T U,
      precise_flow x G T (typ_bnd U) ->
      precise_flow x G T (open_typ x U)
  | pf_and1 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U1
  | pf_and2 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U2
.

Hint Constructors precise_flow.

Lemma precise_flow_lemma : forall T U G S x,
    binds x T G ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) U ->
    precise_flow x G T U.
Proof.
  introv Bis Htyp.
  dependent induction Htyp.
  - rewrite (binds_func H Bis).
    constructor. assumption.
  - assert (H : precise_flow x G T (typ_bnd T0)).
    { apply IHHtyp; auto. }
    auto.
  - eapply pf_and1; auto.
  - eapply pf_and2; auto.
Qed.

Lemma precise_flow_lemma' : forall U G S x,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) U ->
    exists T, precise_flow x G T U.
Proof.
  introv H.
  pose proof (typing_implies_bound H) as [T H1].
  exists T. apply precise_flow_lemma with (S:=S); auto.
Qed.

Lemma precise_flow_implies_bound : forall T U G x,
    precise_flow x G T U ->
    binds x T G.
Proof.
  introv H. induction H; auto.
Qed.

Lemma precise_flow_lemma_rev : forall T U G S x,
    precise_flow x G T U ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) U.
Proof.
  introv H.
  pose proof (precise_flow_implies_bound H) as H1.
  induction H; eauto.
Qed.

Lemma ty_precise_var_and_inv1 : forall x G S T U,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_and T U) ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) T.
Proof.
  introv H.
  destruct (precise_flow_lemma' H) as [T' Hpf].
  apply pf_and1 in Hpf.
  apply (precise_flow_lemma_rev S Hpf).
Qed.

Lemma ty_precise_var_and_inv2 : forall x G S T U,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_and T U) ->
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) U.
Proof.
  introv H.
  destruct (precise_flow_lemma' H) as [T' Hpf].
  apply pf_and2 in Hpf.
  apply (precise_flow_lemma_rev S Hpf).
Qed.

Lemma precise_flow_all_inv : forall x G S T U,
    precise_flow x G (typ_all S T) U ->
    U = (typ_all S T).
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf S T eq_refl); inversion IHHpf.
Qed.

Lemma precise_flow_ref_inv : forall x G T U,
    precise_flow x G (typ_ref T) U ->
    U = (typ_ref T).
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf T eq_refl); inversion IHHpf.
Qed.

Lemma precise_flow_nref_inv : forall x G T U,
    precise_flow x G (typ_nref T) U ->
    U = (typ_nref T).
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf T eq_refl); inversion IHHpf.
Qed.

Lemma precise_flow_bnd_eq_or_record : forall x G T,
    record_type T ->
    (forall U, precise_flow x G (typ_bnd T) U ->
          (exists U', U = (typ_bnd U') /\ record_type U') \/ record_type U).
Proof.
  introv [ls Hrt].
  induction Hrt. intros U.
  - intros Hpf.
    dependent induction Hpf.
    + left. exists (typ_rcd D).
      split.
      * reflexivity.
      * exists \{ label_of_dec D}.
        constructor; auto.
    + destruct (IHHpf D H eq_refl eq_refl) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1. right.
        apply open_record_type. auto.
      * inversion IH.
    + destruct (IHHpf D H eq_refl eq_refl) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1.
      * inversion IH. right. exists ls0. auto.
    + destruct (IHHpf D H eq_refl eq_refl) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1.
      * inversion IH. right. exists \{ l}.
        constructor; auto.
  - intros U Hpf.
    dependent induction Hpf.
    + left. exists (typ_and T (typ_rcd D)).
      split.
      * reflexivity.
      * remember (label_of_dec D) as l.
        exists (union ls \{l}).
        apply rt_cons; auto.
    + specialize (IHHpf H1 D H eq_refl T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * assert (H2 : U'=U).
        { inversion IH1; auto. }
        rewrite H2 in IH2.
        right. apply open_record_type.
        assumption.
      * inversion IH.
    + specialize (IHHpf H1 D H eq_refl T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * inversion IH1.
      * right. inversion IH.
        exists ls0. apply H3.
    + specialize (IHHpf H1 D H eq_refl T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * inversion IH1.
      * right. inversion IH.
        exists \{ l}. constructor; auto.
Qed.

Lemma precise_flow_bnd_inv : forall x G T U,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_bnd U) ->
    (T = U).
Proof.
  introv Hrt Hpf.
  dependent induction Hpf.
  - reflexivity.
  - pose proof (precise_flow_bnd_eq_or_record Hrt Hpf) as [[U' [Heq H]] | [? Contra]]; try inversion Contra.
    inversion Heq; subst.
    pose proof (open_record_type x0 H) as H1.
    rewrite x in H1.
    destruct H1 as [ls H1].
    inversion H1.
  - pose proof (precise_flow_bnd_eq_or_record Hrt Hpf) as H.
    destruct H as [[U' [H1 H2]] | [ls H]].
    + inversion H1.
    + inversion H.
      inversion H2.
  - pose proof (precise_flow_bnd_eq_or_record Hrt Hpf) as H.
    destruct H as [[U' [H1 H2]] | [ls H]].
    + inversion H1.
    + inversion H.
Qed.

Lemma precise_flow_and_inv : forall x G T T1 T2,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_and T1 T2) ->
    exists D, T2 = typ_rcd D.
Proof.
  introv Hrt Hpf.
  pose proof (precise_flow_bnd_eq_or_record Hrt Hpf) as [[? [Contra _]] | [ls H]];
  try inversion Contra.
  inversion H.
  exists D; auto.
Qed.

Lemma record_precise_dec_implies_record_dec : forall x G T D,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_rcd D) ->
    record_dec D.
Proof.
  introv Hrt Hpf.
  pose proof (precise_flow_bnd_eq_or_record Hrt Hpf) as [[U [Contra H1]] | [ls H1]].
  - inversion Contra.
  - inversion H1. assumption.
Qed.

Lemma precise_flow_record_sub : forall x G T,
    record_type T ->
    (forall T', precise_flow x G (typ_bnd T) T' ->
           (T' = typ_bnd T) \/
           forall D, record_has T' D -> record_has (open_typ x T) D).
Proof.
  introv Hrt.
  introv Hpf.
  dependent induction Hpf.
  - left. reflexivity.
  - destruct (IHHpf T Hrt) as [IH | IH]; auto.
    + inversion IH.
      right. auto.
    + right. apply (precise_flow_bnd_inv Hrt) in Hpf.
      rewrite Hpf. auto.
  - destruct (IHHpf T Hrt eq_refl) as [IH | IH].
    + inversion IH.
    + right. auto.
  - destruct (IHHpf T Hrt eq_refl) as [IH | IH].
    + inversion IH.
    + right.
      pose proof (precise_flow_and_inv Hrt Hpf) as [D' H].
      subst U2. intros D Hrh.
      inversion Hrh; subst.
      apply IH.
      auto.
Qed.

Lemma precise_flow_record_has: forall S G x D,
    record_type S ->
    precise_flow x G (typ_bnd S) (typ_rcd D) ->
    record_has (open_typ x S) D.
Proof.
  introv Hrec Hpf.
  pose proof (precise_flow_record_sub Hrec Hpf) as [Contra | H].
  - inversion Contra.
  - apply H.
    auto.
Qed.

Lemma record_unique_tight_bounds : forall G x T A,
    record_type T ->
    ( forall T1 T2,
        precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T1 T1)) ->
        precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T2 T2)) ->
        T1 = T2).
Proof.
  introv Hrt Hpf1 Hpf2.
  pose proof (precise_flow_record_has Hrt Hpf1) as H1.
  pose proof (precise_flow_record_has Hrt Hpf2) as H2.
  apply open_record_type with (x:=x) in Hrt.
  eapply unique_rcd_typ; eauto.
Qed.
