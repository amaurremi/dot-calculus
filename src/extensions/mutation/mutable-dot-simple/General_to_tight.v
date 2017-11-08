Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Narrowing.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Tight_possible_types.

(* ###################################################################### *)
(** ** Tight to precise *)

(* Lemma 1 *)
Lemma tight_to_precise_typ_dec: forall G S x A V U,
  inert G ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_rcd (dec_typ A V U)) ->
  exists T,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) /\
    subtyp sub_tight G S T U /\
    subtyp sub_tight G S V T.
Proof.
  introv HG Ht.
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - lets Hp: (inert_precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHtp A T U0 HG eq_refl). 
    destruct IHHtp as [W [Hx [Hs1 Hs2]]].
    exists W. split*.
Qed.

Lemma tight_to_precise_trm_dec: forall G S x a T,
  inert G ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  exists T',
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_trm a T')) /\
    subtyp sub_tight G S T' T.
Proof.
  introv Hgd Ht.
  lets Htp: (tight_possible_types_lemma Hgd Ht). clear Ht.
  dependent induction Htp.
  - exists T. auto.
  - specialize (IHHtp _ _ Hgd eq_refl). destruct IHHtp as [V [Hx Hs]].
    exists V. split; auto.
    eapply subtyp_trans; eassumption.
Qed.

Lemma tight_to_precise_typ_all: forall G S x V T,
  inert G ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_all V T) ->
  exists V' T' L,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_all V' T') /\
    subtyp sub_tight G S V V' /\
    (forall y,
        y \notin L ->
            subtyp sub_general (G & y ~ V) S (open_typ y T') (open_typ y T))
    .
Proof.
  introv HG Ht.
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - exists V T (dom G); auto.
  - specialize (IHHtp _ _ HG eq_refl).
    destruct IHHtp as [V' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists V' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : subtyp sub_tight G S (typ_all V0 T0) (typ_all V T)).
    { apply subtyp_all with (L:=L); assumption. }
    split.
    + eapply subtyp_trans; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ V)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: subtyp sub_general (G & y ~ V) S (open_typ y T') (open_typ y T0)).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

Lemma tight_to_precise_typ_ref: forall G S x T,
  inert G ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_ref T) ->
  exists T',
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_ref T') /\
    subtyp sub_tight G S T' T /\
    subtyp sub_tight G S T T'.
Proof.
  introv Hg Ht.
  lets Htp: (tight_possible_types_lemma Hg Ht). clear Ht.
  dependent induction Htp.
  - exists T. split*.
  - specialize (IHHtp T0 Hg eq_refl). 
    destruct IHHtp as [U [Hx Hs]]. exists U. split*.
Qed.

(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G S x A V U,
    inert G ->
    ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_rcd (dec_typ A V U)) ->
    (subtyp sub_tight G S (typ_sel (avar_f x) A) U /\
     subtyp sub_tight G S V (typ_sel (avar_f x) A)).
Proof.
  introv HG Hty.
  pose proof (tight_to_precise_typ_dec HG Hty) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_tight in Ht. apply subtyp_trans with (T:=T); auto.
  - apply subtyp_sel2_tight in Ht. apply subtyp_trans with (T:=T); auto.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall m1 m2 G S t T,
     ty_trm m1 m2 G S t T ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G S t T) /\
  (forall m2 G S V U,
     subtyp m2 G S V U ->
     G = G0 ->
     m2 = sub_general ->
     subtyp sub_tight G S V U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply tight_subtyping_sel; auto]; eauto.
Qed.

Lemma general_to_tight_typing: forall G S t T,
  inert G ->
  ty_trm ty_general sub_general G S t T ->
  ty_trm ty_general sub_tight G S t T.
Proof.
  intros. apply* general_to_tight.
Qed.
