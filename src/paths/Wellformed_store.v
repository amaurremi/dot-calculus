Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Some_lemmas.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Invertible_typing.
Require Import Narrowing.

(* ###################################################################### *)
(** ** Well-formed store *)

Lemma wf_sto_to_ok_G: forall s G,
  G ~~ s -> ok G.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_s: forall s G,
  G ~~ s -> ok s.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_G.

Lemma tpt_to_precise_rec: forall G v T,
    G |-##v v : typ_bnd T ->
    G |-! trm_val v : typ_bnd T.
Proof.
  introv Ht.
  inversions Ht. inversions H. apply_fresh ty_new_intro_p as z; auto.
Qed.

Lemma tpt_to_precise_lambda: forall G v S T,
    G |-##v v : typ_all S T ->
    inert G ->
    exists L S' T',
      G |-! trm_val v : typ_all S' T' /\
      G |- S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S |- T' ||^ y <: T ||^ y).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt S0 T0 eq_refl Hg) as [L' [S1 [T1 [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S1 T1. split. assumption. split. apply subtyp_trans with (T:=S0).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok. {
      apply* ok_push. apply* inert_ok.
    }
    apply subtyp_trans with (T:=T0 ||^ y).
    eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general.
    assumption. assumption.
    apply* H0.
Qed.

Lemma precise_forall_inv : forall G v S T,
    G |-! trm_val v : typ_all S T ->
    exists t, v = val_lambda S t.
Proof.
  introv Ht. inversions Ht. exists* t.
Qed.

Lemma precise_bnd_inv : forall G v S,
    G |-! trm_val v : typ_bnd S ->
    exists ds, v = val_new S ds.
Proof.
  introv Ht. inversions Ht. exists* ds.
Qed.

Lemma precise_obj_typ : forall G T ds U,
    G |-! trm_val (val_new T ds) : U ->
    U = typ_bnd T.
Proof.
  introv Hp. dependent induction Hp; auto.
Qed.

Lemma tpt_obj_all : forall G S ds T U,
    G |-##v val_new S ds: typ_all T U ->
    False.
Proof.
  introv Ht. dependent induction Ht.
  apply precise_obj_typ in H. inversion H.
  apply* IHHt.
Qed.

Lemma corresponding_types: forall G s x T,
  G ~~ s ->
  inert G ->
  binds x T G ->
  ((exists L S U S' U' t, binds x (val_lambda S t) s /\
                  G |-! trm_val (val_lambda S t): typ_all S U /\
                  T = typ_all S' U' /\
                  G |- S' <: S /\
                  (forall y, y \notin L ->
                    G & y ~ S' |- U ||^ y <: U' ||^ y)) \/
   (exists S ds, binds x (val_new S ds) s /\
                 G |-! trm_val (val_new S ds) : typ_bnd S /\
                 T = typ_bnd S)).
Proof.
  introv H Hgd Bi. induction H.
  - false* binds_empty_inv.
  - assert (inert G) as Hg. {
      inversions Hgd. false* empty_push_inv. destruct (eq_push_inv H3) as [Hx [Hv HG]]. subst*.
    }
    unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists (L \u dom G) T0 U T0 U t.
        split*. split*.
        apply* weaken_ty_trm_p.
      * right. exists T0. exists ds. split*. split*.
        apply* weaken_ty_trm_p.
      * apply general_to_tight_typing in H2.
        lets Hpt: (invertible_lemma_v Hg H2).
        assert (inert_typ T) as HgT. {
          inversions Hgd. false* empty_push_inv. destruct (eq_push_inv H5) as [Hx [Hv HG]]. subst*.
        }
        inversions HgT.
        apply tpt_to_precise_lambda in Hpt. destruct Hpt as [L [S' [T' [Hss [Hs1 Hs2]]]]].
        destruct (precise_forall_inv Hss) as [t Heq]. subst. left.
        exists (L \u dom G \u \{ x0}) S' T' S T1 t.
        split. apply* f_equal. split. apply* weaken_ty_trm_p. split. reflexivity.
        split. apply* weaken_subtyp. intros y Hy.
        apply (proj44 weaken_rules) with (G:=G & y ~ S). apply* Hs2. reflexivity.
        apply ok_push. apply* inert_ok. simpl_dom. rewrite notin_union. split*.
        assumption.
        apply tpt_to_precise_rec in Hpt.
        destruct (precise_bnd_inv Hpt) as [ds Heq]. subst. right. exists T1 ds.
        split. reflexivity. split. apply* weaken_ty_trm_p. reflexivity.
        assumption.
    + specialize (IHwf_sto Hg Bi).
      destruct IHwf_sto as [[L [S [U [S' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] |
                            [S [ds [Hv [Ht He]]]]].
      * left. exists (L \u dom G \u \{x0}) S U S' U' t. split. assumption. split.
        apply* weaken_ty_trm_p.
        split. assumption. split. apply* weaken_subtyp.
        intros y Hy. apply (proj44 (weaken_rules)) with (G:=G & y ~ S'). apply* Hs2.
        reflexivity. apply ok_push. apply* inert_ok. auto.
      * right. exists S ds. split. assumption. split. apply* weaken_ty_trm_p. assumption.
Qed.

Lemma sto_binds_to_ctx_binds: forall G s x v,
  G ~~ s -> binds x v s -> exists S, binds x S G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  induction Hwf.
  false* binds_empty_inv.
  destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
  - exists* T.
  - destruct (IHHwf Hb Hwf) as [S HS]. exists S.
    apply* binds_push_neq.
Qed.

Lemma wf_sto_val_new_in_G: forall G s x T ds,
  G ~~ s ->
  inert G ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Hg Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [S Bi].
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
      apply invertible_lemma_v in H1; auto.
      inversions H1; try solve [inversion HT].
      * apply* precise_obj_typ.
      * false* tpt_obj_all.
    }
    subst*.
  - apply binds_push_neq_inv in Bi; auto.
Qed.

Lemma val_new_typing: forall G s x T ds,
  G ~~ s ->
  inert G ->
  binds x (val_new T ds) s ->
  G |-! trm_val (val_new T ds) : typ_bnd T.
Proof.
  introv Hwf Hg Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Hg Bi) as [H | H].
  - destruct H as [_ [S [_ [_ [_ [t [Contra _]]]]]]].
    false.
  - destruct H as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    pose proof (binds_func Bis Bis') as Heq; inversions Heq.
    assumption.
Qed.
