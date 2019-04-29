(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Runtime Configuration Lookup of Paths *)
Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import Sequences.
Require Import Definitions Binding.

(** Looking up a path in a store (generalization of variable binding). *)
Reserved Notation "γ '⟦' t '⤳' u '⟧'" (at level 40).

Inductive lookup_step : sta -> def_rhs -> def_rhs -> Prop :=

(** [γ(x) = v ]   #<br>#
    [―――――――――]   #<br>#
    [γ ⊢ x ⤳ v]   *)
| lookup_var : forall γ x v,
    binds x v γ ->
    γ ⟦ pvar x ⤳ defv v ⟧

(** [γ ⊢ p ⤳ q ]              #<br>#
    [――――――――――――――――――――――]    #<br>#
    [γ ⊢ p.a ⤳ q.a ]          *)
| lookup_sel_p : forall γ p q a,
    γ ⟦ p ⤳ defp q ⟧ ->
    γ ⟦ p•a ⤳ defp (q•a) ⟧

(** [γ ⊢ p ⤳ ν(T)...{a = t}... ]   #<br>#
    [――――――――――――――――――――――]         #<br>#
    [γ ⊢ p.a ⤳ t ]                 *)
| lookup_sel_v : forall γ p a t T ds,
    γ ⟦ p ⤳ defv (val_new T ds) ⟧ ->
    defs_has ds { a := t } ->
    γ ⟦ p•a ⤳ open_defrhs_p p t ⟧

where "γ '⟦' p '⤳' t '⟧'" := (lookup_step γ (defp p) t).

(** Reflexive, transitive closure of path lookup *)
Notation "γ '⟦' t '⤳*' u '⟧'" := (star (lookup_step γ) t u) (at level 40).

Hint Constructors lookup_step star.

(** *** Properties of path lookup *)

(** Paths cannot be looked up in the empty context *)
Lemma lookup_empty : forall p u,
    empty ⟦ p ⤳ u ⟧ -> False.
Proof.
  intros. dependent induction H; eauto. false* binds_empty_inv.
Qed.

Ltac solve_lookup :=
  match goal with
  | [ H : _ • _ = p_sel _ _ |- _ ] =>
    rewrite <- H; econstructor; simpl_dot; eauto
  end.

(** Removing an element [x] from a value environment does not affect the
    lookup of [y.bs] as long as [x≠y]. *)
Lemma lookup_strengthen_one: forall γ y v x bs t,
    γ & y ~ v ⟦ p_sel (avar_f x) bs ⤳ t ⟧ ->
    y <> x ->
    γ ⟦ p_sel (avar_f x) bs ⤳ t ⟧.
Proof.
  introv Hl Hn. dependent induction Hl; try solve_lookup.
  constructor. eapply binds_push_neq_inv; eauto.
Qed.

(** Removing a part [γ2] from a value environment [γ1, y=_, γ2] does not affect the
    lookup of [y.bs] as long as [y ∉ γ2]. *)
Lemma lookup_strengthen γ γ1 γ2 x v bs t :
  ok γ ->
  γ = γ1 & x ~ v & γ2 ->
  γ ⟦ p_sel (avar_f x) bs ⤳ t ⟧ ->
  γ1 & x ~ v ⟦ p_sel (avar_f x) bs ⤳ t ⟧.
Proof.
  intros Hok -> Hs. induction γ2 using env_ind.
  - rewrite concat_empty_r in Hs; auto.
  - destruct (classicT (x0 = x)) as [-> | Hn].
    + apply ok_middle_inv_r in Hok. simpl_dom. apply notin_union in Hok as [Contra _]. false* notin_same.
    + rewrite concat_assoc in *.
      apply lookup_strengthen_one in Hs; auto.
Qed.

(** If a path can be looked up in a value environment, that path starts
    with a named variable *)
Lemma named_lookup_step: forall γ t p,
    γ ⟦ p ⤳ t ⟧ ->
    exists x bs, p = p_sel (avar_f x) bs.
Proof.
  intros. dependent induction H.
  - repeat eexists; eauto.
  - specialize (IHlookup_step _ eq_refl) as [? [? ->]]. simpl. repeat eexists; eauto.
  - specialize (IHlookup_step _ eq_refl) as [? [? ->]]. simpl. repeat eexists; eauto.
Qed.

(** The reflexive, transitive closure of looking up a value always results
    in the same value *)
Lemma lookup_val_inv: forall γ v t,
    γ ⟦ defv v ⤳* t ⟧ ->
    t = defv v.
Proof.
  introv Hs. dependent induction Hs. auto. inversion H.
Qed.

(** The lookup relation is functional *)
Lemma lookup_step_func: forall γ t t1 t2,
    γ ⟦ t ⤳ t1 ⟧ ->
    γ ⟦ t ⤳ t2 ⟧ ->
    t1 = t2.
Proof.
  introv Hl1. gen t2. dependent induction Hl1; introv Hl2.
  - inversions Hl2; try simpl_dot. apply (binds_functional H) in H2. f_equal*.
  - dependent induction Hl2; try simpl_dot;
    specialize (IHHl1 _ eq_refl _ Hl2); inversions IHHl1; eauto.
  - dependent induction Hl2; try simpl_dot;
      lets IH: (IHHl1 _ eq_refl _ Hl2); inversions IH; eauto.
    lets Hd: (defs_has_inv H H0). subst*.
Qed.

(** No lookup transitions are possible from values *)
Lemma lookup_irred: forall γ v,
    irred (lookup_step γ) (defv v).
Proof.
  inversion 1.
Qed.

(** Two lookup reduction sequences that start with a path result in the same value *)
Lemma lookup_func : forall γ p v1 v2,
    γ ⟦ defp p ⤳* defv v1 ⟧ ->
    γ ⟦ defp p ⤳* defv v2 ⟧ ->
    v1 = v2.
Proof.
  introv Hs1 Hs2.
  lets H: (lookup_step_func). specialize (H γ).
  assert (irred (lookup_step γ) (defv v1)) as Hirr1 by apply* lookup_irred.
  assert (irred (lookup_step γ) (defv v2)) as Hirr2 by apply* lookup_irred.
  assert (forall a b c : def_rhs, lookup_step γ a b -> lookup_step γ a c -> b = c) as H'. {
    intros. destruct a; try solve [inversion H0]. apply* H.
  }
  lets Hf: (finseq_unique H' Hs1 Hirr1 Hs2 Hirr2). inversion* Hf.
Qed.

(** Weakening for the lookup relation by one element *)
Lemma lookup_step_weaken_one : forall γ x bs v y t,
    γ ⟦ p_sel (avar_f x) bs ⤳ t ⟧ ->
    y # γ ->
    γ & y ~ v ⟦ p_sel (avar_f x) bs ⤳ t ⟧.
Proof.
  introv Hp Hn. dependent induction Hp; try solve_lookup.
  constructor. apply* binds_push_neq. intro. subst. eapply binds_fresh_inv; eauto.
Qed.

(** Weakening for the lookup relation *)
Lemma lookup_step_weaken γ p t γ' :
  ok (γ & γ') ->
  γ ⟦ p ⤳ t ⟧ ->
  γ & γ' ⟦ p ⤳ t ⟧.
Proof.
  intros Hok Hs. induction γ' using env_ind.
  - rewrite concat_empty_r in *; auto.
  - rewrite concat_assoc in *. apply ok_push_inv in Hok as [Hok Hn].
    destruct (named_lookup_step Hs) as [y [bs ->]].
    apply* lookup_step_weaken_one.
Qed.

(** Weakening for the reflexive, transitive closure of the lookup relation by one element *)
Lemma lookup_weaken_one : forall γ x bs v y t,
    γ ⟦ defp (p_sel (avar_f x) bs) ⤳* t ⟧ ->
    y # γ ->
    γ & y ~ v ⟦ defp (p_sel (avar_f x) bs) ⤳* t ⟧.
Proof.
  introv Hl Hn. gen y. dependent induction Hl; introv Hn.
  - apply star_refl.
  - destruct b; subst.
    * destruct Hl.
      ** apply* star_trans. apply star_one. apply* lookup_step_weaken_one.
      ** apply* star_trans.
         assert (exists q, a = defp q) as [q ->] by (inversions H0; eauto).
         pose proof (named_lookup_step H0) as [? [? ->]].
         specialize (IHHl _ _ eq_refl). eapply star_trans. apply star_one.
         apply* lookup_step_weaken_one. eauto.
    * apply lookup_val_inv in Hl. subst. apply star_one. apply* lookup_step_weaken_one.
Qed.

(** Weakening for the reflexive, transitive closure of the lookup relation *)
Lemma lookup_weaken γ t1 t2 γ' :
  ok (γ & γ') ->
  γ ⟦ t1 ⤳* t2 ⟧ ->
  γ & γ' ⟦ t1 ⤳* t2 ⟧.
Proof.
  intros Hok Hs. induction γ' using env_ind.
  - rewrite concat_empty_r in *; auto.
  - rewrite concat_assoc in *. apply ok_push_inv in Hok as [Hok Hn].
    assert (t1 = t2 \/ exists y bs, t1 = defp (p_sel (avar_f y) bs)) as [-> | [y [bs ->]]].
    { inversions Hs; auto. right. destruct t1.
      - destruct (named_lookup_step H) as [? [? ->]]. eauto.
      - inversion H.
    }
    + apply star_refl.
    + apply* lookup_weaken_one.
Qed.
