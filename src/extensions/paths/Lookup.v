(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import Sequences.
Require Import Definitions Binding.

(** * Environment Lookup *)

(** * Path lookup *)

(** Looking up a path in a stack (generalization of variable binding). *)

Reserved Notation "s '∋' t" (at level 40).
Reserved Notation "s '⟦' t '⟼' u '⟧'" (at level 40).

Inductive lookup_step : sta -> def_rhs -> def_rhs -> Prop :=

(** [s(x) = v ]   #<br>#
    [―――――――――]   #<br>#
    [s[x ⟼ v]]   *)
| lookup_var : forall s x v,
    binds x v s ->
    s ⟦ pvar x ⟼ defv v ⟧

(** [s ⟦ p ⟼ q ⟧ ]              #<br>#
    [――――――――――――――――――――――]    #<br>#
    [s ⟦ p.a ⟼ q.a ⟧ ]          *)
| lookup_sel_p : forall s p q a,
    s ⟦ p ⟼ defp q ⟧ ->
    s ⟦ p • a ⟼ defp (q • a) ⟧

(** [s ⟦ p ⟼ ν(T)...{a = t}... ⟧ ]   #<br>#
    [――――――――――――――――――――――]         #<br>#
    [s ⟦ p.a ⟼ t ⟧ ]                 *)
| lookup_sel_v : forall s p a t T ds,
    s ⟦ p ⟼ defv (val_new T ds) ⟧ ->
    defs_has ds { a := t } ->
    s ⟦ p•a ⟼ open_defrhs_p p t ⟧

where "s '⟦' p '⟼' t '⟧'" := (lookup_step s (defp p) t).

Notation "s '⟦' t '⟼*' u '⟧'" := (star (lookup_step s) t u) (at level 40).

Inductive lookup : sta -> path * val -> Prop :=
| lookup_def: forall s p v,
    s ⟦ defp p ⟼* defv v ⟧ ->
    s ∋ (p, v)

where "s '∋' t" := (lookup s t).

Hint Constructors lookup lookup_step.

(** ** Lemmas about Environment Lookup *)

Lemma lookup_empty : forall t u,
    empty ⟦ t ⟼ u ⟧ -> False.
Proof.
  intros. dependent induction H; eauto. false* binds_empty_inv.
Qed.

Ltac solve_lookup :=
  match goal with
  | [ H : _ • _ = p_sel _ _ |- _ ] =>
    rewrite <- H; econstructor; simpl_dot; eauto
  end.

Lemma lookup_strengthen_one: forall s y v x bs t,
    s & y ~ v ⟦ p_sel (avar_f x) bs ⟼ t ⟧ ->
    y <> x ->
    s ⟦ p_sel (avar_f x) bs ⟼ t ⟧.
Proof.
  introv Hl Hn. dependent induction Hl; try solve_lookup.
  constructor. eapply binds_push_neq_inv; eauto.
Qed.

Lemma lookup_strengthen s s1 s2 x v bs t :
  ok s ->
  s = s1 & x ~ v & s2 ->
  s ⟦ p_sel (avar_f x) bs ⟼ t ⟧ ->
  s1 & x ~ v ⟦ p_sel (avar_f x) bs ⟼ t ⟧.
Proof.
  intros Hok -> Hs. induction s2 using env_ind.
  - rewrite concat_empty_r in Hs; auto.
  - destruct (classicT (x0 = x)) as [-> | Hn].
    + apply ok_middle_inv_r in Hok. simpl_dom. apply notin_union in Hok as [Contra _]. false* notin_same.
    + rewrite concat_assoc in *.
      apply lookup_strengthen_one in Hs; auto.
Qed.

Lemma named_lookup_step: forall s t p,
        s ⟦ p ⟼ t ⟧ ->
        exists x bs, p = p_sel (avar_f x) bs.
Proof.
  intros. Admitted.

Lemma named_path_lookup_step: forall s t p,
        s ⟦ t ⟼ defp p ⟧ ->
        exists x bs, p = p_sel (avar_f x) bs.
Proof.
  intros. Admitted.

Lemma lookup_val_inv: forall s v t,
    s ⟦ defv v ⟼* t ⟧ ->
    t = defv v.
Proof.
  introv Hs. dependent induction Hs. auto. inversion H.
Qed.

Lemma lookup_step_func: forall s t t1 t2,
      s ⟦ t ⟼ t1 ⟧ ->
      s ⟦ t ⟼ t2 ⟧ ->
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

Lemma lookup_irred: forall s v,
    irred (lookup_step s) (defv v).
Proof.
  inversion 1.
Qed.

Lemma lookup_func : forall s p v1 v2,
    s ∋ (p, v1) ->
    s ∋ (p, v2) ->
    v1 = v2.
Proof.
  introv Hs1 Hs2.
  lets H: (lookup_step_func). specialize (H s). inversions Hs1. inversions Hs2.
  assert (irred (lookup_step s) (defv v1)) as Hirr1 by apply* lookup_irred.
  assert (irred (lookup_step s) (defv v2)) as Hirr2 by apply* lookup_irred.
  assert (forall a b c : def_rhs, lookup_step s a b -> lookup_step s a c -> b = c) as H'. {
    intros. destruct a; try solve [inversion H0]. apply* H.
  }
  lets Hf: (finseq_unique H' H2 Hirr1 H3 Hirr2). inversion* Hf.
Qed.

Lemma lookup_step_weaken_one : forall s x bs v y t,
    s ⟦ p_sel (avar_f x) bs ⟼ t ⟧ ->
    y # s ->
    s & y ~ v ⟦ p_sel (avar_f x) bs ⟼ t ⟧.
Proof.
  introv Hp Hn. dependent induction Hp; try solve_lookup.
  constructor. apply* binds_push_neq. intro. subst. eapply binds_fresh_inv; eauto.
Qed.

Lemma lookup_step_weaken s p t s' :
  ok (s & s') ->
  s ⟦ p ⟼ t ⟧ ->
  s & s' ⟦ p ⟼ t ⟧.
Proof.
  intros Hok Hs. induction s' using env_ind.
  - rewrite concat_empty_r in *; auto.
  - rewrite concat_assoc in *. apply ok_push_inv in Hok as [Hok Hn].
    destruct (named_lookup_step Hs) as [y [bs ->]].
    apply* lookup_step_weaken_one.
Qed.

Lemma lookup_weaken_one : forall s x bs v y t,
    s ⟦ defp (p_sel (avar_f x) bs) ⟼* t ⟧ ->
    y # s ->
    s & y ~ v ⟦ defp (p_sel (avar_f x) bs) ⟼* t ⟧.
Proof.
  introv Hl Hn. gen y. dependent induction Hl; introv Hn.
  - apply star_refl.
  - destruct b; subst.
    * lets Hnl: (named_path_lookup_step H). destruct_all. subst.
      apply* star_trans. apply star_one. apply* lookup_step_weaken_one.
    * apply lookup_val_inv in Hl. subst. apply star_one. apply* lookup_step_weaken_one.
Qed.

Lemma lookup_weaken s t1 t2 s' :
  ok (s & s') ->
  s ⟦ t1 ⟼* t2 ⟧ ->
  s & s' ⟦ t1 ⟼* t2 ⟧.
Proof.
  intros Hok Hs. induction s' using env_ind.
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
