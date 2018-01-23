(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import LibLN.
Require Import Sequences.
Require Import Definitions Binding.

(** * Environment Lookup *)

(** * Path lookup *)

(** Looking up a path in a stack (generalization of variable binding). *)

Reserved Notation "s '∋' t" (at level 40).
Reserved Notation "s '⟦' t '⟼' u '⟧'" (at level 40).
Reserved Notation "s '↓' p '==' ds" (at level 40).

Inductive lookup_step : sta -> def_rhs -> def_rhs -> Prop :=

(** [s(x) = v ]   #<br>#
    [―――――――――]   #<br>#
    [s[x ⟼ v]]   *)
| lookup_var : forall s x v,
    binds x v s ->
    s ⟦ pvar x ⟼ defv v ⟧

(** [s ↓ p = ...{a = t}... ]   #<br>#
    [――――――――――――――――――――――]   #<br>#
    [s[p.a ⟼ t]]              *)
| lookup_sel : forall s p ds a t,
    s ↓ p == ds ->
    defs_has ds { a := t } ->
    s ⟦ p•a ⟼ t ⟧

where "s '⟦' p '⟼' t '⟧'" := (lookup_step s (defp p) t)

(** Opening of definitions:
    If [s ∋ (p, ν(x: T)ds)], then [lookup_open] gives us [ds] opened with [p]. *)

with lookup_open : sta -> path -> defs -> Prop :=

(** [s [[ p ⟼ ν(T)ds ]] ]    #<br>#
    [――――――――――――――――――――]    #<br>#
    [s ↓ p = ds^p        ]        *)
| lookup_defs : forall s p T ds,
    s ⟦ p ⟼ defv (val_new T ds) ⟧ ->
    s ↓ p == open_defs_p p ds

where "s '↓' p '==' ds" := (lookup_open s p ds).

Notation "s '⟦' t '⟼*' u '⟧'" := (star (lookup_step s) t u) (at level 40).

Inductive lookup : sta -> path * val -> Prop :=
| lookup_def: forall s p v,
    s ⟦ defp p ⟼* defv v ⟧ ->
    s ∋ (p, v)

where "s '∋' t" := (lookup s t).

Hint Constructors lookup lookup_open lookup_step.

Scheme lookup_mut := Induction for lookup_step Sort Prop
  with lookup_open_mut := Induction for lookup_open Sort Prop.
Combined Scheme lookup_mutind from lookup_mut, lookup_open_mut.

(** ** Lemmas about Environment Lookup *)

Lemma lookup_empty_mut :
  (forall s t u,
      s ⟦ t ⟼ u ⟧ ->
      s = empty ->
      False) /\
  (forall s p ds,
      s ↓ p == ds ->
      s = empty ->
      False).
Proof.
  Admitted.

Lemma lookup_empty : forall t u,
    empty ⟦ t ⟼ u ⟧ -> False.
Proof.
  intros. eapply (proj21 lookup_empty_mut); eauto.
Qed.

Lemma lookup_push_eq_inv_var :
    forall s x v t,
    s & x ~ v ⟦ pvar x ⟼ t ⟧ ->
    t = defv v.
Proof.
  introv Hx. inversions Hx;
    try (destruct (last_field _ _ H) as [bs Hbs]; inversion Hbs).
  apply binds_push_eq_inv in H1. subst*.
Qed.

Lemma lookup_step_push_neq : forall s x bs v y t,
    s ⟦ p_sel (avar_f x) bs ⟼ t ⟧ ->
    y # s ->
    s & y ~ v ⟦ p_sel (avar_f x) bs ⟼ t ⟧.
Proof.
  introv Hp Hn. dependent induction Hp.
(*
  assert (x <> y) as Hxy. {
    lets Hb: (lookup_implies_binds H). destruct_all. intro. subst.
      lets Hb: (binds_destruct). apply binds_destruct in H0.
      destruct_all. subst. simpl_dom. apply notin_union_r in Hn. destruct_all. apply notin_union_r in H0.
      destruct_all. apply* notin_same.*)
  Admitted.

Lemma lookup_strengthen: forall s y v x bs t,
    s & y ~ v ⟦ p_sel (avar_f x) bs ⟼ t ⟧ ->
    y <> x ->
    s ⟦ p_sel (avar_f x) bs ⟼ t ⟧.
Proof.
Admitted.

Lemma named_path_lookup_step_mut:
    (forall s t1 t2,
        s ⟦ t1 ⟼ t2 ⟧ -> forall p,
        t2 = defp p ->
        exists x bs, p = p_sel (avar_f x) bs) /\
    (forall s p ds,
        s ↓ p == ds ->
        exists x bs, p = p_sel (avar_f x) bs).
Proof.
  Admitted.

Lemma named_path_lookup_step: forall s t p,
        s ⟦ t ⟼ defp p ⟧ ->
        exists x bs, p = p_sel (avar_f x) bs.
Proof.
  intros. apply* (proj21 named_path_lookup_step_mut).
Qed.

Lemma named_path_lookup: forall s p v,
    s ∋ (p, v) ->
    exists x bs, p = p_sel (avar_f x) bs.
Proof.
  intros. inversions H. dependent induction H2; eauto. admit.
Qed.

Lemma lookup_val_inv: forall s v t,
    s ⟦ defv v ⟼* t ⟧ ->
    t = defv v.
Proof.
  introv Hs. dependent induction Hs. auto. inversion H.
Qed.
Lemma lookup_path_inv: forall s t p,
    s ⟦ t ⟼* defp p ⟧ ->
    exists q, t = defp q.
Proof.
  introv Hs. dependent induction Hs; eauto. destruct (IHHs _ eq_refl) as [q Heq]. subst.
  inversions H; eauto.
Qed.

Lemma lookup_last_path: forall s p v,
    s ∋ (p, v) ->
    exists q, s ⟦ defp p ⟼* defp q ⟧ /\
         s ⟦ q ⟼ defv v ⟧.
Proof.
  introv Hl.
  inversions Hl. dependent induction H1. destruct b; subst.
  - specialize (IHstar _ _ eq_refl eq_refl). destruct IHstar as [r [Hs Hl]].
    exists r. split. eapply star_trans. apply star_one. apply  H. all: auto.
  - apply lookup_val_inv in H1. inversions H1.
    exists p. split*. apply star_refl.
Qed.

Lemma lookup_step_func_mut :
  (forall s t t1,
      s ⟦ t ⟼ t1 ⟧ -> forall t2,
      s ⟦ t ⟼ t2 ⟧ ->
      t1 = t2) /\
  (forall s p ds1,
    s ↓ p == ds1 -> forall ds2,
    s ↓ p == ds2 ->
    ds1 = ds2).
Proof.
  Admitted. (*
  apply lookup_mutind; intros.
  - Case "lookup_var".
    inversions H. lets Hb: (binds_func b H2). subst*.
    unfolds sel_fields. destruct p. inversion H0.
  - Case "lookup_sel".
    inversions H0; unfolds sel_fields; destruct p. inversion H1. destruct p0.
    inversions H1. specialize (H _ H2). subst. apply* defs_has_inv.
  - Case "lookup_defs".
    lets Hl: (lookup_defs l). inversions H0. specialize (H _ H1). inversion* H.
Qed.*)

Lemma lookup_step_func: forall s t t1 t2,
      s ⟦ t ⟼ t1 ⟧ ->
      s ⟦ t ⟼ t2 ⟧ ->
      t1 = t2.
Proof.
  intros. apply* lookup_step_func_mut.
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
  Admitted. (*lets Hf: (finseq_unique H H2 Hirr1 H3 Hirr2). inversion* Hf.*)

Lemma lookup_implies_binds : forall s x bs t,
    s ⟦ p_sel (avar_f x) bs ⟼ t ⟧ ->
    exists v, binds x v s.
Proof.
  introv Hl. dependent induction Hl. eauto. Admitted.

Lemma lookup_push_neq : forall s x bs v y t,
    s ⟦ defp (p_sel (avar_f x) bs) ⟼* t ⟧ ->
    y # s ->
    s & y ~ v ⟦ defp (p_sel (avar_f x) bs) ⟼* t ⟧.
Proof.
  introv Hl Hn. gen y. dependent induction Hl; introv Hn.
  - apply star_refl.
  - destruct b; subst.
    * lets Hnl: (named_path_lookup_step H). destruct_all. subst.
      apply* star_trans. apply star_one. apply* lookup_step_push_neq.
    * apply lookup_val_inv in Hl. subst. apply star_one. apply* lookup_step_push_neq.
Qed.
