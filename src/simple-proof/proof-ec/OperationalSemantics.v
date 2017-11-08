Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding.

(** * Normal Forms
A normal form is defined in the WadlerFest DOT paper as:

[n ::= x | v | let x = v in n]

This corresponds to an evaluation context of the form
[(let x = v in)* [ ]] whose hole is filled by a variable [x]
or value [v]. *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v)
| nf_let: forall v t, normal_form t -> normal_form (trm_let (trm_val v) t).

(** * Operational Semantics

The first four reduction rules correspond directly to the rules in Figure 7 of the paper.

The last two rules are congruence rules that implement the meaning of evaluation contexts.
Specifically, if a term [u] decomposes into an evaluation context and subterm
as [u = e[t]] and [e[t]] reduces to [e[t']] according to the rules from Figure 7,
then the purpose of the two congruence rules is to ensure that [u] also reduces
to [u'], where [u'] is the term [u' = e[t']]. The grammar for evaluation contexts
in the paper is:

[e ::= [] | let x = [] in t | let x = v in e]

A sentential form [eta] in a derivation of an evaluation context [e] is a string
of terminals (the elements of DOT terms) and the non-terminal [e]. Define
[e(eta)] to be a string of terminals formed by replacing [e] with [[]] in [eta].
We argue that whenever [eta_1] directly derives [eta_2] ([eta_1 => eta_2]),
and the reduction rules infer that [e(eta_2)[t_2] |-> e(eta_2)[t_2']], then the
reduction rules also infer that [e(eta_1)[t_1] |-> e(eta_1)[t_1']], where
[e(eta_2)[t_2] = e(eta_1)[t_1]] and [e(eta_2)[t_2'] = e(eta_1)[t_1']].
The argument is by considering each of the three cases
in the evaluation context grammar that justify [eta_1 => eta_2].
The first case replaces [e] with [[]], so [e(eta_1) = e(eta_2)], so the conclusion
trivially holds. The second case replaces [e] with [let x = [] in t]. In this case,
the reduction congruence rule [red_let_trm] has [e(eta_2)[t_2] |-> e(eta_2)[t_2']]
as a premise and [e(eta_1)[t_1] |-> e(eta_1)[t_1']] as a conclusion. The third case
replaces [e] with [let x = v in e].  Similarly, the congruence rule [red_let_val]
has [e(eta_2)[t_2] |-> e(eta_2)[t_2']] as a premise and [e(eta_1)[t_1] |-> e(eta_1)[t_1']]
as a conclusion. Thus, whenever [eta_1 => eta_2] and [e(eta_2)[t_2] |-> e(eta_2)[t_2']],
we also have that [e(eta_1)[t_1] |-> e(eta_1)[t_1']].

Reasoning inductively about the steps in the context-free grammar derivation of [e],
for every sentential
form [eta] that occurs in that derivation, the congruence reduction rules infer that
[e(eta)[u] |-> e(eta)[u']], where
[e(eta)[u] = e[t]] and [e(eta)[u'] = e[t']]. In particular, this is true for the
sentential form [eta = e], the first sentential form of every derivation. Since
[e(eta) = e(e) = []], we have shown that the congruence reduction rules infer that [u |-> u'].

Starting with an evaluation context [e] in its conclusion, the [red_let_val] rule appends
[let x = v] to the context to yield a new context used in its premise.
(More precisely, the rule replaces the non-terminal [e] within the context in the conclusion by
[let x = v in e].) This is the only reduction rule that modifies an existing evaluation context. Therefore,
in a derivation of a reduction judgment [u |-> u'] in an empty evaluation context, every evaluation context
that appears in the derivation is of the form [let x_1 = v_1 in ... let x_n = v_n in []].
Therefore, in order to be able to represent every step of every such derivation of a reduction
judgement in the Coq proof, it is sufficient to represent evaluation contexts by a data structure
that can represent all evaluation contexts of this form. The proof represents these evaluation
contexts by a list of pairs of variables and values.
*)


Reserved Notation "e '[' t1 '|->' t2 ']'" (at level 60, t1 at level 39).

Inductive red : ec -> trm -> trm -> Prop :=
(** [e(x) = lambda(T)t]    #<br>#
    [――――――――――――――――――――]  #<br>#
    [e[x y] |-> e[t^y] ]  *)
| red_apply : forall x y e T t,
    lc_trm (trm_app (avar_f x) (avar_f y)) ->
    binds x (val_lambda T t) e ->
    e [ trm_app (avar_f x) (avar_f y) |-> open_trm y t ]
(** [e(x) = nu(T)...{a = t}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [e[x.a] |-> e[t]]  *)
| red_project : forall x a e T ds t,
    lc_trm (trm_sel (avar_f x) a) ->
    binds x (val_new T ds) e ->
    defs_has (open_defs x ds) (def_trm a t) ->
    e [ trm_sel (avar_f x) a |-> t ]
(** [e[let x = y in t] |-> e[t^y]] *)
| red_let_var : forall y t e,
    lc_trm (trm_let (trm_var (avar_f y)) t) ->
    e [ trm_let (trm_var (avar_f y)) t |-> open_trm y t ]
(** [e[let x = (let y = s in t) in u] |-> e[let y = s in let x = t in u]] *)
| red_let_let : forall s t u e,
    lc_trm (trm_let (trm_let s t) u) ->
    e [ trm_let (trm_let s t) u |-> trm_let s (trm_let t u) ]
(** [e[t] |-> e[t']]                            #<br>#
    [――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [e[let x = t in u] |-> e[let x = t' in u]]     *)
| red_let_trm : forall e t t' u,
    lc_trm (trm_let t u) ->
    e [ t |-> t' ] ->
    e [ trm_let t u |-> trm_let t' u ]
(** [(e, x = v) [t] |-> (e, x = v) [t']]        #<br>#
    [――――――――――――――――――――――――――――――――――――――――]   #<br>#
    [e[let x = v in t] |-> e[let x = v in t']]   *)
| red_let_val: forall e t t' v L,
    lc_trm (trm_let (trm_val v) t) ->
    (forall x, x \notin L  ->
      (e & x ~ v) [ open_trm x t |-> open_trm x t' ]) ->
    e [ trm_let (trm_val v) t |-> trm_let (trm_val v) t' ]
where "e [ t |-> t' ]" := (red e t t').
Hint Constructors red normal_form.

(** Reduction in an empty context *)
Notation "t '|->' u" := (empty [t |-> u]) (at level 50).

(** Typing in an empty context *)
Notation "'⊢' t ':' T" := (empty ⊢ t: T) (at level 40, t at level 59).

(** If [e] is locally closed and [e[t] |-> e[t']], then [t'] is locally closed.  *)
Lemma lc_env_eval_to_lc_trm : forall e t t',
    lc_ec e ->
    e [t |-> t'] ->
    lc_trm t'.
Proof with auto.
  introv Hlce He.
  induction He;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    end;
    repeat constructor;
    do 2 try
       match goal with
       | [ H : binds _ _ _ |- _ ] => apply lc_ec_binds_inv in H; eauto
       | [ H : lc_at_val _ _ |- _ ] => inversions H
       | [ H : lc_at_trm _ _ |- _ ] => solve [inversions H; auto]
       end;
    try applys lc_at_to_open_trm_val_def_defs;
    eauto.
  - apply lc_defs_has in H1... inversion H1...
    applys lc_at_to_open_trm_val_def_defs...
  - eapply lc_at_relaxing_trm_val_def_defs; try eassumption.
    omega.
  - inversion H4. pick_fresh x.
    assert (x \notin L); auto.
    assert (lc_ec (e & x ~ v)); auto.
    specialize (H1 x H3 H6).
    applys open_to_lc_at_trm_val_def_defs. eassumption.
Qed.

(** The next two lemmas show that if [t^x] is in normal form, then [t] is in normal form. *)
Lemma open_rec_preserve_normal_form: forall k x t,
    x \notin fv_trm t ->
    normal_form (open_rec_trm k x t) ->
    normal_form t.
Proof.
  intros. generalize dependent x.
  generalize dependent k.
  induction t; auto; intros;
    try solve [
    unfold open_trm in H0; unfold open_rec_trm in H0;
    inversion H0].
  unfold open_trm in H0. unfold open_rec_trm in H0.
  inversion H0. fold open_rec_trm in *.
  unfold fv_trm in H. fold fv_trm in H.
  assert (x \notin fv_trm t2); auto.
  specialize (IHt2 _ _ H4 H2).

  destruct t1; simpl; inversion H1.
  constructor. auto.
Qed.

(** See previous lemma [open_rec_preserve_normal_form]. *)
Lemma open_preserve_normal_form : forall x t,
    x \notin fv_trm t ->
    normal_form (open_trm x t) ->
    normal_form t.
Proof.
  apply open_rec_preserve_normal_form.
Qed.

(** [x] fresh                            #<br>#
    [e] and [v] are locally closed       #<br>#
    [(e, x=v)[t^x] |-> (e, x=v)[t']]     #<br>#
    [――――――――――――――――――――――――――――――――――] #<br>#
    [exists f. x \notin fv(f) and t' = f^x    *)
Lemma open_rec_eval_to_open_rec : forall e x t t' v,
    x \notin dom e \u fv_trm t \u fv_val v ->
    lc_ec e -> lc_val v ->
    e & x ~ v[ open_trm x t |-> t'] ->
    exists f, (x \notin (fv_trm f)) /\ t' = open_trm x f.
Proof.
  intros. exists (close_trm x t'). remember (close_trm x t') as ct. split.
  - subst ct. apply close_rec_trm_val_def_defs_no_capture.
  - symmetry. rewrite Heqct. apply open_left_inverse_close_trm_val_def_defs.
    eauto using lc_env_eval_to_lc_trm, lc_ec_cons.
Qed.

(** Substitution for reduction *)

(** [x, y] fresh                                                  #<br>#
    [(e1, x=v, e2)[t1] |-> (e1, x=v, e2)[t2]]                     #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――――――――――――――] #<br>#
    [(e1, y=v[y/x], e2)[t1[y/x]] |-> (e1, y=v[y/x], e2)[t2[y/x]]] *)
Lemma eval_renaming_subst : forall x y e1 e2 v t1 t2,
    x \notin dom e1 \u fv_ec_vals e1 \u dom e2 ->
    y \notin dom e1 \u fv_ec_vals e1
      \u dom e2 \u fv_ec_vals e2 \u fv_val v \u fv_trm t1 ->
    (e1 & x ~ v & e2)[t1 |-> t2] ->
    (e1 & y ~ subst_val x y v & subst_env x y e2)[subst_trm x y t1 |-> subst_trm x y t2].
Proof.
  Local Hint Resolve binds_subst_env.

  Local Ltac contra_bind :=
    repeat match goal with
           | [ H : _ \notin _ \u _ |- _ ] => apply notin_union in H; destruct H
           end;
    match goal with
    | [ _ : ?x \notin dom ?e, _ : binds ?x _ ?e |- _ ] =>
      exfalso; eapply binds_fresh_inv; [eassumption | auto 1]
    end.

  Local Ltac solve_left_most :=
    apply binds_concat_left; unfold subst_env; try rewrite dom_map;
    try rewrite (proj1 (proj2 (subst_fresh_trm_val_def_defs _ _))); auto;
    eapply binds_fv_ec_vals; eauto 2.

  introv Hfx Hfy He. dependent induction He; simpls.
  - apply binds_middle_inv in H0; destruct_all; case_if; subst;
      try contra_bind;
      rewrite subst_open_commut_trm; unfold subst_fvar; case_if;
        apply red_apply with (subst_typ x y T);
          assert (Hs : val_lambda (subst_typ x y T) (subst_trm x y t) =
                       subst_val x y (val_lambda T t)) by auto;
          auto 2;
          rewrite Hs;
          try match goal with
              | [ |- binds ?y _ (_ & ?y ~ _ & _) ] =>
                apply binds_middle_eq; unfold subst_env; rewrite dom_map; auto 1
              end;
          try solve [apply binds_concat_right, binds_subst_env; trivial];
          solve_left_most.
  - apply binds_middle_inv in H0; destruct_all; case_if; subst;
      try contra_bind;
      apply red_project with (T:=subst_typ x y T) (ds:=subst_defs x y ds); auto 1;
        assert (Hs : val_new (subst_typ x y T) (subst_defs x y ds) = subst_val x y (val_new T ds));
        auto 2;
        try rewrite Hs.
    + apply binds_concat_right; apply binds_subst_env; trivial.
    + apply open_subst_defs; auto.
    + apply binds_middle_eq; unfold subst_env; rewrite dom_map; auto.
    + apply open_subst_defs2; auto.
    + solve_left_most.
    + apply open_subst_defs; auto.
  - case_if; simpls;
      subst; rewrite subst_open_commut_trm; unfold subst_fvar;
        case_if; constructor;
          inversion H; constructor; auto;
            apply lc_at_subst_trm_val_def_defs; trivial.
  - inversion H. inversion H2.
    repeat constructor; auto;
      apply lc_at_subst_trm_val_def_defs; trivial.
  - inversion H.
    repeat constructor; auto;
      apply lc_at_subst_trm_val_def_defs; trivial.
  - econstructor.
    + inversion H. inversion H4.
      repeat constructor;
        apply lc_at_subst_trm_val_def_defs; trivial.
    + intros.
      instantiate (1 := L \u dom e1 \u fv_ec_vals e1 \u dom e2 \u fv_ec_vals e2
                            \u fv_val v \u fv_val v0 \u fv_trm t \u \{x} \u \{y}) in H2.

      assert (x0 <> x) by auto.
      assert (x0 <> y) by auto.

      assert (subst_fvar x y x0 = x0). {
        unfold subst_fvar. case_if; auto.
      }
      rewrite <- H5.
      rewrite <- subst_open_commut_trm. rewrite <- subst_open_commut_trm.
      rewrite H5.

      assert (x0 \notin L) by auto.
      specialize (H1 _ H6 v (e2 & x0 ~ v0) e1).

      assert (y \notin fv_trm (open_trm x0 t)). {
        apply open_fv_trm_val_def_defs; auto.
      }
      assert (y \notin fv_ec_vals (e2 & x0 ~ v0)) by rewrite~ fv_ec_vals_push_eq.

      assert (y \notin dom e1 \u fv_ec_vals e1
                \u dom (e2 & x0 ~ v0) \u fv_ec_vals (e2 & x0 ~ v0)
                \u fv_val v \u fv_trm (open_trm x0 t)); auto.

      assert (x \notin dom e1 \u fv_ec_vals e1 \u dom (e2 & x0 ~ v0)); auto.

      assert (subst_env x y (e2 & x0 ~ v0) = subst_env x y e2 & x0 ~ subst_val x y v0). {
        unfold subst_env. apply map_push.
      }
      specialize (H1 H9 _ H10).
      rewrite H11 in H1.
      rewrite? concat_assoc in H1.
      apply H1. auto.
Qed.
