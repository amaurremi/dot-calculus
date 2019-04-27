(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Replacement (Introduction-qp) Typing *)

(** This module contains lemmas related to replacement typing
    ([|-//] and [|-//v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Sequences.
Require Import Definitions Binding InvertibleTyping Narrowing PreciseTyping
        RecordAndInertTypes Replacement Subenvironments TightTyping Weakening.

(** Whereas invertible typing does replacement for singleton types in one direction,
    replacement typing does the replacment in the other direction.

    Note that we can't simply define this using three rules:
    1) identity from invertible typing
    2) two repl subtyping rules
    The reason is that if we did that, repl typing would necessarily apply the replacement
    in all subterms of a term, whereas we want to be able to say, for example:
    [Г ⊢## p: T] #<br>#
    [Г ⊢// p: U] #<br>#
    [__________] #<br>#
    [Г ⊢// p: T ∧ U] #<br>#
 *)

(** ** Replacement Typing for Paths *)

Reserved Notation "G '⊢//' p ':' T" (at level 40, p at level 59).

Inductive ty_repl : ctx -> path -> typ -> Prop :=

(** [G ⊢## p: T]     #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢// p: T]     *)
| ty_inv_r : forall G p T,
    G ⊢## p: T ->
    G ⊢// p: T

(** [G ⊢// p : T]     #<br>#
    [G ⊢// p : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢// p : T /\ U]      *)
| ty_and_r : forall G p T U,
    G ⊢// p: T ->
    G ⊢// p: U ->
    G ⊢// p: T ∧ U

(** [G ⊢## p : T^p]  #<br>#
    [――――――――――――――] #<br>#
    [G ⊢## p : μ(T)]      *)
| ty_bnd_r : forall G p T,
    G ⊢// p: open_typ_p p T ->
    G ⊢// p: μ T

(** [G ⊢// p : T]             #<br>#
    [G ⊢! q: _ ⪼ {A: T..T}]  #<br>#
    [―――――――――――――――――――――――] #<br>#
    [G ⊢//p : q.A]      *)
| ty_sel_r : forall G p T q S A,
    G ⊢// p: T ->
    G ⊢! q: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢// p: q↓A

(** [G ⊢// p.a: T]    #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢// p: {a: T}]     *)
| ty_rcd_intro_r : forall G p a T,
    G ⊢// p•a : T ->
    G ⊢// p : typ_rcd { a ⦂ T }

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: μ(T)]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: μ(T[q/p,n])]      *)
| ty_rec_qp_r : forall G p q r T T' n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢// r : μ T ->
    repl_typ n q p T T' ->
    G ⊢// r : μ T'

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: r'.A]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: (r'.A)[q/p,n]]      *)
| ty_sel_qp_r : forall G p q r r' r'' A n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢// r : r'↓A ->
    repl_typ n q p (r'↓A) (r''↓A) ->
    G ⊢// r : r''↓A

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: r'.type]          #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: (r'.type)[q/p,n]]      *)
| ty_sngl_qp_r : forall G p q r r' r'' n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢// r : {{ r' }} ->
    repl_typ n q p {{ r'}} {{ r'' }} ->
    G ⊢// r : {{ r'' }}

where "G '⊢//' p ':' T" := (ty_repl G p T).

Hint Constructors ty_repl.

(** *** From Replacement To Precise Typing *)

(** Replacement-to-precise typing for function types:
    if [G ⊢// p: forall(S)T] then
    - [exists S', T'. G ⊢!!! p: forall(S')T'],
    - [G ⊢# S <: S'], and
    - [G ⊢# T'^y <: T^y],
    where [y] is fresh. *)
Lemma repl_to_precise_typ_all: forall G p S T,
  inert G ->
  G ⊢// p : ∀(S) T ->
  exists S' T' L,
    G ⊢!!! p : ∀(S') T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hp. inversions Hp. apply* invertible_to_precise_typ_all.
Qed.

(** Replacement-to-precise typing for records:
    if [G |-// p: {A: S..U}] then
    - [exists T. G |-// p: {A: T..T}],
    - [G |-# T <: U], and
    - [G |-# S <: T] *)
Lemma repl_to_precise_rcd: forall G p A S U,
  inert G ->
  G ⊢// p : typ_rcd {A >: S <: U} ->
  exists T,
    G ⊢!!! p : typ_rcd {A >: T <: T} /\
    G ⊢# T <: U /\
    G ⊢# S <: T.
Proof.
  introv HG Hr. dependent induction Hr.
  apply* invertible_to_precise_rcd.
Qed.

(** *** Properties of replacement typing *)

Lemma repl_and: forall G p T U,
    inert G ->
    G ⊢// p: T ∧ U ->
    G ⊢// p: T /\ G ⊢// p: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct (invertible_and Hi H). split*.
Qed.

(** Replacement typing is closed under [qp] replacement
    when we know [q]'s precise type *)
Lemma replacement_repl_closure_qp : forall G p q r T T' n U,
    inert G ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ n r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr Hp.
  gen q r T' n U. induction Hp; introv Hq; introv Hr' Hr; try solve [invert_repl; eauto 5].
  - Case "ty_inv_r"%string.
    gen q r T' n U. induction H; introv Hq; introv Hr; introv Hr'; try solve [invert_repl; eauto 5].
    -- SCase "ty_precise_inv"%string.
       destruct (pt3_inertsngl Hi H) as [[Hit | Hs] | Hst].
       + SSCase "ty_precise_inv_1"%string.
         inversions Hit; invert_repl.
         ++ apply ty_inv_r. eapply ty_all_inv with (L := \{}).
            apply* ty_precise_inv. apply repl_swap in H6.
            eauto. introv Hy. auto.
         ++ apply ty_inv_r.
            eapply ty_all_inv with (L := dom G).
            apply* ty_precise_inv. auto. introv Hy.
            eapply repl_open_var in H6; try solve_names.
            eapply subtyp_sngl_qp. apply* weaken_ty_trm.
            eapply precise_to_general. apply Hq. apply* weaken_ty_trm. apply* precise_to_general2. apply H6.
         ++ apply* ty_rec_qp_r.
       + SSCase "ty_precise_inv_2"%string.
         inversions Hs. invert_repl. eauto.
       + SSCase "ty_precise_inv_3"%string.
         inversion Hst as [x Hx].
         generalize dependent T'.
         dependent induction Hx; introv Hr; subst; invert_repl.
         ++ apply ty_inv_r. destruct D2.
            * invert_repl; apply ty_precise_inv in H;
              eapply ty_dec_typ_inv; eauto.
              assert (Hts : G ⊢# t0 <: T1).
              { apply repl_swap in H7. eauto. }
              eauto.
            * invert_repl. eapply ty_precise_inv in H.
              eapply ty_dec_trm_inv; eauto.
        ++ assert (Hpt0 : G ⊢!!! p : T) by (eapply pt3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pt3_and_destruct2; eauto).
           apply* ty_and_r.
        ++ assert (Hpt0 : G ⊢!!! p : T) by (eapply pt3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pt3_and_destruct2; eauto).
          apply ty_and_r; eauto. apply ty_inv_r.
          destruct D2; invert_repl;
          apply ty_precise_inv in Hpd.
          * eapply ty_dec_typ_inv; eauto.
            apply repl_swap in H8. eauto.
          * eapply ty_dec_typ_inv; eauto.
          * eapply ty_dec_trm_inv; eauto.
    -- SCase "ty_dec_trm_inv"%string.
       invert_repl. eapply ty_inv_r. eapply ty_dec_trm_inv.
       apply H. apply subtyp_trans_t with (T:=U); eauto.
    -- SCase "ty_dec_typ_inv"%string.
       invert_repl.
         * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
           eapply subtyp_trans_t. apply repl_swap in H10.
           eapply subtyp_sngl_pq_t. eauto. eauto.
           apply H10. auto. auto.
         * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
           eauto. eapply subtyp_trans_t. apply H1. eauto.
    -- SCase "ty_all_inv"%string.
       invert_repl; apply ty_inv_r.
       + eapply ty_all_inv with (L := L \u (dom G)).
         * apply H.
         * assert (Hts : G ⊢# T3 <: S2).
           { apply repl_swap in H8. eauto. }
           eauto.
         * introv Hy. eapply narrow_subtyping.
           apply H1. eauto.
           assert (Hts : G ⊢ T3 <: S2).
           { apply tight_to_general.
           apply repl_swap in H8. eauto. }
           constructor; eauto.
       + eapply ty_all_inv with (L := L \u (dom G)).
         * eauto.
         * assumption.
         * introv Hy. eapply subtyp_trans.
           apply* H1. eapply repl_open_var in H8.
           ** eapply subtyp_sngl_qp.
              apply precise_to_general in Hq.
              apply weaken_ty_trm. apply Hq. eauto.
              apply weaken_ty_trm. apply* precise_to_general2. eauto.
              eauto.
           ** solve_names.
           ** apply precise_to_general_h in Hq as [Hq].
              eapply typed_paths_named. apply Hq.
    -- SCase "ty_sel_qp_inv"%string.
       inversions Hr. eauto.
    -- SCase "ty_sngl_qp_inv"%string.
       inversions Hr. eauto.
  - Case "ty_sel_qp_r"%string.
    lets ?: (ty_sel_qp_r H H0 Hp H1). invert_repl. eauto.
  - Case "ty_sngl_qp_r"%string.
    lets ?: (ty_sngl_qp_r H H0 Hp H1). invert_repl. eauto.
Qed.

(** Replacement typing is closed under [qp] replacement
    when we know [q]'s II-level precise type *)
Lemma replacement_repl_closure_qp2 : forall G p q r T T' n U,
    inert G ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ n r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr' Hp Hr. gen U. dependent induction Hq; introv Hr'.
  - lets Heq: (pf_sngl_T Hi H). subst.
    apply* replacement_repl_closure_qp.
  - pose proof (repl_field_elim _ _ _ Hr) as Hr''.
    pose proof (pt2_backtrack _ _ Hr') as [U' Hq]. eauto.
Qed.

(** Replacement typing is closed under [qp] replacement
    when we know [q]'s III-level precise type *)
Lemma replacement_repl_closure_qp3 : forall G p q r T T' n U,
    inert G ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ n r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr' Hp Hr. gen p T T' U. dependent induction Hq; introv Hp; introv Hr; introv Hr'.
  - apply* replacement_repl_closure_qp2.
  - specialize (IHHq _ Hi eq_refl _ _ Hp).
    destruct (repl_insert q Hr) as [V [Hr1 Hr2]].
    pose proof (pt2_exists Hq) as [S Hs].
    specialize (IHHq _ Hr1 _ Hr'). eapply replacement_repl_closure_qp2.
    auto. apply H. apply Hs. apply IHHq. eauto.
Qed.

(** Replacement typing is closed under repeated [qp] replacements *)
Lemma replacement_repl_closure_qp_comp: forall G p q r T T' U,
    inert G ->
    G ⊢// p: T ->
    G ⊢!!! q: {{ r }} ->
    G ⊢!! r : U ->
    repl_repeat_typ r q T T' ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hq Hr Hc. gen p. dependent induction Hc; introv Hp; eauto.
  unfolds repl_some_typ. destruct_all.
  apply* IHHc. apply* replacement_repl_closure_qp3.
Qed.

(** Replacement typing is closed under opening of recursive types *)
Lemma repl_rec_intro: forall G p T,
    inert G ->
    G ⊢// p: μ T ->
    G ⊢// p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - Case "ty_inv_r"%string.
    destruct* (invertible_bnd Hi H) as [Hr | [q [U [Hr [[S Hs]%pt2_exists Hr']]]]].
    eapply replacement_repl_closure_qp_comp. auto. apply* ty_inv_r.
    apply Hr. eauto.
    apply* repl_comp_open.
  - Case "ty_rec_pq_r"%string.
    specialize (IHHp _ Hi eq_refl).
    apply repl_open with (r:= r) in H1; try solve_names. apply* replacement_repl_closure_qp.
Qed.

(** If [G ⊢// r: T[q1 / p1, n]], [G ⊢!!! p2: q2.type], and [n <> m], then
    [G ⊢// r: T[p2 / q2, m][q1 / p1, n]] *)
Lemma replacement_swap_closure: forall G r q1 p1 T T1 p2 q2 T2 T21 n m U,
    inert G ->
    repl_typ n p1 q1 T T1 ->
    G ⊢// r: T1 ->
    G ⊢! p2: {{ q2 }} ⪼ {{ q2 }} ->
    G ⊢!! q2 : U ->
    repl_typ m q2 p2 T T2 ->
    repl_typ n p1 q1 T2 T21 ->
    n <> m ->
    G ⊢// r: T21.
Proof.
  introv Hi HTT1 Hr1 Hp2 Hq2 HTT2 HT2T21 Hn.
  destruct (repl_preserved2 HTT1 HTT2 Hn) as [V HV].
  lets Hc: (replacement_repl_closure_qp Hi Hp2 Hq2 Hr1 HV).
  lets Heq: (repl_order_swap HTT1 HV Hn HTT2 HT2T21). subst*.
Qed.

(** Helper lemma to prove that replacement typing is closed under [pq] replacement *)
Lemma replacement_repl_closure_pq_helper : forall G r q1 p1 T T1 p2 q2 T2 n,
    inert G ->
    G ⊢// r: T ->
    G ⊢! p1: {{ q1 }} ⪼ {{ q1 }} ->
    G ⊢! p2: {{ q2 }} ⪼ {{ q2 }} ->
    repl_typ n q1 p1 T T1 ->
    repl_typ n p2 q2 T1 T2 ->
    G ⊢// r: T2.
Proof.
  introv Hi Hr Hp1 Hp2 Hr1 Hr2.
  destruct (repl_prefixes Hr1 Hr2) as [bs [Heq | Heq]].
  - subst. assert (bs = nil) as Heq by apply* pf_sngl_flds_elim. subst.
    rewrite field_sel_nil in *.
    lets Hu: (pf_T_unique Hi Hp1 Hp2). inversions Hu. apply repl_swap in Hr1.
    lets Heq: (repl_unique Hr1 Hr2). subst*.
  - subst. assert (bs = nil) as Heq. {
      eapply pf_sngl_flds_elim. apply Hi. apply Hp1. apply Hp2.
    }
    subst. rewrite field_sel_nil in *.
    lets Hu: (pf_T_unique Hi Hp1 Hp2). inversions Hu.
    apply repl_swap in Hr1.
    lets Heq: (repl_unique Hr1 Hr2). subst*.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s precise type *)
Lemma replacement_repl_closure_pq : forall G p q r n T T' U,
    inert G ->
    G ⊢// p : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hqr.
  gen q r n T' U. induction Hp; introv Hq; introv Hr' Hr; eauto.
   - Case "ty_inv_r"%string.
     constructor. apply* invertible_repl_closure.
   - Case "ty_and_r"%string.
     invert_repl; eauto.
   - Case "ty_bnd_r"%string.
     invert_repl. apply (repl_open p) in H3; try solve_names. eauto.
   - Case "ty_sel_r"%string.
     clear IHHp. invert_repl. lets Heq: (pf_sngl_flds_elim _ Hi Hq H). subst.
     rewrite field_sel_nil in *.
     lets Heq: (pf_T_unique Hi H Hq). subst.
     apply pf_sngl_U in H. inversion H.
   - Case "ty_rcd_intro_r"%string. invert_repl. eauto.
   - Case "ty_rec_qp_r"%string.
     invert_repl. specialize (IHHp Hi _ _ Hq).
     destruct (classicT (n=n0)) as [-> | Hn].
     * apply* (replacement_repl_closure_pq_helper Hi Hp H Hq (rbnd H1) (rbnd H6)).
     * destruct (repl_preserved1 H1 H6 Hn) as [V Hv]. apply rbnd in Hv.
       specialize (IHHp _ _ _ Hr' Hv).
       eapply (replacement_swap_closure Hi Hv IHHp H); eauto.
   - Case "ty_sel_pq_r"%string.
     assert (n0 = 0) as -> by inversion* Hr. assert (n = 0) as -> by inversion* H1.
     eapply (replacement_repl_closure_pq_helper Hi Hp H Hq); eauto.
   - Case "ty_sngl_pq_r"%string.
     assert (n0 = 0) as -> by inversion* Hr. assert (n = 0) as -> by inversion* H1.
     eapply (replacement_repl_closure_pq_helper Hi Hp H Hq); eauto.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s II-level precise type *)
Lemma replacement_repl_closure_pq2 : forall G p q r T T' n U,
    inert G ->
    G ⊢// p : T ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hr' Hr. gen U. dependent induction Hq; introv Hr'.
  - apply* replacement_repl_closure_pq. lets Heq: (pf_sngl_T Hi H). subst. auto.
  - pose proof (repl_field_elim _ _ _ Hr).
    pose proof (pt2_backtrack _ _ Hr') as [U' Hq'].
    specialize (IHHq1 _ Hi Hp eq_refl H _ Hq').
    eauto.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s III-level precise type *)
Lemma replacement_repl_closure_pq3 : forall G p q r T T' n U,
    inert G ->
    G ⊢// p : T ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hr. gen p T U. dependent induction Hq; introv Hp; introv Hr' Hr.
  - apply* replacement_repl_closure_pq2.
  - destruct (repl_insert q Hr) as [U' [Hr1 Hr2]].
    pose proof (pt2_exists Hq) as [S Hq'].
    lets Hc: (replacement_repl_closure_pq2 Hi Hp H Hq' Hr1). apply* IHHq.
Qed.

(** Replacement typing is closed under repeated [pq] replacement *)
Lemma replacement_repl_closure_pq_comp: forall G p q r T T' U,
    inert G ->
    G ⊢// p: T ->
    G ⊢!!! q: {{ r }} ->
    G ⊢!! r : U ->
    repl_repeat_typ q r T T' ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hq Hr Hc. gen p. dependent induction Hc; introv Hp; eauto.
  unfolds repl_some_typ. destruct_all.
  apply* IHHc. apply* replacement_repl_closure_pq3.
Qed.

(** Replacement typing is closed under [<:-Sel] subtyping when
    we know that a path's II-level precise type has a type member *)
Lemma path_sel_repl2: forall G p A T q,
    inert G ->
    G ⊢!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : T ->
    G ⊢// q : p ↓ A.
Proof.
  introv Hi Hp Hq. dependent induction Hp; eauto.
Qed.

(** Replacement typing is closed under [<:-Sel] subtyping when
    we know that a path's III-level precise type has a type member *)
Lemma path_sel_repl: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : T ->
    G ⊢// q : p ↓ A.
Proof.
  introv Hi Hp Hq. dependent induction Hp; eauto.
  apply* path_sel_repl2.
  specialize (IHHp _ _ Hi eq_refl Hq).
  assert (forall q, q = q •• nil) as Hnil. {
    intro. rewrite* field_sel_nil.
  }
  lets He1: (Hnil q0). lets He2: (Hnil p).
  pose proof (pt2_exists Hp) as [U Hp0].
  eapply (replacement_repl_closure_qp2 Hi H Hp0 IHHp).
  rewrite He1 at 2. rewrite He2 at 2. apply rpath.
Qed.

(** Replacement typing is closed under [Sel-<:] subtyping *)
Lemma path_sel_repl_inv: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : p ↓ A ->
    G ⊢// q : T.
Proof.
  introv Hi Hp Hq. dependent induction Hq.
  - Case "ty_inv_r"%string.
    constructor. apply* path_sel_inv.
  - Case "ty_sel_r"%string.
    clear IHHq. lets Heq: (pf_pt3_unique Hi H Hp). subst*.
  - Case "ty_sel_qp_r"%string.
    destruct (repl_prefixes_sel H1) as [bs [He1 He2]].
    subst. assert (record_type (typ_rcd {A >: T <: T})) as Hrt by eauto.
    lets Hqbs: (pf_pt3_trans_inv_mult' _ Hi H Hp (or_intror Hrt)). apply* IHHq.
Qed.

(** If a path has a replacement type it has also an invertible type *)
Lemma repl_to_inv G p T :
  G ⊢// p : T ->
  exists U, G ⊢## p : U.
Proof.
  induction 1; eauto. destruct IHty_repl as [U Hp].
  clear H. apply ty_rcd_intro_inv in Hp. eauto.
Qed.

(** Replacement typing is closed under ⊤-subtyping *)
Lemma repl_top: forall G r T,
    G ⊢// r: T ->
    G ⊢// r: ⊤.
Proof.
  introv Hr. apply repl_to_inv in Hr as [? ?]. constructor*.
Qed.

(** Replacement typing is closed under tight subtyping *)
Lemma replacement_subtyping_closure : forall G T U p,
    inert G ->
    G ⊢# T <: U ->
    G ⊢// p: T ->
    G ⊢// p: U.
Proof.
  introv Hi Hs. gen p. induction Hs; introv Hp; auto.
  - Case "subtyp_top"%string.
    apply* repl_top.
  - Case  "subtyp_bot"%string.
    inversions Hp. false* invertible_bot.
  - Case "subtyp_and1"%string.
    apply (repl_and Hi) in Hp. destruct_all. auto.
  - Case "subtyp_and2"%string.
    apply (repl_and Hi) in Hp. destruct_all. auto.
  - Case "subtyp_fld"%string.
    dependent induction Hp; eauto.
  - Case "subtyp_typ"%string.
    dependent induction Hp; eauto.
  - Case "subtyp_sngl_pq"%string.
    pose proof (pt2_exists H0) as [? ?].
    apply* replacement_repl_closure_pq3.
  - Case "subtyp_sngl_qp"%string.
    pose proof (pt2_exists H0) as [? ?].
    apply* replacement_repl_closure_qp3.
  - Case "subtyp_sel2"%string.
    apply* path_sel_repl.
  - Case "subtyp_sel1"%string.
    apply* path_sel_repl_inv.
  - Case "subtyp_all"%string.
    dependent induction Hp; eauto.
Qed.

(** If a path has a replacement type it also has a III-level precise type *)
Lemma repl_prec_exists: forall G p T,
    G ⊢// p: T ->
    exists U, G ⊢!!! p: U.
Proof.
  introv Hp. apply repl_to_inv in Hp as [? Hp].
  induction Hp; eauto. apply* inv_to_prec.
Qed.

(** Replacement is closed under field selection on paths *)
Lemma repl_fld : forall G p a T,
    inert G ->
    G ⊢// p: typ_rcd {a ⦂ T} ->
    G ⊢// p•a : T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  dependent induction H; eauto.
  - dependent induction H.
    * dependent induction H; eauto.
      apply pf_fld in H; apply ty_inv_r; apply* ty_precise_inv.
    * lets Hq: (pt3_field_elim H0).
      lets Hp: (pt3_trans _ H Hq). eauto.
  - specialize (IHty_path_inv _ _ eq_refl Hi). apply ty_inv_r in H.
    eapply replacement_subtyping_closure. auto. apply H0. auto.
Qed.

(** If [G ⊢// p: T] and [T] and [T'] are equivalent then [G ⊢// p: T'] *)
Lemma replacement_repl_closure_comp_typed: forall G p T T',
    inert G ->
    G ⊢// p: T ->
    G ⊢ T' ⟿ T ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  destruct H as [p' [q' [n [S [Hpq [Hq Hr']]]]]].
  lets Hrc: (replacement_repl_closure_qp Hi Hpq Hq Hp Hr'). eauto.
Qed.

(** From replacement typing of singleton types to invertible typing of singleton types *)
Lemma repl_to_invertible_sngl_repl_comp: forall G p q,
    inert G ->
    G ⊢// p: {{ q }} ->
    exists q', G ⊢ q ⟿' q' /\ G ⊢## p: {{ q' }}.
Proof.
  introv Hi Hp. dependent induction Hp.
  - Case "ty_inv_r"%string.
    exists q. split*. apply star_refl.
  - Case "ty_sngl_qp_r"%string.
    specialize (IHHp _ Hi eq_refl). destruct IHHp as [p' [Hr Hr']].
    eexists. split*. eapply star_trans. apply Hr.  apply star_one. repeat eexists; eauto.
Qed.

(** If a path [p] has type [q.type] under replacement typing and [q] is well-typed,
    then the invertible type of [p] has a singleton type [q'.type], and [q] and [q']
    are aliases. *)
Lemma repl_to_invertible_sngl: forall G p q U,
    inert G ->
    G ⊢// p: {{ q }} ->
    G ⊢!! q : U ->
    exists q' S, G ⊢## p: {{ q' }} /\ G ⊢!! q' : S /\ (q = q' \/ G ⊢!!! q: {{ q' }}).
Proof.
  introv Hi Hp Hq. gen U. dependent induction Hp; introv Hq.
  - repeat eexists; eauto.
  - invert_repl.
    pose proof (pf_pt2_trans_inv_mult _ Hi H Hq) as ->.
    pose proof (pt2_qbs_typed _ Hi H H0 Hq) as [S Hq'].
    specialize (IHHp _ Hi eq_refl _ Hq') as [q' [W [Hrq' [Hq'' [<- | Hqq']]]]]; repeat eexists; eauto.
Qed.

(** If [p]'s replacement type is [q.type] and [q] is well-typed, then
    [p.a]'s replacement type is [q.a.type] *)
Lemma path_elim_repl: forall G p q a T,
    inert G ->
    G ⊢// p: {{ q }} ->
    G ⊢// q•a : T ->
    G ⊢// p•a : {{ q•a }}.
Proof.
  introv Hi Hp Hq.
  destruct (repl_to_invertible_sngl_repl_comp Hi Hp) as [p' [Hc Hpi]].
  destruct (repl_comp_sngl_inv1 Hc) as [r Heq]. inversions Heq.
  destruct (inv_to_precise_sngl_repl_comp Hpi) as [r' [Hp' Hrc]].
  destruct (repl_prec_exists Hq) as [U Hq']. clear Hq.
  destruct (field_typing_comp1 _ Hi Hc Hq') as [T1 Hra].
  destruct (field_typing_comp2 _ Hi Hrc Hra) as[T2 Hr'a].
  lets Hper: (path_elim_prec _ Hi Hp' Hr'a).
  lets Hinv: (ty_precise_inv Hper).
  assert (G ⊢ r' • a ⟿' r • a) as Hr'
    by apply* repl_composition_fld_elim.
  assert (G ⊢ q • a ⟿' r • a) as Hr''
   by apply* repl_composition_fld_elim.
  lets Hic: (invertible_repl_closure_comp_typed Hi Hinv Hr').
  apply* replacement_repl_closure_comp_typed.
Qed.

(** Replacement typing is closed under singleton transitivity with a type [q.type]
    if [q] is typeable under invertible typing *)
Lemma inv_sngl_trans: forall G p q T,
    inert G ->
    G ⊢// p : {{ q }} ->
    G ⊢## q : T ->
    G ⊢// p : T.
Proof.
  introv Hi Hpq Hq. gen p. induction Hq; introv Hpq; eauto; try solve [apply* replacement_repl_closure_pq].
  - pose proof (pt2_exists H) as [U H'].
    destruct (repl_to_invertible_sngl Hi Hpq H') as [r [S [Hpr [Hq Hrc]]]].
    destruct (inv_to_precise_sngl Hi Hpr (pt3 Hq)) as [r' [Hpr' Hrc']]. clear Hpr Hpq H'.
    destruct Hrc, Hrc'; subst.
    * do 2 constructor. apply* pt3_sngl_trans3.
    * do 2 constructor. repeat apply* pt3_sngl_trans3.
    * lets Hpi: (pt3_invert Hi H H0). destruct_all; subst; auto.
      ** do 2 constructor. apply* pt3_sngl_trans3.
      ** apply ty_precise_inv in Hpr'. apply ty_inv_r in Hpr'.
         apply* replacement_repl_closure_qp3. apply* repl_intro_sngl.
    * lets Hpi: (pt3_invert Hi H H0). destruct_all; subst.
      ** do 2 constructor. do 2 apply* pt3_sngl_trans3.
      ** do 2 constructor. apply* pt3_sngl_trans3.
      ** apply ty_precise_inv in Hpr'. apply ty_inv_r in Hpr'.
         lets Hc: (replacement_repl_closure_pq3 Hi Hpr' H1 Hq (repl_intro_sngl r' r)).
         apply* replacement_repl_closure_qp3. apply* repl_intro_sngl.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_fld_t.
    apply H. auto.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_typ_t.
    apply H. apply H0. auto.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_all_t.
    apply H. apply H0. auto.
  - apply* repl_top.
  - pose proof (path_elim_repl _ Hi Hpq (ty_inv_r Hq)) as Hp0a. specialize (IHHq Hi _ Hp0a). eauto.
Qed.

(** Replacement typing is closed under singleton transitivity *)
Lemma repl_sngl_trans: forall G p q T,
    inert G ->
    G ⊢// p : {{ q }} ->
    G ⊢// q : T ->
    G ⊢// p : T.
Proof.
  introv Hi Hpq Hq. gen p. induction Hq; introv Hpq; eauto.
  - apply* inv_sngl_trans.
  - specialize (IHHq Hi _ Hpq). apply ty_bnd_r.
    pose proof (repl_to_inv Hq) as [_ [_ [U Hq']%pt2_exists]%inv_to_prec].
    destruct (repl_to_invertible_sngl Hi Hpq Hq') as [r [S [Hpr [Hs Hor]]]].
    destruct (inv_to_precise_sngl Hi Hpr (pt3 Hs)) as [r' [Hpr' Hor']]. clear Hpr Hpq.
    destruct Hor, Hor'; subst.
    * assert (repl_repeat_typ r p0 (open_typ_p r T) (open_typ_p p0 T)) as Hrr by apply* repl_comp_open_rec.
      apply* replacement_repl_closure_qp_comp.
    * assert (repl_repeat_typ r r' (open_typ_p r T) (open_typ_p r' T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_qp_comp Hi IHHq H0 Hs Hrr).
      apply pt2_exists in H0 as [? ?].
      eapply (replacement_repl_closure_qp_comp Hi Hc). apply Hpr'. eauto.
      apply* repl_comp_open_rec.
    * assert (repl_repeat_typ p r (open_typ_p p T) (open_typ_p r T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_pq_comp Hi IHHq H Hs Hrr).
      apply* replacement_repl_closure_qp_comp. apply* repl_comp_open_rec.
    * assert (repl_repeat_typ p r (open_typ_p p T) (open_typ_p r T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_pq_comp Hi IHHq H Hs Hrr).
      assert (repl_repeat_typ r r' (open_typ_p r T) (open_typ_p r' T)) as Hrr' by apply* repl_comp_open_rec.
      lets Hc': (replacement_repl_closure_qp_comp Hi Hc H0 Hs Hrr').
      pose proof (pt2_exists H0) as [? ?].
      eapply (replacement_repl_closure_qp_comp Hi). auto. apply Hc'. apply Hpr'. eauto. apply* repl_comp_open_rec.
  - pose proof (path_elim_repl _ Hi Hpq Hq) as Hp0a. specialize (IHHq Hi _ Hp0a). eauto.
Qed.

(** Tight typing implies replacement typing *)
Lemma replacement_closure : forall G p T,
  inert G ->
  G ⊢# trm_path p : T ->
  G ⊢// p: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  - Case "ty_var_t"%string.
    repeat econstructor; eauto.
  - Case "ty_new_elim_t"%string.
    apply* repl_fld.
  - Case "ty_sngl_t"%string.
    apply* repl_sngl_trans.
  - Case "ty_path_elim_t"%string.
    apply* path_elim_repl.
  - Case "ty_rec_elim_t"%string.
    specialize (IHHp _ Hi eq_refl). apply* repl_rec_intro.
  - Case "ty_sub_t"%string.
    specialize (IHHp _ Hi eq_refl).
    eapply replacement_subtyping_closure. auto. apply H. auto.
Qed.

(** ** Replacement typing for values

    The definition of replacement typing for values
    is similar to replacement typing for paths, but simpler. The same holds for
    its lemmas. To see the documentation for a replacement-typing-for-values lemma,
    please refer to its replacement-typing-for-paths version. *)

Reserved Notation "G '⊢//v' v ':' T" (at level 40, v at level 59).

Inductive ty_replv : ctx -> val -> typ -> Prop :=
| ty_inv_rv : forall G v T,
    G ⊢##v v: T ->
    G ⊢//v v: T
| ty_and_rv : forall G v T U,
    G ⊢//v v: T ->
    G ⊢//v v: U ->
    G ⊢//v v: T ∧ U
| ty_sel_rv : forall G v T q S A,
    G ⊢//v v: T ->
    G ⊢! q: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢//v v: q ↓ A
| ty_rec_qp_rv : forall G p q v T T' n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : μ T ->
    repl_typ n q p T T' ->
    G ⊢//v v : μ T'
| ty_sel_qp_rv : forall G p q v r' r'' A n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : r' ↓ A ->
    repl_typ n q p (r' ↓ A) (r'' ↓ A) ->
    G ⊢//v v : r''↓A
where "G '⊢//v' v ':' T" := (ty_replv G v T).

Hint Constructors ty_replv.

Lemma invertible_andv: forall G v T U,
    inert G ->
    G ⊢##v v: T ∧ U ->
    G ⊢##v v: T /\ G ⊢##v v: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. inversion H.
Qed.

Lemma repl_andv: forall G v T U,
    inert G ->
    G ⊢//v v: T ∧ U ->
    G ⊢//v v: T /\ G ⊢//v v: U.
Proof.
  introv Hi Hv. dependent induction Hv; eauto.
  destruct (invertible_andv Hi H). split*.
Qed.

Lemma replacement_repl_closure_qp_v G v p q T T' n U :
    inert G ->
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : T ->
    repl_typ n q p T T' ->
    G ⊢//v v : T'.
Proof.
  intros Hi Hpq Hq Hv.
  gen p q T' n U. induction Hv; introv Hpq; introv Hq Hr.
  - Case "ty_inv_rv"%string.
    gen p q T' n U. induction H; introv Hpq; introv Hr; introv Hq;
    try solve [invert_repl; eauto].
    -- destruct (pfv_inert H).
      + invert_repl.
        ++ eapply ty_inv_rv.
           eapply ty_all_invv with (L := \{}).
           eapply ty_precise_invv. apply H.
           apply repl_swap in H6.
           eauto.
           introv Hy. auto.
        ++ eapply ty_inv_rv.
           eapply ty_all_invv with (L := dom G).
           eapply ty_precise_invv. apply H.
           auto.
           introv Hy.
           eapply repl_open_var in H6; try solve_names.
           eapply subtyp_sngl_qp. apply* weaken_ty_trm.
           eapply precise_to_general. apply Hpq. apply weaken_ty_trm; auto. apply* precise_to_general2. apply H6.
      + invert_repl; eauto.
    -- invert_repl; apply ty_inv_rv.
       + eapply ty_all_invv with (L := L \u (dom G)).
         * apply H.
         * assert (Hts : G ⊢# T3 <: S2).
           { apply repl_swap in H8. eauto. }
           eauto.
         * introv Hy. eapply narrow_subtyping.
           apply H1. eauto.
           assert (Hts : G ⊢ T3 <: S2).
           { apply tight_to_general.
           apply repl_swap in H8. eauto. }
           constructor; eauto. (* narrowing *)
       + eapply ty_all_invv with (L := L \u (dom G)).
         * eauto.
         * assumption.
         * introv Hy. eapply subtyp_trans.
           apply* H1. eapply repl_open_var in H8.
           ** eapply subtyp_sngl_qp.
              apply precise_to_general in Hpq.
              apply weaken_ty_trm. apply Hpq. eauto.
              apply weaken_ty_trm; auto. apply* precise_to_general2. eauto.
           ** solve_names.
           ** solve_names.
  - Case "ty_and_rv"%string.
    invert_repl; eauto.
  - Case "ty_sel_rv"%string.
    invert_repl; eauto.
  - Case "ty_rec_qp_rv"%string.
    invert_repl; eauto.
  - Case "ty_sel_qp_rv"%string.
    lets ?: (ty_sel_qp_rv H H0 Hv H1).
    invert_repl; eauto.
Qed.

Lemma replacement_repl_closure_qp2_v : forall G p v r T T' n U,
    inert G ->
    G ⊢!! p : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢//v v : T ->
    repl_typ n r p T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hp Hr Hv Hrp. gen U. dependent induction Hp; introv Hr.
  - lets Heq: (pf_sngl_T Hi H). subst.
    apply* replacement_repl_closure_qp_v.
  - lets Hr': (repl_field_elim _ _ _ Hrp). pose proof (pt2_backtrack _ _ Hr) as [? Hq']. eauto.
Qed.

Lemma replacement_repl_closure_qp3_v : forall G v p r T T' n U,
    inert G ->
    G ⊢!!! p : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢//v v : T ->
    repl_typ n r p T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hp Hr Hv Hrp. gen v T T' U. dependent induction Hp; introv Hv; introv Hrp; introv Hr.
  - apply* replacement_repl_closure_qp2_v.
  - specialize (IHHp _ Hi eq_refl).
    destruct (repl_insert q Hrp) as [U' [Hr1 Hr2]].
    pose proof (pt2_exists Hp) as [W Hp'].
    specialize (IHHp _ _ Hv _ Hr1). eapply replacement_repl_closure_qp2_v.
    auto. eauto. eauto. apply* IHHp. eauto.
Qed.

Lemma replacement_swap_closure_v: forall G v q1 p1 T T1 p2 q2 T2 T21 n m U,
    inert G ->
    repl_typ n p1 q1 T T1 ->
    G ⊢//v v: T1 ->
    G ⊢! p2: {{ q2 }} ⪼ {{ q2 }} ->
    G ⊢!! q2 : U ->
    repl_typ m q2 p2 T T2 ->
    repl_typ n p1 q1 T2 T21 ->
    n <> m ->
    G ⊢//v v: T21.
Proof.
  introv Hi HTT1 Hr1 Hp2 Hq2 HTT2 HT2T21 Hn.
  destruct (repl_preserved2 HTT1 HTT2 Hn) as [V HV].
  lets Hc: (replacement_repl_closure_qp_v Hi Hp2 Hq2 Hr1 HV).
  lets Heq: (repl_order_swap HTT1 HV Hn HTT2 HT2T21). subst*.
Qed.

Lemma replacement_repl_closure_pq_v_helper : forall G v p1 q1 T T1 p2 q2 T2 n,
    inert G ->
    G ⊢//v v: T ->
    G ⊢! p1: {{ q1 }} ⪼ {{ q1 }} ->
    G ⊢! p2: {{ q2 }} ⪼ {{ q2 }} ->
    repl_typ n q1 p1 T T1 ->
    repl_typ n p2 q2 T1 T2 ->
    G ⊢//v v: T2.
Proof.
  introv Hi Hr Hp1 Hp2 Hr1 Hr2.
  destruct (repl_prefixes Hr1 Hr2) as [bs [Heq | Heq]].
  - subst. assert (bs = nil) as Heq by apply* pf_sngl_flds_elim. subst.
    rewrite field_sel_nil in *.
    lets Hu: (pf_T_unique Hi Hp1 Hp2). inversions Hu. apply repl_swap in Hr1.
    lets Heq: (repl_unique Hr1 Hr2). subst*.
  - subst. assert (bs = nil) as Heq. {
      eapply pf_sngl_flds_elim. apply Hi. apply Hp1. apply Hp2.
    }
    subst. rewrite field_sel_nil in *.
    lets Hu: (pf_T_unique Hi Hp1 Hp2). inversions Hu.
    apply repl_swap in Hr1.
    lets Heq: (repl_unique Hr1 Hr2). subst*.
Qed.

Lemma replacement_repl_closure_pq_v : forall G v q r n T T' U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hqr Hr'.
  gen q r n T' U. induction Hv; introv Hq; introv Hr' Hr; eauto.
   - Case "ty_inv_r"%string.
     constructor. apply* invertible_repl_closure_v.
   - Case "ty_and_r"%string.
     invert_repl; eauto.
   - Case "ty_sel_r"%string.
     clear IHHv. invert_repl. lets Heq: (pf_sngl_flds_elim _ Hi Hq H). subst.
     rewrite field_sel_nil in *.
     lets Heq: (pf_T_unique Hi H Hq). subst.
     apply pf_sngl_U in H. inversion H.
  - Case "ty_rec_qp_r"%string.
    invert_repl. specialize (IHHv Hi _ _ Hq).
    destruct (classicT (n=n0)).
    * subst. specialize (IHHv n0).
      apply* (replacement_repl_closure_pq_v_helper Hi Hv H Hq (rbnd H1) (rbnd H6)).
    * destruct (repl_preserved1 H1 H6 n1) as [V Hr]. apply rbnd in Hr.
      specialize (IHHv _ _ _ Hr' Hr).
      eapply (replacement_swap_closure_v Hi Hr IHHv H); eauto.
  - Case "ty_sel_pq_r"%string.
    specialize (IHHv Hi _ _ Hq 0).
    assert (n0 = 0) as Heq by inversion* Hr. assert (n = 0) as Heq' by inversion* H1. subst.
    eapply (replacement_repl_closure_pq_v_helper Hi Hv H Hq); eauto.
Qed.

Lemma replacement_repl_closure_pq2_v : forall G v q r T T' n U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hq Hr' Hr. gen U. dependent induction Hq; introv Hr'.
  - apply* replacement_repl_closure_pq_v.
    lets Heq: (pf_sngl_T Hi H). subst. auto.
  - lets Hr'': (repl_field_elim _ _ _ Hr). pose proof (pt2_backtrack _ _ Hr') as [? ?]. eauto.
Qed.

Lemma replacement_repl_closure_pq3_v : forall G v q r T T' n U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hq Hr Hr'. gen v T U. dependent induction Hq; introv Hv Hr; introv Hr'.
  - apply* replacement_repl_closure_pq2_v.
  - destruct (repl_insert q Hr) as [? [Hr1 Hr2]].
    pose proof (pt2_exists Hq) as [? Hq'].
    lets Hc: (replacement_repl_closure_pq2_v Hi Hv H Hq' Hr1). apply* IHHq.
Qed.

Lemma path_sel_repl2_v: forall G p A T v,
    inert G ->
    G ⊢!! p : typ_rcd {A >: T <: T} ->
    G ⊢//v v : T ->
    G ⊢//v v : p↓A.
Proof.
  introv Hi Hp Hv. dependent induction Hp; eauto.
Qed.

Lemma path_sel_repl_v: forall G p A T v,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢//v v : T ->
    G ⊢//v v : p↓A.
Proof.
  introv Hi Hp Hv. dependent induction Hp; eauto.
  apply* path_sel_repl2_v.
  specialize (IHHp _ _ Hi eq_refl Hv).
  assert (forall q, q = q •• nil) as Hnil. {
    intro. rewrite* field_sel_nil.
  }
  lets He1: (Hnil q). lets He2: (Hnil p).
  pose proof (pt2_exists Hp) as [? Hq].
  eapply (replacement_repl_closure_qp2_v Hi H Hq IHHp).
  rewrite He1 at 2. rewrite He2 at 2. apply rpath.
Qed.

Lemma path_sel_repl_inv_v: forall G p A T v,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢//v v : p↓A ->
    G ⊢//v v : T.
Proof.
  introv Hi Hp Hv. dependent induction Hv.
  - Case "ty_inv_r"%string.
    constructor. apply* path_sel_inv_v.
  - Case "ty_sel_r"%string.
    clear IHHv. lets Heq: (pf_pt3_unique Hi H Hp). subst*.
  - Case "ty_sel_qp_r"%string.
    destruct (repl_prefixes_sel H1) as [bs [He1 He2]].
    subst. assert (record_type (typ_rcd {A >: T <: T})) as Hrt by eauto.
    lets Hqbs: (pf_pt3_trans_inv_mult' _ Hi H Hp (or_intror Hrt)). apply* IHHv.
Qed.

Lemma invertible_typing_closure_tight_v: forall G v T U,
  inert G ->
  G ⊢//v v : T ->
  G ⊢# T <: U ->
  G ⊢//v v : U.
Proof.
  introv Hi HT Hsub.
  induction Hsub; auto.
  - dependent induction HT; eauto.
  - dependent induction HT. dependent induction H. inversion H.
  - destruct* (repl_andv Hi HT).
  - destruct* (repl_andv Hi HT).
  - dependent induction HT. dependent induction H. dependent induction H.
  - dependent induction HT. dependent induction H. dependent induction H.
  - pose proof (pt2_exists H0) as [? ?]. apply* replacement_repl_closure_pq3_v.
    (* repl closure for vals *)
  - pose proof (pt2_exists H0) as [? ?]. apply* replacement_repl_closure_qp3_v.
    (* repl closure for vals *)
  - apply* path_sel_repl_v.
  - apply* path_sel_repl_inv_v.
  - dependent induction HT. constructor*.
Qed.

Lemma replacement_closure_v : forall G v T,
    inert G ->
    G ⊢# trm_val v : T ->
    G ⊢//v v : T.
Proof.
  introv Hi Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hi eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.

Lemma repl_to_invertible_obj G U v :
  inert G ->
  G ⊢//v v : μ U ->
  exists U', G ⊢##v v : μ U' /\ G ⊢ U ⟿ U'.
Proof.
  intros Hi Hv. dependent induction Hv.
  - exists U. split*. constructor.
  - specialize (IHHv _ Hi eq_refl) as [U' [Hinv Hrc]].
    eexists. split.
    * eauto.
    * eapply star_trans. apply Hrc. apply star_one. econstructor. repeat eexists.
      apply H. eauto. eauto.
Qed.
