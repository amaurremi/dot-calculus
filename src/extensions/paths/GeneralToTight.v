(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Sequences.
Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        Replacement ReplacementTyping.

Lemma pt2_dec_typ_tight: forall G p A S U,
    inert G ->
    G ⊢!! p: typ_rcd {A >: S <: U} ->
    S = U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pf_dec_typ_tight.
Qed.

Lemma pt3_dec_typ_tight: forall G p A S U,
    inert G ->
    G ⊢!!! p: typ_rcd {A >: S <: U} ->
    S = U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pt2_dec_typ_tight.
Qed.

(** * Sel-<: Premise
    This lemma corresponds to Lemma 3.5 in the paper.

    [inert G]                    #<br>#
    [G |-## x: {A: S..U}]        #<br>#
    [――――――――――――――――――――――――――――]   #<br>#
    [exists T. G |-## x: {A: T..T}]   #<br>#
    [G |-# T <: U]               #<br>#
    [G |-# S <: T]                    *)
Lemma sel_premise_inv: forall G p A S U,
  inert G ->
  G ⊢## p : typ_rcd {A >: S <: U} ->
  exists T,
    G ⊢!!! p : typ_rcd {A >: T <: T} /\
    G ⊢# T <: U /\
    G ⊢# S <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - lets Hp: (pt3_dec_typ_tight HG H). subst.
    exists U. split*.
  - specialize (IHHinv _ _ _ HG eq_refl).
    destruct IHHinv as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma sel_premise: forall G p A S U,
  inert G ->
  G ⊢// p : typ_rcd {A >: S <: U} ->
  exists T,
    G ⊢!!! p : typ_rcd {A >: T <: T} /\
    G ⊢# T <: U /\
    G ⊢# S <: T.
Proof.
  introv HG Hr. dependent induction Hr.
  apply* sel_premise_inv.
Qed.

(** * Sel-<: Replacement
    This lemma corresponds to Lemma 3.4 in the paper.

    [inert G]              #<br>#
    [G ⊢# x: {A: S..U}]   #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢# x.A <: U]       #<br>#
    [G ⊢# S <: x.A]            *)
Lemma sel_replacement: forall G p A S U,
    inert G ->
    G ⊢# trm_path p : typ_rcd {A >: S <: U} ->
    (G ⊢# p↓A <: U /\
     G ⊢# S <: p↓A).
Proof.
  introv Hi Hty.
  pose proof (replacement_closure Hi Hty) as Hinv.
  pose proof (sel_premise Hi Hinv) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

Lemma tight_to_prec_exists G p T :
  inert G ->
  G ⊢# trm_path p : T ->
  exists U, G ⊢!! p : U.
Proof.
  intros Hi Hp. pose proof (replacement_closure Hi Hp).
  apply repl_to_inv in H as [? ?]. apply inv_to_prec in H as [? ?]. apply* pt2_exists.
Qed.

Lemma sngl_replacement: forall G p q n T U S,
    inert G ->
    G ⊢# trm_path p: {{ q }} ->
    G ⊢# trm_path q : S ->
    repl_typ n p q T U ->
    G ⊢# T <: U /\ G ⊢# U <: T.
Proof.
  introv Hi Hp Hr.
  apply (tight_to_prec_exists Hi) in Hr as [V Hq].
  lets Hc: (replacement_closure Hi Hp).
  pose proof (repl_to_invertible_sngl Hi Hc Hq) as [r [W [Hpt [Hq' [-> | Hpq]]]]];
    pose proof (inv_to_precise_sngl Hi Hpt (pt3 Hq')) as [r' [Ht [-> | Hrc']]].
  - split. eauto. apply repl_swap in H. eauto.
  - split.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      eapply subtyp_sngl_pq_t. eapply pt3_sngl_trans3. apply Ht. eauto. eauto. eauto.
    + destruct (repl_insert r' H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      * apply repl_swap in Hr2. eauto.
      * apply repl_swap in Hr1. eauto.
  - split.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X); eauto.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      apply repl_swap in Hr2. eauto. apply repl_swap in Hr1. eauto.
  - split.
    + destruct (repl_insert r' H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      * eauto.
      * destruct (repl_insert r Hr2) as [S' [Hr1' Hr2']].
        apply subtyp_trans_t with (T:=S'); eauto.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      * apply repl_swap in Hr2. eauto.
      * destruct (repl_insert r' Hr1) as [S' [Hr1' Hr2']].
        apply subtyp_trans_t with (T:=S').
        ** apply repl_swap in Hr2'. eauto.
        ** apply repl_swap in Hr1'. eauto.
Qed.

(** * General to Tight [⊢ to ⊢#] *)
(** The following lemma corresponds to Theorem 3.3 in the paper.
    It says that in an inert environment, general typing ([ty_trm] [⊢]) can
    be reduced to tight typing ([ty_trm_t] [⊢#]).
    The proof is by mutual induction on the typing and subtyping judgements.

    [inert G]           #<br>#
    [G ⊢ t: T]          #<br>#
    [――――――――――――――]    #<br>#
    [G ⊢# t: T] #<br># #<br>#

    and                 #<br># #<br>#
    [inert G]           #<br>#
    [G ⊢ S <: U]        #<br>#
    [――――――――――――――――]  #<br>#
    [G ⊢# S <: U]         *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G t T,
     G ⊢ t : T ->
     G = G0 ->
     G ⊢# t : T) /\
  (forall G S U,
     G ⊢ S <: U ->
     G = G0 ->
     G ⊢# S <: U).
Proof.
  intros G0 Hi.
  apply ts_mutind; intros; subst;
    try solve [eapply sel_replacement; auto]; eauto.
  - destruct* (sngl_replacement Hi (H eq_refl) (H0 eq_refl) r).
  - apply repl_swap in r. destruct* (sngl_replacement Hi (H eq_refl) (H0 eq_refl) r).
Qed.

(** The general-to-tight lemma, formulated for term typing. *)
Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G ⊢ t : T ->
  G ⊢# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.

Ltac proof_recipe :=
  match goal with
  | [ Hg: ?G ⊢ _ : _,
      Hi: inert ?G |- _ ] =>
    apply (general_to_tight_typing Hi) in Hg;
    ((apply (replacement_closure Hi) in Hg) || (apply (replacement_closure_v Hi) in Hg));
    try lets Hok: (inert_ok Hi);
    try match goal with
        | [ Hr: ?G ⊢// _ : ∀(_) _,
            Hok: ok ?G |- _ ] =>
          destruct (repl_to_precise_typ_all Hi Hr) as [Spr [Tpr [Lpr [Hpr [Hspr1 Hspr2]]]]]
        | [ Hr: ?G ⊢// _ : {{ ?q }},
            Hq: ?G ⊢!! ?q : _ |- _ ] =>
          destruct (repl_to_precise_sngl Hi Hr Hq) as [q2 [q3 [Hpq3 [[-> | Hqq2] [-> | Hq3q2]]]]]
        | [ Hrv: ?G ⊢//v _ : μ _ |- _ ] =>
          apply (repl_to_invertible_obj Hi) in Hrv as [U' [Hrv Hrc]];
          apply (invertible_to_precise_obj Hi) in Hrv as [U'' [Hrv Hrc']];
          try match goal with
              | [ Hv: _ ⊢!v val_new ?T _ : μ ?U |- _ ] =>
                assert (T = U) as <- by (inversion Hv; subst*)
              end
        | [ Hrv: ?G ⊢//v _ : ∀(_) _ |- _ ] =>
          inversions Hrv;
          match goal with
          | [ Hrv: ?G ⊢##v _ : ∀(_) _,
              Hok: ok ?G |- _ ] =>
            apply invertible_val_to_precise_lambda in Hrv as [L1 [S1 [T1 [Hvpr [HS1 HS2]]]]]; auto
          end
       end
  end.
