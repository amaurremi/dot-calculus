(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Sequences.
Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping Replacement.

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
    (G ⊢# typ_path p A <: U /\
     G ⊢# S <: typ_path p A).
Proof.
  introv HG Hty.
  pose proof (replacement_closure HG Hty) as Hinv.
  pose proof (sel_premise HG Hinv) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

(*Lemma sngl_premise_inv: forall G p q,
    inert G ->
    G ⊢## p: typ_sngl q ->
    exists r,
      G ⊢!!! p: typ_sngl r /\ G ⊢# typ_sngl q <: typ_sngl r.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  specialize (IHHp _ Hi eq_refl). destruct IHHp as [r'' [Hr' Hs]].
  exists r''. split. auto. eapply subtyp_trans_t. apply repl_swap in H0.
  eapply subtyp_sngl_qp_t. constructor. econstructor. apply H. eauto. eauto.
Qed.

Lemma sngl_premise: forall G p q,
    inert G ->
    G ⊢// p: typ_sngl q ->
    exists r,
      G ⊢!!! p: typ_sngl r /\ G ⊢# typ_sngl q <: typ_sngl r.
Proof.
  introv Hi Hp. dependent induction Hp.
  - apply* sngl_premise_inv.
  - specialize (IHHp _ Hi eq_refl). destruct IHHp as [r'' [Hr'' Hs]].
    exists r''. split. auto. eapply subtyp_trans_t.
    apply repl_swap in H0. eapply subtyp_sngl_pq_t. constructor.
    econstructor. apply H. eauto. eauto.
Qed.*)

Lemma sngl_typed : forall G p q,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    exists T, G ⊢! q: T ⪼ T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto; try solve [apply pf_sngl_U in Hp; inversion Hp].
  - apply binds_inert in H0. inversion H0. auto.
  - destruct (pf_bnd_T2 Hi Hp) as [U Heq]. subst. destruct (pf_rec_rcd_U Hi Hp).
    * inversion H.
    * inversions H. inversions H0. admit.
      (* here we change the def of inertness and get what we want? *)
Qed.

Lemma sngl_typed2 : forall G p q,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    exists T, G ⊢!! q: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. lets Heq: (pf_sngl_T Hi H). subst.
  destruct* (sngl_typed Hi H).
Qed.

Lemma sngl_typed3 : forall G p q,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    exists T, G ⊢!!! q: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct* (sngl_typed2 Hi H).
Qed.

Lemma repl_composition_sngl: forall G p q T,
    inert G ->
    repl_composition_qp G (typ_sngl q) (typ_sngl p) ->
    G ⊢!!! p : T ->
    p = q \/ G ⊢!!! p : typ_sngl q.
Proof.
  introv Hi Hc Hq. dependent induction Hc; eauto.
  assert (exists r, b = typ_sngl r) as [p3 Heq] by admit. subst.
  specialize (IHHc _ _ Hi eq_refl eq_refl Hq).
  destruct H as [r1 [r2 [n [H Hr]]]]. inversions Hr.
  rewrite proj_rewrite_mult in *. set (p_sel qx qbs) as q in *.
  set (p_sel px pbs) as p' in *.
  lets H': (pt3 (pt2 H)).
  destruct IHHc as [Heq | Hp]; subst.
  - lets Htt: (pt3_trans_trans _ Hi H' Hq).
    right*.
  - right.
    destruct (sngl_typed3 Hi Hp) as [S Hqbs].
    lets Htt: (pt3_trans_trans _ Hi H' Hqbs). apply* pt3_sngl_trans3.
Qed.

Lemma repl_composition_sngl2: forall G p q T,
    inert G ->
    repl_composition_qp G (typ_sngl q) (typ_sngl p) ->
    G ⊢!!! q : T ->
    p = q \/ G ⊢!!! p : typ_sngl q.
Proof.
  introv Hi Hc Hq. gen T. dependent induction Hc; introv Hq; eauto.
  assert (exists r, b = typ_sngl r) as [p3 Heq] by admit. subst.
  specialize (IHHc _ _ Hi eq_refl eq_refl).
  destruct H as [r1 [r2 [n [H Hr]]]]. inversions Hr.
  rewrite proj_rewrite_mult in *. set (p_sel qx qbs) as q in *.
  set (p_sel px pbs) as p' in *.
  lets H': (pt3 (pt2 H)).
  assert (exists S, G ⊢!!! q •• bs : S) as [S Hqs]. {
    eexists. apply* pt3_field_trans.
  }
  destruct (IHHc _ Hqs) as [Heq | Hp]; subst.
  - lets Htt: (pt3_trans_trans _ Hi H' Hqs).
    right*.
  - right.
    destruct (sngl_typed3 Hi Hp) as [S' Hqbs].
    lets Htt: (pt3_trans_trans _ Hi H' Hqbs). apply* pt3_sngl_trans3.
Qed.

Lemma sngl_replacement: forall G p q n T U,
    inert G ->
    G ⊢# trm_path p: typ_sngl q ->
    repl_typ n p q T U ->
    G ⊢# T <: U /\ G ⊢# U <: T.
Proof.
  introv Hi Hp Hr.
  lets Hc: (replacement_closure Hi Hp).
  lets Hri: (repl_to_invertible Hi Hc). destruct Hri as [V [Hrc Hpt]].
  destruct (repl_comp_sngl_inv Hrc) as [r Heq]. subst.
  destruct (inv_to_precise_sngl Hpt) as [r' [Ht Hrc']].
  destruct (sngl_typed3 Hi Ht) as [V Hst].
  destruct (repl_composition_sngl Hi Hrc' Hst) as [Heq | Hpq].
  - subst. destruct (repl_composition_sngl2 Hi Hrc Hst).
    * subst. split. eauto. apply repl_swap in Hr. eauto.
    * split.
      ** destruct (repl_insert r Hr) as [S [Hr1 Hr2]].
         apply subtyp_trans_t with (T:=S); eauto.
      ** apply repl_swap in Hr.
         destruct (repl_insert r Hr) as [S [Hr1 Hr2]].
         apply subtyp_trans_t with (T:=S); eauto.
  - destruct (sngl_typed3 Hi Hpq) as [T' Ht'].
    destruct (repl_composition_sngl2 Hi Hrc Ht').
    * subst. split.
      ** destruct (repl_insert r' Hr) as [S [Hr1 Hr2]].
         apply subtyp_trans_t with (T:=S); eauto.
      ** apply repl_swap in Hr.
         destruct (repl_insert r' Hr) as [S [Hr1 Hr2]].
         apply subtyp_trans_t with (T:=S); eauto.
    * destruct (repl_insert r' Hr) as [S [Hr1 Hr2]].
      split.
      ** apply subtyp_trans_t with (T:=S). eauto.
         destruct (repl_insert r Hr2) as [S' [Hr1' Hr2']].
         apply subtyp_trans_t with (T:=S'); eauto.
      ** apply repl_swap in Hr. destruct (repl_insert r Hr) as [S' [Hr1' Hr2']].
         apply subtyp_trans_t with (T:=S'). eauto.
         destruct (repl_insert r' Hr2') as [S'' [Hr1'' Hr2'']].
         apply subtyp_trans_t with (T:=S''); eauto.
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
  intros G0 HG.
  apply ts_mutind; intros; subst;
    try solve [eapply sel_replacement; auto]; eauto.
  - destruct* (sngl_replacement HG (H eq_refl) r).
  - apply repl_swap in r. destruct* (sngl_replacement HG (H eq_refl) r).
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
    apply (replacement_closure Hi) in Hg;
    try lets Hok: (inert_ok Hi);
    try match goal with
        | [ Hinv: ?G ⊢// _ : typ_all _ _,
            Hok: ok ?G |- _ ] =>
          destruct (repl_to_precise_typ_all Hok Hinv) as [Spr [Tpr [Upr [Lpr [Hpr [Hspr1 Hspr2]]]]]]
        | [ Hinv: ?G ⊢// _ : typ_rcd { _ ⦂ _ } |- _ ] =>
          destruct (repl_to_precise_trm_dec Hinv) as [Tpr [Upr [Hpr Hspr]]]
        end
  end.
