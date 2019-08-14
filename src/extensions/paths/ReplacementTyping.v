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

| ty_rec_qp_r : forall G p q r T T' U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢// r : μ T ->
    repl_typ q p T T' ->
    G ⊢// r : μ T'

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: r'.A]             #<br>#x
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: (r'.A)[q/p,n]]      *)
| ty_sel_qp_r : forall G p q r A bs U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q: U ->
    G ⊢// r : (q •• bs)↓A ->
    G ⊢// r : (p •• bs)↓A

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: r'.type]          #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: (r'.type)[q/p,n]]      *)
| ty_sngl_qp_r : forall G p q r bs U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q: U ->
    G ⊢// r : {{ q •• bs }} ->
    G ⊢// r : {{ p •• bs }}

(** [G ⊢## p]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_r : forall G p T,
  G ⊢// p : T ->
  G ⊢// p : ⊤

(** [G ⊢## p: {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p: {a: U}]     *)

| ty_dec_trm_r : forall G p a T U,
  G ⊢// p : typ_rcd {a ⦂ T} ->
  G ⊢# T <: U ->
  G ⊢// p : typ_rcd {a ⦂ U}
(** [G ⊢## p: {A: T1..S1}]   #<br>#
    [G ⊢# T2 <: T1]         #<br>#
    [G ⊢# S1 <: S2]         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## p: {A: T2..S2}]     *)

| ty_dec_typ_r : forall G p A T1 T2 S1 S2,
  G ⊢// p : typ_rcd {A >: T1 <: S1} ->
  G ⊢# T2 <: T1 ->
  G ⊢# S1 <: S2 ->
  G ⊢// p : typ_rcd {A >: T2 <: S2}

(** [G ⊢## p: forall(S1)T1]          #<br>#
    [G ⊢# S2 <: S1]            #<br>#
    [G, y: S2 ⊢ T1^y <: T2^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## p: forall(S')T']            *)
| ty_all_r : forall G T1 T2 S1 S2 L p,
  G ⊢// p : ∀(S1) T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢// p : ∀(S2) T2

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
  introv Hi Hp. dependent induction Hp. apply* invertible_to_precise_typ_all.
  specialize (IHHp _ _ Hi eq_refl). destruct IHHp as [S' [T' [L' [Hp' [Hs1 Hs]]]]].
  exists  S' T' (L \u L' \u dom G). repeat split; auto. eauto.
  introv Hy. eapply subtyp_trans.
  + eapply narrow_subtyping. apply* Hs. apply subenv_last. apply* tight_to_general.
    apply* ok_push.
  + eauto.
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
  introv HG Hr. dependent induction Hr. apply* invertible_to_precise_rcd.
  specialize (IHHr _ _ _ HG eq_refl).
  destruct IHHr as [V [Hx [Hs1 Hs2]]]. exists V. split*.
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
Lemma replacement_repl_closure_qp : forall G p q r T T' U,
    inert G ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr Hp.
  gen q r T' U. induction Hp; introv Hq; introv Hr' Hr; try solve [invert_repl; eauto 5].
  - Case "ty_inv_r"%string.
    gen q r T' U. induction H; introv Hq; introv Hr; introv Hr'; try solve [invert_repl; eauto 5].
    -- SCase "ty_precise_inv"%string.
       destruct (pt3_inertsngl Hi H) as [[Hit | Hs] | Hst].
       + SSCase "ty_precise_inv_1"%string.
         inversions Hit; invert_repl.
         ++ eapply ty_all_r with (L := \{}).
            apply ty_inv_r.
            apply* ty_precise_inv. apply repl_swap in H5.
            eauto. introv Hy. auto.
         ++ eapply ty_all_r with (L := dom G).
            apply ty_inv_r.
            apply* ty_precise_inv. auto. introv Hy.
            eapply repl_open_var in H5; try solve_names.
            eapply subtyp_sngl_qp. apply* weaken_ty_trm.
            eapply precise_to_general. apply Hq. apply* weaken_ty_trm. apply* precise_to_general2. apply H5.
         ++ apply* ty_rec_qp_r.
       + SSCase "ty_precise_inv_2"%string.
         inversions Hs. invert_repl.
         eapply ty_sngl_qp_r; eauto.
       + SSCase "ty_precise_inv_3"%string.
         inversion Hst as [x Hx].
         generalize dependent T'.
         dependent induction Hx; introv Hr; subst; invert_repl.
         ++ destruct D2.
            * invert_repl. apply ty_precise_inv in H.
              assert (Hts : G ⊢# t0 <: T1).
              { apply repl_swap in H6. eauto. }
              eauto.
              invert_repl. apply ty_precise_inv in H.
              assert (Hts : G ⊢# T1 <: t1).
              { eauto. } eauto.
            * invert_repl. eapply ty_precise_inv in H.
              eapply ty_dec_trm_r; eauto.
        ++ assert (Hpt0 : G ⊢!!! p : T) by (eapply pt3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pt3_and_destruct2; eauto).
           apply* ty_and_r.
        ++ assert (Hpt0 : G ⊢!!! p : T) by (eapply pt3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pt3_and_destruct2; eauto).
          apply ty_and_r; eauto.
          destruct D2; invert_repl;
          apply ty_precise_inv in Hpd.
          * eapply ty_dec_typ_r; eauto. apply repl_swap in H7. eauto.
          * eapply ty_dec_typ_r; eauto.
          * eapply ty_dec_trm_r; eauto.
    -- SCase "ty_sel_qp_inv"%string.
       inversions Hr.
       specialize (ty_sel_pq_inv _ H H0 H1). intros Hr.
       rewrite <- H5 in Hr. eapply ty_sel_qp_r; eauto.
    -- SCase "ty_sngl_qp_inv"%string.
       inversions Hr.
       specialize (ty_sngl_pq_inv _ H H0 H1). intros Hr.
       rewrite <- H5 in Hr. eapply ty_sngl_qp_r; eauto.
  - Case "ty_sel_qp_r"%string.
    invert_repl. specialize (IHHp Hi _ _ H _ _ H0 (rpath q p bs A)).
    rewrite <- H4 in IHHp. eapply ty_sel_qp_r; eauto.
  - Case "ty_sngl_qp_r"%string.
    invert_repl. specialize (IHHp Hi _ _ H _ _ H0 (rsngl q p bs)).
    rewrite <- H4 in IHHp. eapply ty_sngl_qp_r; eauto.
  - Case "ty_dec_trm_r"%string.
    invert_repl. eapply ty_dec_trm_r; eauto. eapply subtyp_trans_t; eauto.
  - Case "ty_dec_typ_r"%string.
    invert_repl; eapply ty_dec_typ_r; eauto.
    -- eapply subtyp_trans_t. eapply subtyp_sngl_pq_t; eauto.
       apply repl_swap in H8. eauto. auto.
    -- eapply subtyp_trans_t. eauto.  eapply subtyp_sngl_qp_t; eauto.
  - Case "ty_all_r"%string.
    invert_repl.
    -- eapply ty_all_r with (L:=L \u dom G); eauto.
       * apply repl_swap in H6. eapply subtyp_trans_t.
         eapply subtyp_sngl_pq_t; eauto. auto.
       * introv Hy. eapply narrow_subtyping. apply H0. auto. constructor; auto.
         apply tight_to_general. eapply subtyp_sngl_pq_t; eauto. apply repl_swap.
         auto.
    -- eapply ty_all_r with (L:=L \u dom G); eauto.
       introv Hy. eapply subtyp_trans. apply H0. auto.
       eapply repl_open_var in H6; try solve_names.
       eapply subtyp_sngl_qp. apply* weaken_ty_trm. eapply precise_to_general.
       apply Hq.
       apply* weaken_ty_trm. apply* precise_to_general2. eapply H6.
Qed.

(** Replacement typing is closed under [qp] replacement
    when we know [q]'s II-level precise type *)
Lemma replacement_repl_closure_qp2 : forall G p q r T T' U,
    inert G ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ r q T T' ->
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
Lemma replacement_repl_closure_qp3 : forall G p q r T T' U,
    inert G ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr' Hp Hr. gen p T T' U. dependent induction Hq; introv Hp; introv Hr; introv Hr'.
  - apply* replacement_repl_closure_qp2.
  - specialize (IHHq _ Hi eq_refl _ _ Hp).
    destruct (repl_insert q Hr) as [V [Hr1 Hr2]].
    pose proof (pt2_exists Hq) as [S Hs].
    specialize (IHHq _ Hr1 _ Hr'). eapply replacement_repl_closure_qp2.
    auto. auto. apply H. apply Hs. apply IHHq. eauto.
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
  apply* IHHc. apply* replacement_repl_closure_qp3.
Qed.

Lemma replacement_repl_closure_pq_helper_mutind: (forall q p T T',
    repl_typ q p T T' ->
    forall q0 r0 T2 G, repl_typ q0 r0 T' T2 ->
    inert G ->
    G ⊢! p: {{ q }} ⪼ {{ q }} ->
    G ⊢! q0: {{ r0 }} ⪼ {{ r0 }} ->
             T = T2 \/ exists T3, repl_typ q0 r0 T T3 /\ repl_typ q p T3 T2) /\
    (forall q p D D',
        repl_dec q p D D' ->
    forall q0 r0 D2 G,
    repl_dec q0 r0 D' D2 ->
    inert G ->
    G ⊢! p: {{ q }} ⪼ {{ q }} ->
    G ⊢! q0: {{ r0 }} ⪼ {{ r0 }} ->
    D = D2 \/ exists D3, repl_dec q0 r0 D D3 /\ repl_dec q p D3 D2).
Proof.
  apply repl_mutind; intros; eauto.
  - invert_repl. destruct (H _ _ _ _ H7 H1 H2 H3); subst; eauto.
    right. destruct H0 as [D4 [Hl Hr]]. exists (typ_rcd D4). split; eauto.
  - invert_repl.
    * destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T5 [Hl Hr]]. exists (T5 ∧ U). split; eauto.
    * right. exists (T1 ∧ T4). split; auto.
  - invert_repl.
    * right. exists (T4 ∧ T1). split; auto.
    * destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
      destruct H0 as [T5 [Hl Hr]]. right. exists (U ∧ T5). split; auto.
  - invert_repl. left. assert (p •• bs = r0 •• bs0).
    eapply pf_sngl_sel_unique; eauto. rewrite H. auto.
  - invert_repl. destruct (H _ _ _ _ H7 H1 H2 H3); subst; eauto.
    right. destruct H0 as [T5 [Hl Hr]]. exists (μ T5). split; auto.
  - invert_repl.
    * destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T5 [Hl Hr]]. exists (∀ (T5) U). split; auto.
    * right. exists (∀ (T1) T4). split; auto.
  - invert_repl.
    * right. exists (∀ (T4) T1). split; auto.
    * destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T5 [Hl Hr]]. exists (∀ (U) T5). split; auto.
  - invert_repl. left. assert (p •• bs = r0 •• bs0).
    eapply pf_sngl_sel_unique; eauto. rewrite H. auto.
  - invert_repl.
    * destruct (H _ _ _ _ H10 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T4 [Hl Hr]]. exists (dec_typ A T4 U). split; auto.
    * right. exists (dec_typ A T1 T3). split; auto.
  - invert_repl.
    * right. exists (dec_typ A T3 T1). split; auto.
    * destruct (H _ _ _ _ H10 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T4 [Hl Hr]]. exists (dec_typ A U T4). split; auto.
  - invert_repl. destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
    right. destruct H0 as [T4 [Hl Hr]]. exists ({a ⦂ T4}). split; auto.
Qed.


Lemma replacement_repl_closure_pq_helper: forall p q T T',
    repl_typ q p T T' ->
    forall q0 r0 T2 G, repl_typ q0 r0 T' T2 ->
    inert G ->
    G ⊢! p: {{ q }} ⪼ {{ q }} ->
    G ⊢! q0: {{ r0 }} ⪼ {{ r0 }} ->
    T = T2 \/ exists T3, repl_typ q0 r0 T T3 /\ repl_typ q p T3 T2.
Proof.
  destruct replacement_repl_closure_pq_helper_mutind; eauto.
Qed.

Lemma pt2_field_elim_p: forall G p q a U,
    inert G ->
    G ⊢!! p: {{ q }}->
    G ⊢!! p • a : U ->
    G ⊢!! p • a : {{ q•a }}.
Proof.
  introv Hi Hpq Hpa. destruct (field_elim_q _ Hi Hpq Hpa) as [T Hqa].
  apply* pt2_sngl_trans.
Qed.

Lemma invertible_repl_closure_helper :
  (forall D,
      record_dec D -> forall G p q r D' U,
      inert G ->
      G ⊢!!! p: typ_rcd D ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : U ->
      repl_dec q r D D' ->
      G ⊢// p: typ_rcd D') /\
  (forall U ls,
      record_typ U ls -> forall G p q r U' V,
      inert G ->
      G ⊢!!! p: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : V ->
      repl_typ q r U U' ->
      G ⊢// p: U') /\
  (forall U,
      inert_typ U -> forall G p q r U' V,
      inert G ->
      G ⊢!!! p: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : V ->
      repl_typ q r U U' ->
      G ⊢// p: U').
Proof.
  apply rcd_mutind; intros; try solve [invert_repl; eauto].
  - invert_repl; eapply ty_dec_typ_r. eapply ty_inv_r.
    eapply ty_precise_inv. apply H0.
    solve_repl_sub. eauto. solve_repl_sub. eauto. eauto.
  - invert_repl. eapply ty_dec_trm_r. eapply ty_inv_r.
    eapply ty_precise_inv. eauto. eauto.
  - invert_repl. eapply ty_dec_trm_r. eapply ty_inv_r.
    eapply ty_precise_inv. eauto. eauto.
  - invert_repl; eapply ty_and_r. apply* H. apply* pt3_and_destruct1.
    apply pt3_and_destruct2 in H2; auto.
    apply pt3_and_destruct1 in H2; auto.
    invert_repl. apply pt3_and_destruct2 in H2; auto. eauto.
  - pose proof (typed_paths_named (precise_to_general H1)) as Ht.
    invert_repl; eapply ty_all_r with (L:=dom G). eauto. apply repl_swap in H9. eauto.
    introv Hy. eauto. eauto. eauto.
    introv Hy.
    pose proof (typed_paths_named (precise_to_general2 H2)) as Hs.
    lets Ho: (repl_open_var y H9 Ht Hs). eapply weaken_subtyp. solve_repl_sub.
    apply* ok_push.
Qed.

(** Singleton-subtyping closure for invertible typing:
    If [Γ ⊢## p: T] and [Γ ⊢! q: r.type] then [Γ ⊢## p: T[r/q]] *)
Lemma invertible_repl_closure : forall G p q r T T' U,
    inert G ->
    G ⊢## p : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hqr Hr Hrep. gen q r T' U.
  induction Hp; introv Hq; introv Hrep; introv Hr'.
  - Case "ty_precise_inv"%string.
    destruct (pt3_inertsngl Hi H) as [[Hin | Hs] | Hr].
    * inversions Hin.
      ** apply* invertible_repl_closure_helper.
      ** invert_repl. eauto.
    * inversions Hs. invert_repl. eapply ty_inv_r. eapply ty_sngl_pq_inv; eauto.
    * inversions Hr. eapply (proj32 invertible_repl_closure_helper); eauto.
  - Case "ty_rec_pq_inv"%string.
    invert_repl. eauto.
  - Case "ty_sel_pq_inv"%string.
    assert (exists r''', T' = r'''↓A) as [r''' Heq]. {
      invert_repl. eauto.
    } subst.
    destruct (repl_prefixes_sel Hrep) as [bs0 [He1 He2]]. subst.
    apply ty_inv_r.
    apply ty_sel_pq_inv with (p:=q0) (U:=U0); auto.
    rewrite <- He1; auto. eapply ty_sel_pq_inv; eauto.
  - Case "ty_sngl_qp_inv"%string.
    assert (exists r''', T' = {{ r'''}}) as [r''' Heq]. {
      invert_repl. eauto.
    } subst.
    destruct (repl_prefixes_sngl Hrep) as [bs0 [He1 He2]]. subst.
    apply ty_inv_r.
    apply ty_sngl_pq_inv with (p:=q0) (U:=U0); auto.
    rewrite <- He1; auto. eapply ty_sngl_pq_inv; eauto.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s precise type *)
Lemma replacement_repl_closure_pq : forall G p q r T T' U,
    inert G ->
    G ⊢// p : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hqr.
  gen q r T' U. induction Hp; introv Hq; introv Hr' Hr; eauto.
   - Case "ty_inv_r"%string.
     apply* invertible_repl_closure.
   - Case "ty_and_r"%string.
     invert_repl; eauto.
   - Case "ty_bnd_r"%string.
     invert_repl. apply (repl_open p) in H2; try solve_names. eauto.
   - Case "ty_sel_r"%string.
     clear IHHp. invert_repl. lets Heq: (pf_sngl_flds_elim _ Hi Hq H). subst.
     rewrite field_sel_nil in *.
     lets Heq: (pf_T_unique Hi H Hq). subst.
     apply pf_sngl_U in H. inversion H.
   - Case "ty_rcd_intro_r"%string. invert_repl. eauto.
   - Case "ty_rec_qp_r"%string.
     invert_repl. specialize (IHHp Hi _ _ Hq).
     destruct (replacement_repl_closure_pq_helper H1 H5 Hi H Hq).
     * rewrite <- H2. auto.
     * destruct H2 as [T3 [Hl Hr]].
       assert (G ⊢// r : μ T3) by (eapply IHHp; eauto).
       apply (ty_rec_qp_r H H0 H2 Hr).
   - Case "ty_sel_pq_r"%string. invert_repl.
     specialize (pf_sngl_sel_unique _ _ Hi H Hq H4) as Heq. rewrite <- Heq.
     auto.
   - Case "ty_sngl_pq_r"%string. invert_repl.
     specialize (pf_sngl_sel_unique _ _ Hi H Hq H4) as Heq. rewrite <- Heq.
     auto.
   - Case "ty_top_r"%string. invert_repl.
   - Case "ty_dec_trm_r"%string. invert_repl. eapply ty_dec_trm_r; eauto.
     eapply subtyp_trans_t; eauto.
   - Case "ty_dec_typ_r"%string. invert_repl; eapply ty_dec_typ_r; eauto.
     * eapply subtyp_trans_t. apply repl_swap in H8. eapply subtyp_sngl_qp_t; eauto.
       auto.
     * eapply subtyp_trans_t; eauto.
   - Case "ty_all_r"%string. invert_repl; eapply ty_all_r with (L:=L \u dom G); eauto.
     * eapply subtyp_trans_t. apply repl_swap in H6. eapply subtyp_sngl_qp_t; eauto.
       auto.
     * introv Hy. eapply narrow_subtyping. apply H0. eauto.
       constructor; auto. apply tight_to_general.
       eapply subtyp_sngl_qp_t; eauto. apply repl_swap; auto.
     * introv Hy. apply repl_swap in H6. eapply subtyp_trans.
       + apply H0. eauto.
       + eapply repl_open_var in H6; try solve_names.
         eapply subtyp_sngl_pq. apply* weaken_ty_trm.
         eapply precise_to_general. apply Hq.
         apply* weaken_ty_trm. apply* precise_to_general2.
         apply repl_swap in H6. eauto.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s II-level precise type *)
Lemma replacement_repl_closure_pq2 : forall G p q r T T' U,
    inert G ->
    G ⊢// p : T ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
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
Lemma replacement_repl_closure_pq3 : forall G p q r T T' U,
    inert G ->
    G ⊢// p : T ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
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
  apply* IHHc. apply* replacement_repl_closure_pq3.
Qed.


(** Replacement typing is closed under opening of recursive types *)
Lemma repl_rec_intro: forall G p T,
    inert G ->
    G ⊢// p: μ T ->
    G ⊢// p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - Case "ty_inv_r"%string.
    dependent induction H.
    + destruct (pt3_bnd Hi H) as [Hp | [q [U [Hp1 [Hq Hp2]]]]].
      * eapply ty_inv_r. eapply ty_precise_inv. eauto.
      * eapply replacement_repl_closure_qp_comp. auto. auto. apply* ty_inv_r.
        apply Hp1. eauto. apply* repl_comp_open.
    + specialize (IHty_path_inv _ eq_refl Hi).
      eapply replacement_repl_closure_pq; eauto.
      apply* repl_open. all: solve_names.
  - Case "ty_rec_pq_r"%string.
    specialize (IHHp _ Hi eq_refl).
    apply repl_open with (r:= r) in H1; try solve_names. apply* replacement_repl_closure_qp.
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
    assert (record_type (typ_rcd {A >: T <: T})) as Hrt by eauto.
    apply IHHq with (p := q •• bs) (A0 := A); eauto.
    eapply pf_pt3_trans_inv_mult'; eauto.
Qed.

(** If a path has a replacement type it has also an invertible type *)
Lemma repl_to_inv G p T :
  G ⊢// p : T ->
  exists U, G ⊢## p : U.
Proof.
  induction 1; eauto. destruct IHty_repl as [U Hp].
  clear H. apply inv_backtrack in Hp. eauto.
Qed.

(** Replacement typing is closed under ⊤-subtyping *)
Lemma repl_top: forall G r T,
    G ⊢// r: T ->
    G ⊢// r: ⊤.
Proof.
  apply ty_top_r.
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
  induction Hp; eauto.
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
  - specialize (IHHp _ _ Hi eq_refl).
    eapply replacement_subtyping_closure; eauto.
Qed.

(** If [G ⊢// p: T] and [T] and [T'] are equivalent then [G ⊢// p: T'] *)
Lemma replacement_repl_closure_comp_typed: forall G p T T',
    inert G ->
    G ⊢// p: T ->
    G ⊢ T' ⟿ T ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  destruct H as [p' [q' [S [Hpq [Hq Hr']]]]].
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
  - destruct (pt2_qbs_typed _ Hi H H0 Hq) as [T Hq0bs].
    specialize (IHHp _ Hi eq_refl _ Hq0bs).
    destruct IHHp as [q' [S [Hr [Hq' [Heq | Hq0']]]]]. subst.
    + exists (q0 •• bs) T. split; auto. split; auto. right.
      eapply pt3_trans_trans; eauto.
    + exists q' S. split; auto. split; auto. right. eapply pt3_sngl_trans; eauto.
      eapply pt2_field_trans; eauto.
Qed.

Lemma invertible_repl_closure_comp_typed: forall G p q q',
    inert G ->
    G ⊢## p: {{ q }} ->
    G ⊢ q ⟿' q' ->
    G ⊢## p: {{ q' }}.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  inversions H. eapply ty_sngl_pq_inv; eauto.
Qed.

Lemma replacement_repl_closure_comp_typed_path: forall G p q q',
    inert G ->
    G ⊢// p: {{ q }} ->
    G ⊢ q' ⟿' q ->
    G ⊢// p: {{ q' }}.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  inversions H. apply IHHr. eapply ty_sngl_qp_r; eauto.
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
  destruct (inv_to_precise_sngl_repl_comp Hpi) as [r' [Hp' Hrc]].
  destruct (repl_prec_exists Hq) as [U Hq']. clear Hq.
  destruct (field_typing_comp1 _ Hi Hc Hq') as [T1 Hra].
  destruct (field_typing_comp2 _ Hi Hrc Hra) as[T2 Hr'a].
  lets Hper: (path_elim_prec _ Hi Hp' Hr'a).
  lets Hinv: (ty_precise_inv Hper).
  assert (G ⊢ r' • a ⟿' p' • a) as Hr'
      by apply* repl_composition_fld_elim.
  assert (G ⊢ q • a ⟿' p' • a) as Hr''
      by apply* repl_composition_fld_elim.
  lets Hic: (invertible_repl_closure_comp_typed Hi Hinv Hr').
  apply* replacement_repl_closure_comp_typed_path.
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
    eapply replacement_subtyping_closure; eauto.
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
| ty_rec_qp_rv : forall G p q v T T' U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : μ T ->
    repl_typ q p T T' ->
    G ⊢//v v : μ T'
| ty_sel_qp_rv : forall G p q v r' r'' A U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : r' ↓ A ->
    repl_typ q p (r' ↓ A) (r'' ↓ A) ->
    G ⊢//v v : r''↓A
(** [G ⊢## p: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_rv : forall G v T,
  G ⊢//v v : T ->
  G ⊢//v v : ⊤

| ty_all_rv : forall G T1 T2 S1 S2 L v,
  G ⊢//v v : ∀(S1) T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢//v v : ∀(S2) T2

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

Lemma replacement_repl_closure_qp_v G v p q T T' U :
    inert G ->
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : T ->
    repl_typ q p T T' ->
    G ⊢//v v : T'.
Proof.
  intros Hi Hpq Hq Hv.
  gen p q T' U. induction Hv; introv Hpq; introv Hq Hr.
  - Case "ty_inv_rv"%string.
    gen p q T' U. induction H; introv Hpq; introv Hr; introv Hq;
    try solve [invert_repl; eauto].
    -- destruct (pfv_inert H).
      + invert_repl.
        ++ eapply ty_all_rv with (L := \{}).
           eapply ty_inv_rv.
           eapply ty_precise_invv. apply H.
           apply repl_swap in H5.
           eauto.
           introv Hy. auto.
        ++ eapply ty_all_rv with (L := dom G).
           eapply ty_inv_rv.
           eapply ty_precise_invv. apply H.
           auto.
           introv Hy.
           eapply repl_open_var in H5; try solve_names.
           eapply subtyp_sngl_qp. apply* weaken_ty_trm.
           eapply precise_to_general. apply Hpq. apply weaken_ty_trm; auto. apply* precise_to_general2. apply H5.
      + invert_repl; eauto.
  - Case "ty_and_rv"%string.
    invert_repl; eauto.
  - Case "ty_sel_rv"%string.
    invert_repl; eauto.
  - Case "ty_rec_qp_rv"%string.
    invert_repl; eauto.
  - Case "ty_sel_qp_rv"%string.
    lets ?: (ty_sel_qp_rv H H0 Hv H1).
    invert_repl; eauto.
  - Case "ty_top_rv"%string.
    invert_repl; eauto.
  - Case "ty_all_rv"%string.
    invert_repl; eauto.
    -- eapply ty_all_rv with (L:=L \u dom G); eauto.
      + eapply subtyp_trans_t. eapply subtyp_sngl_pq_t; eauto.
        apply repl_swap in H6. eauto. eauto.
      + introv Hy. eapply narrow_subtyping. apply H0. auto. constructor; auto.
        apply tight_to_general. eapply subtyp_sngl_pq_t; eauto.
        apply repl_swap. auto.
    -- eapply ty_all_rv with (L:=L \u dom G); eauto.
       introv Hy. eapply subtyp_trans. apply H0. auto.
       eapply repl_open_var in H6; try solve_names.
       eapply subtyp_sngl_qp. apply* weaken_ty_trm. eapply precise_to_general.
       apply Hpq. apply* weaken_ty_trm. apply* precise_to_general2. eapply H6.
Qed.

Lemma replacement_repl_closure_qp2_v : forall G p v r T T' U,
    inert G ->
    G ⊢!! p : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢//v v : T ->
    repl_typ r p T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hp Hr Hv Hrp. gen U. dependent induction Hp; introv Hr.
  - lets Heq: (pf_sngl_T Hi H). subst.
    apply* replacement_repl_closure_qp_v.
  - lets Hr': (repl_field_elim _ _ _ Hrp). pose proof (pt2_backtrack _ _ Hr) as [? Hq']. eauto.
Qed.

Lemma replacement_repl_closure_qp3_v : forall G v p r T T' U,
    inert G ->
    G ⊢!!! p : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢//v v : T ->
    repl_typ r p T T' ->
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

Lemma invertible_repl_closure_v_helper :
  (forall D,
      record_dec D -> forall G v q r D' T,
      inert G ->
      G ⊢!v v: typ_rcd D ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : T ->
      repl_dec q r D D' ->
      G ⊢//v v: typ_rcd D') /\
  (forall U ls,
      record_typ U ls -> forall G v q r U' T,
      inert G ->
      G ⊢!v v: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : T ->
      repl_typ q r U U' ->
      G ⊢//v v: U') /\
  (forall U,
      inert_typ U -> forall G v q r U' T,
      inert G ->
      G ⊢!v v: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : T ->
      repl_typ q r U U' ->
      G ⊢//v v: U').
Proof.
  apply rcd_mutind; intros; try solve [invert_repl; eauto].
  - inversions H0.
  - inversions H1.
  - inversions H0.
  - inversions H2.
  - lets Ht: (typed_paths_named (precise_to_general H1)).
    invert_repl; eapply ty_all_rv with (L:=dom G).
    * eauto.
    * apply repl_swap in H9. eauto.
    * eauto.
    * eauto.
    * eauto.
    * introv Hy. lets Ho: (repl_open_var y H9 Ht).
      eapply weaken_subtyp; auto.
      pose proof (typed_paths_named (precise_to_general2 H2)) as Hs.
      specialize (Ho Hs). solve_repl_sub.
Qed.

Lemma invertible_repl_closure_v : forall G v q r T T' U,
    inert G ->
    G ⊢##v v : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hqr Hr Hrep. gen q r T' U.
  induction Hv; introv Hq; introv Hr; introv Hrep.
  - Case "ty_precise_invv"%string.
    lets Ht: (pfv_inert H).
    inversions Ht.
    * apply* invertible_repl_closure_v_helper.
    * invert_repl; eauto.
  - Case "ty_rec_pq_invv"%string.
    invert_repl. eauto.
Qed.

Lemma replacement_repl_closure_pq_v : forall G v q r T T' U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hqr Hr'.
  gen q r T' U. induction Hv; introv Hq; introv Hr' Hr; eauto.
   - Case "ty_inv_rv"%string.
     apply* invertible_repl_closure_v.
   - Case "ty_and_rv"%string.
     invert_repl; eauto.
   - Case "ty_sel_rv"%string.
     clear IHHv. invert_repl. lets Heq: (pf_sngl_flds_elim _ Hi Hq H). subst.
     rewrite field_sel_nil in *.
     lets Heq: (pf_T_unique Hi H Hq). subst.
     apply pf_sngl_U in H. inversion H.
  - Case "ty_rec_qp_rv"%string.
    invert_repl. specialize (IHHv Hi _ _ Hq).
    destruct (replacement_repl_closure_pq_helper H1 H5 Hi H Hq).
    * rewrite <- H2. auto.
    * destruct H2 as [T3 [Hl Hr]].
      assert (G ⊢//v v : μ T3) by (eapply IHHv; eauto).
      apply (ty_rec_qp_rv H H0 H2 Hr).
  - Case "ty_sel_pq_rv"%string. invert_repl.
    specialize (IHHv Hi _ _ Hq).
    assert (q •• bs0 = r •• bs). eapply pf_sngl_sel_unique; eauto.
    rewrite <- H1. auto.
  - Case "ty_top_rv"%string. invert_repl.
  - Case "ty_all_rv"%string.
    invert_repl; eapply ty_all_rv with (L:=L \u dom G); eauto.
    * eapply subtyp_trans_t. apply repl_swap in H6. eapply subtyp_sngl_qp_t; eauto.
      auto.
    * introv Hy. eapply narrow_subtyping. apply H0. eauto.
      constructor; auto. apply tight_to_general.
      eapply subtyp_sngl_qp_t; eauto. apply repl_swap; auto.
    * introv Hy. apply repl_swap in H6. eapply subtyp_trans.
      + apply H0. eauto.
      + eapply repl_open_var in H6; try solve_names.
        eapply subtyp_sngl_pq. apply* weaken_ty_trm.
        eapply precise_to_general. apply Hq.
        apply* weaken_ty_trm. apply* precise_to_general2.
        apply repl_swap in H6. eauto.
Qed.

Lemma replacement_repl_closure_pq2_v : forall G v q r T T' U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hq Hr' Hr. gen U. dependent induction Hq; introv Hr'.
  - apply* replacement_repl_closure_pq_v.
    lets Heq: (pf_sngl_T Hi H). subst. auto.
  - lets Hr'': (repl_field_elim _ _ _ Hr). pose proof (pt2_backtrack _ _ Hr') as [? ?]. eauto.
Qed.

Lemma replacement_repl_closure_pq3_v : forall G v q r T T' U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
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
  - dependent induction HT; eauto.
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

Lemma repl_val_to_precise_lambda: forall G v S T,
    G ⊢//v v : ∀(S) T ->
    inert G ->
    exists L S' T',
      G ⊢!v v : ∀(S') T' /\
      G ⊢ S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Ht Hg. dependent induction Ht.
  - apply invertible_val_to_precise_lambda; auto.
  - destruct (IHHt _ _ eq_refl Hg) as [L' [S' [T' [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S' T'. split. assumption. split. apply subtyp_trans with (T:=S1).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok by apply* ok_push.
    apply subtyp_trans with (T:=open_typ y T1).
    * eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general. auto.
    * apply* H0.
Qed.