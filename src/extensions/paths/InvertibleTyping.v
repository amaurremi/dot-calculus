(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Invertible (Introduction-pq) Typing *)

(** This module contains lemmas related to invertible typing for paths and values
    ([|-##] and [|-##v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Sequences.
Require Import Definitions Binding Narrowing PreciseFlow
        PreciseTyping RecordAndInertTypes Replacement
        Subenvironments TightTyping Weakening.

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⊢!!! p: {a: T}],
and [G ⊢ T <: T'], then [G ⊢## p: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). Additionally, invertible typing is closed under
singleton-subtyping in one direction: if [Γ ⊢! p : q.type] then singleton subtyping is
closed under replacement of [p] with [q], but not under replacement of [q] with [p], which
is taken care by _replacement typing_ (⊢//, [ty_repl]). *)

(** ** Invertible typing of paths [G ⊢## p: T] *)

Reserved Notation "G '⊢##' p ':' T" (at level 40, p at level 59).

Inductive ty_path_inv : ctx -> path -> typ -> Prop :=

(** [G ⊢!!! p: T]     #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: T]     *)
| ty_precise_inv : forall G p T,
  G ⊢!!! p : T ->
  G ⊢## p : T

(** [G ⊢## p: {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p: {a: U}]     *)
| ty_dec_trm_inv : forall G p a T U,
  G ⊢## p : typ_rcd {a ⦂ T} ->
  G ⊢# T <: U ->
  G ⊢## p : typ_rcd {a ⦂ U}

(** [G ⊢## p: {A: T1..S1}]   #<br>#
    [G ⊢# T2 <: T1]         #<br>#
    [G ⊢# S1 <: S2]         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## p: {A: T2..S2}]     *)
| ty_dec_typ_inv : forall G p A T1 T2 S1 S2,
  G ⊢## p : typ_rcd {A >: T1 <: S1} ->
  G ⊢# T2 <: T1 ->
  G ⊢# S1 <: S2 ->
  G ⊢## p : typ_rcd {A >: T2 <: S2}

(** [G ⊢## p: forall(S1)T1]          #<br>#
    [G ⊢# S2 <: S1]            #<br>#
    [G, y: S2 ⊢ T1^y <: T2^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## p: forall(S')T']            *)
| ty_all_inv : forall G T1 T2 S1 S2 L p,
  G ⊢## p : ∀(S1) T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢## p : ∀(S2) T2

(** [G ⊢## p : T]     #<br>#
    [G ⊢## p : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p : T /\ U]      *)
| ty_and_inv : forall G p S1 S2,
  G ⊢## p : S1 ->
  G ⊢## p : S2 ->
  G ⊢## p : S1 ∧ S2

(** [G ⊢## p]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_inv : forall G p T,
  G ⊢## p : T ->
  G ⊢## p : ⊤

(** [G ⊢## p.a: T]    #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: {a: T}]     *)
| ty_rcd_intro_inv : forall G p a T,
    G ⊢## p•a : T ->
    G ⊢## p : typ_rcd { a ⦂ T }

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢## r: μ(T)]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢## p: μ(T[q/p,n])]      *)
| ty_rec_pq_inv : forall G p q r T T' n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢## r : μ T ->
    repl_typ n p q T T' ->
    G ⊢## r : μ T'

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢## r: r'.A]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢## p: (r'.A)[q/p,n]]      *)
| ty_sel_pq_inv : forall G p q r r' r'' A n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q: U ->
    G ⊢## r : r'↓A ->
    repl_typ n p q (r'↓A) (r''↓A) ->
    G ⊢## r : r''↓A

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢## r: r'.type]          #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢## p: (r'.type)[q/p,n]]      *)
| ty_sngl_pq_inv : forall G p q r r' r'' n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢## r : {{ r' }} ->
    repl_typ n p q {{ r'}} {{ r'' }} ->
    G ⊢## r : {{ r'' }}

where "G '⊢##' p ':' T" := (ty_path_inv G p T).

Hint Constructors ty_path_inv.

(** *** From Invertible to Precise Typing *)

(** Invertible-to-precise typing for function types: #<br>#
    [ok G]                        #<br>#
    [G ⊢## p: forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⊢!!! p: forall(S')T']  #<br>#
    [G ⊢# S <: S']               #<br>#
    [G ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma invertible_to_precise_typ_all: forall G p S T,
  inert G ->
  G ⊢## p : ∀(S) T ->
  exists S' T' L,
    G ⊢!!! p : ∀(S') T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - do 2 eexists. exists (dom G). eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [S' [T' [L' [Hp [Hs1 Hs]]]]].
    exists  S' T' (L \u L' \u dom G). repeat split; auto. eauto.
    introv Hy. eapply subtyp_trans.
    + eapply narrow_subtyping. apply* Hs. apply subenv_last. apply* tight_to_general.
      apply* ok_push.
    + eauto.
Qed.

(** Invertible-to-precise typing for records:
    [inert G]                    #<br>#
    [G |-## p: {A: S..U}]        #<br>#
    [――――――――――――――――――――――――――――]   #<br>#
    [exists T. G |-## p: {A: T..T}]   #<br>#
    [G |-# T <: U]               #<br>#
    [G |-# S <: T]                    *)
Lemma invertible_to_precise_rcd: forall G p A S U,
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

(** *** Invertible Replacement Closure *)

Ltac solve_names :=
  match goal with
    | [H: _ ⊢! ?p : _ ⪼ _ |- named_path ?p ] =>
      apply precise_to_general in H;
      apply* typed_paths_named
    | [H: _ ⊢!!! ?p : _ |- named_path ?p ] =>
      apply precise_to_general3 in H;
      apply* typed_paths_named
    | [H: _ ⊢!! ?p : _ |- named_path ?p ] =>
      apply precise_to_general2 in H;
      apply* typed_paths_named
    | [H: _ ⊢ trm_path ?p : _ |- named_path ?p ] =>
      apply* typed_paths_named
  end.

(** Subtyping between equivalent types in which the paths *)
Lemma repl_sub: forall G p q T U n V,
    repl_typ n p q T U ->
    G ⊢!!! p: {{q}} ->
    G ⊢!! q : V ->
    G ⊢# U <: T.
Proof.
  introv Hr Hpq Hq. apply repl_swap in Hr. eauto.
Qed.

(** Subtyping between equivalent types formulated without precise typing *)
Lemma repl_composition_sub G T U :
  G ⊢ T ⟿ U ->
  G ⊢ U <: T /\ G ⊢ T <: U.
Proof.
  intros Hr. dependent induction Hr; eauto.
  destruct H as [q [r [n [S [Hq%precise_to_general [Hq' Hrt]]]]]]. destruct_all.
  split.
  - eapply subtyp_trans. apply* subtyp_sngl_qp. apply* precise_to_general2. eauto.
  - eapply subtyp_trans. apply H0. apply repl_swap in Hrt. eapply subtyp_sngl_pq; eauto. apply* precise_to_general2.
Qed.

Ltac solve_repl_sub :=
    try (apply* tight_to_general);
    try solve [apply* repl_sub];
    eauto.

(** Singleton-subtyping closure for inert and record types:
    If [Γ ⊢!!! p: T] and [Γ ⊢! q: r.type] then [Γ ⊢## p: T[r/q,n]] *)
Lemma invertible_repl_closure_helper :
  (forall D,
      record_dec D -> forall G p q r D' n U,
      inert G ->
      G ⊢!!! p: typ_rcd D ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : U ->
      repl_dec n q r D D' ->
      G ⊢## p: typ_rcd D') /\
  (forall U ls,
      record_typ U ls -> forall G p q r U' n V,
      inert G ->
      G ⊢!!! p: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : V ->
      repl_typ n q r U U' ->
      G ⊢## p: U') /\
  (forall U,
      inert_typ U -> forall G p q r U' n V,
      inert G ->
      G ⊢!!! p: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : V ->
      repl_typ n q r U U' ->
      G ⊢## p: U').
Proof.
  apply rcd_mutind; intros; try solve [invert_repl; eauto].
  - invert_repl; eapply ty_dec_typ_inv. eapply ty_precise_inv. apply H0.
    solve_repl_sub. eauto. solve_repl_sub. eauto. eauto.
  - invert_repl. eapply ty_dec_trm_inv. eapply ty_precise_inv. eauto. eauto.
  - invert_repl. eapply ty_dec_trm_inv. eapply ty_precise_inv. eauto. eauto.
  - invert_repl; eapply ty_and_inv. apply* H. apply* pt3_and_destruct1.
    apply pt3_and_destruct2 in H2; auto.
    apply pt3_and_destruct1 in H2; auto.
    invert_repl. apply pt3_and_destruct2 in H2; auto. eauto.
  - pose proof (typed_paths_named (precise_to_general H1)) as Ht.
    invert_repl; eapply ty_all_inv with (L:=dom G). eauto. apply repl_swap in H10. eauto.
    introv Hy. eauto. eauto. eauto.
    introv Hy.
    pose proof (typed_paths_named (precise_to_general2 H2)) as Hs.
    lets Ho: (repl_open_var y H10 Ht Hs). eapply weaken_subtyp. solve_repl_sub.
    apply* ok_push.
Qed.

(** Singleton-subtyping closure for invertible typing:
    If [Γ ⊢## p: T] and [Γ ⊢! q: r.type] then [Γ ⊢## p: T[r/q,n]] *)
Lemma invertible_repl_closure : forall G p q r T T' n U,
    inert G ->
    G ⊢## p : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢## p : T'.
Proof.
  introv Hi Hp Hqr Hr Hrep. gen q r T' n U.
  induction Hp; introv Hq; introv Hrep; introv Hr'.
  - Case "ty_precise_inv"%string.
    destruct (pt3_inertsngl Hi H) as [[Hin | Hs] | Hr].
    * inversions Hin.
      ** apply* invertible_repl_closure_helper.
      ** invert_repl. eauto.
    * inversions Hs. invert_repl. eauto.
    * inversions Hr. eapply (proj32 invertible_repl_closure_helper); eauto.
  - Case "ty_dec_trm_inv"%string.
    invert_repl. eapply ty_dec_trm_inv. eauto. eapply subtyp_trans_t. apply H. eauto.
  - Case "ty_dec_typ_inv"%string.
    invert_repl; eapply ty_dec_typ_inv.
    * apply Hp; eapply subtyp_trans_t.
    * apply repl_swap in H9. eapply subtyp_trans_t. apply* subtyp_sngl_qp_t. eauto.
    * auto.
    * apply Hp.
    * auto.
    * eapply subtyp_trans_t. apply H0. eauto.
  - Case "ty_all_inv"%string.
    invert_repl.
    + eapply ty_all_inv with (L:=L \u dom G).
      * apply Hp.
      * apply repl_swap in H7. apply subtyp_trans_t with (T:=S2).
        eauto. eauto.
      * introv Hy. eapply narrow_subtyping. apply H0. auto. constructor; auto.
        apply tight_to_general. solve_repl_sub.
    + eapply ty_all_inv with (L:=L \u dom G).
      * apply Hp.
      * auto.
      * introv Hy. eapply subtyp_trans. apply* H0.
        eapply repl_open_var in H7; try solve_names. eapply subtyp_sngl_pq.
        apply* weaken_ty_trm. eapply precise_to_general. apply Hq.
        apply* weaken_ty_trm. apply* precise_to_general2. apply H7.
  - Case "ty_and_inv"%string.
    invert_repl; eauto.
  - Case "ty_top_inv"%string.
    invert_repl.
  - Case "ty_rec_pq_inv"%string.
    invert_repl. eauto.
  - Case "ty_rcd_intro_inv"%string.
    invert_repl. eauto.
  - Case "ty_sel_pq_inv"%string.
    assert (exists r''', T' = r'''↓A) as [r''' Heq]. {
      invert_repl. eauto.
    } subst.
    destruct (repl_prefixes_sel Hrep) as [bs [He1 He2]]. subst.
    destruct (repl_prefixes_sel H1) as [cs [He1 He2]]. subst.
    specialize (IHHp Hi _ _ H _ _ H1). eauto.
  - Case "ty_sngl_qp_inv"%string.
    assert (exists r''', T' = {{ r'''}}) as [r''' Heq]. {
      invert_repl. eauto.
    } subst.
    destruct (repl_prefixes_sngl Hrep) as [bs [-> ->]].
    destruct* (repl_prefixes_sngl H1) as [? [? ?]].
Qed.

(** *** Properties of invertible typing *)

Lemma invertible_bot : forall G p,
    inert G ->
    G ⊢## p: ⊥ -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  dependent induction H; eauto.
  dependent induction H; eauto.
  false* pf_bot.
Qed.

Lemma invertible_and : forall G p T U,
    inert G ->
    G ⊢## p: T ∧ U ->
    G ⊢## p: T /\ G ⊢## p: U.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  split. apply pt3_and_destruct1 in H. eauto. apply pt3_and_destruct2 in H.
  eauto.
Qed.

Lemma invertible_bnd : forall G p T,
    inert G ->
    G ⊢## p: μ T ->
    G ⊢## p: open_typ_p p T \/
             (exists q U, G ⊢!!! p: {{ q }} /\ G ⊢!!! q : U /\ G ⊢## p: open_typ_p q T).
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - destruct (pt3_bnd Hi H) as [Hp | [q [U [Hp1 [Hq Hp2]]]]]. left*. right. repeat eexists; eauto.
  - destruct (IHHp _ Hi eq_refl) as [Hr | [q' [S [Hr [Hq Hr']]]]].
    * left. apply* invertible_repl_closure. apply* repl_open; solve_names.
    * right. repeat eexists. eauto. apply repl_open with (r:=q') in H1. apply Hq. solve_names. solve_names.
      eapply invertible_repl_closure. auto. apply Hr'. apply H. apply H0. apply* repl_open.
      all: solve_names.
Qed.

Lemma path_sel_inv: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢## q : p↓A ->
    G ⊢## q : T.
Proof.
  introv Hi Hp Hq. dependent induction Hq.
  - Case "ty_precise_inv"%string.
    false* pt3_psel.
  - Case "ty_sel_pq_inv"%string.
    destruct (repl_prefixes_sel H1) as [bs [Heq1 Heq2]].
    subst.
    lets Hh: (pt3_field_trans' _ Hi (pt3 (pt2 H)) Hp).
    specialize (IHHq _ _ Hi Hh eq_refl). eauto.
Qed.

Lemma invertible_repl_closure_comp_typed: forall G p T T',
    inert G ->
    G ⊢## p: T ->
    G ⊢ T ⟿ T' ->
    G ⊢## p: T'.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  destruct H as [p' [q' [n [Hpq Hr']]]].
  apply* invertible_repl_closure.
  apply* repl_swap.
Qed.

Lemma inv_to_precise_sngl_repl_comp: forall G p q,
    G ⊢## p: {{ q }} ->
    exists r, G ⊢!!! p: {{ r }} /\ G ⊢ r ⟿' q.
Proof.
  introv Hp.
  dependent induction Hp.
  - exists q. split*. apply star_refl.
  - specialize (IHHp _ eq_refl). destruct IHHp as [r'' [Hr' Hc']].
    exists r''. split*. eapply star_trans.
    apply star_one. unfold typed_repl_comp_qp.
    repeat eexists; eauto. apply* repl_swap. eauto.
Qed.

Lemma inv_to_precise_sngl: forall G p q U,
    inert G ->
    G ⊢## p: {{ q }} ->
    G ⊢!!! q : U ->
    exists r, G ⊢!!! p: {{ r }} /\ (r = q \/ G ⊢!!! r: {{ q }}).
Proof.
  introv Hi Hp Hq. destruct (inv_to_precise_sngl_repl_comp Hp) as [r [Hpr Hrc]].
  exists r. split*. clear Hp.
  gen p U. dependent induction Hrc; introv Hpr; introv Hq; auto.
  inversion H as [r1 [r2 [n [V [Hr1 [Hqr2 Hr]]]]]]. invert_repl.
  pose proof (pt3_field_trans _ Hi (pt3 (pt2 Hr1)) Hq) as Hr1bs.
  specialize (IHHrc _ Hi _ eq_refl eq_refl _ Hpr _ Hr1bs) as [-> | Hr1r2]; eauto.
  right. apply* pt3_sngl_trans3.
Qed.

(** If a path has an invertible type it also has a III-level precise type. *)
Lemma inv_to_prec G p T :
  G ⊢## p : T ->
  exists U, G ⊢!!! p : U.
Proof.
  induction 1; eauto.
  destruct IHty_path_inv as [? ?]. apply* pt3_backtrack.
Qed.

(** ** Invertible typing for values *)

Reserved Notation "G '⊢##v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_inv : ctx -> val -> typ -> Prop :=

(** [G ⊢ p: qs ⪼ T]  #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: T]     *)
| ty_precise_invv : forall G v T,
  G ⊢!v v : T ->
  G ⊢##v v : T

| ty_all_invv : forall G T1 T2 S1 S2 L v,
  G ⊢##v v : ∀(S1) T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢##v v : ∀(S2) T2

(** [G ⊢## p : T]     #<br>#
    [G ⊢## p : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p : T /\ U]      *)
| ty_and_invv : forall G v S1 S2,
  G ⊢##v v : S1 ->
  G ⊢##v v : S2 ->
  G ⊢##v v : S1 ∧ S2

(** [G ⊢## p: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_invv : forall G v T,
  G ⊢##v v : T ->
  G ⊢##v v : ⊤

| ty_rec_pq_invv : forall G p q v T T' n U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢##v v : μ T ->
    repl_typ n p q T T' ->
    G ⊢##v v : μ T'

where "G '⊢##v' v ':' T" := (ty_val_inv G v T).

Hint Constructors ty_val_inv.


Lemma invertible_repl_closure_v_helper :
  (forall D,
      record_dec D -> forall G v q r D' n T,
      inert G ->
      G ⊢!v v: typ_rcd D ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : T ->
      repl_dec n q r D D' ->
      G ⊢##v v: typ_rcd D') /\
  (forall U ls,
      record_typ U ls -> forall G v q r U' n T,
      inert G ->
      G ⊢!v v: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : T ->
      repl_typ n q r U U' ->
      G ⊢##v v: U') /\
  (forall U,
      inert_typ U -> forall G v q r U' n T,
      inert G ->
      G ⊢!v v: U ->
      G ⊢! q : {{ r }} ⪼ {{ r }} ->
      G ⊢!! r : T ->
      repl_typ n q r U U' ->
      G ⊢##v v: U').
Proof.
  apply rcd_mutind; intros; try solve [invert_repl; eauto].
  - inversions H0.
  - inversions H1.
  - inversions H0.
  - inversions H2.
  - lets Ht: (typed_paths_named (precise_to_general H1)).
    invert_repl; eapply ty_all_invv with (L:=dom G).
    * eauto.
    * apply repl_swap in H10; eauto.
    * introv Hy. eauto.
    * eauto.
    * eauto.
    * introv Hy. lets Ho: (repl_open_var y H10 Ht).
      eapply weaken_subtyp; auto.
      pose proof (typed_paths_named (precise_to_general2 H2)) as Hs. specialize (Ho Hs).
      solve_repl_sub.
Qed.

Lemma invertible_repl_closure_v : forall G v q r T T' n U,
    inert G ->
    G ⊢##v v : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ n q r T T' ->
    G ⊢##v v : T'.
Proof.
  introv Hi Hv Hqr Hr Hrep. gen q r T' n U.
  induction Hv; introv Hq; introv Hr; introv Hrep.
  - Case "ty_precise_invv"%string.
    lets Ht: (pfv_inert H).
    inversions Ht.
    * apply* invertible_repl_closure_v_helper.
    * invert_repl; eauto.
  - Case "ty_all_invv"%string.
    invert_repl.
    + eapply ty_all_invv with (L:=L \u dom G).
      * apply Hv.
      * apply repl_swap in H7. apply subtyp_trans_t with (T:=S2); eauto.
      * introv Hy. eapply narrow_subtyping. apply H0. auto. constructor; auto.
        apply tight_to_general. solve_repl_sub.
    + eapply ty_all_invv with (L:=L \u dom G).
      * apply Hv.
      * auto.
      * introv Hy. eapply subtyp_trans. apply* H0.
        eapply repl_open_var in H7; try solve_names. eapply subtyp_sngl_pq.
        apply* weaken_ty_trm. eapply precise_to_general. apply Hq. eapply weaken_ty_trm.
        apply* precise_to_general2. eauto.
        apply H7.
  - Case "ty_and_invv"%string.
    invert_repl; eauto.
  - Case "ty_top_invv"%string.
    invert_repl.
  - Case "ty_rec_pq_invv"%string.
    invert_repl. eauto.
Qed.

Lemma path_sel_inv_v: forall G p A T v,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢##v v : p↓A ->
    G ⊢##v v : T.
Proof.
  introv Hi Hp Hv. inversions Hv.
  inversions H.
Qed.

(** If [G ⊢##v v: forall(S)T] then
    - [exists S', T', G ⊢! v: forall(S')T'],
    - [G ⊢ S <: S'], and
    - [forall fresh y, G, y: S ⊢ T'^y <: T^y] *)
Lemma invertible_val_to_precise_lambda: forall G v S T,
    G ⊢##v v : ∀(S) T ->
    inert G ->
    exists L S' T',
      G ⊢!v v : ∀(S') T' /\
      G ⊢ S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt _ _ eq_refl Hg) as [L' [S' [T' [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S' T'. split. assumption. split. apply subtyp_trans with (T:=S1).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok by apply* ok_push.
    apply subtyp_trans with (T:=open_typ y T1).
    * eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general. auto.
    * apply* H0.
Qed.

(** If the invertible type of a value is a recursive type then its precise type
    is an equivalent recursive type. *)
Lemma invertible_to_precise_obj G U v :
  inert G ->
  G ⊢##v v : μ U ->
  exists T, G ⊢!v v : μ T /\ G ⊢ T ⟿ U.
Proof.
  intros Hi Hv. dependent induction Hv.
  - Case "ty_precise_invv"%string.
    inversions H. eexists. split*. constructor.
  - Case "ty_rec_pq_invv"%string.
    specialize (IHHv _ Hi eq_refl) as [T' [Hinv Hrc]].
    eexists. split.
    * eauto.
    * eapply star_trans. apply star_one. econstructor. repeat eexists. apply H. eauto.
      apply* repl_swap.
      apply Hrc.
Qed.
