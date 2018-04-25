(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import Sequences.
Require Import Definitions Binding Narrowing PreciseTyping RecordAndInertTypes Replacement
               Subenvironments TightTyping Weakening.

(** ** Invertible typing *)

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⊢! x: {a: T}],
and [G ⊢ T <: T'], then [G ⊢## x: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). *)

(** ** Invertible typing of paths [G ⊢## p: T] *)

Reserved Notation "G '⊢##' p ':' T" (at level 40, p at level 59).

Inductive ty_path_inv : ctx -> path -> typ -> Prop :=

(** [G ⊢• p: qs ⪼ T]  #<br>#
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

(** [G ⊢## p: T^p]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: mu(T)] *)
| ty_bnd_inv : forall G p T,
  G ⊢## p : open_typ_p p T ->
  G ⊢## p : typ_bnd T

(** [G ⊢## p: forall(S1)T1]          #<br>#
    [G ⊢# S2 <: S1]            #<br>#
    [G, y: S2 ⊢ T1^y <: T2^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## p: forall(S')T']            *)
| ty_all_inv : forall G T1 T2 S1 S2 L p,
  G ⊢## p : typ_all S1 T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢## p : typ_all S2 T2

(** [G ⊢## p : T]     #<br>#
    [G ⊢## p : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p : T /\ U]      *)
| ty_and_inv : forall G p S1 S2,
  G ⊢## p : S1 ->
  G ⊢## p : S2 ->
  G ⊢## p : typ_and S1 S2

(** [G ⊢## p: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_inv : forall G p T,
  G ⊢## p : T ->
  G ⊢## p : typ_top

(* replacement rules: recursive types, selection types, singleton types *)

| ty_rec_pq_inv : forall G p q r T T' n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢## r : typ_bnd T ->
    repl_typ n p q T T' ->
    G ⊢## r : typ_bnd T'

| ty_sel_pq_inv : forall G p q r r' r'' A n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢## r : typ_path r' A ->
    repl_typ n p q (typ_path r' A) (typ_path r'' A) ->
    G ⊢## r : typ_path r'' A

| ty_sngl_pq_inv : forall G p q r r' r'' n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢## r : typ_sngl r' ->
    repl_typ n p q (typ_sngl r') (typ_sngl r'') ->
    G ⊢## r : typ_sngl r''

where "G '⊢##' p ':' T" := (ty_path_inv G p T).

Hint Constructors ty_path_inv.

Lemma repl_sub: forall G p q T U n,
    repl_typ n p q T U ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢# U <: T.
Proof.
  introv Hr Hpq. apply repl_swap in Hr. eauto.
Qed.

Lemma repl_sub_swap: forall G p q T U n,
    repl_typ n q p T U ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢# U <: T.
Proof.
  introv Hr Hpq. apply repl_swap in Hr. eauto.
Qed.

Ltac solve_repl_sub :=
    try (apply* tight_to_general);
    try solve [apply* repl_sub];
    try solve [apply* repl_sub_swap];
    eauto.

(** *** Invertible to Precise Typing [|-## to |-!] *)

(** Invertible typing implies tight typing. *)
Lemma inv_to_tight: forall G p T,
    inert G ->
    G ⊢## p: T ->
    G ⊢# trm_path p: T.
Proof.
  introv Hi Ht. induction Ht; try (specialize (IHHt Hi)); eauto.
  apply* precise_to_tight3. eapply ty_sub_t. apply IHHt. eauto.
Qed.

(** Invertible-to-precise typing for field declarations: #<br>#
    [G |-## p: {a: T}]            #<br>#
    [――――――――――――――――――――――]      #<br>#
    [exists T', G |-! p: {a: T'}]      #<br>#
    [G |-# T' <: T]. *)
Lemma invertible_to_precise_trm_dec: forall G p a T,
  inert G ->
  G ⊢## p : typ_rcd {a ⦂ T} ->
  exists T',
    G ⊢!!! p: typ_rcd {a ⦂ T'} /\
    G ⊢# T' <: T.
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  repeat eexists; eauto.
  specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [T' [Hp Hs]]. repeat eexists; eauto.
Qed.

(** Invertible-to-precise typing for function types: #<br>#
    [ok G]                        #<br>#
    [G ⊢## x: forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⊢! x: forall(S')T']  #<br>#
    [G ⊢# S <: S']               #<br>#
    [G ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma invertible_to_precise_typ_all: forall G p S T,
  inert G ->
  G ⊢## p : typ_all S T ->
  exists S' T' L,
    G ⊢!!! p : typ_all S' T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - repeat eexists; eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [S' [T' [L' [Hp [Hs1 Hs]]]]].
    exists  S' T' (L \u L'). repeat split; auto. eauto. (* renaming *)
Admitted.

(** ** Invertible Replacement Closure *)

Ltac solve_names :=
  match goal with
    | [H: _ ⊢! ?p : typ_sngl ?q ⪼ _ |- named_path ?p ] =>
      apply precise_to_general in H;
      apply* typed_paths_named
    | [H: _ ⊢! ?p : typ_sngl ?q ⪼ _  |- named_path ?q ] =>
      apply precise_to_general in H;
      apply* sngl_path_named
    | [H: _ ⊢!!! ?p : typ_sngl ?q |- named_path ?p ] =>
      apply precise_to_general3 in H;
      apply* typed_paths_named
    | [H: _ ⊢!!! ?p : typ_sngl ?q |- named_path ?q ] =>
      apply precise_to_general3 in H;
      apply* sngl_path_named
    end.

Lemma invertible_repl_closure_helper :
  (forall D,
      record_dec D -> forall G p q r D' n,
      inert G ->
      G ⊢!!! p: typ_rcd D ->
      G ⊢! q : typ_sngl r ⪼ typ_sngl r ->
      repl_dec n q r D D' ->
      G ⊢## p: typ_rcd D') /\
  (forall U ls,
      record_typ U ls -> forall G p q r U' n,
      inert G ->
      G ⊢!!! p: U ->
      G ⊢! q : typ_sngl r ⪼ typ_sngl r ->
      repl_typ n q r U U' ->
      G ⊢## p: U') /\
  (forall U,
      inert_typ U -> forall G p q r U' n,
      inert G ->
      G ⊢!!! p: U ->
      G ⊢! q : typ_sngl r ⪼ typ_sngl r ->
      repl_typ n q r U U' ->
      G ⊢## p: U').
Proof.
  apply rcd_mutind; intros; try solve [invert_repl; eauto].
  - invert_repl; eapply ty_dec_typ_inv. eapply ty_precise_inv. apply H0.
    solve_repl_sub. eauto.
    eauto. eauto. solve_repl_sub.
  - invert_repl. eapply ty_dec_trm_inv. eapply ty_precise_inv. eauto. eauto.
  - invert_repl. eapply ty_dec_trm_inv. eapply ty_precise_inv. eauto. eauto.
  - invert_repl; eapply ty_and_inv. apply* H. apply* pf3_and_destruct1.
    apply pf3_and_destruct2 in H2; auto. eauto.
    apply pf3_and_destruct1 in H2; auto. eauto.
    invert_repl. apply pf3_and_destruct2 in H2; auto. eauto.
  - lets Hg: (precise_to_general H1).
    lets Hs: (sngl_path_named Hg). lets Ht: (typed_paths_named Hg).
    invert_repl; eapply ty_all_inv with (L:=dom G). eauto. apply repl_swap in H9. eauto.
    introv Hy. eauto. eauto. eauto.
    introv Hy.
    lets Ho: (repl_open_var y H9 Ht Hs). apply* weaken_subtyp.
Qed.

Lemma invertible_repl_closure : forall G p q r T T' n,
    inert G ->
    G ⊢## p : T ->
    G ⊢! q : typ_sngl r ⪼ typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢## p : T'.
Proof.
  introv Hi Hp Hqr Hrep. gen q r T' n.
  induction Hp; introv Hq Hrep.
  - Case "ty_precise_inv".
    destruct (pf3_inertsngl Hi H) as [[Hin | Hs] | Hr].
    * inversions Hin.
      ** apply* invertible_repl_closure_helper.
      ** invert_repl. eauto.
    * inversions Hs. invert_repl. eauto.
    * inversions Hr. eapply (proj32 invertible_repl_closure_helper); eauto.
  - Case "ty_dec_trm_inv".
    invert_repl. eapply ty_dec_trm_inv. eauto. eapply subtyp_trans_t. apply H. eauto.
  - Case "ty_dec_typ_inv".
    invert_repl; eapply ty_dec_typ_inv.
    * apply Hp; eapply subtyp_trans_t.
    * apply repl_swap in H9. eapply subtyp_trans_t. apply* subtyp_sngl_qp_t. eauto.
    * auto.
    * apply Hp.
    * auto.
    * eapply subtyp_trans_t. apply H0. eauto.
  - Case "ty_bnd_inv".
    invert_repl. eauto.
  - Case "ty_all_inv".
    invert_repl.
    + eapply ty_all_inv with (L:=L \u dom G).
      * apply Hp.
      * apply repl_swap in H7. eauto.
      * introv Hy. eapply narrow_subtyping. apply H0. auto. constructor; auto.
        apply tight_to_general. solve_repl_sub.
    + eapply ty_all_inv with (L:=L \u dom G).
      * apply Hp.
      * auto.
      * introv Hy. eapply subtyp_trans. apply* H0.
        eapply repl_open_var in H7; try solve_names. eapply subtyp_sngl_pq.
        apply* weaken_ty_trm. eapply precise_to_general. apply Hq. apply H7.
  - Case "ty_and_inv".
    invert_repl; eauto.
  - Case "ty_top_inv".
    invert_repl.
  - Case "ty_rec_pq_inv".
    invert_repl. eauto.
  - Case "ty_sel_pq_inv".
    assert (exists r''', T' = typ_path r''' A) as [r''' Heq]. {
      invert_repl. eauto.
    } subst.
    destruct (repl_prefixes_sel Hrep) as [bs [He1 He2]]. subst.
    destruct (repl_prefixes_sel H0) as [cs [He1 He2]]. subst.
    specialize (IHHp Hi _ _ H _ _ H0). eauto.
  - Case "ty_sngl_qp_inv".
    assert (exists r''', T' = typ_sngl r''') as [r''' Heq]. {
      invert_repl. eauto.
    } subst.
    destruct (repl_prefixes_sngl Hrep) as [bs [He1 He2]]. subst.
    destruct (repl_prefixes_sngl H0) as [cs [He1 He2]]. subst.
    specialize (IHHp Hi _ _ H _ _ H0). eauto.
Qed.

Lemma invertible_repl_closure2 : forall G p q r T T' n,
    inert G ->
    G ⊢## p : T ->
    G ⊢!! q : typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢## p : T'.
Proof.
  introv Hi Hp Hq Hr. dependent induction Hq.
  - apply* invertible_repl_closure. lets Heq: (pf_sngl_T Hi H). subst. auto.
  - lets Hr': (repl_field_elim _ _ _ Hr).
    eauto.
Qed.

Lemma invertible_repl_closure3 : forall G p q r T T' n,
    inert G ->
    G ⊢## p : T ->
    G ⊢!!! q : typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢## p : T'.
Proof.
  introv Hi Hp Hq Hr. gen p T. dependent induction Hq; introv Hp Hr.
  - apply* invertible_repl_closure2.
  - destruct (repl_insert q Hr) as [U [Hr1 Hr2]].
    lets Hc: (invertible_repl_closure2 Hi Hp H Hr1). apply* IHHq.
Qed.

Lemma invertible_repl_closure_comp: forall G p q r T T',
    inert G ->
    G ⊢## p: T ->
    G ⊢!!! q: typ_sngl r ->
    repl_repeat_typ q r T T' ->
    G ⊢## p: T'.
Proof.
  introv Hi Hp Hq Hc. gen p. dependent induction Hc; introv Hp; eauto.
  unfolds repl_some_typ. destruct_all.
  apply* IHHc. apply* invertible_repl_closure3.
Qed.

Lemma invertible_bot : forall G p,
    inert G ->
    G ⊢## p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  dependent induction H; eauto.
  dependent induction H; eauto.
  false* pf_bot.
Qed.

Lemma invertible_and : forall G p T U,
    inert G ->
    G ⊢## p: typ_and T U ->
    G ⊢## p: T /\ G ⊢## p: U.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  split. apply pf3_and_destruct1 in H. eauto. apply pf3_and_destruct2 in H.
  eauto.
Qed.

Lemma invertible_bnd : forall G p T,
    inert G ->
    G ⊢## p: typ_bnd T ->
    G ⊢## p: open_typ_p p T \/
             (exists q, G ⊢!!! p: typ_sngl q /\ G ⊢## p: open_typ_p q T).
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - destruct (pt3_bnd Hi H) as [Hp | [q [Hp1 Hp2]]]. left*. right*.
  - destruct (IHHp _ Hi eq_refl) as [Hr | [q' [Hr Hr']]].
    * left. apply* invertible_repl_closure. apply* repl_open; solve_names.
    * right. repeat eexists. eauto. eapply repl_open in H0.
      eapply invertible_repl_closure. auto. apply Hr'. apply H. apply H0.
      all: solve_names.
Qed.

Lemma path_sel_inv: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢## q : typ_path p A ->
    G ⊢## q : T.
Proof.
  introv Hi Hp Hq. dependent induction Hq.
  - Case "ty_precise_inv".
    false* pt3_psel.
  - Case "ty_sel_pq_inv".
    destruct (repl_prefixes_sel H0) as [bs [Heq1 Heq2]].
    subst.
    lets Hh: (pt3_field_trans' _ Hi (pt3 (pt2 H)) Hp).
    specialize (IHHq _ _ Hi Hh eq_refl). eauto.
Qed.

Lemma invertible_repl_closure_comp_typed: forall G p T T',
    inert G ->
    G ⊢## p: T ->
    repl_composition_qp G T' T ->
    G ⊢## p: T'.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  destruct H as [p' [q' [n [Hpq Hr']]]].
  apply* invertible_repl_closure. apply* repl_swap.
Qed.
