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

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢## r: μ(T)]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢## p: μ(T[q/p])]      *)
| ty_rec_pq_inv : forall G p q r T T' U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢## r : μ T ->
    repl_typ p q T T' ->
    G ⊢## r : μ T'

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢## r: r'.A]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢## p: (r'.A)[q/p]]      *)
| ty_sel_pq_inv : forall G p q r A bs U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q: U ->
    G ⊢## r : (p •• bs)↓A ->
    G ⊢## r : (q •• bs)↓A

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢## r: r'.type]          #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢## p: (r'.type)[q/p]]      *)
| ty_sngl_pq_inv : forall G p q r bs U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q: U ->
    G ⊢## r : {{ p •• bs }} ->
    G ⊢## r : {{ q •• bs }}

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
  do 2 eexists. exists (dom G). eauto.
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
  lets Hp: (pt3_dec_typ_tight HG H). subst.
  exists U. split*.
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
Lemma repl_sub: forall G p q T U V,
    repl_typ p q T U ->
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
  destruct H as [q [r [S [Hq%precise_to_general [Hq' Hrt]]]]]. destruct_all.
  split.
  - eapply subtyp_trans. apply* subtyp_sngl_qp. apply* precise_to_general2. eauto.
  - eapply subtyp_trans. apply H0. apply repl_swap in Hrt. eapply subtyp_sngl_pq; eauto. apply* precise_to_general2.
Qed.

Ltac solve_repl_sub :=
    try (apply* tight_to_general);
    try solve [apply* repl_sub];
    eauto.

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
    lets Hh: (pt3_field_trans' _ Hi (pt3 (pt2 H)) Hp).
    specialize (IHHq _ _ Hi Hh eq_refl). eauto.
Qed.

Lemma inv_to_precise_sngl_repl_comp: forall G p q,
    G ⊢## p: {{ q }} ->
    exists r, G ⊢!!! p: {{ r }} /\ G ⊢ r ⟿' q.
Proof.
  introv Hp.
  dependent induction Hp.
  - exists q. split*. apply star_refl.
  - specialize (IHHp _ eq_refl). destruct IHHp as [r'' [Hr' Hc']].
    exists r''. split*. apply star_trans with (b:= p •• bs).
    apply star_one. econstructor; eauto. apply Hc'.
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
  inversions H.
  assert (G ⊢!!! p0 •• bs : U).
  { apply (pt3_field_trans' _ Hi (pt3 (pt2 H0)) Hq). }
  destruct (IHHrc _ Hpr _ H).
  - subst. right. eapply pt3_field_trans; eauto.
  - right. eapply pt3_sngl_trans3; eauto. eapply pt3_field_trans; eauto.
Qed.

(** If a path has an invertible type it also has a III-level precise type. *)
Lemma inv_to_prec G p T :
  G ⊢## p : T ->
  exists U, G ⊢!!! p : U.
Proof.
  induction 1; eauto.
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

| ty_rec_pq_invv : forall G p q v T T' U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢##v v : μ T ->
    repl_typ p q T T' ->
    G ⊢##v v : μ T'

where "G '⊢##v' v ':' T" := (ty_val_inv G v T).

Hint Constructors ty_val_inv.

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
  exists (dom G) S T. split*.
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

Lemma inv_backtrack G p a T :
  G ⊢## p • a : T ->
  exists U, G ⊢## p: U.
Proof.
  introv Hp. dependent induction Hp; eauto.
  apply pt3_backtrack in H as [? ?]; eauto.
Qed.
