(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes.

(** * Precise Typing

    Precise typing is used to reason about the types of variables and values.
    Precise typing does not "modify" a variable's or value's type through subtyping.
    - For values, precise typing allows to only retrieve the "immediate" type of the value.
      It types objects with recursive types, and functions with dependent-function types. #<br>#
      For example, if a value is the object [nu(x: {a: T}){a = x.a}], the only way to type
      the object through precise typing is [G ⊢! nu(x: {a: T}){a = x.a}: mu(x: {a: T})].
    - For variables, we start out with a type [T=G(x)] (the type to which the variable is
      bound in [G]). Then we use precise typing to additionally deconstruct [T]
      by using recursion elimination and intersection elimination. #<br>#
      For example, if [G(x)=mu(x: {a: T} /\ {B: S..U})], then we can derive the following
      precise types for [x]:               #<br>#
      [G ⊢! x: mu(x: {a: T} /\ {B: S..U})] #<br>#
      [G ⊢! x: {a: T} /\ {B: S..U}]        #<br>#
      [G ⊢! x: {a: T}]                    #<br>#
      [G ⊢! x: {B: S..U}].                *)

(** ** Precise typing for values *)
Reserved Notation "G '⊢!v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_p : ctx -> val -> typ -> Prop :=

(** [G, x: T ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⊢! lambda(T)t: forall(T) U]     *)
| ty_all_intro_p : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢!v val_lambda T t : typ_all T U

(** [G, x: T^x ⊢ ds^x :: T^x]   #<br>#
    [x fresh]                   #<br>#
    [―――――――――――――――――――――――]   #<br>#
    [G ⊢! nu(T)ds :: mu(T)]        *)
| ty_new_intro_p : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G ⊢!v val_new T ds : typ_bnd T

where "G '⊢!v' v ':' T" := (ty_val_p G v T).

Hint Constructors ty_val_p.


(** * Precise Flow *)
(** We use the precise flow relation to reason about the relations between
    the precise type of a variable [G ⊢! x: T] and the type that the variable
    is bound to in the context [G(x)=T'].#<br>#
    If [G(x) = T], the [precise_flow] relation describes all the types [U] that [x] can
    derive through precise typing ([⊢!] (see paper)).
    If [precise_flow x G T U], denoted as [G ⊢ x: T ⪼ U],
    then [G(x) = T] and [G ⊢! x: U].   #<br>#
    For example, if [G(x) = mu(x: {a: T} /\ {B: S..U})], then we can derive the following
    precise flows for [x]:                                                  #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ mu(x: {a: T} /\ {B: S..U}]         #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ {a: T} /\ {B: S..U}]               #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ {a: T}]                           #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ {B: S..U}]. *)

Reserved Notation "G '⊢!' x ':' T '⪼' U" (at level 40, x at level 59).

Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=

(** [G(x) = T]       #<br>#
    [ok G]           #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! x: T ⪼ T] *)
  | pf_bind : forall x G T,
      binds x T G ->
      G ⊢! x: T ⪼ T

(** [G ⊢! x: T ⪼ mu(U)] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢! x: T ⪼ U^x]       *)
  | pf_open : forall x G T U,
      G ⊢! x: T ⪼ typ_bnd U ->
      G ⊢! x: T ⪼ open_typ x U

(** [G ⊢! x: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! x: T ⪼ U1]        *)
  | pf_and1 : forall x G T U1 U2,
      G ⊢! x: T ⪼ typ_and U1 U2 ->
      G ⊢! x: T ⪼ U1

(** [G ⊢! x: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! x: T ⪼ U2]        *)
  | pf_and2 : forall x G T U1 U2,
      G ⊢! x: T ⪼ typ_and U1 U2 ->
      G ⊢! x: T ⪼ U2

where "G '⊢!' x ':' T '⪼' U" := (precise_flow x G T U).

Hint Constructors precise_flow.

(** ** Precise Flow Lemmas *)

(** If [G ⊢! x: T ⪼ U] then [G(x) = T]. *)
Lemma pf_binds: forall G x T U,
    G ⊢! x: T ⪼ U ->
    binds x T G.
Proof.
  introv Pf. induction Pf; auto.
Qed.

(** If [G(x) = forall(S)T], then [x]'s precise type can be only [forall(S)T]. *)
Lemma precise_flow_all_inv : forall x G S T U,
    G ⊢! x: typ_all S T ⪼ U ->
    U = typ_all S T.
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf S T eq_refl); inversion IHHpf.
Qed.

(** The precise type of a value is inert. *)
Lemma precise_inert_typ : forall G v T,
    G ⊢!v v : T ->
    inert_typ T.
Proof.
  introv Ht. inversions Ht; constructor; rename T0 into T.
  pick_fresh z. assert (Hz: z \notin L) by auto.
  match goal with
  | [H: forall x, _ \notin _ -> _,
     Hz: ?z \notin _ |- _] =>
    specialize (H z Hz);
      pose proof (ty_defs_record_type H);
      assert (Hz': z \notin fv_typ T) by auto;
      apply* record_type_open
  end.
Qed.

(** The following two lemmas say that the type to which a variable is bound in an inert context is inert. *)
Lemma binds_inert : forall G x T,
    binds x T G ->
    inert G ->
    inert_typ T.
Proof.
  introv Bi HiG. induction HiG.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H1. subst. assumption.
    + destruct H1. apply (IHHiG H2).
Qed.

(** See [binds_inert]. *)
Lemma pf_inert_T : forall G x T U,
    inert G ->
    G ⊢! x: T ⪼ U ->
    inert_typ T.
Proof.
  introv Hi Pf. induction Pf; eauto.
  apply (binds_inert H Hi).
Qed.

(** See [inert_typ_bnd_record] *)
Lemma pf_rcd_T : forall G x T U,
    inert G ->
    G ⊢! x: (typ_bnd T) ⪼ U ->
    record_type T.
Proof.
  introv Hi Pf. apply (pf_inert_T Hi) in Pf; inversions Pf; assumption.
Qed.

(** If [G(x) = mu(x: T)], then [x]'s precise type can be only [mu(x: T)]
     or a record type. *)
Lemma pf_bnd_same_or_rcd : forall G x T U,
    inert G ->
    G ⊢! x: typ_bnd T ⪼ U ->
    U = typ_bnd T \/ record_type U.
Proof.
  introv Hi Pf.
  dependent induction Pf; try solve [left*]; right.
  - specialize (IHPf T Hi eq_refl). destruct IHPf as [eq | r].
    * apply open_record_type.
      inversion eq. apply* pf_rcd_T.
    * inversion r. inversion H.
  - destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    exists ls. assumption.
  - destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    eexists. apply* rt_one.
Qed.

(** If [x]'s precise type is [mu(x: U)], then [G(x) = mu(x: U)] *)
Lemma pf_inert_bnd_U: forall G x T U,
    inert G ->
    G ⊢! x: T ⪼ typ_bnd U ->
    T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf).
  destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf) as [Heq | Hr].
    + auto.
    + inversion Hr. inversion H0.
Qed.

(** If [x]'s precise type is a field or type declaration, then [G(x)] is
    a recursive type. *)
Lemma pf_inert_rcd_U: forall G x T D,
    inert G ->
    G ⊢! x: T ⪼ typ_rcd D ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf).
  destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - exists* T.
Qed.


(** If [x]'s precise type is a record type, then [G(x)] is a recursive type. *)
Lemma pf_inert_rcd_typ_U: forall G x T Ds,
    inert G ->
    G ⊢! x: T ⪼ Ds ->
    record_type Ds ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf Hr.
  lets HT: (pf_inert_T Hi Pf).
  destruct HT.
  - apply precise_flow_all_inv in Pf. subst.
    inversion Hr. inversion H.
  - exists* T.
Qed.

(** The following two lemmas express that if [x]'s precise type is a function type,
    then [G(x)] is the same function type. *)
Lemma pf_inert_lambda_U : forall x G S T U,
    inert G ->
    G ⊢! x: U ⪼ typ_all S T ->
    U = typ_all S T.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert_T Hi Pf).
  destruct Hiu.
  - apply precise_flow_all_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf) as [H1 | H1]; inversions H1.
    inversion H0.
Qed.

(** See [pf_inert_lambda_U]. *)
Lemma inert_precise_all_inv : forall x G S T U,
    inert G ->
    G ⊢! x : U ⪼ typ_all S T ->
    binds x (typ_all S T) G.
Proof.
  introv Hi Htyp. lets H: (pf_inert_lambda_U Hi Htyp). subst.
  apply* pf_binds.
Qed.

(** In an inert context, the precise type of a variable
    cannot be bottom. *)
Lemma pf_bot_false : forall G x T,
    inert G ->
    G ⊢! x: T ⪼ typ_bot ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf); inversion H0. inversion H1.
Qed.

(** In an inert context, the precise type of
    a variable cannot be type selection. *)
Lemma pf_psel_false : forall G T x y A,
    inert G ->
    G ⊢! x: T ⪼ typ_sel y A ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf); inversion H0. inversion H1.
Qed.

(** If [G(x) = mu(T)], and [G ⊢! x: ... /\ D /\ ...], then [T^x = ... /\ D /\ ...]. *)
Lemma pf_record_sub : forall x G T T' D,
    inert G ->
    G ⊢! x: typ_bnd T ⪼ T' ->
    record_has T' D ->
    record_has (open_typ x T) D.
Proof.
  introv Hi Pf Hr. dependent induction Pf; auto.
  - inversions Hr.
  - apply (pf_inert_bnd_U Hi) in Pf. congruence.
Qed.

(** If [G(x) = mu(S)] and [G ⊢! x: D], where [D] is a field or type declaration,
    then [S^x = ... /\ D /\ ...]. *)
Lemma precise_flow_record_has: forall S G x D,
    inert G ->
    G ⊢! x: typ_bnd S ⪼ typ_rcd D ->
    record_has (open_typ x S) D.
Proof.
  introv Hi Pf. apply* pf_record_sub.
Qed.

(** If
    - [G ⊢! x: mu(T) ⪼ {A: T1..T1}]
    - [G ⊢! x: mu(T) ⪼ {A: T2..T2}]
    then [T1 = T2]. *)
Lemma pf_record_unique_tight_bounds_rec : forall G x T A T1 T2,
    inert G ->
    G ⊢! x: typ_bnd T ⪼ typ_rcd (dec_typ A T1 T1) ->
    G ⊢! x: typ_bnd T ⪼ typ_rcd (dec_typ A T2 T2) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (precise_flow_record_has Hi Pf1) as H1.
  pose proof (precise_flow_record_has Hi Pf2) as H2.
  eapply unique_rcd_typ; eauto.
  apply open_record_type; apply* pf_rcd_T.
Qed.

(** If
    - [G ⊢! x: T ⪼ {A: T1..T1}]
    - [G ⊢! x: T ⪼ {A: T2..T2}]
    then [T1 = T2]. *)(** *)
Lemma pf_inert_unique_tight_bounds : forall G x T T1 T2 A,
    inert G ->
    G ⊢! x: T ⪼ typ_rcd (dec_typ A T1 T1) ->
    G ⊢! x: T ⪼ typ_rcd (dec_typ A T2 T2) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (pf_inert_rcd_U Hi Pf1) as [?U ?H]; subst.
  apply* pf_record_unique_tight_bounds_rec.
Qed.

(** The type to which a variable is bound in an environment is unique. *)
Lemma x_bound_unique: forall G x T1 T2 U1 U2,
    G ⊢! x: T1 ⪼ U1 ->
    G ⊢! x: T2 ⪼ U2 ->
    T1 = T2.
Proof.
  introv Pf1 Pf2.
  apply pf_binds in Pf1.
  apply pf_binds in Pf2.
  apply (binds_functional Pf1 Pf2).
Qed.

(** If a typing context is inert, then the variables in its domain are distinct. #<br>#
    Note: [ok] is defined in [TLC.LibEnv.v]. *)
Lemma inert_ok : forall G,
    inert G ->
    ok G.
Proof.
  introv Hi. induction Hi; auto.
Qed.

Hint Resolve inert_ok.

(** If [G ⊢! x: {A: S..U}] then [S = U]. *)
Lemma pf_dec_typ_inv : forall G x T A S U,
    inert G ->
    G ⊢! x: T ⪼ typ_rcd (dec_typ A S U) ->
    S = U.
Proof.
  introv Hi Pf. destruct (pf_inert_rcd_U Hi Pf) as [V H]. subst.
  destruct (pf_bnd_same_or_rcd Hi Pf); try congruence.
  destruct H as [?ls ?H]. inversions H. inversions* H1.
Qed.

(** Precise typing implies general typing. *)
(** - for variables *)
Lemma precise_to_general: forall G x T U,
    G ⊢! x : T ⪼ U ->
    G ⊢ trm_var (avar_f x) : U.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.

(** - for values *)
Lemma precise_to_general_v: forall G v T,
    G ⊢!v v : T ->
    G ⊢ trm_val v: T.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.
