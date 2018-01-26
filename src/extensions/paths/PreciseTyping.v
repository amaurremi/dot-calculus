(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions Binding RecordAndInertTypes Subenvironments Narrowing.

Definition inert_sngl T := inert_typ T \/ exists p, T = typ_sngl p.

(* todo consistent lemma naming *)
(* todo finish doc *)
(** ** Precise typing *)
(** Precise typing is used to reason about the types of paths and values.
    Precise typing does not "modify" a path's or value's type through subtyping.
    - For values, precise typing allows to only retrieve the "immediate" type of the value.
      It types objects with recursive types, and functions with dependent-function types. #<br>#
      For example, if a value is the object [nu(x: {a: T}){a = x.a}], the only way to type
      the object through precise typing is [G ⊢! nu(x: {a: T}){a = x.a}: mu(x: {a: T})].
    - For paths, we start out with a type [T=G(x)] (the type to which the variable is
      bound in [G]). Then we use precise typing to additionally deconstruct [T]
      by using recursion elimination and intersection elimination. #<br>#
      For example, if [G(x)=mu(x: {a: T} /\ {B: S..U})], then we can derive the following
      precise types for [x]:               #<br>#
      [G ⊢! p: mu(x: {a: T} /\ {B: S..U})] #<br>#
      [G ⊢! p: {a: T} /\ {B: S..U}]        #<br>#
      [G ⊢! p: {a: T}]                    #<br>#
      [G ⊢! p: {B: S..U}].                *)

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

(** [x; []; P; G, x: T^x ⊢ ds^x: T^x]       #<br>#
    [x fresh]                               #<br>#
    [―――――――――――――――――――――――――――――――]       #<br>#
    [G ⊢! ν(T)ds: μ(T)]                     *)
| ty_new_intro_p
     : forall (L : fset var) (G : env typ) (T : typ) (ds : defs) (P : paths),
       (forall x : var, x \notin L -> x; nil; P; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T) ->
       G ⊢!v val_new T ds : typ_bnd T

where "G '⊢!v' v ':' T" := (ty_val_p G v T).

Hint Constructors ty_val_p.


(** * Precise Flow *)
(** We use the precise flow relation to reason about the relations between
    the precise type of a path [G |-! p: T] and the type that the variable
    is bound to in the context [G(x)=T'].#<br>#
    If [G(x) = T], the [precise_flow] relation describes all the types [U] that [x] can
    derive through precise typing ([|-!], see [ty_trm_p]).
    If [precise_flow x G T U], then [G(x) = T] and [G |-! x: U].   #<br>#
    For example, if [G(x) = mu(x: {a: T} /\ {B: S..U})], then we can derive the following
    precise flows for [x]:                                                 #<br>#
    [G ⊢! p: mu(x: {a: T} /\ {B: S..U}) ⪼ mu(x: {a: T} /\ {B: S..U}]         #<br>#
    [G ⊢! p: mu(x: {a: T} /\ {B: S..U}) ⪼ {a: T} /\ {B: S..U}]               #<br>#
    [G ⊢! p: mu(x: {a: T} /\ {B: S..U}) ⪼ {a: T}]                           #<br>#
    [G ⊢! p: mu(x: {a: T} /\ {B: S..U}) ⪼ {B: S..U}]. *)

Reserved Notation "G '⊢!' p ':' T '⪼' U" (at level 40, p at level 59).

Inductive precise_flow : path -> ctx -> typ -> typ -> Prop :=

(** [G(x) = T]       #<br>#
    [ok G]           #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! x: T ⪼ T] *)
| pf_bind : forall x G T,
      ok G ->
      binds x T G ->
      G ⊢! pvar x: T ⪼ T

(** [G ⊢! p: T ⪼ {a: U}]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p.a: U ⪼ U]        *)
  | pf_fld : forall G p a T U,
      G ⊢! p: T ⪼ typ_rcd {a ⦂ U} ->
      G ⊢! p•a : U ⪼ U

(** [G ⊢! p: T ⪼ mu(U)] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢! p: T ⪼ U^x]       *)
  | pf_open : forall p G T U,
      G ⊢! p: T ⪼ typ_bnd U ->
      G ⊢! p: T ⪼ open_typ_p p U

(** [G ⊢! p: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p: T ⪼ U1]        *)
  | pf_and1 : forall p G T U1 U2,
      G ⊢! p: T ⪼ typ_and U1 U2 ->
      G ⊢! p: T ⪼ U1

(** [G ⊢! p: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p: T ⪼ U2]        *)
  | pf_and2 : forall p G T U1 U2,
      G ⊢! p: T ⪼ typ_and U1 U2 ->
      G ⊢! p: T ⪼ U2

(** [G ⊢! p: q.type ⪼ _  ] #<br>#
    [G ⊢! q: T ⪼ _       ] #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢! p: q.type ⪼ T  ]      *)
| pf_sngl : forall G p q T T' U,
    G ⊢! p : typ_sngl q ⪼ U ->
    G ⊢! q : T ⪼ T' ->
    G ⊢! p : T ⪼ T

| pf_repl : forall G p q T U U',
    G ⊢! p : typ_sngl q ⪼ T ->
    G ⊢! p : U ⪼ U' ->
    inert_typ U ->
    G ⊢! p : U ⪼ repl_typ p q U'

where "G '⊢!' p ':' T '⪼' U" := (precise_flow p G T U).

Hint Constructors precise_flow.

Ltac fresh_constructor_p :=
  apply_fresh ty_new_intro_p as z ||
  apply_fresh ty_all_intro_p as z; auto.

Lemma precise_to_general_h: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢ trm_path p: T /\ G ⊢ trm_path p: U.
Proof.
  intros. induction H; intros; subst; destruct_all; eauto.
  split; constructor*.
Qed.

(** Precise typing implies general typing. *)
(** - for variables *)
Lemma precise_to_general: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢ trm_path p: U.
Proof.
  apply* precise_to_general_h.
Qed.

(** - for values *)
Lemma precise_to_general_v: forall G v T,
    G ⊢!v v : T ->
    G ⊢ trm_val v: T.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.

Lemma narrow_precise_v : forall G G' v T,
    G ⊢!v v: T ->
    G' ⪯ G ->
    G' ⊢!v v: T.
Proof.
  introv Hv Hs. inversions Hv; fresh_constructor_p;
  assert (z \notin L) as Hz by auto; specialize (H z Hz);
  (apply* narrow_typing || apply* narrow_defs); destruct (subenv_implies_ok Hs);
  apply* subenv_extend; apply ok_push.
Qed.

(** ** Precise Flow Lemmas *)

Lemma pf_top_top: forall p G T,
    G ⊢! p: typ_top ⪼ T ->
    T = typ_top.
Proof.
  introv Pf.
  dependent induction Pf; auto;
    try (specialize (IHPf eq_refl); inversion IHPf).
  specialize (IHPf2 eq_refl). subst*.
Qed.

(** The following two lemmas say that the type to which a variable is bound in an inert context is inert. *)
Lemma binds_inert : forall G x T,
    binds x T G ->
    inert G ->
    inert_typ T.
Proof.
  introv Bi Hinert. induction Hinert.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H1. subst. assumption.
    + destruct H1. apply (IHHinert H2).
Qed.

(** If [G ⊢! x: T ⪼ U] then [G(x) = T]. *)
Lemma pf_binds: forall G x T U,
    inert G ->
    G ⊢! pvar x: T ⪼ U ->
    binds x T G.
Proof.
  introv Hi Pf. dependent induction Pf; auto. destruct (last_field _ _ x) as [bs Hbs].
  inversion* Hbs. specialize (IHPf1 _ Hi eq_refl). apply (binds_inert IHPf1) in Hi. inversion Hi.
Qed.

Lemma pf_precise_U: forall G p T U,
    G ⊢! p: T ⪼ U ->
    G ⊢! p: T ⪼ T.
Proof.
  introv Hp. induction Hp; eauto.
Qed.

(** The precise type of a value is inert. *)
Lemma precise_inert_typ : forall G v T,
    G ⊢!v v : T ->
    inert_typ T.
Proof.
  introv Ht. inversions Ht. econstructor; rename T0 into T.
  pick_fresh z. assert (Hz: z \notin L) by auto.
  match goal with
  | [H: forall x, _ \notin _ -> _ |- _ ] =>
    specialize (H z Hz);
      pose proof (ty_defs_record_type H) as Hr;
      destruct Hr as [ls Hr];
      apply inert_typ_bnd with ls;
      apply* record_open
  end.
Qed.

Lemma pf_lambda_T : forall G p T U S,
    G ⊢! p: typ_all T U ⪼ S ->
    exists T' U', S = typ_all T' U'.
Proof.
  introv Pf. dependent induction Pf;
               try (repeat eexists; specialize (IHPf _ _ eq_refl); destruct_all; inversion IHPf);
               try (specialize (IHPf _ _ eq_refl); destruct_all; inversion H).
  specialize (IHPf2 _ _ eq_refl). destruct_all. subst. repeat eexists.
Qed.

(** See [binds_inert]. *)
Lemma pf_inert_rcd_TU : forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ U ->
    inert_sngl T /\ (inert_sngl U \/ record_type U).
Proof.
  introv Hi Pf. induction Pf; eauto; unfolds inert_sngl.
  - apply (binds_inert H0) in Hi. split; left*.
  - destruct (IHPf Hi) as [HT [Hd | Hd]]. destruct_all; inversion H.
    inversions Hd. inversions H. inversions H1. auto. split. right*. left. right*.
  - split*. destruct (IHPf Hi) as [HT [Hd | Hd]]. destruct_all; try solve [inversion H].
    right. inversions H. eexists. apply* open_record_typ_p.
    subst. right. inversions H. eexists. apply* open_record_typ_p.
    inversion Hd. inversion H.
  - split*. destruct (IHPf Hi) as [HT [Hd | Hd]]; destruct_all; try solve [inversion H].
    right. inversions Hd. inversion* H0.
    subst. right. inversions Hd. inversion* H.
  - split*. destruct (IHPf Hi) as [HT [Hd | Hd]]; destruct_all; try solve [inversion H].
    right. inversions Hd. inversions H0. eauto.
    subst. right. inversions Hd. inversion* H.
  - split*.
  - split. auto. specialize (IHPf1 Hi). specialize (IHPf2 Hi).
    destruct_all; inversions H0; inversions H2;
      try solve [left; left; apply* inert_repl];
      try solve [left; right; eexists; simpl; eauto];
      try solve [right; unfolds record_type; destruct_all; eexists; apply* inert_repl_mut].
Qed.

(** See [binds_inert]. *)
Lemma pf_inert_T : forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ U ->
    inert_sngl T.
Proof.
  apply* pf_inert_rcd_TU.
Qed.

(** See [inert_typ_bnd_record] *)
Lemma pf_rcd_T : forall G p T U,
    inert G ->
    precise_flow p G (typ_bnd T) U ->
    record_type T.
Proof.
  introv Hi Pf. apply pf_inert_T in Pf; inversions Pf; eauto. inversion* H. destruct_all. inversion H.
Qed.

(** If [G(x) = mu(x: T)], then [x]'s precise type can be only [mu(x: T)]
     or a record type. *)
Lemma pf_inert_or_rcd : forall G p T U,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ U ->
    U = typ_bnd T \/ record_type U.
Proof.
  introv Hi Pf.
  dependent induction Pf; try solve [left*].
  - specialize (IHPf T Hi eq_refl). destruct IHPf as [eq | r].
    * inversions eq. right. lets Hr: (pf_rcd_T Hi Pf).
      apply* open_record_type_p.
    * inversion r. inversion H.
  - right. destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    exists ls. assumption.
  - right. destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    eexists. apply* rt_one.
  - specialize (IHPf2 _ Hi eq_refl). destruct_all; subst. admit.
    right. unfolds record_type. destruct_all. eexists. apply* inert_repl_mut.
Qed.

Lemma pf_sngl_U: forall G p q U,
    G ⊢! p : typ_sngl q ⪼ U ->
    U = typ_sngl q.
Proof.
  introv Hp. dependent induction Hp; eauto; try (specialize (IHHp _ eq_refl); inversion IHHp).
  inversion H.
Qed.

(** If [x]'s precise type is [mu(x: U)], then [G(x) = mu(x: U)] *)
Lemma pf_inert_bnd_U: forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ typ_bnd U ->
    T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf).
  inversions HT; dependent induction Pf; auto;
    try solve [destruct_all; subst; apply pf_sngl_U in Pf; inversion Pf].
  - destruct U0; inversions x.
    specialize (IHPf _ Hi eq_refl H). destruct_all; subst; inversions H. inversion H1.
  - inversions H. apply pf_lambda_T in Pf. inversion Pf.
    destruct_all. inversion H.
    destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
    * inversions Heq.
    * inversions Hr. inversions H. inversions H3.
  - inversions H. apply pf_lambda_T in Pf. inversion Pf.
    destruct_all. inversion H.
    destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
    * inversions Heq.
    * inversions Hr. inversions H.
  - destruct U'; inversions x. admit.
  - destruct_all. subst. inversion H.
Qed.

Lemma pf_sngl_T: forall G p q T,
    inert G ->
    G ⊢! p : T ⪼ typ_sngl q ->
    T = typ_sngl q.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct U; inversions x. lets H: (pf_inert_bnd_U Hi Hp). subst.
  apply (pf_inert_T Hi) in Hp. inversion* Hp. inversions H. inversion H1. destruct_all.
  inversion H.
  destruct (pf_inert_rcd_TU Hi Hp) as [_ [H | H]]. inversion H. inversion H0. destruct_all. inversion H0.
  inversions H. inversions H0. inversion H2.
  destruct (pf_inert_rcd_TU Hi Hp) as [_ [H | H]]. inversion H. inversion H0. destruct_all.
  inversion H0. inversion H. inversion H0.
  destruct U'; inversions x. admit.
Qed.

(** If [x]'s precise type is a field or type declaration, then [G(x)] is
    a recursive type. *)
Lemma pf_inert_rcd_U: forall G p T D,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd D ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf).
  inversions HT; dependent induction Pf; auto;
    try (solve [(destruct_all; subst; inversion H) |
                (destruct_all; subst; apply pf_sngl_U in Pf; inversion Pf)]).
  - inversion H1.
  - destruct U; inversions x. apply (pf_inert_bnd_U Hi) in Pf. destruct_all; subst; eauto.
  - inversions H. apply pf_lambda_T in Pf. destruct_all. inversion H. eauto.
  - inversions H. apply pf_lambda_T in Pf. destruct_all. inversion H. eauto.
  - destruct U'; inversions x. specialize (IHPf2 _ Hi eq_refl H0). destruct_all. subst. eauto.
  - destruct_all. inversion H1.
Qed.

(** If [x]'s precise type is a record type, then [G(x)] is a recursive type. *)
Lemma pf_inert_rcd_typ_U: forall G p T Ds,
    inert G ->
    G ⊢! p: T ⪼ Ds ->
    record_type Ds ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf Hr.
  lets HT: (pf_inert_T Hi Pf).
  destruct* HT.
  inversions H.
  apply pf_lambda_T in Pf. destruct_all. subst. inversion Hr. inversion H. eauto. destruct_all. subst.
  apply pf_sngl_U in Pf. subst. inversion Hr. inversion H.
Qed.

(** The following two lemmas express that if [x]'s precise type is a function type,
    then [G(x)] is the same function type. *)
Lemma pf_inert_lambda_U : forall p G S T U,
    inert G ->
    G ⊢! p: U ⪼ typ_all S T ->
    exists S' T', U = typ_all S' T'.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert_T Hi Pf).
  inversions Hiu.
  - inversions H. apply pf_lambda_T in Pf. destruct_all. repeat eexists.
    destruct (pf_inert_or_rcd Hi Pf) as [H1 | H1]; inversions H1. inversion H.
  - destruct_all; subst; apply pf_sngl_U in Pf; inversion Pf.
Qed.

(** See [pf_inert_lambda_U]. *)
Lemma inert_precise_all_inv : forall x G S T U,
    inert G ->
    G ⊢! pvar x : U ⪼ typ_all S T ->
    exists S' T', binds x (typ_all S' T') G.
Proof.
  introv Hi Htyp. lets H: (pf_inert_lambda_U Hi Htyp). subst. destruct_all; subst.
  repeat eexists. apply* pf_binds.
Qed.

(** In an inert context, the precise type of a variable
    cannot be bottom. *)
Lemma pf_bot_false : forall G p T,
    inert G ->
    G ⊢! p: T ⪼ typ_bot ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). inversions HT.
  - inversions H. apply pf_lambda_T in Pf. destruct_all. inversion H.
    destruct (pf_inert_or_rcd Hi Pf); inversion H0; inversion H. inversion H5. inversion H7.
  - destruct_all. subst. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** In an inert context, the precise type of
    a variable cannot be type selection. *)
Lemma pf_psel_false : forall G T p q A,
    inert G ->
    G ⊢! p: T ⪼ typ_path q A ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). inversions HT.
  - inversions H.
    * apply pf_lambda_T in Pf. destruct_all. inversion H.
    * destruct (pf_inert_or_rcd Hi Pf); inversion H. inversion H1.
  - destruct H as [r Heq]. subst. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** If [G(x) = mu(T)], and [G ⊢! p: ... /\ D /\ ...], then [T^x = ... /\ D /\ ...]. *)
Lemma pf_record_sub : forall p G T T' D,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ T' ->
    record_has T' D ->
    record_has (open_typ_p p T) D.
Proof.
  introv Hi Pf Hr. dependent induction Pf.
  - inversions Hr.
  - inversions Hr.
  - apply (pf_inert_bnd_U Hi) in Pf. inversion* Pf.
  - apply* IHPf.
  - apply* IHPf.
  - inversion Hr.
  - Abort.

(** If [G(x) = mu(S)] and [G ⊢! p: D], where [D] is a field or type declaration,
    then [S^x = ... /\ D /\ ...]. *)
Lemma precise_flow_record_has: forall S G p D,
    inert G ->
    G ⊢! p: typ_bnd S ⪼ typ_rcd D ->
    record_has (open_typ_p p S) D.
Proof.
  introv Hi Pf. Abort. (*apply* pf_record_sub.
Qed.*)

(** If
    - [G ⊢! p: mu(T) ⪼ {A: T1..T1}]
    - [G ⊢! p: mu(T) ⪼ {A: T2..T2}]
    then [T1 = T2]. *)
Lemma pf_record_unique_tight_bounds_rec : forall G p T A T1 T2,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ typ_rcd {A >: T1 <: T1} ->
    G ⊢! p: typ_bnd T ⪼ typ_rcd {A >: T2 <: T2} ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (precise_flow_record_has Hi Pf1) as H1.
  pose proof (precise_flow_record_has Hi Pf2) as H2.
  lets Hr: (pf_rcd_T Hi Pf1).
  assert (record_type (open_typ_p p T)) as Hrt
      by apply* open_record_type_p.
  apply* unique_rcd_typ.
Qed.

Lemma pf_rcd_unique: forall G p T a U1 U2,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd {a ⦂ U1} ->
    G ⊢! p: T ⪼ typ_rcd {a ⦂ U2} ->
    U1 = U2.
Proof.
  introv Hi Pf1 Pf2.
  destruct (pf_inert_rcd_U Hi Pf1) as [T1 He1]. subst.
  destruct (pf_inert_or_rcd Hi Pf1) as [Ht | Ht]; inversions Ht.
  destruct (pf_inert_or_rcd Hi Pf2) as [Ht | Ht]; inversions Ht.
  dependent induction Pf1.
  - lets Hb: (pf_inert_bnd_U Hi Pf1). inversions Hb.
    destruct U; inversions x. admit.
  - admit.
  - admit.
(*  - assert (record_type (typ_rcd (dec_trm a U2))) as Hrt. {

      eexists. apply* rt_one. constructor.

    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    destruct U; inversions x. destruct d; inversions H0.
    apply (pf_inert_bnd_U Hi) in Pf1. inversions Pf1.
    lets Hr: (precise_flow_record_has Hi Pf2). inversion* Hr.
  - assert (record_type (typ_rcd (dec_trm a U2))) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    assert (record_has (typ_and (typ_rcd (dec_trm a U1)) U0) (dec_trm a U1)) as H
        by (apply* rh_andl).
    lets Hr1: (pf_record_sub Hi Pf1 H).
    lets Hr2: (precise_flow_record_has Hi Pf2).
    assert (record_type (open_typ_p p S)) as Hs. {
      apply open_record_type_p. apply pf_inert_T in Pf1; auto. inversions Pf1. inversion* H1.
    }
    apply* unique_rcd_trm.
  - assert (record_type (typ_rcd (dec_trm a U2))) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    assert (record_has (typ_and U3 (typ_rcd (dec_trm a U1))) (dec_trm a U1)) as H
        by (apply* rh_andr).
    lets Hr1: (pf_record_sub Hi Pf1 H).
    lets Hr2: (precise_flow_record_has Hi Pf2).
    assert (record_type (open_typ_p p S)) as Hs. {
      apply open_record_type_p. apply pf_inert_T in Pf1; auto. inversions Pf1. inversion* H.
    }
    apply* unique_rcd_trm.*)
Qed.

(* todo: prove that p goes through a series of singleton types after which it
         terminates at a unique value *)
Lemma p_bound_rec_unique: forall G p T1 T2 U1 U2,
    inert G ->
    G ⊢! p: typ_bnd T1 ⪼ U1 ->
    G ⊢! p: typ_bnd T2 ⪼ U2 ->
    T1 = T2.
Proof.
  introv Hi Hp1 Hp2. gen T2 U2. dependent induction Hp1; intros; eauto.
  - apply (pf_binds Hi) in Hp2. apply (binds_func H0) in Hp2. inversion* Hp2.
  - destruct (pf_inert_rcd_U Hi Hp1) as [U Heq]. subst.
    specialize (IHHp1 _ Hi eq_refl _ _ Hp1).
    dependent induction Hp2; eauto; try unfold sel_fields in x.
    * destruct p. inversion x.
    * destruct p0, p. inversions x.
      destruct (pf_inert_rcd_U Hi Hp2) as [T' Heq]. subst.
      specialize (IHHp2 _ _ eq_refl Hp1 Hi). Admitted. (*
  - lets Hs: (pf_sngl_U Hp1_1). subst. specialize (IHHp1_2 _ Hi eq_refl). clear IHHp1_1.
    specialize (IHHp1_2 _ _ Hp1_2).*)

(** If a typing context is inert, then the variables in its domain are distinct. #<br>#
    Note: [ok] is defined in [TLC.LibEnv.v]. *)
Lemma inert_ok : forall G,
    inert G ->
    ok G.
Proof.
  intros G HG. induction G using env_ind.
  auto.
  inversions HG. false* empty_push_inv.
  destruct (eq_push_inv H) as [Hx [HT HG]]. subst.
  apply* ok_push.
Qed.

Hint Resolve inert_ok.

(** If [G ⊢! p: {A: S..U}] then [S = U]. *)
Lemma pf_dec_typ_inv : forall G p T A S U,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd {A >: S <: U} ->
    S = U.
Proof.
  introv Hi Pf. destruct (pf_inert_rcd_U Hi Pf) as [V H]. subst.
  destruct (pf_inert_or_rcd Hi Pf) as [H1 | H1]; inversions H1. inversions H.
  inversions* H1.
Qed.

(*
Lemma narrow_precise : forall G G' x T U,
    G ⊢! x: T ⪼ U->
    G' ⪯ G ->
    exists T', G' ⊢! x: T' ⪼ U.
Proof.
  introv Hx Hs. inversions Hx.
  - admit.

  assert (z \notin L) as Hz by auto; specialize (H z Hz);
  (apply* narrow_typing || apply* narrow_defs); destruct (subenv_implies_ok Hs);
  apply* subenv_extend; apply ok_push.
Qed.
*)

Lemma pf_strengthen: forall G y V x bs T U,
    ok (G & y ~ V) ->
    G & y ~ V ⊢! p_sel (avar_f x) bs : T ⪼ U ->
    x <> y ->
    G ⊢! p_sel (avar_f x) bs : T ⪼ U.
Proof.
  introv Hi Ht Hneq. dependent induction Ht; eauto.
  - apply (binds_push_neq_inv H0) in Hneq. constructor*.
  - destruct p. inversions x.
    specialize (IHHt _ _ _ _ _ Hi eq_refl JMeq_refl Hneq).
    lets Hf: (pf_fld IHHt). eauto.
  - assert (exists G1 G2 V, G = G1 & x ~ V & G2) as Heq. {
      apply precise_to_general in Ht1. destruct (typing_implies_bound Ht1) as [V' Hb].
      apply binds_push_neq_inv in Hb; auto.
      lets Hbd: (binds_destruct Hb). destruct_all. eauto.
    }
    destruct Heq as [G1 [G2 [V' Heq]]]. rewrite Heq in Ht1. rewrite <- concat_assoc in Ht1.
    assert (named_path q) as Hnq. {
      apply precise_to_general in Ht2. apply* typed_paths_named.
    }
    inversions Hnq. destruct H as [cs Heq]. rewrite Heq in Ht1. Admitted.
(*
Lemma sngl_diff_inv: forall G p a T,
    inert G ->
    G ⊢! p : T ⪼ typ_rcd { a ⦂ typ_sngl p•a } ->
    False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  - apply (binds_inert H0) in Hi. inversion Hi.
  - A*)

Lemma precise_sngl_var : forall G x p T,
    inert G ->
    G ⊢! pvar x : typ_sngl p ⪼ T ->
    False.
Proof.
  introv Hi Hx. dependent induction Hx; eauto.
  apply (binds_inert H0) in Hi. inversion Hi.
  unfolds sel_fields. destruct p0. inversion x.
Qed.

Lemma sngl_diff_pf: forall G p a T,
    inert G ->
    G ⊢! p • a : typ_sngl p•a ⪼ T ->
    False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  - apply (binds_inert H0) in Hi. inversion Hi.
  - unfold sel_fields in x. destruct p0, p. inversions x.
    apply pf_fld in Hp. Admitted.
