(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Sequences.
Require Import Coq.Program.Equality List.
Require Import Definitions Binding RecordAndInertTypes Subenvironments Narrowing.

Definition is_sngl T := exists p, T = typ_sngl p.
Definition inert_sngl T := inert_typ T \/ is_sngl T.

Ltac invert_repl :=
  repeat match goal with
         | [H: repl_dec _ _ _ {_ ⦂ _} _ |- _ ] =>
           inversions H
         | [H: repl_dec _ _ _ _ {_ ⦂ _} |- _ ] =>
           inversions H
         | [H: repl_dec _ _ _ {_ >: _ <: _} _ |- _ ] =>
           inversions H
         | [H: repl_dec _ _ _ _ {_ >: _ <: _} |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_rcd _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ (typ_rcd _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_and _ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ (typ_and _ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_bnd _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ (typ_bnd _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_all _ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ (typ_all _ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_path _ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ (typ_path _ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ typ_top _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ typ_top |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ typ_bot _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ typ_bot |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_sngl _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ _ (typ_sngl _) |- _ ] =>
           inversions H
    end.

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
Reserved Notation "G '⊢!!' p ':' T" (at level 40, p at level 59).
Reserved Notation "G '⊢!!!' p ':' T" (at level 40, p at level 59).

Inductive precise_flow : ctx -> path -> typ -> typ -> Prop :=

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

where "G '⊢!' p ':' T '⪼' U" := (precise_flow G p T U).

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
    G ⊢! p : T ⪼ U->
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

Lemma narrow_to_precise_v : forall G G' v T,
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

Lemma pf_U_top: forall p G T,
    G ⊢! p: typ_top ⪼ T ->
    T = typ_top.
Proof.
  introv Pf.
  dependent induction Pf; auto;
    try (specialize (IHPf eq_refl); inversion IHPf).
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

Lemma pf_TT: forall G p T U,
    G ⊢! p: T ⪼ U ->
    G ⊢! p: T ⪼ T.
Proof.
  introv Hp. induction Hp; eauto.
Qed.

(** The precise type of a value is inert. *)
Lemma pfv_inert : forall G v T,
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

Lemma pf_forall_U : forall G p T U S,
    G ⊢! p: typ_all T U ⪼ S->
    S = typ_all T U.
Proof.
  introv Pf. dependent induction Pf; eauto;
               try (repeat specialize (IHPf _ _ eq_refl); destruct_all; inversion IHPf);
               try (specialize (IHPf _ _ eq_refl); destruct_all; inversion H).
Qed.

(** See [binds_inert]. *)
Lemma pf_inertsngl : forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ U ->
    inert_sngl T /\ (inert_sngl U \/ record_type U).
Proof.
  introv Hi Pf. induction Pf; eauto; unfolds inert_sngl.
  - apply (binds_inert H0) in Hi. split; left*.
  - specialize (IHPf Hi). destruct IHPf as [HT [Hd | Hd]].
    * destruct_all; inversion H.
      inversions H1. inversions H. inversions H1.
    * destruct HT as [HT | HT]; split; inversions Hd; inversions H; inversions H1;
        try solve [left*; right*; eexists; auto];
        right*; eexists; auto.
  - split*. destruct (IHPf Hi) as [HT [Hd | Hd]]. destruct_all; try solve [inversion H].
    right. inversions H. eexists. apply* open_record_typ_p.
    subst. right. inversions H. eexists. apply* open_record_typ_p. inversion H. inversion H1.
    inversion H. inversion H1. inversion Hd. inversion H.
  - split*. destruct (IHPf Hi) as [HT [Hd | Hd]]; destruct_all; try solve [inversions H; inversion H1];
    inversions Hd; inversions H0; right*.
  - split*. destruct (IHPf Hi) as [HT [Hd | Hd]]; destruct_all; try solve [inversions H; inversion H1];
              inversions Hd; inversions H0; right*.
Qed.

(** See [binds_inert]. *)
Lemma pf_inert : forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ U ->
    inert_sngl T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply (binds_inert H0) in Hi. left*.
  apply* pf_inertsngl.
Qed.

Hint Resolve pf_inert.

(** See [inert_typ_bnd_record] *)
Lemma pf_rcd_T : forall G p T U,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ U ->
    record_type T.
Proof.
  introv Hi Pf. apply pf_inert in Pf; inversions Pf; eauto. inversion* H. destruct_all. inversions H.
  inversion H0.
Qed.

(** If [G(x) = mu(x: T)], then [x]'s precise type can be only [mu(x: T)]
     or a record type. *)
Lemma pf_rec_rcd_U : forall G p T U,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ U->
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
Qed.

Lemma pf_sngl_U: forall G p q U,
    G ⊢! p : typ_sngl q ⪼ U->
    U = typ_sngl q.
Proof.
  introv Hp. dependent induction Hp; eauto; try (specialize (IHHp _ eq_refl); inversion IHHp).
Qed.

(** If [x]'s precise type is [mu(x: U)], then [G(x) = mu(x: U)] *)
Lemma pf_bnd_T: forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ typ_bnd U ->
    T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf).
  inversions HT.
  - inversions H. apply pf_forall_U in Pf. inversion Pf.
    apply (pf_rec_rcd_U Hi) in Pf. destruct Pf. inversion* H. inversion H. inversion H1.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

Lemma pf_sngl_T: forall G p q T,
    inert G ->
    G ⊢! p : T ⪼ typ_sngl q ->
    T = typ_sngl q.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct U; inversions x. lets H: (pf_bnd_T Hi Hp). subst.
  apply (pf_inert Hi) in Hp. inversion* Hp. inversions H. inversion H1. destruct_all.
  inversion H. inversion H0.
  lets His: (pf_inertsngl Hi Hp). destruct_all; progress (repeat inversions H0); inversion H1; inversions H0.
  inversion H3.
  lets His: (pf_inertsngl Hi Hp). destruct_all; progress (repeat inversions H0); inversion H1; inversions H0.
Qed.

(** If [x]'s precise type is a field or type declaration, then [G(x)] is
    a recursive type. *)
Lemma pf_bnd_T2: forall G p T D,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd D ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf).
  inversions HT; dependent induction Pf; auto;
    try (solve [(destruct_all; subst; inversion H) |
                (destruct_all; subst; apply pf_sngl_U in Pf; inversion Pf)]).
  - inversion H1.
  - destruct U; inversions x. apply (pf_bnd_T Hi) in Pf. destruct_all; subst; eauto.
  - inversions H. apply pf_forall_U in Pf. inversion* Pf. eauto.
  - inversions H. apply pf_forall_U in Pf. destruct_all. inversion Pf. eauto.
  - inversion H1. inversion H2.
  - inversion H. inversion H0.
  - destruct U; inversions x. apply pf_bnd_T in Pf. subst*. auto.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** If [x]'s precise type is a record type, then [G(x)] is a recursive type. *)
Lemma pf_bnd_T3: forall G p T Ds,
    inert G ->
    G ⊢! p: T ⪼ Ds ->
    record_type Ds ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf Hr.
  lets HT: (pf_inert Hi Pf).
  destruct* HT.
  inversions H.
  apply pf_forall_U in Pf. destruct_all. subst. inversion Hr. inversion H. eauto.
  inversions H. apply pf_sngl_U in Pf. subst. inversion Hr. inversion H.
Qed.

(** The following two lemmas express that if [x]'s precise type is a function type,
    then [G(x)] is the same function type. *)
Lemma pf_forall_T : forall p G S T U,
    inert G ->
    G ⊢! p: T ⪼ typ_all S U->
    T = typ_all S U.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert Hi Pf).
  inversions Hiu.
  - inversions H. apply pf_forall_U in Pf. inversion* Pf.
    destruct (pf_rec_rcd_U Hi Pf) as [H1 | H1]; inversions H1. inversion H.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** If [G ⊢! x: T ⪼ U] then [G(x) = T]. *)
(** If [G ⊢! x: T ⪼ U] then [G(x) = T]. *)
Lemma pf_binds: forall G x T U,
    inert G ->
    G ⊢! pvar x: T ⪼ U ->
    binds x T G.
Proof.
  introv Hi Pf. dependent induction Pf; try simpl_dot; auto.
Qed.

(** See [pf_lambda_T]. *)
Lemma binds_forall : forall x G S T U,
    inert G ->
    G ⊢! pvar x : U ⪼ typ_all S T ->
    binds x (typ_all S T) G.
Proof. Abort. (*
  introv Hi Htyp. lets H: (pf_forall_T Hi Htyp). subst. destruct_all; subst.
  repeat eexists. apply* pf_binds.
Qed.*)

(** In an inert context, the precise type of a variable
    cannot be bottom. *)
Lemma pf_bot : forall G p T,
    inert G ->
    G ⊢! p: T ⪼ typ_bot ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf). inversions HT.
  - inversions H. apply pf_forall_U in Pf. inversion Pf.
    destruct (pf_rec_rcd_U Hi Pf); inversion H0; inversion H. inversion H5. inversion H7.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** In an inert context, the precise type of
    a variable cannot be type selection. *)
Lemma pf_psel : forall G T p q A,
    inert G ->
    G ⊢! p: T ⪼ typ_path q A ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf). inversions HT.
  - inversions H.
    * apply pf_forall_U in Pf. inversion Pf.
    * destruct (pf_rec_rcd_U Hi Pf); inversion H. inversion H1.
  - destruct H as [r Heq]. subst. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(*Definition original_path G p T U q :=
    G ⊢! p: T ⪼ U /\
    G ⊢! q: T ⪼ T /\
    (p = q \/ G ⊢! p: typ_sngl q ⪼ typ_sngl q).

Lemma original_path_not_opened: forall G p T U,
    G ⊢! p: T ⪼ U ->
    original_path G p T U p.
Proof.
  introv Hp. unfold original_path. split*. split.
  apply* pf_TT. left*.
Qed.

Lemma original_path_unique: forall G p T1 T2 U1 U2 q1 q2,
    original_path G p T1 U1 q1 ->
    original_path G p T2 U2 q2 ->
    q1 = q2.
Proof.
  introv [Hp1 [Hq1 H1]] [Hp2 [Hq2 H2]].
Admitted.

Lemma original_path_exists: forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ U ->
    exists q T', original_path G p T' T' q.
Proof.
  introv Hi Hp. induction Hp; try specialize (IHHp Hi);
                  try solve [unfolds original_path; destruct_all;
                             do 2 eexists; eauto; split*].
Qed.
*)
(** If [G(x) = mu(T)], and [G ⊢! p: ... /\ D /\ ...], then [T^x = ... /\ D /\ ...]. *)
Lemma pf_record_has_T : forall p G T T' D,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ T' ->
    record_has T' D ->
    (*original_path G p (typ_bnd T) T' q ->
    record_has (open_typ_p q T) D.*)
    record_has (open_typ_p p T) D.
Proof.
  introv Hi Pf Hr.
  dependent induction Pf; eauto; try solve [inversion Hr].
  apply pf_bnd_T in Pf; auto. inversion* Pf.
Qed.

(** If [G(x) = mu(S)] and [G ⊢! p: D], where [D] is a field or type declaration,
    then [S^x = ... /\ D /\ ...]. *)
Lemma pf_record_has_U: forall S G p D,
    inert G ->
    G ⊢! p: typ_bnd S ⪼ typ_rcd D ->
    record_has (open_typ_p p S) D.
Proof.
  introv Hi Pf.
  apply* pf_record_has_T.
Qed.

(** If
    - [G ⊢! p: mu(T) ⪼ {A: T1..T1}]
    - [G ⊢! p: mu(T) ⪼ {A: T2..T2}]
    then [T1 = T2]. *)
Lemma pf_dec_typ_unique : forall G p T A T1 T2,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ typ_rcd {A >: T1 <: T1} ->
    G ⊢! p: typ_bnd T ⪼ typ_rcd {A >: T2 <: T2} ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (pf_record_has_U Hi Pf1) as H1.
  pose proof (pf_record_has_U Hi Pf2) as H2.
  lets Hr: (pf_rcd_T Hi Pf1).
  assert (record_type (open_typ_p p T)) as Hrt
      by apply* open_record_type_p.
  apply* unique_rcd_typ.
 Qed.

Lemma pf_dec_fld_unique : forall G p T a U1 U2,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd {a ⦂ U1} ->
    G ⊢! p: T ⪼ typ_rcd {a ⦂ U2} ->
    U1 = U2.
Proof.
  introv Hi Pf1 Pf2.
  destruct (pf_bnd_T2 Hi Pf1) as [T1 He1]. subst.
  destruct (pf_rec_rcd_U Hi Pf1) as [Ht | Ht]; inversions Ht.
  destruct (pf_rec_rcd_U Hi Pf2) as [Ht | Ht]; inversions Ht.
  dependent induction Pf1.
  - lets Hb: (pf_bnd_T Hi Pf1). inversions Hb.
    destruct U; inversions x. destruct d; inversions H2.
    lets Hrh: (pf_record_has_U Hi Pf2).
    inversion* Hrh.
  - lets Hrh: (pf_record_has_U Hi Pf2).
    assert (record_has (typ_and (typ_rcd {a ⦂ U1}) U0) {a ⦂ U1}) as Hrh' by auto.
    lets Hrh'': (pf_record_has_T Hi Pf1 Hrh'). apply (pf_rcd_T Hi) in Pf2.
    lets Hrt: (open_record_type_p p Pf2). apply* unique_rcd_trm.
  - lets Hrh: (pf_record_has_U Hi Pf2).
    assert (record_has (typ_and U3 (typ_rcd {a ⦂ U1})) {a ⦂ U1}) as Hrh' by auto.
    lets Hrh'': (pf_record_has_T Hi Pf1 Hrh'). apply (pf_rcd_T Hi) in Pf2.
    lets Hrt: (open_record_type_p p Pf2). apply* unique_rcd_trm.
Qed.

Lemma pf_T_unique: forall G p T1 T2 U1 U2,
    inert G ->
    G ⊢! p: T1 ⪼ U1 ->
    G ⊢! p: T2 ⪼ U2 ->
    T1 = T2.
Proof.
  introv Hi Hp1. gen T2 U2. induction Hp1; introv Hp2; eauto.
  - Case "pf_bind".
    apply (pf_binds Hi) in Hp2. eapply binds_func. apply H0. auto.
  - Case "pf_fld".
    gen U T. dependent induction Hp2; introv Hp IH; try simpl_dot; eauto.
    * rename a2 into x. rename f0 into bs. clear IHHp2.
      destruct (pf_bnd_T2 Hi Hp) as [S Heq]. subst. lets Hr: (pf_rcd_T Hi Hp).
      destruct (pf_bnd_T2 Hi Hp2) as [S' Heq]. subst. lets Hr': (pf_rcd_T Hi Hp2).
      specialize (IH Hi _ _ Hp2).
      inversions IH. lets Hrh: (pf_record_has_U Hi Hp2).
      lets Hrh': (pf_record_has_U Hi Hp).
      assert (record_type (open_typ_p (p_sel x bs) S')) as Hrt by apply* open_record_type_p.
      apply* unique_rcd_trm.
Qed.

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
Lemma pf_dec_typ_tight : forall G p T A S U,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd {A >: S <: U}->
    S = U.
Proof.
  introv Hi Pf. destruct (pf_bnd_T2 Hi Pf) as [V H]. subst.
  destruct (pf_rec_rcd_U Hi Pf) as [H1 | H1]; inversions H1. inversions H.
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
    inert (G & y ~ V) ->
    G & y ~ V ⊢! p_sel (avar_f x) bs : T ⪼ U->
    x <> y ->
    G ⊢! p_sel (avar_f x) bs : T ⪼ U.
Proof.
  introv Hi Ht Hneq. dependent induction Ht; eauto.
  - apply (binds_push_neq_inv H0) in Hneq. constructor*.
  - destruct p. inversions x.
    specialize (IHHt _ _ _ _ _ Hi JMeq_refl eq_refl Hneq).
    lets Hf: (pf_fld IHHt). eauto.
Qed.

Lemma pf_var_sngl : forall G x p T,
    inert G ->
    G ⊢! pvar x : typ_sngl p ⪼ T ->
    False.
Proof.
  introv Hi Hx. dependent induction Hx; eauto.
  apply (binds_inert H0) in Hi. inversion Hi.
  unfolds sel_fields. destruct p0. inversion x.
Qed.

Lemma pf_inert_bnd : forall G p T D,
    inert G ->
    G ⊢! p : T ⪼ typ_rcd D ->
    inert_typ T.
Proof.
  introv Hi Hp. lets Hr: (pf_bnd_T2 Hi Hp). destruct_all.
  subst. apply pf_rcd_T in Hp; auto. inversions Hp. apply* inert_typ_bnd.
Qed.

Lemma pf_path_sel: forall G p a T U,
    inert G ->
    G ⊢! p•a : T ⪼ U ->
    exists V W, G ⊢! p: typ_bnd V ⪼ typ_rcd {a ⦂ W}.
Proof.
  introv Hi Hp. dependent induction Hp; try simpl_dot; eauto.
  destruct (pf_bnd_T2 Hi Hp) as [V Heq]. subst. eauto.
Qed.

Inductive precise_typing2: ctx -> path -> typ -> Prop :=

| pt2: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢!! p: U

| pt2_sngl_trans : forall G p q a U,
    G ⊢!! p : typ_sngl q ->
    G ⊢!! q•a : U ->
    G ⊢!! p•a : typ_sngl q•a

where "G '⊢!!' p ':' T" := (precise_typing2 G p T).

Inductive precise_typing3: ctx -> path -> typ -> Prop :=

| pt3: forall G p T,
    G ⊢!! p : T ->
    G ⊢!!! p: T

| pt3_sngl_trans : forall G p q T,
    G ⊢!! p : typ_sngl q ->
    G ⊢!!! q : T ->
    G ⊢!!! p : T

where "G '⊢!!!' p ':' T" := (precise_typing3 G p T).

Hint Constructors precise_typing2 precise_typing3.

Lemma precise_to_general2: forall G p T,
    G ⊢!! p: T ->
    G ⊢ trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto using precise_to_general.
Qed.

Lemma precise_to_general3: forall G p T,
    G ⊢!!! p: T ->
    G ⊢ trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto using precise_to_general2.
Qed.

Lemma pf2_and_destruct1: forall G p T U,
    G ⊢!! p: typ_and T U ->
    G ⊢!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pf2_and_destruct2: forall G p T U,
    G ⊢!! p: typ_and T U ->
    G ⊢!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pf3_and_destruct1: forall G p T U,
    G ⊢!!! p: typ_and T U ->
    G ⊢!!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pf2_and_destruct1.
Qed.

Lemma pf3_and_destruct2: forall G p T U,
    G ⊢!!! p: typ_and T U ->
    G ⊢!!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pf2_and_destruct2.
Qed.

Lemma pf2_inertsngl : forall G p T,
    inert G ->
    G ⊢!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf.
  - apply* pf_inertsngl.
  - left. right. eexists. eauto.
Qed.

Lemma pf3_inertsngl : forall G p T,
    inert G ->
    G ⊢!!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf; eauto;
  apply* pf2_inertsngl.
Qed.

Lemma pf2_bot: forall G p,
    inert G ->
    G ⊢!! p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto using pf_bot.
Qed.

Lemma pf3_bot: forall G p,
    inert G ->
    G ⊢!!! p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto using pf2_bot.
Qed.

Lemma pt3_trans: forall G p q a U,
    G ⊢!! p : typ_sngl q ->
    G ⊢!!! q•a : U ->
    G ⊢!!! p•a : U.
Proof.
  introv Hp Hq. gen p. dependent induction Hq; introv Hp; eauto.
Qed.

Lemma pt3_trans2: forall G p q a U,
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q•a : U ->
    G ⊢!!! p•a : U.
Proof.
  introv Hp Hq. gen a U. dependent induction Hp; introv Hq.
  - apply* pt3_trans.
  - specialize (IHHp _ eq_refl _ _ Hq). apply* pt3_trans.
Qed.

Lemma pt3_field_elim: forall G p a T,
    G ⊢!!! p : typ_rcd { a ⦂ T } ->
    G ⊢!!! p•a : T.
Proof.
  introv Hp. dependent induction Hp.
  - dependent induction H; eauto.
  - specialize (IHHp _ _ eq_refl).
    gen p. dependent induction IHHp; introv Hpq; eauto.
Qed.

Lemma path_elim_prec: forall G p q a T,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! q•a : T ->
    G ⊢!!! p•a : typ_sngl q•a.
Proof.
  introv Hi Hp Hq.
  gen a T. dependent induction Hp; introv Hq.
  - inversion* Hq.
  - specialize (IHHp _ Hi eq_refl _ _ Hq). apply* pt3_trans.
Qed.

Lemma pf_pt2: forall G p T U V,
    inert G ->
    G ⊢! p: T ⪼ U ->
    G ⊢!! p: V ->
    inert_sngl V ->
    T = V.
Proof.
  introv Hi Hp1 Hp2 His. gen T U. induction Hp2; introv Hp1.
  - lets Heq: (pf_T_unique Hi Hp1 H). subst. destruct His.
    * destruct H0. apply* pf_forall_T. apply* pf_bnd_T.
    * inversions H0. destruct_all. apply* pf_sngl_T.
  - destruct (pf_path_sel _ _ Hi Hp1) as [V [W Hp]].
    lets Hpa: (pf_fld Hp). lets Heq: (pf_T_unique Hi Hp1 Hpa). subst.
    assert (inert_sngl (typ_sngl q)) as His'. { right. eexists. auto. }
    specialize (IHHp2_1 Hi His' _ _ Hp). inversion IHHp2_1.
Qed.

Lemma pf_pt2_sngl: forall G p T U q,
    inert G ->
    G ⊢! p: T ⪼ U ->
    G ⊢!! p: typ_sngl q ->
    T = typ_sngl q.
Proof.
  introv Hi Hp1 Hp2. apply* pf_pt2. right. eexists. auto.
Qed.

Lemma field_elim_q0: forall G p q a T,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢!! p•a : T ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen q.
  dependent induction Hpa; introv Hp; eauto.
  - dependent induction H; try simpl_dot; eauto.
    lets Heq: (pf_T_unique Hi Hp H). subst.
    apply pf_sngl_U in H. inversion H.
  - clear IHHpa1 IHHpa2. simpl_dot.
    lets Heq: (pf_pt2_sngl Hi Hp Hpa1). inversion* Heq.
Qed.

Lemma field_elim_q0': forall G p q a T T',
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢! p•a : T ⪼ T' ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen q.
  dependent induction Hpa; introv Hp; try simpl_dot; eauto.
  lets Hp2: (pf_pt2_sngl Hi Hpa Hp). subst.
  apply pf_sngl_U in Hpa. inversion Hpa.
Qed.

Lemma pt2_unique: forall G p T1 T2,
    inert G ->
    G ⊢!! p: T1 ->
    G ⊢!! p: T2 ->
    inert_sngl T1 ->
    inert_sngl T2 ->
    T1 = T2.
Proof.
  introv Hi Hp1 Hp2 His1 His2. gen T2. dependent induction Hp1; introv Hp2 His2.
  - dependent induction Hp2.
    * lets HU: (pf_T_unique Hi H H0). subst.
      admit. (*easy*)
    * clear His2. lets Hp: (pt2_sngl_trans _ Hp2_1 Hp2_2).
      lets Heq: (pf_pt2_sngl Hi H Hp). subst.
      apply* pf_sngl_U.
  - assert (inert_sngl (typ_sngl q)) as His. { right. eexists. auto. }
    clear His1 His.
    gen q U. dependent induction Hp2; introv Hp1 IH1 Hqa IH2; eauto.
    * lets Hp: (pt2_sngl_trans _ Hp1 Hqa).
      lets Heq: (pf_pt2_sngl Hi H Hp). subst. lets Heq: (pf_sngl_U H). auto.
    * simpl_dot.
      assert (inert_sngl (typ_sngl q0)) as His. { right. eexists. auto. }
      assert (inert_sngl (typ_sngl q)) as His'. { right. eexists. auto. }
      specialize (IH1 Hi His _ Hp2_1 His'). inversion* IH1.
Qed.

Lemma field_elim_q: forall G p q a T,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢!! p•a : T ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen a T. dependent induction Hp; introv Hpa.
  - lets Heq: (pf_sngl_T Hi H). subst. apply* field_elim_q0.
  - clear IHHp1 IHHp2.
    gen q0 U. dependent induction Hpa; introv Hp; introv Hq0.
    * apply* field_elim_q0'.
    * unfold sel_fields in x. destruct p0, p. inversions x.
      lets Hxbs: (pt2_sngl_trans _ Hp Hq0).
      assert (inert_sngl (typ_sngl q)) as His. {
        right. eexists. eauto.
      }
      assert (inert_sngl (typ_sngl q0•a)) as His'. {
        right. eexists. eauto.
      }
      lets Hu: (pt2_unique Hi Hpa1 Hxbs His His').
      inversions Hu. eauto.
Qed.

Lemma field_elim_q2: forall G p q a T,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!! p•a : T ->
    exists U, G ⊢!!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen a T. dependent induction Hp; introv Hpa.
  - destruct* (field_elim_q _ Hi H Hpa).
  - specialize (IHHp _ Hi eq_refl).
    destruct (field_elim_q _ Hi H Hpa) as [V Hqa]. apply* IHHp.
Qed.

Lemma field_elim_q3: forall G p q a T,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! p•a : T ->
    exists U, G ⊢!!! q•a: U.
Proof.
  introv Hi Hp Hpa.
  gen q. dependent induction Hpa; introv Hp.
  - gen a T. dependent induction Hp; introv Hpa;
               destruct* (field_elim_q _ Hi H Hpa).
  - clear IHHpa Hpa T. gen a q. dependent induction Hp; introv Hpa.
    * destruct* (field_elim_q _ Hi H Hpa).
    * lets Hp': (pt3_sngl_trans H Hp). apply* field_elim_q2.
Qed.

Lemma pt3_field_elim_p: forall G p q a U,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! p • a : U ->
    G ⊢!!! p • a : typ_sngl q • a.
Proof.
  introv Hi Hpq Hpa. destruct (field_elim_q3 _ Hi Hpq Hpa) as [T Hqa].
  apply* path_elim_prec.
Qed.

Lemma pt2_backtrack : forall G p a T,
    G ⊢!! p • a : T ->
    exists U, G ⊢!! p : U.
Proof.
  introv Hp. dependent induction Hp; eauto.
  - dependent induction H; try simpl_dot; eauto.
  - simpl_dot. eauto.
Qed.

Lemma pt3_backtrack : forall G p a T,
    G ⊢!!! p • a : T ->
    exists U, G ⊢!!! p : U.
Proof.
  introv Hp. dependent induction Hp;
               apply pt2_backtrack in H; destruct_all; eauto.
Qed.

Lemma pt3_sngl_trans3: forall G p q T,
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! q: T ->
    G ⊢!!! p : T.
Proof.
  introv Hp Hq. gen T. dependent induction Hp; introv Hq; eauto.
Qed.

Lemma pt3_field_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q••bs : T ->
    G ⊢!!! p••bs : typ_sngl q••bs.
Proof.
  introv Hi Hp Hq. gen T q. induction bs; introv Hp Hq;
                              unfolds sel_fields; destruct q, p; simpls; auto.
  rewrite proj_rewrite in *.
  destruct (pt3_backtrack _ _ Hq) as [U Hb].
  specialize (IHbs _ _ Hp Hb). rewrite proj_rewrite. apply* path_elim_prec.
Qed.

Lemma pt3_field_trans': forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q••bs : T ->
    G ⊢!!! p••bs : T.
Proof.
  introv Hi Hp1 Hp2. gen p q T.
  induction bs; introv Hp1; introv Hp2; unfolds sel_fields; destruct q, p; simpls.
  - apply* pt3_sngl_trans3.
  - rewrite proj_rewrite in *.
    destruct (pt3_backtrack _ _ Hp2) as [S Hb].
    lets Hh: (pt3_field_trans _ Hi Hp1 Hb).
    apply* pt3_sngl_trans3. apply* path_elim_prec.
Qed.

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

Lemma pt3_trans_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! p••bs : T ->
    G ⊢!!! p••bs : typ_sngl q••bs.
Proof.
  introv Hi Hp Hpbs. gen p q T.
  induction bs; introv Hp; introv Hpbs; unfolds sel_fields; destruct p, q; simpls; auto.
  repeat rewrite proj_rewrite in *. apply* pt3_field_elim_p.
  specialize (IHbs _ _ Hp). apply pt3_backtrack in Hpbs. destruct_all. eauto.
Qed.

Lemma pf_sngl_fld_elim: forall G p q a T U,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢! p•a : T ⪼ U ->
    False.
Proof.
  introv Hi Hp Hpa. dependent induction Hpa; try simpl_dot; eauto.
  lets Hu: (pf_T_unique Hi Hpa Hp). subst. apply pf_sngl_U in Hpa. false*.
Qed.

Lemma pf_sngl_flds_elim: forall G p q T U bs,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢! p••bs : T ⪼ U ->
    bs = nil.
Proof.
  introv Hi Hp Hpbs. gen T U. induction bs; introv Hpbs. auto.
  assert (exists T' U', G ⊢! p •• bs : T' ⪼ U') as [T' [U' Hpbs']]. {
    clear IHbs Hp. dependent induction Hpbs; try simpl_dot; eauto.
    unfolds sel_field, sel_fields. destruct p0, p. inversions x. repeat eexists. eauto.
  }
  specialize (IHbs _ _ Hpbs'). subst. unfold sel_fields in Hpbs. destruct p. simpls.
  rewrite proj_rewrite in *. false* pf_sngl_fld_elim.
Qed.

(** Lemmas about replacement composition *)

Definition typed_repl_comp_qp G T1 T2 :=
  exists p q n,
    G ⊢! p: typ_sngl q ⪼ typ_sngl q /\ repl_typ n q p T1 T2.

Definition repl_composition_qp G := star (typed_repl_comp_qp G).

Lemma repl_comp_sngl_inv : forall G T p,
    repl_composition_qp G T (typ_sngl p) ->
    exists q, T = typ_sngl q.
Proof.
  introv Hr. dependent induction Hr; eauto.
  specialize (IHHr _ eq_refl). destruct_all. subst.
  inversions H. destruct_all. invert_repl. eexists; eauto.
Qed.

Lemma repl_comp_and1: forall G T T' U,
    repl_composition_qp G T T' ->
    repl_composition_qp G (typ_and T U) (typ_and T' U).
Proof.
  introv Hr. dependent induction Hr.
  - apply star_refl.
  - apply star_trans with (b:=typ_and b U); auto. apply star_one.
    unfolds typed_repl_comp_qp. destruct_all.
    repeat eexists; eauto.
Qed.

Lemma repl_comp_and2: forall G T T' U,
    repl_composition_qp G T T' ->
    repl_composition_qp G (typ_and U T) (typ_and U T').
Proof.
  introv Hr. dependent induction Hr.
  - apply star_refl.
  - apply star_trans with (b:=typ_and U b); auto. apply star_one.
    unfolds typed_repl_comp_qp. destruct_all.
    repeat eexists; eauto.
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

Lemma field_typing_comp1: forall G r q a U,
  inert G ->
  repl_composition_qp G (typ_sngl r) (typ_sngl q) ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hq; eauto.
  destruct (repl_comp_sngl_inv Hr) as [p Heq]. subst.
  destruct H as [p' [q' [n [Hp' Hr']]]].
  specialize (IHHr _ _ Hi eq_refl eq_refl _ _ Hq). destruct IHHr as [T Hpa].
  assert (G ⊢!!! p : typ_sngl r) as Hpr. {
    clear Hq Hr. inversions Hr'. gen qx qbs a T. induction bs; introv Hpa Hq. auto.
    simpl. repeat rewrite proj_rewrite in *.
    destruct (pt3_backtrack _ _ Hq) as [T1 Ht1]. simpls. rewrite proj_rewrite in *.
    constructor*.
    simpls. repeat rewrite proj_rewrite in *.
    simpls. rewrite proj_rewrite in *.
    apply pt3_backtrack in Hq. destruct_all. rewrite proj_rewrite in *.
    apply* pt3_field_elim_p.
  }
  apply* field_elim_q3.
Qed.

Lemma field_typing_comp2: forall G r q a U,
  inert G ->
  repl_composition_qp G (typ_sngl q) (typ_sngl r) ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hqa; eauto. inversions H.
  rename x into p.
  destruct H0 as [q' [n [Hp Hr']]].
  assert (exists q', b = typ_sngl q') as [q'' Heq] by inversion* Hr'.
  subst. specialize (IHHr _ _ Hi eq_refl eq_refl). invert_repl. apply* IHHr. clear IHHr Hr.
  gen px pbs a U. induction bs; intros; simpls.
  - rewrite proj_rewrite in *. apply* pt3_trans2.
  - do 2 rewrite app_comm_cons in *. rewrite proj_rewrite_mult in *. apply* pt3_field_trans'.
Qed.

Lemma repl_composition_fld_elim: forall G p q a T,
    inert G ->
    repl_composition_qp G (typ_sngl p) (typ_sngl q) ->
    G ⊢!!! p • a : T ->
    repl_composition_qp G (typ_sngl p•a) (typ_sngl q•a).
Proof.
  introv Hi Hr. gen T. dependent induction Hr; introv Hpa.
  - apply star_refl.
  - assert (exists p', b = typ_sngl p') as [p' Heq]. {
      dependent induction H; destruct_all; eauto. inversions H0. eauto.
    } subst.
    specialize (IHHr _ _ Hi eq_refl eq_refl).
    destruct H as [p'' [q' [n [Hpq Hr']]]]. apply star_trans with (b:=typ_sngl p' • a).
    * apply star_one.
      repeat eexists. apply Hpq.
      inversions Hr'. eapply rsngl. simpl. rewrite app_comm_cons. all: auto.
    * invert_repl. apply* IHHr. clear IHHr. simpls. rewrite app_comm_cons.
      rewrite proj_rewrite_mult in *.
      apply* pt3_field_trans'.
Qed.
