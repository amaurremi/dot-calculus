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

Definition is_sngl T := exists p, T = typ_sngl p.
Definition inert_sngl T := inert_typ T \/ is_sngl T.

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

Reserved Notation "G '⊢!' p ':' T '⪼' U '//' m" (at level 40, p at level 59).

Inductive precise_mode := | not_opened | opened.

Inductive precise_flow : ctx -> path -> typ -> typ -> precise_mode -> Prop :=

(** [G(x) = T]       #<br>#
    [ok G]           #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! x: T ⪼ T] *)
| pf_bind : forall x G T,
      ok G ->
      binds x T G ->
      G ⊢! pvar x: T ⪼ T // not_opened

(** [G ⊢! p: T ⪼ {a: U}]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p.a: U ⪼ U]        *)
  | pf_fld : forall G p a T U,
      G ⊢! p: T ⪼ typ_rcd {a ⦂ U} // opened ->
      G ⊢! p•a : U ⪼ U // not_opened

(** [G ⊢! p: T ⪼ mu(U)] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢! p: T ⪼ U^x]       *)
  | pf_open : forall p G T U,
      G ⊢! p: T ⪼ typ_bnd U // not_opened ->
      G ⊢! p: T ⪼ open_typ_p p U // opened

(** [G ⊢! p: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p: T ⪼ U1]        *)
  | pf_and1 : forall p G T U1 U2,
      G ⊢! p: T ⪼ typ_and U1 U2 // opened ->
      G ⊢! p: T ⪼ U1 // opened

(** [G ⊢! p: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p: T ⪼ U2]        *)
  | pf_and2 : forall p G T U1 U2,
      G ⊢! p: T ⪼ typ_and U1 U2 // opened ->
      G ⊢! p: T ⪼ U2 // opened

  | pf_sngl_trans : forall G p q T U U' m,
      G ⊢! p : T ⪼ typ_sngl q // m ->
      G ⊢! q : U ⪼ U' // opened ->
      G ⊢! p : U ⪼ U' // opened

  | pf_not_opened : forall G p T U,
      G ⊢! p : T ⪼ U // not_opened ->
      G ⊢! p : T ⪼ U // opened

where "G '⊢!' p ':' T '⪼' U '//' m" := (precise_flow G p T U m).


Hint Constructors precise_flow.

Ltac fresh_constructor_p :=
  apply_fresh ty_new_intro_p as z ||
  apply_fresh ty_all_intro_p as z; auto.

Lemma precise_to_general_h: forall G p T U m,
    G ⊢! p : T ⪼ U // m ->
    G ⊢ trm_path p: T /\ G ⊢ trm_path p: U.
Proof.
  intros. induction H; intros; subst; destruct_all; eauto.
  split; constructor*.
Qed.

(** Precise typing implies general typing. *)
(** - for variables *)
Lemma precise_to_general: forall G p T U m,
    G ⊢! p : T ⪼ U // m->
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

Lemma pf_U_top: forall p G T m,
    G ⊢! p: typ_top ⪼ T // m ->
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

Lemma pf_TT: forall G p T U m,
    G ⊢! p: T ⪼ U // m ->
    G ⊢! p: T ⪼ T // m.
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

Lemma pf_forall_U : forall G p T U S m,
    G ⊢! p: typ_all T U ⪼ S // m->
    S = typ_all T U.
Proof.
  introv Pf. dependent induction Pf; eauto;
               try (repeat specialize (IHPf _ _ eq_refl); destruct_all; inversion IHPf);
               try (specialize (IHPf _ _ eq_refl); destruct_all; inversion H).
Qed.

(** See [binds_inert]. *)
Lemma pf_inertsngl : forall G p T U m,
    inert G ->
    G ⊢! p: T ⪼ U // m ->
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
Lemma pf_inert : forall G p T U m,
    inert G ->
    G ⊢! p: T ⪼ U // m ->
    inert_sngl T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply (binds_inert H0) in Hi. left*.
  apply* pf_inertsngl.
Qed.

Hint Resolve pf_inert.

(** See [inert_typ_bnd_record] *)
Lemma pf_rcd_T : forall G p T U m,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ U // m ->
    record_type T.
Proof.
  introv Hi Pf. apply pf_inert in Pf; inversions Pf; eauto. inversion* H. destruct_all. inversions H.
  inversion H0.
Qed.

(** If [G(x) = mu(x: T)], then [x]'s precise type can be only [mu(x: T)]
     or a record type. *)
Lemma pf_rec_rcd_U : forall G p T U m,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ U // m->
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
  - eauto.
  - eauto.
Qed.

Lemma pf_sngl_U: forall G p q U m,
    G ⊢! p : typ_sngl q ⪼ U // m->
    U = typ_sngl q.
Proof.
  introv Hp. dependent induction Hp; eauto; try (specialize (IHHp _ eq_refl); inversion IHHp).
Qed.

(** If [x]'s precise type is [mu(x: U)], then [G(x) = mu(x: U)] *)
Lemma pf_bnd_T: forall G p T U m,
    inert G ->
    G ⊢! p: T ⪼ typ_bnd U // m ->
    T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf).
  inversions HT.
  - inversions H. apply pf_forall_U in Pf. inversion Pf.
    apply (pf_rec_rcd_U Hi) in Pf. destruct Pf. inversion* H. inversion H. inversion H1.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

Lemma pf_sngl_T: forall G p q T m,
    inert G ->
    G ⊢! p : T ⪼ typ_sngl q // m ->
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
Lemma pf_bnd_T2: forall G p T D m,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd D // m ->
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
  - eauto.
  - eauto.
  - inversion H1. inversion H2.
  - inversion H. inversion H0.
  - destruct U; inversions x. apply pf_bnd_T in Pf. subst*. auto.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
  - eauto.
  - eauto.
Qed.

(** If [x]'s precise type is a record type, then [G(x)] is a recursive type. *)
Lemma pf_bnd_T3: forall G p T Ds m,
    inert G ->
    G ⊢! p: T ⪼ Ds // m ->
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
Lemma pf_forall_T : forall p G S T U m,
    inert G ->
    G ⊢! p: T ⪼ typ_all S U // m->
    exists S' U', T = typ_all S' U'.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert Hi Pf).
  inversions Hiu.
  - inversions H. apply pf_forall_U in Pf. destruct_all. repeat eexists.
    destruct (pf_rec_rcd_U Hi Pf) as [H1 | H1]; inversions H1. inversion H.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** See [pf_lambda_T]. *)
Lemma binds_forall : forall x G S T U m,
    inert G ->
    G ⊢! pvar x : U ⪼ typ_all S T // m ->
    binds x (typ_all S T) G.
Proof. Abort. (*
  introv Hi Htyp. lets H: (pf_forall_T Hi Htyp). subst. destruct_all; subst.
  repeat eexists. apply* pf_binds.
Qed.*)

(** In an inert context, the precise type of a variable
    cannot be bottom. *)
Lemma pf_bot : forall G p T m,
    inert G ->
    G ⊢! p: T ⪼ typ_bot // m ->
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
Lemma pf_psel : forall G T p q A m,
    inert G ->
    G ⊢! p: T ⪼ typ_path q A // m ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf). inversions HT.
  - inversions H.
    * apply pf_forall_U in Pf. inversion Pf.
    * destruct (pf_rec_rcd_U Hi Pf); inversion H. inversion H1.
  - destruct H as [r Heq]. subst. apply pf_sngl_U in Pf. inversion Pf.
Qed.

Definition original_path G p T q := forall U,
    G ⊢! p: T ⪼ U // opened ->
            G ⊢! q: T ⪼ T // not_opened /\
            (p = q \/ G ⊢! p: typ_sngl q ⪼ typ_sngl q // opened).

Lemma original_path_not_opened: forall G p T U,
    G ⊢! p: T ⪼ U // not_opened ->
    original_path G p T p.
Proof.
  introv Hp. unfold original_path. introv Hp'. split*.
  apply* pf_TT.
Qed.

Lemma original_path_exists: forall G p T U,
    G ⊢! p: T ⪼ U // opened ->
    exists q, original_path G p T q.
Proof. Admitted.

Lemma original_path_unique: forall G p T q1 q2,
    original_path G p T q1 ->
    original_path G p T q2 ->
    q1 = q2.
Proof. Admitted.

(** If [G(x) = mu(T)], and [G ⊢! p: ... /\ D /\ ...], then [T^x = ... /\ D /\ ...]. *)
Lemma pf_record_has_T : forall p G T T' D m q,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ T' // m ->
    record_has T' D ->
    original_path G p (typ_bnd T) q ->
    record_has (open_typ_p q T) D.
Proof.
  introv Hi Pf Hr Hop.
  assert (m = opened) as Heq. {
    gen D. dependent induction Pf; introv Hr; eauto; inversion Hr.
  }
  subst.
  dependent induction Pf; eauto.
  - clear IHPf. lets Heq: (pf_bnd_T Hi Pf). inversions Heq.
    lets Hop': (original_path_not_opened Pf).
    lets Hu: (original_path_unique Hop Hop'). subst*.
  - specialize (IHPf2 _ Hi eq_refl eq_refl Hr). lets Heq: (pf_sngl_T Hi Pf1). subst. clear IHPf1.



  - inversions Hr.
  - apply (pf_bnd_T Hi) in Pf. inversion* Pf.
  - specialize (IHPf2 _ Hi eq_refl Hr). lets Heq: (pf_sngl_T Hi Pf1). subst.
Qed.

(** If [G(x) = mu(S)] and [G ⊢! p: D], where [D] is a field or type declaration,
    then [S^x = ... /\ D /\ ...]. *)
Lemma pf_record_has_U: forall S G p D m,
    inert G ->
    G ⊢! p: typ_bnd S ⪼ typ_rcd D // m ->
    record_has (open_typ_p p S) D.
Proof.
  introv Hi Pf. Admitted. (*apply* pf_record_has_T.*)


(** If
    - [G ⊢! p: mu(T) ⪼ {A: T1..T1}]
    - [G ⊢! p: mu(T) ⪼ {A: T2..T2}]
    then [T1 = T2]. *)
Lemma pf_dec_typ_unique : forall G p T A T1 T2 m1 m2,
    inert G ->
    G ⊢! p: typ_bnd T ⪼ typ_rcd {A >: T1 <: T1} // m1 ->
    G ⊢! p: typ_bnd T ⪼ typ_rcd {A >: T2 <: T2} // m2 ->
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

Lemma pf_dec_fld_unique : forall G p T a U1 U2 m1 m2,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd {a ⦂ U1} // m1 ->
    G ⊢! p: T ⪼ typ_rcd {a ⦂ U2} // m2 ->
    U1 = U2.
Proof.
 Admitted. (* introv Hi Pf1 Pf2.
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
  - eauto.
Qed.*)

(** If [G ⊢! x: T ⪼ U] then [G(x) = T]. *)
(** If [G ⊢! x: T ⪼ U] then [G(x) = T]. *)
Lemma pf_binds: forall G x T U m,
    inert G ->
    G ⊢! pvar x: T ⪼ U // m ->
    binds x T G.
Proof.
  introv Hi Pf. dependent induction Pf; try simpl_dot; auto.
  specialize (IHPf1 _ Hi eq_refl). apply pf_sngl_T in Pf1; auto. subst. apply binds_inert in IHPf1.
  inversion IHPf1. auto.
Qed.


(* we need to be able to show that if
   G ⊢! p: T ⪼ {a: q.type}
   then q is in the environment, and it also has an inert type. But for this we would need to
   - define inertness differently
   - apply an induction hypothesis to q. And for that, we would need to define this lemma in some different way
     that I don't know how to do. *)
Lemma pf_inert_typ : forall G p T U m,
    inert G ->
    G ⊢! p : T ⪼ U // m ->
    exists S m', G ⊢! p : S ⪼ S // m' /\ inert_typ S.
Proof.
  introv Hi Hp. induction Hp; eauto.
  - Case "pf_bind".
    exists T elim_rules. split. auto. apply binds_inert in H0; auto.
  - Case "pf_fld".
    specialize (IHHp Hi). destruct IHHp as [S [m' [Hps Hs]]]. (*
    lets Hpf: (pf_fld Hp).
    exists U. eexists. split*. destruct (pf_bnd_T2 Hi Hp) as [U' Heq]. subst.
    destruct (pf_rec_rcd_U Hi Hp) as [H | H]. inversion H. inversions H. inversions H0.
    inversions H1; auto.*)
Abort.

(* this lemma statement is too weak:
   what if p.a has an inert type, but ⊢! p: q.type?
   then we don't get an IH for q *)
Lemma pf_T_unique': forall G p T1 T2 U1 U2 m1 m2,
    inert G ->
    G ⊢! p: T1 ⪼ U1 // m1 ->
    G ⊢! p: T2 ⪼ U2 // m2 ->
    inert_typ T1 ->
    inert_typ T2 ->
    T1 = T2.
Proof.
  introv Hi Hp1. gen T2 U2. induction Hp1; introv Hp2 Ht1 Ht2; eauto.
  - Case "pf_bind".
    apply (pf_binds Hi) in Hp2. eapply binds_func. apply H0. auto.
  - Case "pf_fld".
    gen U T. dependent induction Hp2; introv Hiu; introv Hp IH; try simpl_dot; eauto.
    * rename a2 into x. rename f0 into bs. clear IHHp2.
      destruct (pf_bnd_T2 Hi Hp) as [S Heq]. subst. lets Hr: (pf_rcd_T Hi Hp).
      destruct (pf_bnd_T2 Hi Hp2) as [S' Heq]. subst. lets Hr': (pf_rcd_T Hi Hp2).
      assert (inert_typ (typ_bnd S)) as His. {
        inversions Hr. apply* inert_typ_bnd.
      }
      assert (inert_typ (typ_bnd S')) as His'. {
        inversions Hr'. apply* inert_typ_bnd.
      } (*
      specialize (IH Hi _ _ Hp2 His His').
      inversions IH. lets Hrh: (pf_record_has_U Hi Hp2).
      lets Hrh': (pf_record_has_U Hi Hp).
      assert (record_type (open_typ_p (p_sel x bs) S')) as Hrt by apply* open_record_type_p.
      apply* unique_rcd_trm.
    * lets Hqs: (pf_sngl_T Hi Hp2_1). subst.*)
  Abort.

(* I don't think we can prove this b/c we need to do induction on a sequence of singleton-path transitions.
   Maybe we should define a type lookup relation and prove that pf_T_unique implies that relation. *)
(*Lemma pf_T_unique_sngl: forall G p q T1 T2 U1 U2 m1 m2 m3,
    inert G ->
    G ⊢! p: T1 ⪼ U1 // m1 ->
    G ⊢! q: T2 ⪼ U2 // m2 ->
    (p = q \/ G ⊢! p: T2 ⪼ typ_sngl q // m3) ->
    inert_typ T1 ->
    inert_typ T2 ->
    T1 = T2.
Proof.
  introv Hi Hp1. gen q T2 U2. induction Hp1; introv Hq Hpq Hi1 Hi2; eauto.
  - Case "pf_bind".
    destruct Hpq as [Heq | Hp2]; subst.
    * apply (pf_binds Hi) in Hq. eapply binds_func. apply H0. auto.
    * lets Hs: (pf_sngl_T Hi Hp2). subst. inversion Hi2.
  - Case "pf_fld".
    gen p T a U. induction Hq; introv IH; introv Hpq; introv Hp1 Hiu; eauto.
    * SCase "pf_bind".
      destruct Hpq as [Heq | Hp2]. simpl_dot. lets Hs: (pf_sngl_T Hi Hp2). subst.
      apply binds_inert in H0. inversion H0. auto.
    * SCase "pf_fld".
      destruct (pf_bnd_T2 Hi Hq) as [S Heq]. subst.
      lets Hr: (pf_rcd_T Hi Hq). inversions Hr. lets Hb: (inert_typ_bnd H).
      destruct Hpq as [Heq | Hp2].
      ** simpl_dot.
         destruct (pf_bnd_T2 Hi Hp1) as [U' Heq]. subst.
         lets Hr: (pf_rcd_T Hi Hp1). inversions Hr. apply inert_typ_bnd in H0.
         assert (typ_bnd U' = typ_bnd S) as Heq by apply* IH. inversions Heq.
         lets Hrh: (pf_record_has_U Hi Hp1).
         lets Hrh': (pf_record_has_U Hi Hq).
         assert (record_type (open_typ_p (p_sel a2 f0) S)) as Hrt by apply* open_record_type_p.
         apply* unique_rcd_trm.
      ** specialize (IHHq Hi Hb _ _ IH).
         lets Heq: (pf_sngl_T Hi Hp2). subst. inversion Hi2.
    * SCase "pf_sngl_trans".
      lets Heq: (pf_sngl_T Hi Hq1). subst. clear IHHq1. destruct Hpq as [Heq | Hp0p].
      ** subst. specialize (IHHq2 Hi Hi2 _ _ IH).
         admit.
      ** specialize (IHHq2 Hi Hi2 _ _ IH).
         admit.
  - SCase "pf_sngl_trans".
    lets Hs: (pf_sngl_T Hi Hp1_1). subst.
    destruct Hpq as [Heq | Hp]. subst.
    * clear IHHp1_1.
      admit.
    * lets Hs: (pf_sngl_T Hi Hp). subst. inversion Hi2.
Qed.

Lemma pf_T_unique: forall G p T1 T2 U1 U2,
    inert G ->
    G ⊢! p: T1 ⪼ U1 ->
    G ⊢! p: T2 ⪼ U2 ->
    inert_typ T1 ->
    inert_typ T2 ->
    T1 = T2.
Proof.
  introv Hp1 Hp2 Ht1 Ht2. apply* pf_T_unique_sngl.
Qed.*)

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
Lemma pf_dec_typ_tight : forall G p T A S U m,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd {A >: S <: U} // m->
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

Lemma pf_strengthen: forall G y V x bs T U m,
    inert (G & y ~ V) ->
    G & y ~ V ⊢! p_sel (avar_f x) bs : T ⪼ U // m->
    x <> y ->
    G ⊢! p_sel (avar_f x) bs : T ⪼ U // m.
Proof.
  introv Hi Ht Hneq. dependent induction Ht; eauto.
  - apply (binds_push_neq_inv H0) in Hneq. constructor*.
  - destruct p. inversions x.
    specialize (IHHt _ _ _ _ _ Hi JMeq_refl eq_refl Hneq).
    lets Hf: (pf_fld IHHt). eauto.
  - specialize (IHHt1 _ _ _ _ _ Hi JMeq_refl eq_refl Hneq).
    apply inert_prefix in Hi. lets Hs: (pf_sngl_T Hi IHHt1). subst.
    apply* pf_sngl_trans. Abort.
(*
Lemma sngl_diff_inv: forall G p a T,
    inert G ->
    G ⊢! p : T ⪼ typ_rcd { a ⦂ typ_sngl p•a } ->
    False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  - apply (binds_inert H0) in Hi. inversion Hi.
  - A*)

Lemma pf_var_sngl : forall G x p T m,
    inert G ->
    G ⊢! pvar x : typ_sngl p ⪼ T // m ->
    False.
Proof.
  introv Hi Hx. dependent induction Hx; eauto.
  apply (binds_inert H0) in Hi. inversion Hi.
  unfolds sel_fields. destruct p0. inversion x.
  lets Hs: (pf_sngl_T Hi Hx1). subst. apply* IHHx1.
Qed.

Lemma pf_inert_sngl : forall G p q T U m1 m2,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q // m1 ->
    G ⊢! p: T ⪼ U // m2 ->
    inert_typ T ->
    G ⊢! q: T ⪼ T // elim_rules.
Proof.
  introv Hi Hpq Hp Ht. gen q. dependent induction Hp; introv Hpq; eauto.
  - apply pf_binds in Hpq. apply binds_inert in Hpq. inversion Hpq. all: auto.
  - destruct (pf_bnd_T2 Hi Hp) as [S Heq]. subst.
    lets Hr: (pf_rcd_T Hi Hp). inversions Hr. lets His: (inert_typ_bnd H).
    admit.
  - admit. Abort.

Lemma pf_inert_bnd : forall G p T D m,
    inert G ->
    G ⊢! p : T ⪼ typ_rcd D // m ->
    inert_typ T.
Proof.
  introv Hi Hp. lets Hr: (pf_bnd_T2 Hi Hp). destruct_all.
  subst. apply pf_rcd_T in Hp; auto. inversions Hp. apply* inert_typ_bnd.
Qed.

Lemma pf_and_destruct1: forall G p T T1 T2 m,
    G ⊢! p : T ⪼ typ_and T1 T2 // m ->
    G ⊢! p:  T ⪼ T1 // m.
Proof.
  introv Hp. dependent induction Hp; eauto. destruct U; inversions x.
  assert (T = typ_bnd (typ_and U1 U2)) as Heq by admit. subst.
  apply pf_open in Hp. apply* pf_and1.
Qed.

Lemma pf_and_destruct2: forall G p T T1 T2 m,
    G ⊢! p : T ⪼ typ_and T1 T2 // m ->
    G ⊢! p : T ⪼ T2 // m.
Proof.
  introv Hp. dependent induction Hp; eauto. destruct U; inversions x.
  assert (T = typ_bnd (typ_and U1 U2)) as Heq by admit. subst.
  apply pf_open in Hp. apply* pf_and2.
Qed.
