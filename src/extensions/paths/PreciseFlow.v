(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Precise Typing (Elimination Typing I) *)
(** This module reasons about the precise types ⊢! of paths and values. *)

Set Implicit Arguments.

Require Import Sequences.
Require Import Coq.Program.Equality List String.
Require Import Definitions Binding RecordAndInertTypes Subenvironments Narrowing.

(** inverting equivalent types *)
Ltac invert_repl :=
  repeat match goal with
         | [H: repl_dec _ _ {_ ⦂ _} _ |- _ ] =>
           inversions H
         | [H: repl_dec _ _ _ {_ ⦂ _} |- _ ] =>
           inversions H
         | [H: repl_dec _ _ {_ >: _ <: _} _ |- _ ] =>
           inversions H
         | [H: repl_dec _ _ _ {_ >: _ <: _} |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (typ_rcd _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (typ_rcd _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (_ ∧ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (_ ∧ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (μ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (μ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (∀(_) _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (∀(_) _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ (_ ↓ _) _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ (_ ↓ _) |- _ ] =>
           inversions H
         | [H: repl_typ _ _ ⊤ _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ ⊤ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ ⊥ _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ ⊥ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ {{ _ }} _ |- _ ] =>
           inversions H
         | [H: repl_typ _ _ _ {{ _ }} |- _ ] =>
           inversions H
    end.

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
    G ⊢!v λ(T) t : ∀(T) U

(** [x; []; G, x: T^x ⊢ ds^x: T^x]       #<br>#
    [x fresh]                               #<br>#
    [―――――――――――――――――――――――――――――――]       #<br>#
    [G ⊢! ν(T)ds: μ(T)]                     *)
| ty_new_intro_p
     : forall (L : fset var) (G : env typ) (T : typ) (ds : defs),
       (forall x : var, x \notin L -> x; nil; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T) ->
       G ⊢!v ν(T)ds : μ T

where "G '⊢!v' v ':' T" := (ty_val_p G v T).

Hint Constructors ty_val_p.

(** ** Precise Flow for Paths *)
(** We use the precise flow relation, denoted as Γ ⊢! p: T ⪼ U, to reason about the relation
    between the actual type [T] that the environment assigns to [p], and the type [U] that can
    be obtained form [T] through recursion and intersection eliminations.
    We will call [T] the _environment type_, and [U] the _precise type_ of [p]. *)

Reserved Notation "G '⊢!' p ':' T '⪼' U" (at level 40, p at level 59).

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
      G ⊢! p: T ⪼ μ U ->
      G ⊢! p: T ⪼ open_typ_p p U

(** [G ⊢! p: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p: T ⪼ U1]        *)
  | pf_and1 : forall p G T U1 U2,
      G ⊢! p: T ⪼ U1 ∧ U2 ->
      G ⊢! p: T ⪼ U1

(** [G ⊢! p: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! p: T ⪼ U2]        *)
  | pf_and2 : forall p G T U1 U2,
      G ⊢! p: T ⪼ U1 ∧ U2 ->
      G ⊢! p: T ⪼ U2

where "G '⊢!' p ':' T '⪼' U" := (precise_flow G p T U).

Hint Constructors precise_flow.

Ltac fresh_constructor_p :=
  apply_fresh ty_new_intro_p as z ||
  apply_fresh ty_all_intro_p as z; auto.

(** Precise typing implies general typing for the environment and precise type of a path. *)
Lemma precise_to_general_h: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢ trm_path p: T /\ G ⊢ trm_path p: U.
Proof.
  intros. induction H; intros; subst; destruct_all; eauto.
Qed.

(** Precise typing implies general typing. *)
(** - for paths *)
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

(** The type to which a variable is bound in an inert context is inert. *)
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
      destruct_notin;
      apply* record_open
  end.
Qed.

(** If [p]'s environment type is a function type, then it's precise type is the same
    function type. *)
Lemma pf_forall_U : forall G p T U S,
    G ⊢! p: ∀(T) U ⪼ S ->
    S = ∀(T) U.
Proof.
  introv Pf. dependent induction Pf; eauto;
               try (repeat specialize (IHPf _ _ eq_refl); destruct_all; inversion IHPf);
               try (specialize (IHPf _ _ eq_refl); destruct_all; inversion H).
Qed.

(** A path's environment type is either inert or a signleton type.
    A path's precise type type is either inert, a singleton type, or a record type. *)
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

(** In an inert context, a path's environment type is inert or a singleton type. *)
Lemma pf_inert : forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ U ->
    inert_sngl T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply (binds_inert H0) in Hi. left*.
  apply* pf_inertsngl.
Qed.

Hint Resolve pf_inert.

(** If a path's environment type is a recursive type [μ(x: T)] then [T] is a record type. *)
Lemma pf_rcd_T : forall G p T U,
    inert G ->
    G ⊢! p: μ T ⪼ U ->
    record_type T.
Proof.
  introv Hi Pf. apply pf_inert in Pf; inversions Pf; eauto. inversion* H. destruct_all. inversions H.
  inversion H0.
Qed.

(** If a path's environment type is recursive then its precise type is the same recursive type or
    a record type. *)
Lemma pf_rec_rcd_U : forall G p T U,
    inert G ->
    G ⊢! p: μ T ⪼ U->
    U = μ T \/ record_type U.
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

(** If a path's environment type is a singleton type then its precise type is the same
    singleton type. *)
Lemma pf_sngl_U: forall G p q U,
    G ⊢! p : {{ q }} ⪼ U->
    U = {{ q }}.
Proof.
  introv Hp. dependent induction Hp; eauto; try (specialize (IHHp _ eq_refl); inversion IHHp).
Qed.

(** If [p]'s precise type is a recursive type then its environment type is the same recursive type. *)
Lemma pf_bnd_T: forall G p T U,
    inert G ->
    G ⊢! p: T ⪼ μ U ->
    T = μ U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf).
  inversions HT.
  - inversions H. apply pf_forall_U in Pf. inversion Pf.
    apply (pf_rec_rcd_U Hi) in Pf. destruct Pf. inversion* H. inversion H. inversion H1.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** If [p]'s precise type is a singleton type then its environment type is the same singleton type. *)
Lemma pf_sngl_T: forall G p q T,
    inert G ->
    G ⊢! p : T ⪼ {{ q }} ->
    T = {{ q }}.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct U; inversions x. lets H: (pf_bnd_T Hi Hp). subst.
  apply (pf_inert Hi) in Hp. inversion* Hp. inversions H. inversion H1. destruct_all.
  inversion H. inversion H0.
  lets His: (pf_inertsngl Hi Hp). destruct_all; progress (repeat inversions H0); inversion H1; inversions H0.
  inversion H3.
  lets His: (pf_inertsngl Hi Hp). destruct_all; progress (repeat inversions H0); inversion H1; inversions H0.
Qed.

(** If [p]'s precise type is a record, then its envirionment type is a recursive type. *)
Lemma pf_bnd_T2: forall G p T D,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd D ->
    exists U, T = μ U.
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

(** The following two lemmas express that if [p]'s precise type is a function type,
    then its environment type is the same function type. *)
Lemma pf_forall_T : forall p G S T U,
    inert G ->
    G ⊢! p: T ⪼ ∀(S) U->
    T = ∀(S) U.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert Hi Pf).
  inversions Hiu.
  - inversions H. apply pf_forall_U in Pf. inversion* Pf.
    destruct (pf_rec_rcd_U Hi Pf) as [H1 | H1]; inversions H1. inversion H.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** A variable [x]'s environment type is [T] then [G(x)=T]. *)
Lemma pf_binds: forall G x T U,
    inert G ->
    G ⊢! pvar x: T ⪼ U ->
    binds x T G.
Proof.
  introv Hi Pf. dependent induction Pf; try simpl_dot; auto.
Qed.

(** In an inert context, the precise type of a path cannot be bottom. *)
Lemma pf_bot : forall G p T,
    inert G ->
    G ⊢! p: T ⪼ ⊥ ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf). inversions HT.
  - inversions H. apply pf_forall_U in Pf. inversion Pf.
    destruct (pf_rec_rcd_U Hi Pf); inversion H0; inversion H. inversion H5. inversion H7.
  - inversions H. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** In an inert context, the precise type of a path cannot be type selection. *)
Lemma pf_psel : forall G T p q A,
    inert G ->
    G ⊢! p: T ⪼ q ↓ A ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert Hi Pf). inversions HT.
  - inversions H.
    * apply pf_forall_U in Pf. inversion Pf.
    * destruct (pf_rec_rcd_U Hi Pf); inversion H. inversion H1.
  - destruct H as [r Heq]. subst. apply pf_sngl_U in Pf. inversion Pf.
Qed.

(** The following two lemmas say that if a path's precise type is [...∧ D ∧...]
    then its environment type is [μ(...∧ D ∧...)] *)
Lemma pf_record_has_T : forall p G T T' D,
    inert G ->
    G ⊢! p: μ T ⪼ T' ->
    record_has T' D ->
    record_has (open_typ_p p T) D.
Proof.
  introv Hi Pf Hr.
  dependent induction Pf; eauto; try solve [inversion Hr].
  apply pf_bnd_T in Pf; auto. inversion* Pf.
Qed.

Lemma pf_record_has_U: forall S G p D,
    inert G ->
    G ⊢! p: μ S ⪼ typ_rcd D ->
    record_has (open_typ_p p S) D.
Proof.
  introv Hi Pf.
  apply* pf_record_has_T.
Qed.

(** A path's precise type, if it is a record, has unique occurrences of each type label *)
Lemma pf_dec_typ_unique : forall G p T A T1 T2,
    inert G ->
    G ⊢! p: μ T ⪼ typ_rcd {A >: T1 <: T1} ->
    G ⊢! p: μ T ⪼ typ_rcd {A >: T2 <: T2} ->
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

(** A path's environment type is unique *)
Lemma pf_T_unique: forall G p T1 T2 U1 U2,
    inert G ->
    G ⊢! p: T1 ⪼ U1 ->
    G ⊢! p: T2 ⪼ U2 ->
    T1 = T2.
Proof.
  introv Hi Hp1. gen T2 U2. induction Hp1; introv Hp2; eauto.
  - Case "pf_bind"%string.
    apply (pf_binds Hi) in Hp2. eapply binds_functional. apply H0. auto.
  - Case "pf_fld"%string.
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

(** If a typing context is inert, then the variables in its domain are distinct *)
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

(** If a path's precise type is a type declaration then the declaration has tight bounds. *)
Lemma pf_dec_typ_tight : forall G p T A S U,
    inert G ->
    G ⊢! p: T ⪼ typ_rcd {A >: S <: U}->
    S = U.
Proof.
  introv Hi Pf. destruct (pf_bnd_T2 Hi Pf) as [V H]. subst.
  destruct (pf_rec_rcd_U Hi Pf) as [H1 | H1]; inversions H1. inversions H.
  inversions* H1.
Qed.

(** A path [x.bs]'s precise typing in an environment [G, y: T] remains the same
    after removing [y] from the environment, if [x ≠ y] *)
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

(** If [p.a] has a precise type in an environment then [p]'s environment
    type is a recursive type and [p] has a precise type [{a: _}] *)
Lemma pf_path_sel: forall G p a T U,
    inert G ->
    G ⊢! p•a : T ⪼ U ->
    exists V, G ⊢! p: μ V ⪼ typ_rcd {a ⦂ T}.
Proof.
  introv Hi Hp. dependent induction Hp; try simpl_dot; eauto.
  destruct (pf_bnd_T2 Hi Hp) as [V Heq]. subst. eauto.
Qed.

(** If a path [x.bs], where [bs] is nonempty, has a type
    then [x]'s environment type is recursive. *)
Lemma pf_sngl G x bs T U a :
  inert G ->
  G ⊢! (p_sel (avar_f x) bs) • a : T ⪼ U ->
  exists S V, G ⊢! pvar x : μ S ⪼ V.
Proof.
  intros Hi Hp. gen G x a T U. induction bs; introv Hi; introv Hp.
  - simpl in Hp. rewrite proj_rewrite in *. apply (pf_path_sel _ _ Hi) in Hp as [V Hp].
    pose proof (pf_bnd_T2 Hi Hp) as [S [= ->]]. eauto.
  - pose proof (pf_path_sel _ _ Hi Hp) as [V Hp']. eauto.
Qed.

(** Weakening for precise typing with one element *)
Lemma pf_weaken_one G p T U x V :
  ok G ->
  x # G ->
  G ⊢! p : T ⪼ U ->
  G & x ~ V ⊢! p : T ⪼ U.
Proof.
  introv Hok Hx Hp. dependent induction Hp; eauto. apply pf_bind.
  - apply* ok_push.
  - apply* binds_push_neq. intros ->. eapply binds_fresh_inv; eauto.
Qed.

(** Weakening for precise typing with contexts of arbitrary length *)
Lemma pf_weaken G G' p T U :
  ok (G & G') ->
  G ⊢! p : T ⪼ U ->
  G & G' ⊢! p : T ⪼ U.
Proof.
  intros Hok Hp. induction G' using env_ind.
  - rewrite* concat_empty_r.
  - rewrite concat_assoc in *. eapply pf_weaken_one; auto. rewrite <- concat_empty_r in Hok.
    apply* ok_middle_inv_l.
Qed.
