Set Implicit Arguments.

Require Import Definitions.
Require Import LibLN.


Ltac omega := Coq.omega.Omega.omega.


(** * Local Closure

  Our definition of [trm] accepts terms that contain de Bruijn indices that are unbound.
  A symbol [X] is considered locally closed, denoted [lc X], if all de Bruijn indices
  in [X] are bound.
   We will require a term to be locally closed in the final safety theorem. *)

(** Only named variables are locally closed. *)
Inductive lc_at_var (k : nat) : avar -> Prop :=
| lc_at_f : forall x, lc_at_var k (avar_f x)
| lc_at_b : forall i, i < k -> lc_at_var k (avar_b i).
Hint Constructors lc_at_var.


(** Locally closed types and declarations. *)
Inductive lc_at_typ (k : nat) : typ -> Prop :=
| lc_at_typ_top : lc_at_typ k typ_top
| lc_at_typ_bot : lc_at_typ k typ_bot
| lc_at_typ_rcd : forall D,
    lc_at_dec k D ->
    lc_at_typ k (typ_rcd D)
| lc_at_typ_and : forall T1 T2,
    lc_at_typ k T1 ->
    lc_at_typ k T2 ->
    lc_at_typ k (typ_and T1 T2)
| lc_at_typ_sel : forall x L,
    lc_at_var k x ->
    lc_at_typ k (typ_sel x L)
| lc_at_typ_bnd : forall T,
    lc_at_typ (S k) T ->
    lc_at_typ k (typ_bnd T)
| lc_at_typ_all : forall T1 T2,
    lc_at_typ (S k) T2 ->
    lc_at_typ k T1 ->
    lc_at_typ k (typ_all T1 T2)
with lc_at_dec (k : nat) : dec -> Prop :=
| lc_at_dec_typ : forall L T U,
    lc_at_typ k T ->
    lc_at_typ k U ->
    lc_at_dec k (dec_typ L T U)
| lc_at_dec_trm : forall a T,
    lc_at_typ k T ->
    lc_at_dec k (dec_trm a T).
Hint Constructors lc_at_typ lc_at_dec.


(** Locally closed terms, values, and definitions. *)
Inductive lc_at_trm (k : nat) : trm -> Prop :=
| lc_at_trm_var : forall a,
    lc_at_var k a ->
    lc_at_trm k (trm_var a)
| lc_at_trm_val : forall v,
    lc_at_val k v ->
    lc_at_trm k (trm_val v)
| lc_at_trm_sel : forall x a,
    lc_at_var k x ->
    lc_at_trm k (trm_sel x a)
| lc_at_trm_app : forall f a,
    lc_at_var k f ->
    lc_at_var k a ->
    lc_at_trm k (trm_app f a)
| lc_at_trm_let : forall t1 t2,
    lc_at_trm k t1 ->
    lc_at_trm (S k) t2 ->
    lc_at_trm k (trm_let t1 t2)
with lc_at_val (k : nat) : val -> Prop :=
| lc_at_val_new : forall T ds,
    lc_at_typ (S k) T ->
    lc_at_defs (S k) ds ->
    lc_at_val k (val_new T ds)
| lc_at_val_lam : forall T t,
    lc_at_typ k T ->
    lc_at_trm (S k) t ->
    lc_at_val k (val_lambda T t)
with lc_at_def (k : nat) : def -> Prop :=
| lc_at_def_typ : forall L T,
    lc_at_typ k T ->
    lc_at_def k (def_typ L T)
| lc_at_def_trm : forall a t,
    lc_at_trm k t ->
    lc_at_def k (def_trm a t)
with lc_at_defs (k : nat) : defs -> Prop :=
| lc_at_defs_nil : lc_at_defs k defs_nil
| lc_at_defs_cons : forall ds d,
    lc_at_defs k ds ->
    lc_at_def k d ->
    lc_at_defs k (defs_cons ds d).
Hint Constructors lc_at_trm lc_at_val lc_at_def lc_at_defs.


Notation "'rlc_var' x" := (lc_at_var 0 x) (at level 0).
Notation "'rlc_typ' T" := (lc_at_typ 0 T) (at level 0).
Notation "'rlc_dec' D" := (lc_at_dec 0 D) (at level 0).

Notation "'rlc_trm' t" := (lc_at_trm 0 t) (at level 0).
Notation "'rlc_val' v" := (lc_at_val 0 v) (at level 0).
Notation "'rlc_def' d" := (lc_at_def 0 d) (at level 0).
Notation "'rlc_defs' ds" := (lc_at_defs 0 ds) (at level 0).


Scheme lc_at_trm_mut  := Induction for lc_at_trm Sort Prop
with   lc_at_val_mut  := Induction for lc_at_val Sort Prop
with   lc_at_def_mut  := Induction for lc_at_def Sort Prop
with   lc_at_defs_mut := Induction for lc_at_defs Sort Prop.
Combined Scheme lc_at_mutind from lc_at_trm_mut, lc_at_val_mut, lc_at_def_mut, lc_at_defs_mut.

Scheme lc_at_typ_mut := Induction for lc_at_typ Sort Prop
with   lc_at_dec_mut := Induction for lc_at_dec Sort Prop.
Combined Scheme lc_at_typ_mutind from lc_at_typ_mut, lc_at_dec_mut.


(** Locally closed stores *)
Inductive rlc_sto : sto -> Prop :=
| rlc_sto_empty : rlc_sto empty
| rlc_sto_cons : forall x v s,
    rlc_sto s ->
    rlc_val v ->
    rlc_sto (s & x ~ v).
Hint Constructors rlc_sto.


Lemma lc_at_relaxing_avar :
  forall x k j, lc_at_var k x -> j >= k -> lc_at_var j x.
Proof.
  intros. inversions H; constructor; omega.
Qed.


Lemma lc_at_relaxing_typ_dec :
    (forall T k j, lc_at_typ k T -> j >= k -> lc_at_typ j T) /\
    (forall D k j, lc_at_dec k D -> j >= k -> lc_at_dec j D).
Proof with auto.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    | [ H : lc_at_dec _ _ |- _ ] => inversions H
    end;
    try match goal with
    | [ H : lc_at_var _ _ |- _ ] => inversions H
    end;
    repeat constructor;
    try match goal with
        | [ H : _ -> _ |- _ ] => eapply H; try eassumption
        end;
    omega.
Qed.


Lemma lc_at_relaxing_trm_val_def_defs:
  (forall t k j, lc_at_trm k t -> j >= k -> lc_at_trm j t) /\
  (forall v k j, lc_at_val k v -> j >= k -> lc_at_val j v) /\
  (forall d k j, lc_at_def k d -> j >= k -> lc_at_def j d) /\
  (forall ds k j, lc_at_defs k ds -> j >= k -> lc_at_defs j ds).
Proof.
  apply trm_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    | [ H : lc_at_val _ _ |- _ ] => inversions H
    | [ H : lc_at_def _ _ |- _ ] => inversions H
    | [ H : lc_at_defs _ _ |- _ ] => inversions H
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    end;
    repeat match goal with
           | [ H : lc_at_var _ _ |- _ ] => inversions H
           end; 
    repeat constructor;
    try eapply lc_at_relaxing_typ_dec; try eassumption;
    try match goal with
        | [ H : _ -> _ |- _ ] => eapply H; try eassumption
        end;
    omega.
Qed.


Lemma lc_at_to_open_avar : forall x v k,
    lc_at_var (S k) v -> lc_at_var k (open_rec_avar k x v).
Proof with auto.
  intros. inversion H; subst; repeat constructor.
  simpl. case_if...
  constructor. omega.
Qed.


Lemma lc_at_to_open_typ_dec : forall x,
    (forall T k, lc_at_typ (S k) T -> lc_at_typ k (open_rec_typ k x T)) /\
    (forall D k, lc_at_dec (S k) D -> lc_at_dec k (open_rec_dec k x D)).
Proof.
  intro x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_typ (S _) _ |- _ ] => inversions H
    | [ H : lc_at_dec (S _) _ |- _ ] => inversions H
    end;
    try solve [constructor; try fold open_rec_dec; try fold open_rec_typ; auto];
    solve [repeat constructor; apply lc_at_to_open_avar; auto].
Qed.


Lemma lc_at_to_open_trm_val_def_defs : forall x,
    (forall t k, lc_at_trm (S k) t -> lc_at_trm k (open_rec_trm k x t)) /\
    (forall v k, lc_at_val (S k) v -> lc_at_val k (open_rec_val k x v)) /\
    (forall d k, lc_at_def (S k) d -> lc_at_def k (open_rec_def k x d)) /\
    (forall ds k, lc_at_defs (S k) ds -> lc_at_defs k (open_rec_defs k x ds)).
Proof.
  intro x.
  apply trm_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_trm (S _) _ |- _ ] => inversions H
    | [ H : lc_at_val (S _) _ |- _ ] => inversions H
    | [ H : lc_at_def (S _) _ |- _ ] => inversions H
    | [ H : lc_at_defs (S _) _ |- _ ] => inversions H
    | [ H : lc_at_typ (S _) _ |- _ ] => inversions H
    end;
    repeat constructor; auto;
    try solve [try fold open_rec_trm; auto];
    try solve [applys lc_at_to_open_typ_dec; auto];
    solve [apply lc_at_to_open_avar; auto].
Qed.


Lemma open_to_lc_at_avar : forall x v k, lc_at_var k (open_rec_avar k x v) -> lc_at_var (S k) v.
Proof.
  intros. inversion H; subst;
      destruct v; simpl in *;
        try case_if; subst; repeat constructor; auto.
  inversion H0. omega.
Qed.


Lemma open_to_lc_at_typ_dec : forall x,
    (forall T k, lc_at_typ k (open_rec_typ k x T) -> lc_at_typ (S k) T) /\
    (forall D k, lc_at_dec k (open_rec_dec k x D) -> lc_at_dec (S k) D).
Proof with eauto.
  intro x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    | [ H : lc_at_dec _ _ |- _ ] => inversions H
    end;
    repeat constructor; auto;
      eapply open_to_lc_at_avar...
Qed.


Lemma open_to_lc_at_trm_val_def_defs : forall x,
    (forall t k, lc_at_trm k (open_rec_trm k x t) -> lc_at_trm (S k) t) /\
    (forall v k, lc_at_val k (open_rec_val k x v) -> lc_at_val (S k) v) /\
    (forall d k, lc_at_def k (open_rec_def k x d) -> lc_at_def (S k) d) /\
    (forall ds k, lc_at_defs k (open_rec_defs k x ds) -> lc_at_defs (S k) ds).
Proof.
  intro x.
  apply trm_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    | [ H : lc_at_val _ _ |- _ ] => inversions H
    | [ H : lc_at_def _ _ |- _ ] => inversions H
    | [ H : lc_at_defs _ _ |- _ ] => inversions H
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    end;
    repeat constructor; auto;
    try solve [try fold open_rec_trm; auto];
    try solve [applys open_to_lc_at_typ_dec; eauto];
    solve [eapply open_to_lc_at_avar; eauto].
Qed.


Lemma open_left_inverse_close_avar: 
  forall v x k, lc_at_var k v -> x \notin fv_avar v -> open_rec_avar (S k) x (close_rec_avar (S k) x v) = v.
Proof with auto.
  intros. unfold open_rec_avar, close_rec_avar.
  inversion H; repeat case_if; subst...
  omega.
Qed.
Hint Resolve open_left_inverse_close_avar.


Lemma open_left_inverse_close_typ_dec:
  (forall T x k, lc_at_typ k T -> x \notin fv_typ T -> open_rec_typ (S k) x (close_rec_typ (S k) x T) = T) /\
  (forall D x k, lc_at_dec k D -> x \notin fv_dec D -> open_rec_dec (S k) x (close_rec_dec (S k) x D) = D).
Proof with auto.
  apply typ_mutind; intros; simpl in *; auto;
  match goal with
  | [ H : lc_at_typ _ _ |- _ ] => inversions H
  | [ H : lc_at_dec _ _ |- _ ] => inversions H
  end;
  try apply func_eq_2;
  try apply func_eq_1...
Qed.


Lemma open_left_inverse_close_trm_val_def_defs :
  (forall t k x, lc_at_trm k t -> x \notin fv_trm t -> open_rec_trm (S k) x (close_rec_trm (S k) x t) = t) /\
  (forall v k x, lc_at_val k v -> x \notin fv_val v -> open_rec_val (S k) x (close_rec_val (S k) x v) = v) /\
  (forall d k x, lc_at_def k d -> x \notin fv_def d -> open_rec_def (S k) x (close_rec_def (S k) x d) = d) /\
  (forall ds k x, lc_at_defs k ds -> x \notin fv_defs ds -> open_rec_defs (S k) x (close_rec_defs (S k) x ds) = ds).
Proof.
  apply trm_mutind; intros; simpl in *; auto;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    | [ H : lc_at_val _ _ |- _ ] => inversions H
    | [ H : lc_at_def _ _ |- _ ] => inversions H
    | [ H : lc_at_defs _ _ |- _ ] => inversions H
    end;
    try apply func_eq_2;
    try apply func_eq_1; auto;
      solve [applys open_left_inverse_close_typ_dec; auto].
Qed.


(** The following [lc_opening_XYZ] lemmas state that opening a locally
    closed symbol (variables, types, terms, etc.) at any index
    results in the same symbol. *)

(** - variables *)
Lemma lc_opening_avar: forall m n x y,
    n >= m ->
    lc_at_var m y ->
    open_rec_avar n x y = y.
Proof.
  introv Hge Hl. inversion Hl; simpls~.
  case_if~. omega.
Qed.


(** - types and declarations *)
Lemma lc_at_opening_typ_dec: forall x m,
    (forall T, lc_at_typ m T -> forall n, n >= m -> open_rec_typ n x T = T) /\
    (forall D, lc_at_dec m D -> forall n, n >= m -> open_rec_dec n x D = D).
Proof.
  Local Hint Resolve lc_opening_avar.
  intro x. apply lc_at_typ_mutind; intros; simpls; f_equal*;
  match goal with
  | [ H : _ -> _ -> open_rec_typ _ _ _ = _ |- _ ] => apply H
  end; omega.
Qed.


(** - terms, values, definitions, and list of definitions *)
Lemma lc_at_opening_trm_val_def_defs: forall x m,
  (forall t, lc_at_trm m t -> forall n, n >= m -> open_rec_trm n x t = t) /\
  (forall v, lc_at_val m v -> forall n, n >= m -> open_rec_val n x v = v) /\
  (forall d, lc_at_def m d -> forall n, n >= m -> open_rec_def n x d = d) /\
  (forall ds, lc_at_defs m ds -> forall n, n >= m -> open_rec_defs n x ds = ds).
Proof.
  Local Hint Resolve lc_opening_avar.
  intro x.
  apply lc_at_mutind; intros; simpls; f_equal*;
    try solve
        [match goal with
         | [ H : _ -> _ -> ?f _ _ ?t = ?t |- ?f _ _ ?t = ?t ] => apply H
         end; omega];
  applys lc_at_opening_typ_dec;
    try eassumption;
    try omega.
Qed.


(** The [lc_at_opening_trm_val_def_defs] lemma, specialized to terms. *)
Lemma lc_at_opening : forall t n x,
    rlc_trm t ->
    open_rec_trm n x t = t.
Proof.
  intros. applys lc_at_opening_trm_val_def_defs; try eassumption; try omega.
Qed.


Lemma lc_at_opening_change_avar : forall x x' v m n,
    lc_at_var m (open_rec_avar n x v) ->
    n >= m ->
    lc_at_var m (open_rec_avar n x' v).
Proof.
  intros. inversions H;
  unfold open_rec_avar in *; destruct v; try case_if; auto.
  inversion H1. subst. constructor. omega.
Qed.


Lemma lc_at_opening_change_typ_dec: forall x x' m,
    (forall T, lc_at_typ m T -> forall n T',
          n >= m ->
          T = open_rec_typ n x T' ->
          lc_at_typ m (open_rec_typ n x' T')) /\
    (forall D, lc_at_dec m D -> forall n D',
          n >= m ->
          D = open_rec_dec n x D' ->
          lc_at_dec m (open_rec_dec n x' D')).
Proof.
  Local Hint Resolve lc_at_opening_change_avar.
  intros x x'.
  apply lc_at_typ_mutind; intros; simpls;
    match goal with
    | [ H : _ = open_rec_typ _ _ ?T |- _ ] => destruct T; inversions H
    | [ H : _ = open_rec_dec _ _ ?D |- _ ] => destruct D; inversions H
    end;
    repeat constructor; auto;
      try fold open_rec_typ;
      try solve
          [match goal with
           | [ H : _ -> _ |- _ ] => apply H; trivial; omega
           end];
      eauto.
Qed.


Lemma lc_at_opening_change_var_trm_val_def_defs: forall x x' m,
    (forall t, lc_at_trm m t -> forall n t',
          n >= m ->
          t = open_rec_trm n x t' ->
          lc_at_trm n (open_rec_trm n x' t')) /\
    (forall v, lc_at_val m v -> forall n v',
          n >= m ->
          v = open_rec_val n x v' ->
          lc_at_val n (open_rec_val n x' v')) /\
    (forall d, lc_at_def m d -> forall n d',
          n >= m ->
          d = open_rec_def n x d' ->
          lc_at_def n (open_rec_def n x' d')) /\
    (forall ds, lc_at_defs m ds -> forall n ds',
          n >= m ->
          ds = open_rec_defs n x ds' ->
          lc_at_defs n (open_rec_defs n x' ds')).
Proof.
  Local Hint Resolve lc_at_relaxing_avar.
  Local Hint Resolve lc_at_opening_change_avar.
  intros x x'.
  apply lc_at_mutind; intros; simpls;
  match goal with
  | [ H : _ = open_rec_trm _ _ ?t |- _ ] => destruct t; inversions H
  | [ H : _ = open_rec_val _ _ ?v |- _ ] => destruct v; inversions H
  | [ H : _ = open_rec_def _ _ ?d |- _ ] => destruct d; inversions H
  | [ H : _ = open_rec_defs _ _ ?ds |- _ ] => destruct ds; inversions H
  end;
  simpls; repeat constructor;
    try solve
        [match goal with
         | [ H : _ -> _ |- _ ] => apply H; trivial; omega
         end];
    eauto;
    try applys lc_at_opening_change_typ_dec;
    try applys lc_at_relaxing_typ_dec;
    try eassumption; trivial;
      omega.
Qed.

(** * Lemmas About Local Closure *)

(** When a binding is removed from a locally closed store, the
    resulting store and the value in the binding are both
    locally closed. *)
Lemma lc_sto_push_inv : forall s x v,
    rlc_sto (s & x ~ v) ->
    rlc_sto s /\ rlc_val v.
Proof.
  intros s x v H.
  inversion H.
  - destruct (empty_push_inv H1).
  - destruct (eq_push_inv H0) as [? [? ?] ]; subst.
    auto.
Qed.


(** Values in a locally closed store are also locally closed. *)
Lemma lc_sto_binds_inv : forall s x v,
    rlc_sto s ->
    binds x v s ->
    rlc_val v.
Proof.
  intros.
  induction s using env_ind.
  - destruct (binds_empty_inv H0).
  - destruct (binds_push_inv H0) as [[? ?] | [? ?]]; subst.
    + apply (lc_sto_push_inv H).
    + apply IHs; auto.
      apply (lc_sto_push_inv H).
Qed.


(** A definition in a locally closed list of definitions is also
    locally closed. *)
Lemma lc_defs_has : forall ds d,
    rlc_defs ds ->
    defs_has ds d ->
    rlc_def d.
Proof.
  intros.
  induction ds.
  - inversion H0.
  - unfold defs_has in H0; simpl in H0.
    cases_if.
    + inversions H0. inversion H; auto.
    + apply IHds; auto. inversion H; auto.
Qed.
