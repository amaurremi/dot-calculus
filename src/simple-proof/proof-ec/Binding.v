(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(** * Substitution Definitions *)

(** Substitution on variables: [a[u/z]] (substituting [z] with [u] in [a]). *)
Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

(** Substitution on types and declarations: [T[u/z]] and [D[u/z]]. *)
Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_sel x L    => typ_sel (subst_avar z u x) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L U => dec_trm L (subst_typ z u U)
  end.

(** Substitution on terms, values, and definitions:
    [t[u/z]], [v[u/z]], [d[u/z]]. *)
Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_val v        => trm_val (subst_val z u v)
  | trm_sel x1 L     => trm_sel (subst_avar z u x1) L
  | trm_app x1 x2    => trm_app (subst_avar z u x1) (subst_avar z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: var) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | def_trm L t => def_trm L (subst_trm z u t)
  end
with subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

(** Substitution on the types of a typing environment: [G[u/z]]. *)
Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx :=
  map (subst_typ z u) G.

(** Substitution on the values of an evaluation context: [e[y/x]]. *)
Definition subst_env x y e := map (subst_val x y) e.


(** * Opening Lemmas *)

Ltac avar_solve :=
  repeat match goal with
  | [ a: avar |- _ ] =>
    destruct a; simpl; auto; repeat case_if; subst; simpls; repeat case_if*;
    subst; simpls; repeat case_if*
  end.

(** The following [open_fresh_XYZ_injective] lemmas state that given two
    symbols (variables, types, terms, etc.) [X] and [Y] and a variable [z],
    if [z \notin fv(X)] and [z \notin fv(Y)], then [X^z = Y^z] implies [X = Y]. *)

(** - variables *)
Lemma open_fresh_avar_injective : forall x y k z,
    z \notin fv_avar x ->
    z \notin fv_avar y ->
    open_rec_avar k z x = open_rec_avar k z y ->
    x = y.
Proof.
  intros. avar_solve; inversion* H1; try (inversions H3; false* notin_same).
Qed.

(** - types and declarations *)
Lemma open_fresh_typ_dec_injective:
  (forall T T' k x,
    x \notin fv_typ T ->
    x \notin fv_typ T' ->
    open_rec_typ k x T = open_rec_typ k x T' ->
    T = T') /\
  (forall D D' k x,
    x \notin fv_dec D ->
    x \notin fv_dec D' ->
    open_rec_dec k x D = open_rec_dec k x D' ->
    D = D').
Proof.

  Ltac invert_open :=
    match goal with
    | [ H: open_rec_typ _ _ _ = open_rec_typ _ _ ?T' |- _ ] =>
       destruct T'; inversions* H
    | [ H: open_rec_dec _ _ _ = open_rec_dec _ _ ?D' |- _ ] =>
       destruct D'; inversions* H
    end.

  apply typ_mutind; intros; invert_open; simpl in *;
    f_equal; eauto using open_fresh_avar_injective.
Qed.

(** The following [lc_open_rec_open_XYZ] lemmas state that if opening
    a symbol (variables, types, terms, etc.) at index [n] that is
    already opened at index [m] results in the same opened symbol,
    opening the symbol itself at index [n] results in the same symbol. *)


(** - types and declarations *)
Lemma lc_open_rec_open_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) = open_rec_typ m y T ->
        open_rec_typ n x T = T) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) = open_rec_dec m y D ->
        open_rec_dec n x D = D).
Proof.
  introv. apply typ_mutind; intros; simpls; auto; avar_solve;
            try solve [(inversions H1; erewrite H; eauto)
                      || (inversions H2; erewrite H; eauto; erewrite H0; eauto)].
  - inversions H1. rewrite H with (m:=S m); auto.
  - inversions H2. erewrite H; eauto. rewrite H0 with (m:=S m); auto.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma lc_open_rec_open_trm_val_def_defs: forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) = open_rec_trm m y t ->
        open_rec_trm n x t = t) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) = open_rec_val m y v ->
        open_rec_val n x v = v) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) = open_rec_def m y d ->
        open_rec_def n x d = d) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) = open_rec_defs m y ds ->
        open_rec_defs n x ds = ds).
Proof.
  intros.
  pose proof (proj21 (lc_open_rec_open_typ_dec x y)) as Htyp.
  apply trm_mutind;
    intros; simpls; auto;
      match goal with
      | [ H : _ = _ |- _ ] => injection H as ?; f_equal; eauto
      end; avar_solve.
Qed.

(** [x \notin fv(x, y)] #<br>#
    [―――――――――――――――――] #<br>#
    [x \notin fv(x^y)] *)
Lemma open_fv_avar : forall x z y k,
    x \notin fv_avar z \u \{y} ->
    x \notin fv_avar (open_rec_avar k y z).
Proof.
  intros. destruct z; simpls; try case_if; unfold fv_avar; auto.
Qed.

(** [x \notin fv(T, y)] #<br>#
    [―――――――――――――――――] #<br>#
    [x \notin fv(T^y)] *)
Lemma open_fv_typ_dec :
  (forall T x y k, x \notin fv_typ T \u \{y} -> x \notin fv_typ (open_rec_typ k y T)) /\
  (forall D x y k, x \notin fv_dec D \u \{y} -> x \notin fv_dec (open_rec_dec k y D)).
Proof.
  apply typ_mutind; intros; simpls; auto;
    apply open_fv_avar; auto.
Qed.

(** [x \notin fv(t, y)] #<br>#
    [―――――――――――――――――] #<br>#
    [x \notin fv(t^y)] *)
Lemma open_fv_trm_val_def_defs :
  (forall t x y k, x \notin fv_trm t \u \{y} -> x \notin fv_trm (open_rec_trm k y t)) /\
  (forall v x y k, x \notin fv_val v \u \{y} -> x \notin fv_val (open_rec_val k y v)) /\
  (forall d x y k, x \notin fv_def d \u \{y} -> x \notin fv_def (open_rec_def k y d)) /\
  (forall ds x y k, x \notin fv_defs ds \u \{y} -> x \notin fv_defs (open_rec_defs k y ds)).
Proof.
  Local Hint Resolve open_fv_avar.
  apply trm_mutind; intros; simpls; auto;
    try apply notin_union_l;
    try apply open_fv_typ_dec; auto.
Qed.


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


Notation "'lc_var' x" := (lc_at_var 0 x) (at level 0).
Notation "'lc_typ' T" := (lc_at_typ 0 T) (at level 0).
Notation "'lc_dec' D" := (lc_at_dec 0 D) (at level 0).

Notation "'lc_trm' t" := (lc_at_trm 0 t) (at level 0).
Notation "'lc_val' v" := (lc_at_val 0 v) (at level 0).
Notation "'lc_def' d" := (lc_at_def 0 d) (at level 0).
Notation "'lc_defs' ds" := (lc_at_defs 0 ds) (at level 0).


Scheme lc_at_trm_mut  := Induction for lc_at_trm Sort Prop
with   lc_at_val_mut  := Induction for lc_at_val Sort Prop
with   lc_at_def_mut  := Induction for lc_at_def Sort Prop
with   lc_at_defs_mut := Induction for lc_at_defs Sort Prop.
Combined Scheme lc_at_mutind from lc_at_trm_mut, lc_at_val_mut, lc_at_def_mut, lc_at_defs_mut.

Scheme lc_at_typ_mut := Induction for lc_at_typ Sort Prop
with   lc_at_dec_mut := Induction for lc_at_dec Sort Prop.
Combined Scheme lc_at_typ_mutind from lc_at_typ_mut, lc_at_dec_mut.


(** Locally closed evaluation contexts *)
Inductive lc_ec : ec -> Prop :=
| lc_ec_empty : lc_ec empty
| lc_ec_cons : forall x v e,
    lc_ec e ->
    lc_val v ->
    lc_ec (e & x ~ v).
Hint Constructors lc_ec.

(** ** Local Closure Lemmas *)

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
    try solve [apply lc_at_to_open_typ_dec; auto];
    solve [apply lc_at_to_open_avar; auto].
Qed.


Lemma open_to_lc_at_avar : forall x v k,
    lc_at_var k (open_rec_avar k x v) ->
    lc_at_var (S k) v.
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
  apply trm_mutind; intros; simpl;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    | [ H : lc_at_val _ _ |- _ ] => inversions H
    | [ H : lc_at_def _ _ |- _ ] => inversions H
    | [ H : lc_at_defs _ _ |- _ ] => inversions H
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    end;
    repeat constructor; auto;
    try solve [try fold open_rec_trm; auto];
    first [eapply open_to_lc_at_typ_dec | eapply open_to_lc_at_avar]; eauto.
Qed.


Lemma open_left_inverse_close_avar:
  forall v x k, lc_at_var k v -> open_rec_avar k x (close_rec_avar k x v) = v.
Proof with auto.
  intros. unfold open_rec_avar, close_rec_avar.
  inversion H; repeat case_if; subst...
  omega.
Qed.
Hint Resolve open_left_inverse_close_avar.


Lemma open_left_inverse_close_typ_dec:
  (forall T x k, lc_at_typ k T -> open_rec_typ k x (close_rec_typ k x T) = T) /\
  (forall D x k, lc_at_dec k D -> open_rec_dec k x (close_rec_dec k x D) = D).
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
  (forall t k x, lc_at_trm k t -> open_rec_trm k x (close_rec_trm k x t) = t) /\
  (forall v k x, lc_at_val k v -> open_rec_val k x (close_rec_val k x v) = v) /\
  (forall d k x, lc_at_def k d -> open_rec_def k x (close_rec_def k x d) = d) /\
  (forall ds k x, lc_at_defs k ds -> open_rec_defs k x (close_rec_defs k x ds) = ds).
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
      apply open_left_inverse_close_typ_dec; auto.
Qed.


(** The following [lc_at_opening_XYZ] lemmas state that opening a locally
    closed symbol (variables, types, terms, etc.) at any index
    results in the same symbol. *)

(** - variables *)
Lemma lc_at_opening_avar: forall m n x y,
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
  Local Hint Resolve lc_at_opening_avar.
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
  Local Hint Resolve lc_at_opening_avar.
  intro x.
  apply lc_at_mutind; intros; simpls; f_equal*;
    try solve
        [match goal with
         | [ H : _ -> _ -> ?f _ _ ?t = ?t |- ?f _ _ ?t = ?t ] => apply H
         end; omega];
  eapply lc_at_opening_typ_dec;
    try eassumption;
    try omega.
Qed.


(** The [lc_at_opening_trm_val_def_defs] lemma, specialized to terms. *)
Lemma lc_at_opening : forall t n x,
    lc_trm t ->
    open_rec_trm n x t = t.
Proof.
  intros. eapply lc_at_opening_trm_val_def_defs; try eassumption; try omega.
Qed.

(** When a binding is removed from a locally closed evaluation context, the
    resulting evaluation context and the value in the binding are both
    locally closed. *)
Lemma lc_ec_push_inv : forall s x v,
    lc_ec (s & x ~ v) ->
    lc_ec s /\ lc_val v.
Proof.
  intros s x v H.
  inversion H.
  - destruct (empty_push_inv H1).
  - destruct (eq_push_inv H0) as [? [? ?] ]; subst.
    auto.
Qed.


(** Values in a locally closed evaluation context are also locally closed. *)
Lemma lc_ec_binds_inv : forall e x v,
    lc_ec e ->
    binds x v e ->
    lc_val v.
Proof.
  intros.
  induction e using env_ind.
  - destruct (binds_empty_inv H0).
  - destruct (binds_push_inv H0) as [[? ?] | [? ?]]; subst.
    + apply (lc_ec_push_inv H).
    + apply IHe; auto.
      apply (lc_ec_push_inv H).
Qed.


(** A definition in a locally closed list of definitions is also
    locally closed. *)
Lemma lc_defs_has : forall ds d,
    lc_defs ds ->
    defs_has ds d ->
    lc_def d.
Proof.
  intros.
  induction ds.
  - inversion H0.
  - unfold defs_has in H0; simpl in H0.
    cases_if.
    + inversions H0. inversion H; auto.
    + apply IHds; auto. inversion H; auto.
Qed.

Lemma open_bound_lc_trm : forall k x t,
    lc_trm (open_trm x t) ->
    open_rec_trm (S k) x t = t.
Proof.
  intros.
  apply lc_at_opening with (n:=S k) (x:=x) in H.
  eapply (proj1 (lc_open_rec_open_trm_val_def_defs x _)).
  - instantiate (1 := 0). auto.
  - eassumption.
Qed.

(** If [x] is closed in [t], then [x \notin fv(t)]. *)

(** - for types and declarations *)
Lemma close_rec_typ_dec_no_capture : forall x,
    (forall T k, x \notin fv_typ (close_rec_typ k x T)) /\
    (forall D k, x \notin fv_dec (close_rec_dec k x D)).
Proof.
  intros x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a
    end; simpl;
      try case_if; unfold fv_avar; auto.
Qed.

(** - for terms, values, and definitions *)
Lemma close_rec_trm_val_def_defs_no_capture: forall x,
    (forall t k, x \notin fv_trm (close_rec_trm k x t)) /\
    (forall v k, x \notin fv_val (close_rec_val k x v)) /\
    (forall d k, x \notin fv_def (close_rec_def k x d)) /\
    (forall ds k, x \notin fv_defs (close_rec_defs k x ds)).
Proof.
  intro x.
  apply trm_mutind; intros; simpl; auto;
    try apply notin_union;
    repeat split;
    try apply close_rec_typ_dec_no_capture;
    repeat
      match goal with
      | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a; simpl
      end;
    repeat case_if; unfold fv_avar; auto.
Qed.

(** * Free Variables Lemmas *)

Lemma fv_ctx_types_push_eq : forall G x T,
    fv_ctx_types (G & x ~ T) = fv_ctx_types G \u fv_typ T.
Proof.
  intros.
  rewrite concat_def, single_def.
  unfold fv_ctx_types, fv_in_values; rewrite values_def.
  rewrite union_comm. reflexivity.
Qed.

(** [fv(e, x = v) = fv(e) ∪ fv(v)] *)
Lemma fv_ec_vals_push_eq : forall e x v,
    fv_ec_vals (e & x ~ v) = fv_ec_vals e \u fv_val v.
Proof.
  intros.
  rewrite concat_def, single_def.
  unfold fv_ec_vals, fv_in_values; rewrite values_def.
  rewrite union_comm. reflexivity.
Qed.

(** [e(y) = v]       #<br>#
    [x \notin fv(e)] #<br>#
    [――――――――――――――] #<br>#
    [x \notin fv(v)] *)
Lemma binds_fv_ec_vals : forall x y v e,
    binds y v e ->
    x \notin fv_ec_vals e ->
    x \notin fv_val v.
Proof.
  intros. unfold fv_ec_vals in H0.
  eapply fv_in_values_binds; eauto.
Qed.

(** * Variable Substitution Lemmas *)

(** [e(b) = v]            #<br>#
    [――――――――――――――――――]  #<br>#
    [e[y/x](b) = v[y/x]]  *)
Lemma binds_subst_env : forall x y b v e,
    binds b v e -> binds b (subst_val x y v) (subst_env x y e).
Proof.
  introv. gen x y b v. induction e using env_ind; intros.
  - destruct (binds_empty_inv H).
  - apply binds_push_inv in H.
    destruct_all; subst; unfold subst_env; rewrite map_push.
    + auto.
    + apply binds_push_neq; auto.
Qed.

(** Substitution preserves local closure. *)

(** - for variables *)
Lemma lc_at_subst_avar : forall v x y k,
    lc_at_var k v <-> lc_at_var k (subst_avar x y v).
Proof.
  intros.
  split; intros;
    try solve [inversion H; simpls; auto].
  destruct v; auto.
Qed.

(** - for types and declarations *)
Lemma lc_at_subst_typ_dec : forall k,
  (forall T, lc_at_typ k T -> forall x y, lc_at_typ k (subst_typ x y T)) /\
  (forall D, lc_at_dec k D -> forall x y, lc_at_dec k (subst_dec x y D)).
Proof.
  apply lc_at_typ_mutind; intros; simpls; auto.
  constructor. apply lc_at_subst_avar. trivial.
Qed.

(** - for terms, values, and definitions *)
Lemma lc_at_subst_trm_val_def_defs : forall k,
    (forall t, lc_at_trm k t -> forall x y, lc_at_trm k (subst_trm x y t)) /\
    (forall v, lc_at_val k v -> forall x y, lc_at_val k (subst_val x y v)) /\
    (forall d, lc_at_def k d -> forall x y, lc_at_def k (subst_def x y d)) /\
    (forall ds, lc_at_defs k ds -> forall x y, lc_at_defs k (subst_defs x y ds)).
Proof.
  apply lc_at_mutind; intros; simpls; auto;
    repeat constructor;
    try solve [apply lc_at_subst_avar; trivial];
    try apply lc_at_subst_typ_dec; trivial.
Qed.

(** The following [subst_fresh_XYZ] lemmas state that if [x] is not free
    in a symbol [Y], then [Y[z/x] = Y]. *)

(** Fresh substitution
    - in variables *)
Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

(** - in types and declarations *)
Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*.
  apply* subst_fresh_avar.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec x y).

(** - in terms, values, and definitions *)
Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec).
Qed.

(** [x \notin fv(G, z: T)]                   #<br>#
    [x \notin fv(T)]                         #<br>#
    [―――――――――――――――――――――――――――――――――――――] #<br>#
    [x \notin fv(T)] and [x \notin fv(G)] *)
Lemma invert_fv_ctx_types_push: forall x z T G,
  x \notin fv_ctx_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_ctx_types G).
Proof.
  introv H. rewrite fv_ctx_types_push_eq in H.
  apply~ notin_union.
Qed.

(** [x \notin fv(G)]         #<br>#
    [――――――――――――――――――]    #<br>#
    [G[y/x] = G]    *)
Lemma subst_fresh_ctx: forall x y G,
  x \notin fv_ctx_types G -> subst_ctx x y G = G.
Proof.
  intros x y.
  apply (env_ind (fun G => x \notin fv_ctx_types G -> subst_ctx x y G = G)).
  + intro N. unfold subst_ctx. apply map_empty.
  + intros G z T IH N.
    apply invert_fv_ctx_types_push in N. destruct N as [N1 N2].
    unfold subst_ctx in *. rewrite map_push.
    rewrite (IH N2).
    rewrite ((proj1 (subst_fresh_typ_dec _ _)) _ N1).
    reflexivity.
Qed.

(** Definition of substitution on named variables: #<br>#
    [z[y/x] := if z == x then y else z], where [z] is a named variable. *)
Definition subst_fvar(x y z: var): var := If z = x then y else z.

(** The following lemmas state that substitution commutes with opening:
    for a symbol [Z], #<br>#
    [(Z^a)[y/x] = (Z[y/x])^(a[y/x])]. *)

(** Substitution commutes with opening
    - variables *)
Lemma subst_open_commut_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a)
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

(** - types and declarations *)
Lemma subst_open_commut_typ_dec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*.
  apply subst_open_commut_avar.
Qed.

(** - types only *)
Lemma subst_open_commut_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply subst_open_commut_typ_dec.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma subst_open_commut_trm_val_def_defs: forall x y u,
  (forall t : trm, forall n: Datatypes.nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: Datatypes.nat,
     subst_val x y (open_rec_val n u v)
     = open_rec_val n (subst_fvar x y u) (subst_val x y v)) /\
  (forall d : def , forall n: Datatypes.nat,
     subst_def x y (open_rec_def n u d)
     = open_rec_def n (subst_fvar x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: Datatypes.nat,
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal~;
    (apply subst_open_commut_avar || apply subst_open_commut_typ_dec).
Qed.

(** - terms only *)
Lemma subst_open_commut_trm: forall x y u t,
    subst_trm x y (open_trm u t)
    = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply subst_open_commut_trm_val_def_defs.
Qed.

(** - definitions only *)
Lemma subst_open_commut_defs: forall x y u ds,
    subst_defs x y (open_defs u ds)
    = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros. apply subst_open_commut_trm_val_def_defs.
Qed.

(** The following lemmas state that opening a symbol with a variable [y]
    is the same as opening the symbol with another variable [x] and
    substituting [x] with [y]: #<br>#
    [Z^y = (Z^x)[y/x]] *)

(** Substitution after opening
    - terms *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite subst_open_commut_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite~ (Q t).
  unfold subst_fvar. case_var~.
Qed.

(** - definitions *)
Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr. unfold open_trm. rewrite subst_open_commut_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite~ (Q ds).
  unfold subst_fvar. case_var~.
Qed.

(** - types *)
Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr. unfold open_typ. rewrite subst_open_commut_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite~ (Q T).
  unfold subst_fvar. case_var~.
Qed.

Ltac subst_open_fresh :=
  repeat match goal with
    | [ |- context [ open_typ ?z (subst_typ ?x ?y ?T) ] ] =>
        replace (open_typ z (subst_typ x y T)) with (open_typ (subst_fvar x y z) (subst_typ x y T))
          by (unfold subst_fvar; rewrite~ If_r);
        rewrite_all <- subst_open_commut_typ
    | [ |- context [ open_defs ?z (subst_defs ?x ?y ?ds) ] ] =>
        replace (open_defs z (subst_defs x y ds)) with (open_defs (subst_fvar x y z) (subst_defs x y ds))
          by (unfold subst_fvar; rewrite~ If_r);
        rewrite_all <- subst_open_commut_defs
     | [ |- context [ open_trm ?z (subst_trm ?x ?y ?t) ] ] =>
        replace (open_trm z (subst_trm x y t)) with (open_trm (subst_fvar x y z) (subst_trm x y t))
          by (unfold subst_fvar; rewrite~ If_r);
        rewrite_all <- subst_open_commut_trm
    end.

(** Substitution preserves labels of definitions: [label(d) = label(d[y/x])] *)
Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct d; reflexivity.
Qed.

(** [l \notin labels(ds)]     #<br>#
    [――――――――――――――――――――――] #<br>#
    [l \notin labels(ds[y/x]] *)
Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if~.
Qed.

(** [z <> x]                             #<br>#
    [ds^z = ...{a = t}...]              #<br>#
    [――――――――――――――――――――――――――――――――]  #<br>#
    [(ds[y/x])^z = ...{a = t[y/x]}...]  *)
Lemma open_subst_defs : forall x y z a ds t,
    z <> x ->
    defs_has (open_defs z ds) (def_trm a t) ->
    defs_has (open_defs z (subst_defs x y ds)) (def_trm a (subst_trm x y t)).
Proof.
  introv. gen x y z a t. induction ds; intros.
  - inversion H0.
  - unfold open_defs, defs_has in *; simpls. case_if.
    + destruct d; simpls; case_if; auto.
      inversions H0.
      rewrite subst_open_commut_trm. unfold subst_fvar.
      case_if. auto.
    + case_if; apply IHds; destruct d; auto; contradiction.
Qed.

(** [y <> x]                             #<br>#
    [ds^x = ...{a = t}...]              #<br>#
    [――――――――――――――――――――――――――――――――]  #<br>#
    [(ds[y/x])^y = ...{a = t[y/x]}...]  *)
Lemma open_subst_defs2 : forall x y a ds t,
    y <> x ->
    defs_has (open_defs x ds) (def_trm a t) ->
    defs_has (open_defs y (subst_defs x y ds)) (def_trm a (subst_trm x y t)).
Proof.
  introv. gen x y a t. induction ds; intros.
  - inversion H0.
  - unfold open_defs, defs_has in *.
    simpls; case_if; destruct d; simpls; case_if; auto.
    subst; inversion H0.
    rewrite subst_open_commut_trm. unfold subst_fvar. case_if; auto.
Qed.
