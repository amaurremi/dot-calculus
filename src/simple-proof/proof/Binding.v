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
  | typ_ref T      => typ_ref (subst_typ z u T)
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
  | trm_ref x t      => trm_ref (subst_avar z u x) (subst_typ z u t)
  | trm_deref x      => trm_deref (subst_avar z u x)
  | trm_asg x y      => trm_asg (subst_avar z u x) (subst_avar z u y)
  end
with subst_val (z: var) (u: var) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  | val_loc l        => val_loc l
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

Definition subst_sigma (z: var) (u: var) (G: stoty) : stoty :=
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

(** * Free Variables Lemmas *)

Lemma fv_ctx_types_push_eq : forall G x T,
    fv_ctx_types (G & x ~ T) = fv_ctx_types G \u fv_typ T.
Proof.
  intros.
  rewrite concat_def, single_def.
  unfold fv_ctx_types, fv_in_values; rewrite values_def.
  rewrite union_comm. reflexivity.
Qed.

Lemma fv_stoty_types_push_eq : forall Sigma x T,
    fv_stoty_types (Sigma & x ~ T) = fv_stoty_types Sigma \u fv_typ T.
Proof.
  intros.
  rewrite concat_def, single_def.
  unfold fv_stoty_types, fv_in_values; rewrite values_def.
  rewrite union_comm. reflexivity.
Qed.

(** * Variable Substitution Lemmas *)

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

Lemma invert_fv_stoty_types_push: forall x z T Sigma,
  x \notin fv_stoty_types (Sigma & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_stoty_types Sigma).
Proof.
  introv H. rewrite fv_stoty_types_push_eq in H.
  apply~ notin_union.
Qed.

Lemma subst_fresh_sigma: forall x y Sigma,
  x \notin fv_stoty_types Sigma -> subst_sigma x y Sigma = Sigma.
Proof.
  intros x y.
  apply (env_ind (fun Sigma => x \notin fv_stoty_types Sigma -> subst_sigma x y Sigma = Sigma)).
  + intro N. unfold subst_sigma. apply map_empty.
  + intros Sigma z T IH N.
    apply invert_fv_stoty_types_push in N. destruct N as [N1 N2].
    unfold subst_sigma in *. rewrite map_push.
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

(** If a variable has a type, then it is a named variable. *)
Lemma var_typing_implies_avar_f: forall G Sigma a T,
    G ⋆ Sigma ⊢ trm_var a : T ->
    exists x, a = avar_f x.
Proof.
  introv H; dependent induction H; eauto.
Qed.
