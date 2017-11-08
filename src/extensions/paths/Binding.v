(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import LibLN.
Require Import Definitions LocalClosure.

(** Substitution on variables: [a[u/z]] (substituting [z] with [u] in [a]). *)

Definition subst_var (z: var) (u: var) (x: var): var :=
  If x = z then u else x.

Definition subst_var_p (z: var) (u: path) (x: var): path :=
  If x = z then u else (pvar x).

Hint Unfold subst_var subst_var_p.

Definition subst_avar (z: var) (u: path) (a: avar) : path :=
  match a with
  | avar_b i => p_sel (avar_b i) nil
  | avar_f x => subst_var_p z u x
  end.

(* p    [u / z] where p = x.bs:
   x.bs [u / z] == x [u / z] . bs *)
Definition subst_path (z: var) (u: path) (p: path) : path :=
  match p with
  | p_sel x bs => sel_fields (subst_avar z u x) bs
  end.

(** Substitution on types and declarations: [T[u/z]] and [D[u/z]]. *)
Fixpoint subst_typ (z: var) (u: path) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_path q L    => typ_path (subst_path z u q) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: path) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L U => dec_trm L (subst_typ z u U)
  end.

(** Substitution on terms, values, and definitions:
    [t[u/z]], [v[u/z]], [d[u/z]]. *)
Fixpoint subst_trm (z: var) (u: path) (t: trm) : trm :=
  match t with
  | trm_val v        => trm_val (subst_val z u v)
  | trm_path p       => trm_path (subst_path z u p)
  | trm_app x1 x2    => trm_app (subst_path z u x1) (subst_path z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: path) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  end
with subst_def (z: var) (u: path) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | def_trm L t => def_trm L (subst_trm z u t)
  end
with subst_defs (z: var) (u: path) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

(** Substitution on the types of a typing environment: [G[u/z]]. *)
Definition subst_ctx (z: var) (u: path) (G: ctx) : ctx :=
  map (subst_typ z u) G.

(** Substitution on the values of an evaluation context: [e[y/x]]. *)
Definition subst_env x y e := map (subst_val x y) e.

(** ** Field selection *)

(** [(p^q).bs = (p.bs)^q ] *)
Lemma sel_fields_open : forall n p q bs,
  sel_fields (open_rec_path_p n p q) bs = open_rec_path_p n p (sel_fields q bs).
Proof.
  intros. destruct q. simpl. destruct p. destruct a. case_if; simpl; auto. rewrite* app_assoc.
  simpl. auto.
Qed.

(** [y.bs.b [p/x] = (y.bs [p/x]).b] *)
Lemma sel_fields_subst : forall x p y bs b,
    subst_path x p (p_sel y bs) • b = (subst_path x p (p_sel y bs)) • b.
Proof.
  intros. destruct p, y; auto. simpl. unfold subst_var_p. case_if; simpl; auto.
Qed.

(** [p.a = x.bs]    #<br>#
    [―――――――――――――] #<br>#
    [bs = a :: bs'] *)
Lemma last_field : forall p a x bs,
    p • a = p_sel x bs ->
    exists bs', bs = a :: bs'.
Proof.
  introv Heq. destruct* p. inversion* Heq.
Qed.

(** [p.a = q.b]    #<br>#
    [――――――――――――] #<br>#
    [p = q, a = b] *)
Lemma invert_path_sel : forall p q a b,
    p • a = q • b -> p = q /\ a = b.
Proof.
  introv Heq. destruct p as [x1 bs1]. destruct q as [x2 bs2].
  induction bs1; inversion* Heq.
Qed.

(** * Opening Lemmas *)

(** ** Conversion between opening with paths and variables *)

Lemma open_var_path_eq : forall x p n,
    open_rec_path n x p = open_rec_path_p n (pvar x) p.
Proof.
  intros. destruct p, a. simpl. repeat case_if*. rewrite* app_nil_r.
  simpl. reflexivity.
Qed.

Lemma open_var_typ_dec_eq: forall x,
    (forall T : typ, forall n : nat,
          open_rec_typ n x T = open_rec_typ_p n (pvar x) T) /\
    (forall D : dec, forall n : nat,
          open_rec_dec n x D = open_rec_dec_p n (pvar x) D).
Proof.
  intros. apply typ_mutind; unfold open_typ, open_typ_p; simpl; intros; auto;
            try solve [rewrite* H; rewrite* H0].
  unfold open_rec_avar, open_rec_avar_p. rewrite* open_var_path_eq.
Qed.

Lemma open_var_typ_eq: forall x T,
  open_typ x T = open_typ_p (pvar x) T.
Proof.
  intros. apply open_var_typ_dec_eq.
Qed.

Lemma open_var_dec_eq: forall x D,
  open_dec x D = open_dec_p (pvar x) D.
Proof.
  intros. apply open_var_typ_dec_eq.
Qed.

Hint Rewrite open_var_typ_eq open_var_dec_eq open_var_path_eq.

Lemma open_var_trm_val_def_eq : forall x,
  (forall t n,
      open_rec_trm n x t = open_rec_trm_p n (pvar x) t) /\
  (forall v n,
      open_rec_val n x v = open_rec_val_p n (pvar x) v) /\
  (forall d n,
      open_rec_def n x d = open_rec_def_p n (pvar x) d) /\
  (forall ds n,
      open_rec_defs n x ds = open_rec_defs_p n (pvar x) ds).
Proof.
  introv. apply trm_mutind; intros; simpl; f_equal*;
            try (rewrite* open_var_path_eq); rewrite* (proj1 (open_var_typ_dec_eq x)).
Qed.

Lemma open_var_defs_eq: forall x ds,
    open_defs x ds = open_defs_p (pvar x) ds.
Proof.
  intros. apply* open_var_trm_val_def_eq.
Qed.

Lemma open_var_trm_eq: forall x t,
    open_trm x t = open_trm_p (pvar x) t.
Proof.
  intros. apply* open_var_trm_val_def_eq.
Qed.

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

(** - paths *)
Lemma open_fresh_path_injective : forall p q k z,
    z \notin fv_path p ->
    z \notin fv_path q ->
    open_rec_path k z p = open_rec_path k z q ->
    p = q.
Proof.
  intros. destruct p, q. inversions* H1. simpl in *; f_equal.
  Admitted.

 Ltac invert_open :=
    match goal with
    | [ H: _ = open_rec_typ _ _ ?T' |- _ ] =>
       destruct T'; inversions* H
    | [ H: _ = open_rec_dec _ _ ?D' |- _ ] =>
       destruct D'; inversions* H
    end.

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
  apply typ_mutind; intros; invert_open; simpl in *;
    f_equal; eauto using open_fresh_avar_injective, open_fresh_path_injective.
Qed.

Lemma open_fresh_trm_val_def_defs_injective:
  (forall t t' k x,
      x \notin fv_trm t ->
      x \notin fv_trm t' ->
      open_rec_trm k x t = open_rec_trm k x t' ->
      t = t') /\
  (forall v v' k x,
      x \notin fv_val v ->
      x \notin fv_val v' ->
      open_rec_val k x v = open_rec_val k x v' ->
      v = v') /\
  (forall d d' k x,
      x \notin fv_def d ->
      x \notin fv_def d' ->
      open_rec_def k x d = open_rec_def k x d' ->
      d = d') /\
  (forall ds ds' k x,
      x \notin fv_defs ds ->
      x \notin fv_defs ds' ->
      open_rec_defs k x ds = open_rec_defs k x ds' ->
      ds = ds').
Proof.

  Ltac injective_solver :=
    match goal with
    | [ H: _ = open_rec_trm _ _ ?t |- _ ] =>
      destruct t; inversions H;
      try (f_equal; simpl in *);
           try (apply* open_fresh_avar_injective || apply* open_fresh_path_injective);
           match goal with
           | [ Ho: open_rec_avar _ _ _ = open_rec_avar _ _ _ |- _ ] =>
             apply open_fresh_avar_injective in Ho; subst*
           | [ Heq: forall _ _ _, _ -> _ -> _ -> ?u = _ |- ?u = _ ] =>
             apply* Heq
           end
    | [ H: _ = open_rec_val _ _ ?v |- _ ] =>
      destruct v; inversions H; f_equal; simpl in *;
      try apply* open_fresh_typ_dec_injective; eauto
    | [ H: _ = open_rec_def _ _ ?d |- _ ] =>
      destruct d; inversions H; f_equal;
      try apply* open_fresh_typ_dec_injective; eauto
    | [ H: _ = open_rec_defs _ _ ?ds |- _ ] =>
      destruct ds; inversions H; f_equal; simpl in *; eauto
    end.

  apply trm_mutind; intros; try solve [injective_solver].
Qed.

(** * Variable Substitution Lemmas *)

(** The following [subst_fresh_XYZ] lemmas state that if [x] is not free
    in a symbol [Y], then [Y[z/x] = Y]. *)

(** Fresh substitution
    - in variables *)
Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = p_sel a nil).
Proof.
  intros. destruct* a. simpl. autounfold. case_var*. simpls. notin_false.
Qed.

(** - in paths *)
Lemma subst_fresh_path : forall x q p,
    x \notin fv_path p ->
    subst_path x q p = p.
Proof.
  intros. destruct p as [[n | z] bs]; simpls.
  - Case "p = (avar_b n).bs".
    rewrite* app_nil_r.
  - Case "p = (avar_f z).bs".
    unfold subst_var_p. apply notin_singleton in H. case_if.
    simpl. rewrite* app_nil_r.
Qed.

(** - in types, declarations *)
Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ  , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec  , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_path.
Qed.

Definition subst_fresh_typ x p := proj1 (subst_fresh_typ_dec x p).

(** - in terms, values, and definitions *)
Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_typ_dec || apply* subst_fresh_path).
Qed.

(** [fv(G, x: T) = fv(G) \u fv(T)] *)
Lemma fv_ctx_types_push_eq : forall G x T,
    fv_ctx_types (G & x ~ T) = fv_ctx_types G \u fv_typ T.
Proof.
  intros.
  rewrite concat_def, single_def.
  unfold fv_ctx_types, fv_in_values; rewrite values_def.
  rewrite union_comm. reflexivity.
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
Lemma subst_open_commut_avar: forall x p u y n,
    lc_path p ->
    subst_avar x p (open_rec_avar n u y)
    = open_rec_path_p n (subst_var_p x p u) (subst_avar x p y).
Proof.
  introv Hl. unfold subst_var_p, subst_avar, open_rec_avar, subst_var_p.
  destruct y as [n' | y]; autounfold; destruct p as [z bs]; destruct z as [m | z'];
    repeat case_if; simpl; try case_if*; eauto; inversions  Hl; inversion H0; inversion H1.
Qed.

(** - paths *)
Lemma subst_open_commut_path: forall p n x q u,
    lc_path p ->
    subst_path x p (open_rec_path n u q)
    = open_rec_path_p n (subst_var_p x p u) (subst_path x p q).
Proof.
  introv Hl. destruct q as [z bs]. simpl. rewrite* subst_open_commut_avar. rewrite* sel_fields_open.
Qed.

(** - types and declarations *)
Lemma subst_open_commut_typ_dec: forall x p u,
  lc_path p ->
  (forall t : typ, forall n: nat,
     subst_typ x p (open_rec_typ n u t)
     = open_rec_typ_p n (subst_var_p x p u) (subst_typ x p t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x p (open_rec_dec n u D)
     = open_rec_dec_p n (subst_var_p x p u) (subst_dec x p D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply* subst_open_commut_path.
Qed.

Lemma subst_open_commut_p: forall x p u y n,
    lc_path p ->
    subst_path x p (open_rec_avar_p n u y)
    = open_rec_path_p n (subst_path x p u) (subst_avar x p y).
Proof.
  introv Hl. unfold subst_path, subst_avar, subst_var_p.
  destruct y as [n' | y]; simpl; repeat case_if; destruct u; destruct a; simpl;
    try (rewrite* app_nil_r); repeat case_if; unfold sel_fields; destruct* p;
      inversions Hl; inversions H0; rewrite* app_nil_l; inversion H.
Qed.

Lemma subst_open_commut_path_p: forall p n x q u,
    lc_path q ->
    subst_path x q (open_rec_path_p n u p)
    = open_rec_path_p n (subst_path x q u) (subst_path x q p).
Proof.
  introv Hl. destruct p as [z bs]. simpl.
  unfold subst_path. destruct u. rewrite <- sel_fields_open.
  unfold open_rec_path_p, subst_avar.
  destruct z; simpl; destruct a; repeat case_if*;
    unfold subst_var_p; repeat case_if;
      destruct q; simpl; try (rewrite app_assoc || rewrite app_nil_r);
        inversion* Hl; subst. inversions H0. (*inversions H0. eauto. inversions H.
        try solve [inversion Hl; inversion* H0].*)

Admitted.

Lemma subst_open_commut_typ_dec_p: forall x y u,
  lc_path y ->
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ_p n u t)
     = open_rec_typ_p n (subst_path x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec_p n u D)
     = open_rec_dec_p n (subst_path x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*.
  apply* subst_open_commut_path_p.
Qed.

(** - types only *)
Lemma subst_open_commut_typ: forall x y u T,
  lc_path y ->
  subst_typ x y (open_typ u T) = open_typ_p (subst_var_p x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commut_typ_dec.
Qed.

Lemma subst_open_commut_typ_p: forall x y u T,
    lc_path y ->
    subst_typ x y (open_typ_p u T) = open_typ_p (subst_path x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commut_typ_dec_p.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma subst_open_commut_trm_val_def_defs: forall x y u,
    lc_path y ->
  (forall t : trm, forall n: nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm_p n (subst_var_p x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: nat,
     subst_val x y (open_rec_val n u v)
     = open_rec_val_p n (subst_var_p x y u) (subst_val x y v)) /\
  (forall d : def , forall n: nat,
     subst_def x y (open_rec_def n u d)
     = open_rec_def_p n (subst_var_p x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: nat,
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs_p n (subst_var_p x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
  apply* subst_open_commut_path || apply* subst_open_commut_typ_dec.
Qed.

Lemma subst_open_commut_trm_val_def_defs_p: forall x y u,
    lc_path y ->
  (forall t : trm, forall n: nat,
     subst_trm x y (open_rec_trm_p n u t)
     = open_rec_trm_p n (subst_path x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: nat,
     subst_val x y (open_rec_val_p n u v)
     = open_rec_val_p n (subst_path x y u) (subst_val x y v)) /\
  (forall d : def , forall n: nat,
     subst_def x y (open_rec_def_p n u d)
     = open_rec_def_p n (subst_path x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: nat,
     subst_defs x y (open_rec_defs_p n u ds)
     = open_rec_defs_p n (subst_path x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
  apply* subst_open_commut_typ_dec_p || apply* subst_open_commut_path_p.
Qed.

(** - terms only *)
Lemma subst_open_commut_trm: forall x y u t,
    lc_path y ->
    subst_trm x y (open_trm u t)
    = open_trm_p (subst_var_p x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

Lemma subst_open_commut_trm_p: forall x y u t,
    lc_path y ->
    subst_trm x y (open_trm_p u t)
    = open_trm_p (subst_path x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs_p.
Qed.

(** - definitions only *)
Lemma subst_open_commut_defs: forall x y u ds,
    lc_path y ->
    subst_defs x y (open_defs u ds)
    = open_defs_p (subst_var_p x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

Lemma subst_open_commut_defs_p: forall x y u ds,
    lc_path y ->
    subst_defs x y (open_defs_p u ds)
    = open_defs_p (subst_path x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs_p.
Qed.

(** The following lemmas state that opening a symbol with a variable [y]
    is the same as opening the symbol with another variable [x] and
    substituting [x] with [y]: #<br>#
    [Z^y = (Z^x)[y/x]] *)

(** Substitution after opening
    - terms *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) -> lc_path u ->
  open_trm_p u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr Hl. unfold open_trm. rewrite* subst_open_commut_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite~ (Q t).
  unfold subst_var_p. case_var~.
Qed.

(** - definitions *)
Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) -> lc_path u ->
  open_defs_p u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr Hl. unfold open_trm. rewrite* subst_open_commut_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite~ (Q ds).
  unfold subst_var_p. case_var~.
Qed.

(** - types *)
Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) -> lc_path u ->
  open_typ_p u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr Hl. unfold open_typ. rewrite* subst_open_commut_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
  unfold subst_var_p. case_var*.
Qed.

Ltac subst_open_fresh :=
  match goal with
  | [ |- context [ open_typ ?z (subst_typ ?x ?p ?T) ] ] =>
    replace (open_typ z (subst_typ x p T)) with (open_typ_p (subst_path x p (pvar z)) (subst_typ x p T)) by
        (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_typ_eq; auto)
    | [ |- context [ open_defs ?z (subst_defs ?x ?p ?ds) ] ] =>
        replace (open_defs z (subst_defs x p ds)) with (open_defs_p (subst_path x p (pvar z)) (subst_defs x p ds))
          by (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_defs_eq; auto)
     | [ |- context [ open_trm ?z (subst_trm ?x ?p ?t) ] ] =>
        replace (open_trm z (subst_trm x p t)) with (open_trm_p (subst_path x p (pvar z)) (subst_trm x p t))
          by (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_trm_eq; auto)
    end.

(** Substitution preserves labels of definitions: [label(d) = label(d[y/x])] *)
Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct* d.
Qed.

(** [l \notin labels(ds)]     #<br>#
    [――――――――――――――――――――――] #<br>#
    [l \notin labels(ds[y/x]] *)
Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq; auto.
  unfold get_def. simpl. rewrite <- subst_label_of_def.
  simpl in Eq. case_if~.
Qed.
