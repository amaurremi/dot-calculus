(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import LibLN.
Require Import Definitions.


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

(** * Simple Implications of Typing *)

Definition named_path p := exists x bs, p = p_sel (avar_f x) bs.

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x bs T,
  G ⊢ trm_path (p_sel (avar_f x) bs) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
  destruct (last_field _ _ x) as [bs' Hbs]. subst.
  eapply IHHt. destruct p. inversion* x.
Qed.

Lemma typed_paths_named: forall G p T,
    G ⊢ trm_path p : T ->
    named_path p.
Proof.
  intros. destruct p.
  dependent induction H; eauto; unfolds named_path, pvar.
  - repeat eexists.
  - destruct (last_field _ _ x) as [bs' Hbs]. subst. destruct p.
    specialize (IHty_trm _ _ eq_refl). destruct_all. inversions x. inversions H0. repeat eexists.
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
    named_path p ->
    subst_avar x p (open_rec_avar n u y)
    = open_rec_path_p n (subst_var_p x p u) (subst_avar x p y).
Proof.
  introv Hl. unfold subst_var_p, subst_avar, open_rec_avar, subst_var_p.
  destruct y as [n' | y]; autounfold; destruct p as [z bs]; destruct z as [m | z'];
    repeat case_if; simpl; try case_if*; eauto; inversions  Hl; destruct_all; inversion H.
Qed.

(** - paths *)
Lemma subst_open_commut_path: forall p n x q u,
    named_path p ->
    subst_path x p (open_rec_path n u q)
    = open_rec_path_p n (subst_var_p x p u) (subst_path x p q).
Proof.
  introv Hl. destruct q as [z bs]. simpl. rewrite* subst_open_commut_avar. rewrite* sel_fields_open.
Qed.

(** - types and declarations *)
Lemma subst_open_commut_typ_dec: forall x p u,
  named_path p ->
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
    named_path p ->
    subst_path x p (open_rec_avar_p n u y)
    = open_rec_path_p n (subst_path x p u) (subst_avar x p y).
Proof.
  introv Hl. unfold subst_path, subst_avar, subst_var_p.
  destruct y as [n' | y]; simpl; repeat case_if; destruct u; destruct a; simpl;
    try (rewrite* app_nil_r); repeat case_if; unfold sel_fields; destruct* p;
      inversions Hl; destruct_all; inversions H; rewrite* app_nil_l; inversion H.
Qed.

Lemma subst_open_commut_path_p: forall p n x q u,
    named_path q ->
    subst_path x q (open_rec_path_p n u p)
    = open_rec_path_p n (subst_path x q u) (subst_path x q p).
Proof.
  introv Hl. destruct p as [z bs]. simpl.
  unfold subst_path. destruct u. rewrite <- sel_fields_open.
  unfold open_rec_path_p, subst_avar.
  destruct z; simpl; destruct a; repeat case_if*;
    unfold subst_var_p; repeat case_if;
      destruct q; simpl; try (rewrite app_assoc || rewrite app_nil_r);
        inversion* Hl; subst; destruct_all; inversions H. (*inversions H0. eauto. inversions H.
        try solve [inversion Hl; inversion* H0].*)

Admitted.

Lemma subst_open_commut_typ_dec_p: forall x y u,
  named_path y ->
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
  named_path y ->
  subst_typ x y (open_typ u T) = open_typ_p (subst_var_p x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commut_typ_dec.
Qed.

Lemma subst_open_commut_typ_p: forall x y u T,
    named_path y ->
    subst_typ x y (open_typ_p u T) = open_typ_p (subst_path x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commut_typ_dec_p.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma subst_open_commut_trm_val_def_defs: forall x y u,
    named_path y ->
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
    named_path y ->
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
    named_path y ->
    subst_trm x y (open_trm u t)
    = open_trm_p (subst_var_p x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

Lemma subst_open_commut_trm_p: forall x y u t,
    named_path y ->
    subst_trm x y (open_trm_p u t)
    = open_trm_p (subst_path x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs_p.
Qed.

(** - definitions only *)
Lemma subst_open_commut_defs: forall x y u ds,
    named_path y ->
    subst_defs x y (open_defs u ds)
    = open_defs_p (subst_var_p x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

Lemma subst_open_commut_defs_p: forall x y u ds,
    named_path y ->
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
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) -> named_path u ->
  open_trm_p u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr Hl. unfold open_trm. rewrite* subst_open_commut_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite~ (Q t).
  unfold subst_var_p. case_var~.
Qed.

(** - definitions *)
Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) -> named_path u ->
  open_defs_p u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr Hl. unfold open_trm. rewrite* subst_open_commut_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite~ (Q ds).
  unfold subst_var_p. case_var~.
Qed.

(** - types *)
Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) -> named_path u ->
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

(** [ds = ... /\ {a = t} /\ ...]  #<br>#
    [ds = ... /\ {a = t'} /\ ...] #<br>#
    [―――――――――――――――――――――――――] #<br>#
    [t = t'] *)
Lemma defs_has_inv: forall ds a t t',
    defs_has ds (def_trm a t) ->
    defs_has ds (def_trm a t') ->
    t = t'.
Proof.
  intros. unfold defs_has in *.
  inversions H. inversions H0.
  rewrite H1 in H2. inversions H2.
  reflexivity.
Qed.

Lemma proj_rewrite : forall x bs a,
    (p_sel x (a :: bs)) = (p_sel x bs) • a.
Proof.
  auto. Qed.

Hint Rewrite proj_rewrite.

(** * Environment Lookup *)

(** * Path lookup *)

Reserved Notation "s '∋' t '//' ps" (at level 40).
Reserved Notation "s '↓' p '==' ds '//' ps" (at level 40).


(** Looking up a path in a stack (generalization of variable binding). *)

Inductive lookup : sta -> path * val -> list path -> Prop :=

(** [s(x) = v         ]    #<br>#
    [―――――――――――――――――]    #<br>#
    [s ∋ (x, v) // ps ]        *)
| lookup_var : forall s x v ps,
    binds x v s ->
    s ∋ (pvar x, v) // ps

(** [s ↓ p = ...{a = v}... // ps ]    #<br>#
    [――――――――――――――――――――――――――――]    #<br>#
    [s ∋ (p.a, v) // ps          ]        *)
| lookup_val : forall s p ds a v ps,
    s ↓ p == ds // ps ->
    defs_has ds (def_trm a (trm_val v)) ->
    s ∋ (p•a, v) // ps

(** [s ↓ p = ...{a = q}... // ps         ]    #<br>#
    [q ∉ ps                              ]    #<br>#
    [s ∋ (q, v) // p•a::ps               ]    #<br>#
    [――――――――――――――――――――――――――――――――――――]    #<br>#
    [s ∋ (p.a, v) // ps                  ]        *)
| lookup_path : forall s p ds ps a q v,
    s ↓ p == ds // ps ->
    defs_has ds (def_trm a (trm_path q)) ->
    ~ (In q ps) ->
    s ∋ (q, v) // (p•a :: ps) ->
    s ∋ (p•a, v) // ps

where "s '∋' t '//' ps" := (lookup s t ps)

(** Opening of definitions:
    If [s ∋ (p, ν(x: T)ds)], then [lookup_open] gives us [ds] opened with [p]. *)

with lookup_open : sta -> path -> defs -> list path -> Prop :=

(** [s ∋ (p, ν(T)ds) // ps       ]    #<br>#
    [――――――――――――――――――――――――――――]    #<br>#
    [s ↓ p = ds^p // ps          ]        *)
| lookup_defs : forall s p T ds ps,
    s ∋ (p, val_new T ds) // ps ->
    s ↓ p == open_defs_p p ds // ps

where "s '↓' p '==' ds '//' ps" := (lookup_open s p ds ps).

Hint Constructors lookup lookup_open.

Scheme lookup_mut := Induction for lookup Sort Prop
  with lookup_open_mut := Induction for lookup_open Sort Prop.
Combined Scheme lookup_mutind from lookup_mut, lookup_open_mut.

(** ** Lemmas about Environment Lookup *)

Lemma lookup_func_mut :
  (forall s t ps1,
    s ∋ t // ps1 -> forall p v1 v2 ps2,
    t = (p, v1) ->
    s ∋ (p, v2) // ps2 ->
    v1 = v2) /\
  (forall s p ds1 ps1,
    s ↓ p == ds1 // ps1 -> forall ds2 ps2,
    s ↓ p == ds2 // ps2 ->
    ds1 = ds2).
Proof.
  apply lookup_mutind; intros.
  - Case "lookup_var".
    inversions H. dependent induction H0; unfolds sel_fields; try (destruct p; inversions x).
    lets Hb: (binds_func b H). subst*.
  - Case "lookup_val".
    inversions H0. inversions H1; unfolds sel_fields, pvar; destruct p.
    * inversion H0.
    * destruct p0. inversions H0. specialize (H _ _ H4). subst. lets Hd: (defs_has_inv H6 d). inversion* Hd.
    * inversions H0. destruct p0. inversions H2.
      specialize (H _ _ H3). subst. lets Hd: (defs_has_inv H4 d). inversion Hd.
  - Case "lookup_path".
    inversions H1. inversions H2; unfolds sel_fields, pvar.
    * destruct p. inversion H1.
    * destruct p0, p. inversions H1. specialize (H _ _ H5). subst. lets Hd: (defs_has_inv H7 d). inversion Hd.
    * destruct p0, p. inversions H1.  specialize (H _ _ H4). subst. lets Hd: (defs_has_inv H5 d). inversions Hd.
      simpls. inversions l. inversions H4. apply* H0.
  - Case "lookup_defs".
    lets Hl: (lookup_defs l). inversions H0. specialize (H _ _ _ _ eq_refl H1).
    inversion* H.
Qed.

Lemma lookup_func : forall s p v1 v2 ps1 ps2,
    s ∋ (p, v1) // ps1 ->
    s ∋ (p, v2) // ps2 ->
    v1 = v2.
Proof.
  intros. lets Hl: (proj21 lookup_func_mut). specialize (Hl _ _ _ H _ _ _ _ eq_refl H0). apply Hl.
Qed.

Lemma lookup_empty_mut :
  (forall s t ps,
      s ∋ t // ps ->
      s = empty ->
      False) /\
  (forall s p ds ps,
      s ↓ p == ds // ps ->
      s = empty ->
      False).
Proof.
  apply lookup_mutind; auto. intros. subst. false* binds_empty_inv.
Qed.

Lemma lookup_empty : forall t ps,
    empty ∋ t // ps -> False.
Proof.
  intros. eapply (proj21 lookup_empty_mut); eauto.
Qed.

Lemma lookup_push_eq_inv_var :
    forall s x v v' ps,
    s & x ~ v ∋ (pvar x, v') // ps ->
    v = v'.
Proof.
  introv Hx. inversions Hx;
    try (destruct (last_field _ _ H) as [bs Hbs]; inversion Hbs).
  apply binds_push_eq_inv in H3. subst*.
Qed.

Lemma lookup_push_neq : forall s x bs v y v' ps,
    s ∋ (p_sel (avar_f x) bs, v) // ps ->
    x <> y ->
    s & y ~ v' ∋ (p_sel (avar_f x) bs, v) // ps.
Proof.
  introv Hp Hn. dependent induction Hp.
  Admitted.

Lemma lookup_strengthen: forall s y v x bs w ps,
    s & y ~ v ∋ (p_sel (avar_f x) bs, w) // ps ->
    y <> x ->
    s ∋ (p_sel (avar_f x) bs, w) // ps.
Proof.
Admitted.

Lemma named_path_lookup:
    (forall s t ps,
        s ∋ t // ps -> forall p v,
        t = (p, v) ->
        exists x bs, p = p_sel (avar_f x) bs) /\
    (forall s p ds ps,
        s ↓ p == ds // ps ->
        exists x bs, p = p_sel (avar_f x) bs).
Proof.
  apply lookup_mutind; intros.
  - inversions H. repeat eexists.
  - destruct_all. inversions H0. repeat eexists.
  - inversions H1. destruct_all. subst. repeat eexists.
  - eauto.
Qed.

Lemma named_path_lookup_l: forall s p ps v,
    s ∋ (p, v) // ps ->
    exists x bs, p = p_sel (avar_f x) bs.
Proof.
  intros. apply* (proj21 named_path_lookup).
Qed.

(** * Testing lookup definition *)

Variables a b c d: trm_label.
Variables x y z: var.
Hypothesis (Hab: a <> b).
Hypothesis (Hxy: y <> x).

(* λ(z: ⊤)0.c *)
Definition lambda := val_lambda typ_top (trm_path (p_sel (avar_b 0) (c :: nil))).

(* ν(z: {d: ⊤}) {d = z.d} *)
Definition zObj :=
  val_new (typ_rcd (dec_trm d typ_top))
          (defs_cons defs_nil
                     (def_trm d (trm_path (p_sel (avar_b 0) (d :: nil))))).

(* ν(y: {c: ⊤})
        {c = λ(z: ⊤)y.c} *)
Definition yObj :=
  val_new (typ_rcd (dec_trm c typ_top))
          (defs_cons defs_nil
                     (def_trm c (trm_val lambda))).

(* ν(x: {a: ⊤}    ∧ {b: ⊤})
        {a = x.b} ∧ {b = y.c} *)
Definition xObj :=
  val_new (typ_and
             (typ_rcd (dec_trm a typ_top))
             (typ_rcd (dec_trm b typ_top)))
          (defs_cons (defs_cons defs_nil
             (def_trm b (trm_path (p_sel (avar_f y) (c :: nil)))))
             (def_trm a (trm_path (p_sel (avar_b 0) (b :: nil))))).

(* {y = yObj, x = xObj} *)
Definition s := (y ~ yObj & x ~ xObj).

(* ∃ ps, s ∋ (x.a, λ(x: ⊤)y.c) *)
Lemma test_lookup_x:
  s ∋ ((pvar x) • a, open_val y lambda) // nil.
Proof.
  simpl. rewrite proj_rewrite.
  apply* lookup_path; unfold s.
  - econstructor. apply* lookup_var. apply binds_push_eq.
  - unfold defs_has. simpl. repeat case_if. eauto.
  - rewrite proj_rewrite. apply* lookup_path.
    * econstructor. apply* lookup_var. apply binds_push_eq.
    * unfold defs_has. simpl. repeat case_if*. inversions C. false* Hab.
    * intro. inversion H. inversions H0. apply Hxy. subst*. inversion H0.
    * assert (p_sel (avar_f y) (c :: nil) = (pvar y) • c) as Heq by auto. rewrite Heq.
      apply* lookup_val.
      econstructor. apply* lookup_var. apply binds_push_neq. apply binds_single_eq. apply Hxy.
      unfold defs_has. simpl. repeat case_if. unfold lambda, open_val. simpl. case_if*.
Qed.

Definition s2 := z ~ zObj.

Lemma test_lookup_z: forall ps v,
  s2 ∋ (p_sel (avar_f z) (d :: nil), v) // ps -> False.
Proof.
  introv H.
  dependent induction H; assert (s2 ∋ (pvar z, zObj) // nil) as Hb by (apply* lookup_var; apply* binds_single_eq).
  - unfolds sel_fields. destruct p. inversions x.
    inversions H. unfolds zObj.
    lets Hl: (lookup_func Hb H1). inversions Hl. unfolds defs_has. simpls. repeat case_if.
  - inversions H. unfolds sel_fields. destruct p. inversions x. simpls.
    lets Hl: (lookup_func H3 Hb). inversions Hl. inversions H0. repeat case_if. inversions H4. eauto.
Qed.
