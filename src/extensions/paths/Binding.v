(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Definitions.

Close Scope string_scope.

Ltac simpl_dot :=
  match goal with
  | [ H: ?p • _ = p_sel _ _ |- _ ] =>
    unfold sel_field in H; destruct p; inversions H
  | [ H: _ • _ = pvar _ |- _ ] =>
    unfold pvar in H; simpl_dot
  | [ H: pvar _ = _ • _ |- _ ] =>
    symmetry in H; simpl_dot
  | [ H: p_sel _ _ = _ • _ |- _ ] =>
    symmetry in H; simpl_dot
  | [ H: _ • _ = _ |- _ ] =>
    unfold sel_field in H;
    match goal with
    | [ H: match ?p1 with
           | p_sel _ _ => _
           end = match ?p2 with
                 | p_sel _ _ => _
                 end |- _ ] =>
      destruct p1; destruct p2; inversions H
    end
  | [ H: ?p •• _ = p_sel _ _ |- _ ] =>
    unfold sel_fields in H; destruct p; inversions H
  | [ H: _ •• _ = pvar _ |- _ ] =>
    unfold pvar in H; simpl_dot
  | [ H: pvar _ = _ •• _ |- _ ] =>
    symmetry in H; simpl_dot
  | [ H: p_sel _ _ = _ •• _ |- _ ] =>
    symmetry in H; simpl_dot
  | [ H: _ •• _ = _ |- _ ] =>
    unfold sel_fields in H;
    match goal with
    | [ H: match ?p1 with
           | p_sel _ _ => _
           end = match ?p2 with
                 | p_sel _ _ => _
                 end |- _ ] =>
      destruct p1; destruct p2; inversions H
    end
  end.

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
  | ⊤        => ⊤
  | ⊥        => ⊥
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | T1 ∧ T2        => subst_typ z u T1 ∧ subst_typ z u T2
  | q ↓ L          => subst_path z u q ↓ L
  | μ T            => μ (subst_typ z u T)
  | ∀(T) U         => ∀ (subst_typ z u T) subst_typ z u U
  | {{ p }}        => {{ subst_path z u p }}
  end
with subst_dec (z: var) (u: path) (D: dec) { struct D } : dec :=
  match D with
  | {A >: T <: U} => {A >: subst_typ z u T <: subst_typ z u U}
  | {a ⦂ U}        => {a ⦂ subst_typ z u U }
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
  | ν(T) ds  => ν(subst_typ z u T) subst_defs z u ds
  | λ(T) t   => λ(subst_typ z u T) subst_trm z u t
  end
with subst_def (z: var) (u: path) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | { a := t }  => { a := subst_defrhs z u t }
  end
with subst_defs (z: var) (u: path) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end
with subst_defrhs (z: var) (u: path) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (subst_path z u p)
  | defv v => defv (subst_val z u v)
  end.

(** Substitution on the types of a typing environment: [G[u/z]]. *)
Definition subst_ctx (z: var) (u: path) (G: ctx) : ctx :=
  map (subst_typ z u) G.

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
  eapply IHHt. simpl. eauto.
  simpl_dot. eauto.
Qed.

Lemma typed_paths_named: forall G p T,
    G ⊢ trm_path p : T ->
    named_path p.
Proof.
  intros. destruct p.
  dependent induction H; eauto; unfolds named_path, pvar; try solve [repeat eexists].
  - destruct (last_field _ _ x) as [bs' Hbs]. subst. destruct p.
    specialize (IHty_trm _ _ eq_refl). destruct_all. inversions x. inversions H0. repeat eexists.
  - simpl in *.
    specialize (IHty_trm _ _ eq_refl). destruct_all. inversions H0. repeat eexists.
  - simpl_dot. specialize (IHty_trm1 _ _ eq_refl). destruct_all.
    inversions H1. eauto.
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
  f_equal. apply open_var_path_eq.
Qed.

Lemma open_var_typ_eq: forall x T,
  open_typ x T = open_typ_p (pvar x) T.
Proof.
  intros. apply open_var_typ_dec_eq.
Qed.

Hint Rewrite open_var_typ_eq open_var_path_eq.

Lemma open_var_trm_val_def_eq : forall x,
  (forall t n,
      open_rec_trm n x t = open_rec_trm_p n (pvar x) t) /\
  (forall v n,
      open_rec_val n x v = open_rec_val_p n (pvar x) v) /\
  (forall d n,
      open_rec_def n x d = open_rec_def_p n (pvar x) d) /\
  (forall ds n,
      open_rec_defs n x ds = open_rec_defs_p n (pvar x) ds) /\
  (forall drhs n,
      open_rec_defrhs n x drhs = open_rec_defrhs_p n (pvar x) drhs).
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
  eapply open_fresh_avar_injective; eauto.
Qed.

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
    f_equal; destruct_notin; eauto using open_fresh_avar_injective, open_fresh_path_injective.
Qed.

(** * Variable Substitution Lemmas *)

(** The following [subst_fresh_XYZ] lemmas state that if [x] is not free
    in a symbol [Y], then [Y[z/x] = Y]. *)

Lemma subst_fresh_var x y z :
    x <> y ->
    subst_var x z y = y.
Proof.
  intros Hn.
  unfold subst_var. case_if; auto.
Qed.

(** Fresh substitution
    - in paths *)
Lemma subst_fresh_path : forall x q p,
    x \notin fv_path p ->
    subst_path x q p = p.
Proof.
  intros. destruct p as [[n | z] bs]; simpls.
  - Case "p = (avar_b n).bs"%string.
    rewrite* app_nil_r.
  - Case "p = (avar_f z).bs"%string.
    unfold subst_var_p. apply notin_singleton in H. case_if.
    simpl. rewrite* app_nil_r.
Qed.

(** - in types, declarations *)
Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ  , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec  , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*; apply* subst_fresh_path.
Qed.

(** - in types, declarations *)
Lemma fresh_subst_typ_dec: forall x y,
  (forall T : typ  , x \notin fv_path y -> x \notin fv_typ (subst_typ  x y T)) /\
  (forall D : dec  , x \notin fv_path y -> x \notin fv_dec (subst_dec  x y D)).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*.
  - destruct p. destruct a; simpl; eauto. unfold subst_var_p.
    case_if; subst.
    + destruct y, a; simpl; eauto.
    + simpl. intros Hin. rewrite in_singleton in Hin. false*.
  - destruct p. destruct a; simpl; eauto. unfold subst_var_p.
    case_if; subst.
    + destruct y, a; simpl; eauto.
    + simpl. intros Hin. rewrite in_singleton in Hin. false*.
Qed.

Definition subst_fresh_typ x p := proj1 (subst_fresh_typ_dec x p).

(** - in terms, values, and definitions *)
Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds) /\
  (forall drhs: def_rhs, x \notin fv_defrhs drhs -> subst_defrhs x y drhs = drhs).
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
  intros. apply typ_mutind; intros; simpl; f_equal*; apply* subst_open_commut_path.
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
        inversion* Hl; subst; destruct_all; inversions H;
  unfold sel_fields; reflexivity.
  (*inversions H0. eauto. inversions H.
        try solve [inversion Hl; inversion* H0].*)
Qed.

Lemma subst_open_commut_typ_dec_p: forall x y u,
  named_path y ->
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ_p n u t)
     = open_rec_typ_p n (subst_path x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec_p n u D)
     = open_rec_dec_p n (subst_path x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*;
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
     = open_rec_defs_p n (subst_var_p x y u) (subst_defs x y ds)) /\
  (forall drhs: def_rhs, forall n: nat,
     subst_defrhs x y (open_rec_defrhs n u drhs)
     =  open_rec_defrhs_p n (subst_var_p x y u) (subst_defrhs x y drhs)).
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
     = open_rec_defs_p n (subst_path x y u) (subst_defs x y ds)) /\
  (forall drhs: def_rhs, forall n: nat,
     subst_defrhs x y (open_rec_defrhs_p n u drhs)
     = open_rec_defrhs_p n (subst_path x y u) (subst_defrhs x y drhs)).
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

(** - types *)
Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) -> named_path u ->
  open_typ_p u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr Hl. unfold open_typ. rewrite* subst_open_commut_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
  unfold subst_var_p. case_var*.
Qed.

Lemma subst_intro_defs x u ds : x \notin (fv_defs ds) -> named_path u ->
  open_defs_p u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr Hl. unfold open_defs. rewrite* subst_open_commut_defs.
  destruct (subst_fresh_trm_val_def_defs x u) as [_ [_ [_ [Q _]]]]. rewrite* (Q ds).
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

Lemma subst_label_of_dec: forall x y D,
  label_of_dec D = label_of_dec (subst_dec x y D).
Proof.
  intros. destruct* D.
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

Lemma subst_defs_hasnt_label:
  forall ds d (x : var) (y : path),
  defs_hasnt ds (label_of_def d) ->
  defs_hasnt (subst_defs x y ds) (label_of_def (subst_def x y d)).
Proof.
  intros. rewrite <- subst_label_of_def.
  apply subst_defs_hasnt. apply H.
Qed.

(** [ds = ... /\ {a = t} /\ ...]  #<br>#
    [ds = ... /\ {a = t'} /\ ...] #<br>#
    [―――――――――――――――――――――――――] #<br>#
    [t = t'] *)
Lemma defs_has_inv: forall ds a t t',
    defs_has ds {a := t} ->
    defs_has ds {a := t'} ->
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

Lemma proj_rewrite_mult: forall x bs cs,
    p_sel x (bs ++ cs) = (p_sel x cs) •• bs.
Proof. auto. Qed.

Lemma proj_rewrite': forall p a bs,
    p •• (a :: bs) = (p •• bs) • a.
Proof.
  introv. unfolds sel_fields. destruct p. simpls. auto.
Qed.

Lemma field_sel_nil: forall p,
    p •• nil = p.
Proof.
  introv. unfold sel_fields. destruct p. auto.
Qed.

Lemma field_sel_open: forall p q bs n,
    open_rec_path_p n p (q •• bs) = (open_rec_path_p n p q) •• bs.
Proof.
  introv. unfold sel_fields. destruct p, q, a, a0; simpl; try case_if; auto;
                               rewrite* app_assoc.
Qed.

Lemma open_named_path : forall p q n,
    named_path p ->
    open_rec_path_p n q p = p.
Proof.
  introv Hn. inversions Hn. destruct_all. subst. simpl. destruct q. auto.
Qed.

Hint Rewrite proj_rewrite proj_rewrite_mult proj_rewrite' field_sel_nil field_sel_open.

Lemma typing_empty_false: forall p T,
    empty ⊢ trm_path p: T -> False.
Proof.
  introv Hp. dependent induction Hp; eauto; false* binds_empty_inv.
Qed.

(** [d1 isin ds]             #<br>#
    [label(d2) \notin ds]     #<br>#
    [―――――――――――――――――――――]  #<br>#
    [label(d1) <> label(d2)]  *)
Lemma defs_has_hasnt_neq: forall ds d1 d2,
  defs_has ds d1 ->
  defs_hasnt ds (label_of_def d2) ->
  label_of_def d1 <> label_of_def d2.
Proof.
  introv Hhas Hhasnt.
  unfold defs_has in Hhas.
  unfold defs_hasnt in Hhasnt.
  induction ds.
  - simpl in Hhas. inversion Hhas.
  - simpl in Hhasnt. simpl in Hhas. case_if; case_if.
    + inversions Hhas. assumption.
    + apply IHds; eauto.
Qed.

(** [G ⊢ ds :: ... /\ D /\ ...]       #<br>#
    [―――――――――――――――――――――――]       #<br>#
    [exists d, ds = ... /\ d /\ ...]       #<br>#
    [G ⊢ d: D]                      *)
Lemma record_has_ty_defs: forall z bs G T ds D,
  z; bs; G ⊢ ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ z; bs; G ⊢ d : D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    + unfold defs_has. simpl. rewrite If_l; reflexivity.
    + assumption.
  - inversion Hhas; subst.
    + destruct (IHHdefs H4) as [d' [H1 H2]].
      exists d'. split.
      * unfold defs_has. simpl. rewrite If_r. apply H1.
        apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      * assumption.
    + exists d. split.
      * unfold defs_has. simpl. rewrite If_l; reflexivity.
      * inversions* H4.
Qed.

Lemma inert_subst_mut:
  (forall D, record_dec D -> forall x p,
        record_dec (subst_dec x p D)) /\
  (forall T ls, record_typ T ls -> forall x p,
        record_typ (subst_typ x p T) ls) /\
  (forall T, inert_typ T -> forall x p,
        inert_typ (subst_typ x p T)).
Proof.
  apply rcd_mutind; intros; try solve [constructor*].
  - subst. apply rt_one. apply H. apply* subst_label_of_dec.
  - constructor*. rewrite* <- subst_label_of_dec.
  - apply* inert_typ_bnd.
Qed.

Lemma inert_subst: forall x p T,
    inert_typ T ->
    inert_typ (subst_typ x p T).
Proof.
  introv Hi. apply* inert_subst_mut.
Qed.

Lemma tight_bounds_subst_mut :
  (forall T, tight_bounds T -> forall x p, tight_bounds (subst_typ x p T)) /\
  (forall D, tight_bounds_dec D -> forall x p, tight_bounds_dec (subst_dec x p D)).
Proof.
  apply typ_mutind; intros; subst; simpls; subst; eauto. split*.
Qed.

Lemma tight_bounds_subst x p T :
  tight_bounds T -> tight_bounds (subst_typ x p T).
Proof.
  intros. apply* tight_bounds_subst_mut.
Qed.

Lemma binds_destruct: forall x {A} (v:A) (E:env A),
    binds x v E ->
    exists E1 E2, E = E1 & x ~ v & E2.
Proof.
  introv Hb. induction E using env_ind. false* binds_empty_inv.
  destruct (binds_push_inv Hb) as [[H1 H2] | [H1 H2]]; subst.
  repeat eexists. rewrite* concat_empty_r.
  specialize (IHE H2). destruct_all. subst. exists x1 (x2 & x0 ~ v0). rewrite* concat_assoc.
Qed.

Lemma open_env_rules:
  (forall G t T, G ⊢ t : T -> forall G1 G2 x S,
    G = G1 & x ~ open_typ x S & G2 ->
    ok G ->
    G1 & x ~ (μ S) & G2 ⊢ t : T) /\
  (forall z bs G d D, z; bs; G ⊢ d : D -> forall G1 G2 x S,
    G = G1 & x ~ open_typ x S & G2 ->
    ok G ->
    z; bs; G1 & x ~ (μ S) & G2 ⊢ d : D) /\
  (forall z bs G ds T, z; bs; G ⊢ ds :: T -> forall G1 G2 x S,
    G = G1 & x ~ open_typ x S & G2 ->
    ok G ->
    z; bs; G1 & x ~ (μ S) & G2 ⊢ ds :: T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 x S,
    G = G1 & x ~ open_typ x S & G2 ->
    ok G ->
    G1 & x ~ (μ S) & G2 ⊢ T <: U).
Proof.
  apply rules_mutind; intros; subst; simpl; auto;
    try solve [fresh_constructor; rewrite <- concat_assoc; (apply* H || apply* H0); rewrite* concat_assoc]; eauto.
  - Case "ty_var"%string.
    destruct (classicT (x=x0)) as [-> | Hn]; unfold tvar, pvar.
    + apply binds_middle_eq_inv in b; subst*. rewrite open_var_typ_eq.
      apply ty_rec_elim. constructor. apply* binds_middle_eq. apply* ok_middle_inv_r.
    + constructor. apply binds_subst in b; auto. apply* binds_weaken. apply* ok_middle_change.
Qed.

Lemma open_env_last_defs z bs G x T ds U :
  ok (G & x ~ open_typ x T) ->
  z ; bs ; G & x ~ open_typ x T ⊢ ds :: U ->
  z ; bs ; G & x ~ (μ T) ⊢ ds :: U.
Proof.
  intros Hok Hds. erewrite <- concat_empty_r at 1. apply* open_env_rules.
  rewrite* concat_empty_r.
Qed.

Lemma env_ok_inv {A} (G1 G2 G1' G2' : env A) x T T' :
  G1 & x ~ T & G2 = G1' & x ~ T' & G2' ->
  ok (G1' & x ~ T' & G2') ->
  G1 = G1' /\ T = T' /\ G2 = G2'.
Proof.
  gen G1' G2' T'. induction G2 using env_ind; introv Heq Hn; destruct (env_case G2') as [-> | [y [U [G2'' ->]]]];
             repeat rewrite concat_empty_r in *.
  - apply eq_push_inv in Heq; destruct_all; subst; auto.
  - rewrite concat_assoc in Heq.
    apply eq_push_inv in Heq as [-> [-> ->]].
    apply ok_middle_inv_r in Hn. simpl_dom. apply notin_union in Hn as [C _]. false* notin_same.
  - rewrite concat_assoc in Heq. apply eq_push_inv in Heq as [-> [-> <-]]. rewrite <- concat_assoc in Hn.
    apply ok_middle_inv_r in Hn. simpl_dom. apply notin_union in Hn as [C _]. false* notin_same.
  - rewrite concat_assoc in Hn. repeat rewrite concat_assoc in Heq.
    apply eq_push_inv in Heq as [-> [-> Heq]]. apply ok_concat_inv_l in Hn.
    specialize (IHG2 _ _ _ Heq Hn) as [-> [-> ->]]. auto.
Qed.

Lemma env_ok_inv' {A} (G1 G2 G1' G2' : env A) x T T' :
  G1 & x ~ T & G2 = G1' & x ~ T' & G2' ->
  ok (G1 & x ~ T & G2) ->
  G1 = G1' /\ T = T' /\ G2 = G2'.
Proof.
  intros Heq Hok. rewrite Heq in Hok. apply (env_ok_inv Heq) in Hok.
  split*.
Qed.

Lemma wt_prefix G1 x T G2 s :
  well_typed (G1 & x ~ T & G2) s ->
  exists v s1 s2, s = s1 & x ~ v & s2 /\ well_typed (G1 & x ~ T) (s1 & x ~ v).
Proof.
  intros Hwt. dependent induction Hwt.
  - false* empty_middle_inv.
  - destruct (env_case G2) as [-> | [y [U [G2' ->]]]].
    + rewrite concat_empty_r in *. apply eq_push_inv in x as [-> [-> ->]].
      repeat eexists. rewrite concat_empty_r. eauto. constructor*.
    + rewrite concat_assoc in x. apply eq_push_inv in x as [-> [-> ->]].
      specialize (IHHwt _ _ _ _ JMeq_refl) as [w [s1 [s2 [-> Hwt']]]].
      exists w s1 (s2 & y ~ v). split*. rewrite concat_assoc. auto.
Qed.
