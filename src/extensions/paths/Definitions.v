Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter trm_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive pathmode: Set := strong | gen.

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_path : path -> typ_label -> typ (* x.a1.a2. ... .an.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
  | typ_sngl : path -> typ (* p.type *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> pathmode -> typ -> dec (* {a: T} or {a:! T} *)
with path : Set :=
  | p_var : avar -> path
  | p_sel : path -> trm_label -> path.

Notation "'{' a '[' m ']' T '}'" := (dec_trm a m T).
Notation "'{' A '>:' S '<:' T '}'" := (dec_typ A S T) (S at level 58).

Inductive trm : Set :=
  | trm_val  : val -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
  | trm_path : path -> trm
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env val.

(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm a _ _ => label_trm a
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.
Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

(* ###################################################################### *)
(** ** Opening *)

(** Variable opening replaces in some syntax a bound variable with dangling index (k)
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_path (k: nat) (u: var) (p: path): path :=
  match p with
  | p_var x   => p_var (open_rec_avar k u x)
  | p_sel q m => p_sel (open_rec_path k u q) m
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_path p L   => typ_path (open_rec_path k u p) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  | typ_sngl p     => typ_sngl (open_rec_path k u p)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | { L >: T <: U } => { L >: open_rec_typ k u T <: open_rec_typ k u U }
  | { a [m] T } => { a [m] open_rec_typ k u T }
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_path p     => trm_path (open_rec_path k u p)
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.
Definition open_path u p := open_rec_path  0 u p.

Notation "t '|^' x" := (open_trm x t) (at level 35).
Notation "T '||^' x" := (open_typ x T) (at level 35).
Notation "ds '|||^' x" := (open_defs x ds) (at level 35).

(** Path oopening replaces in some syntax a bound variable with dangling index (k)
   by a path p. *)

Definition open_rec_avar_p (k: nat) (u: path) (a: avar) : path :=
  match a with
  | avar_b i => If k = i then u else p_var (avar_b i)
  | avar_f x => p_var (avar_f x)
  end.

Fixpoint open_rec_path_p (k: nat) (u: path) (p: path): path :=
  match p with
  | p_var x   => open_rec_avar_p k u x
  | p_sel q m => p_sel (open_rec_path_p k u q) m
  end.

Fixpoint open_rec_typ_p (k: nat) (u: path) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec_p k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ_p k u T1) (open_rec_typ_p k u T2)
  | typ_path p L   => typ_path (open_rec_path_p k u p) L
  | typ_bnd T      => typ_bnd (open_rec_typ_p (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ_p k u T1) (open_rec_typ_p (S k) u T2)
  | typ_sngl p     => typ_sngl (open_rec_path_p k u p)
  end
with open_rec_dec_p (k: nat) (u: path) (D: dec): dec :=
  match D with
  | { L >: T <: U } => { L >: open_rec_typ_p k u T <: open_rec_typ_p k u U }
  | { a [m] T} => { a [m] open_rec_typ_p k u T }
  end.

Definition open_avar_p u a := open_rec_avar_p  0 u a.
Definition open_typ_p  u t := open_rec_typ_p   0 u t.
Definition open_dec_p  u D := open_rec_dec_p   0 u D.
Definition open_path_p u p := open_rec_path_p  0 u p.


(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_path (p: path) : vars :=
  match p with
  | p_var x   => fv_avar x
  | p_sel q L => fv_path q
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => fv_dec D
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_path p L   => fv_path p
  | typ_bnd T      => fv_typ T
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  | typ_sngl p     => fv_path p
  end
with fv_dec (D: dec) : vars :=
  match D with
  | { L >: T <: U } => (fv_typ T) \u (fv_typ U)
  | { a [m] T } => fv_typ T
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_val v        => (fv_val v)
  | trm_path p       => (fv_path p)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv_typ T)
  | def_trm _ t     => (fv_trm t)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec { A >: T <: T }
| rd_trm : forall a m T, record_dec { a [m] T }.

Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l}).

Definition record_type T := exists ls, record_typ T ls.

(* Definition (Inert types)

A type is inert if it of the form
  all(x: S)T
  rec(x: T), where T is a record type
 *)

Inductive inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (typ_all S T) (* all(x: S)T *)
  | inert_typ_bnd : forall T,
      (* a record type is ands of record decs *)
      record_type T ->
      inert_typ (typ_bnd T). (* rec(x:T) *)

(* Definition (Inert context)

A context is inert if it is of the form
  {}
  G, x : T where G is a inert context and T is a inert type *)

Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_all : forall pre x T,
      inert pre ->
      inert_typ T ->
      x # pre ->
      inert (pre & x ~ T).

(* ###################################################################### *)
(** ** Operational Semantics *)

Reserved Notation "t1 '/' st1 '⇒' t2 '/' st2" (at level 40, t2 at level 39).

Inductive red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x a s t T ds,
    binds x (val_new T ds) s ->
    defs_has (ds |||^ x) (def_trm a t) ->
    trm_path (p_sel (p_var (avar_f x)) a) / s ⇒ t / s
| red_path : forall p a b s,
    trm_path (p_sel (p_sel p a) b) / s ⇒
             trm_let (trm_path (p_sel p a)) (trm_path (p_sel (p_var (avar_b 0)) b)) / s
| red_app : forall x y s T t,
    binds x (val_lambda T t) s ->
    trm_app (avar_f x) (avar_f y) / s ⇒ t |^ y / s
| red_let : forall v t s x,
    x # s ->
    trm_let (trm_val v) t / s ⇒ t |^ x / s & x ~ v
| red_let_var : forall t s x,
    trm_let (trm_path (p_var (avar_f x))) t / s ⇒ t |^ x / s
| red_let_tgt : forall t u s t' s',
    t / s ⇒ t' / s' ->
    trm_let t u / s ⇒ trm_let t' u / s'
where "t1 '/' st1 '⇒' t2 '/' st2" := (red t1 st1 t2 st2).

(* ###################################################################### *)
(** ** Typing *)

(* is a type inert or a singleton type? *)
Inductive inert_sngl: typ -> Prop :=
| is_inert: forall T, inert_typ T -> inert_sngl T
| is_sngl: forall p, inert_sngl (typ_sngl p).

Reserved Notation "G '|-' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '|-' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '|-\||/' p ':' T" (at level 40, p at level 59).
Reserved Notation "G '&&' z '~' T '|-' d ':' D" (at level 39, z at level 26, T at level 39, d at level 59).
Reserved Notation "G '&&' z '~' T '|-' ds '::' U" (at level 39, z at level 26, T at level 39, ds at level 59).

Inductive ty_trm : ctx -> trm -> typ -> Prop :=
| ty_var : forall G x T,
    binds x T G ->
    G |- trm_path (p_var (avar_f x)) : T
| ty_all_intro : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T |- t |^ x : U ||^ x) ->
    G |- trm_val (val_lambda T t) : typ_all T U
| ty_all_elim : forall G x y S T,
    G |- trm_path (p_var (avar_f x)) : typ_all S T ->
    G |- trm_path (p_var (avar_f y)) : S ->
    G |- trm_app (avar_f x) (avar_f y) : T ||^ y
| ty_new_intro : forall L G T ds,
    (forall x, x \notin L ->
      G && x ~ T ||^ x |- ds |||^ x :: T ||^ x) ->
    G |- trm_val (val_new T ds) : typ_bnd T
| ty_fld_elim : forall G p a T,
    G |- trm_path p : typ_rcd { a [gen] T } ->
    G |- trm_path (p_sel p a) : T
| ty_let : forall L G t u T U,
    G |- t : T ->
    (forall x, x \notin L ->
      G & x ~ T |- u |^ x : U) ->
    G |- trm_let t u : U
| ty_rec_intro : forall G x T,
    G |- trm_path (p_var (avar_f x)) : T ||^ x ->
    G |- trm_path (p_var (avar_f x)) : typ_bnd T
| ty_rec_elim : forall G x T,
    G |- trm_path (p_var (avar_f x)) : typ_bnd T ->
    G |- trm_path (p_var (avar_f x)) : open_typ x T
| ty_and_intro : forall G x T U,
    G |- trm_path (p_var (avar_f x)) : T ->
    G |- trm_path (p_var (avar_f x)) : U ->
    G |- trm_path (p_var (avar_f x)) : typ_and T U
| ty_sngl_intro : forall G x T,
    G |- trm_path (p_var (avar_f x)): T ->
    G |- trm_path (p_var (avar_f x)) : typ_sngl (p_var (avar_f x))
| ty_sub : forall G t T U,
    G |- t : T ->
    G |- T <: U ->
    G |- t : U
where "G '|-' t ':' T" := (ty_trm G t T)

with ty_path : ctx -> path -> typ -> Prop :=
| ty_p_intro: forall G x T,
    G |- trm_path (p_var (avar_f x)): T ->
    G |-\||/ p_var (avar_f x): T
| ty_p_rec_elim : forall G p T,
    G |-\||/ p : typ_bnd T ->
    G |-\||/ p : open_typ_p p T
| ty_p_and_elim1 : forall G p T U,
    G |-\||/ p: typ_and T U ->
    G |-\||/ p: T
| ty_p_and_elim_2 : forall G p T U,
    G |-\||/ p: typ_and T U ->
    G |-\||/ p: U
| ty_p_fld_elim : forall G p a T,
    G |-\||/ p: typ_rcd {a [strong] T} ->
    inert_sngl T ->
    G |-\||/ p_sel p a : T
| ty_p_sub : forall G p T U,
    G |-\||/ p: T ->
    G |- T <: U ->
    G |-\||/ p: U
where "G '|-\||/' p ':' T" := (ty_path G p T)

with ty_def : ctx -> var -> typ -> def -> dec -> Prop := (* Γ; z: U |- d: T U *)
| ty_def_typ : forall z G A T U,
    G && z ~ U |- def_typ A T : { A >: T <: T }
| ty_def_trm : forall z G a t T U,
    G & z ~ U |- t : T ->
    G && z ~ U |- def_trm a t : { a [gen] T }
| ty_def_path : forall z G a p U T,
    G |-\||/ p : T ->
    G && z ~ U |- def_trm a (trm_path p) : { a [strong] T }
| ty_def_val : forall G z U v T a,
    G & z ~ U |- trm_val v : T ->
    G && z ~ U |- def_trm a (trm_val v) : { a [strong] T }
where "G '&&' z '~' T '|-' d ':' D" := (ty_def G z T d D)

with ty_defs : ctx -> var -> typ -> defs -> typ -> Prop :=
| ty_defs_one : forall z G d D U,
    G && z ~ U |- d : D ->
    G && z ~ U |- defs_cons defs_nil d :: typ_rcd D
| ty_defs_cons : forall G ds d z T U D,
    G && z ~ U |- ds :: T ->
    G && z ~ U |- d : D ->
    defs_hasnt ds (label_of_def d) ->
    G && z ~ U |- defs_cons ds d :: typ_and T (typ_rcd D)
where "G '&&' z '~' T '|-' ds '::' U" := (ty_defs G z T ds U)

with subtyp : ctx -> typ -> typ -> Prop :=
| subtyp_top: forall G T,
    G |- T <: typ_top
| subtyp_bot: forall G T,
    G |- typ_bot <: T
| subtyp_refl: forall G T,
    G |- T <: T
| subtyp_trans: forall G S T U,
    G |- S <: T ->
    G |- T <: U ->
    G |- S <: U
| subtyp_and11: forall G T U,
    G |- typ_and T U <: T
| subtyp_and12: forall G T U,
    G |- typ_and T U <: U
| subtyp_and2: forall G S T U,
    G |- S <: T ->
    G |- S <: U ->
    G |- S <: typ_and T U
| subtyp_fld: forall G a T U,
    G |- T <: U ->
    G |- typ_rcd { a [gen] T } <: typ_rcd { a [gen] U }
| subtyp_typ: forall G A S1 T1 S2 T2,
    G |- S2 <: S1 ->
    G |- T1 <: T2 ->
    G |- typ_rcd { A >: S1 <: T1 } <: typ_rcd { A >: S2 <: T2 }
| subtyp_sel2: forall G p A S T,
    G |-\||/ p : typ_rcd { A >: S <: T } ->
    G |- S <: typ_path p A
| subtyp_sel1: forall G p A S T,
    G |-\||/ p : typ_rcd { A >: S <: T } ->
    G |- typ_path p A <: T
| subtyp_sngl_sel1: forall G p q A S U,
    G |-\||/ p: typ_sngl q ->
    G |- trm_path q: typ_rcd { A >: S <: U } ->
    G |- typ_path p A <: typ_path q A
| subtyp_sngl_sel2: forall G p q A S U,
    G |-\||/ p: typ_sngl q ->
    G |- trm_path q: typ_rcd { A >: S <: U } ->
    G |- typ_path q A <: typ_path p A
| subtyp_all: forall L G S1 T1 S2 T2,
    G |- S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 |- T1 ||^ x <: T2 ||^ x) ->
    G |- typ_all S1 T1 <: typ_all S2 T2
| subtyp_path: forall G a T,
    G |- typ_rcd { a [strong] T } <: typ_rcd { a [gen] T }
where "G '|-' T '<:' U" := (subtyp G T U).

Reserved Notation "G '|-!' t ':' T" (at level 40, t at level 59).

Inductive ty_trm_p : ctx -> trm -> typ -> Prop :=
| ty_var_p : forall G x T,
    binds x T G ->
    G |-! trm_path (p_var (avar_f x)) : T
| ty_all_intro_p : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T |- t |^ x : U ||^ x) ->
    G |-! trm_val (val_lambda T t) : typ_all T U
| ty_new_intro_p : forall L G T ds,
    (forall x, x \notin L ->
      G && x ~ T ||^ x |- ds |||^ x :: T ||^ x) ->
    G |-! trm_val (val_new T ds) : typ_bnd T
| ty_rec_elim_p : forall G p T,
    G |-! trm_path p : typ_bnd T ->
    G |-! trm_path p : open_typ_p p T
| ty_and1_p : forall G p T U,
    G |-! trm_path p : typ_and T U ->
    G |-! trm_path p : T
| ty_and2_p : forall G p T U,
    G |-! trm_path p : typ_and T U ->
    G |-! trm_path p : U
| ty_fld_elim_p : forall G p a T,
    G |-! trm_path p: typ_rcd {a [strong] T} ->
    inert_sngl T ->
    G |-! trm_path (p_sel p a): T
where "G '|-!' t ':' T" := (ty_trm_p G t T).

Reserved Notation "G '|-#' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '|-#' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '|-#\||/' p ':' T" (at level 40, p at level 59).

Inductive ty_trm_t : ctx -> trm -> typ -> Prop :=
| ty_var_t : forall G x T,
    binds x T G ->
    G |-# trm_path (p_var (avar_f x)) : T
| ty_all_intro_t : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T |- t |^ x : U ||^ x) ->
    G |-# trm_val (val_lambda T t) : typ_all T U
| ty_all_elim_t : forall G x z S T,
    G |-# trm_path (p_var (avar_f x)) : typ_all S T ->
    G |-# trm_path (p_var (avar_f z)) : S ->
    G |-# trm_app (avar_f x) (avar_f z) : T ||^ z
| ty_new_intro_t : forall L G T ds,
    (forall x, x \notin L ->
      G && x ~ T ||^ x |- ds |||^ x :: T ||^ x) ->
    G |-# trm_val (val_new T ds) : typ_bnd T
| ty_fld_elim_t : forall G p a T,
    G |-# trm_path p : typ_rcd { a [gen] T } ->
    G |-# trm_path (p_sel p a) : T
| ty_let_t : forall L G t u T U,
    G |-# t : T ->
    (forall x, x \notin L ->
      G & x ~ T |- u |^ x : U) ->
    G |-# trm_let t u : U
| ty_rec_intro_t : forall G x T,
    G |-# trm_path (p_var (avar_f x)) : T ||^ x ->
    G |-# trm_path (p_var (avar_f x)) : typ_bnd T
| ty_rec_elim_t : forall G x T,
    G |-# trm_path (p_var (avar_f x)) : typ_bnd T ->
    G |-# trm_path (p_var (avar_f x)) : open_typ x T
| ty_and_intro_t : forall G x T U,
    G |-# trm_path (p_var (avar_f x)) : T ->
    G |-# trm_path (p_var (avar_f x)) : U ->
    G |-# trm_path (p_var (avar_f x)) : typ_and T U
| ty_sngl_intro_t : forall G x T,
    G |-# trm_path (p_var (avar_f x)): T ->
    G |-# trm_path (p_var (avar_f x)) : typ_sngl (p_var (avar_f x))
| ty_sub_t : forall G t T U,
    G |-# t : T ->
    G |-# T <: U ->
    G |-# t : U
where "G '|-#' t ':' T" := (ty_trm_t G t T)

with ty_path_t : ctx -> path -> typ -> Prop :=
| ty_p_intro_t: forall G x T,
    G |-# trm_path (p_var (avar_f x)): T ->
    G |-#\||/ p_var (avar_f x) : T
| ty_p_rec_elim_t : forall G p T,
    G |-#\||/ p : typ_bnd T ->
    G |-#\||/ p : open_typ_p p T
| ty_p_and_elim1_t : forall G p T U,
    G |-#\||/ p: typ_and T U ->
    G |-#\||/ p: T
| ty_p_and_elim_2_t : forall G p T U,
    G |-#\||/ p: typ_and T U ->
    G |-#\||/ p: U
| ty_p_fld_elim_t : forall G p a T,
    G |-#\||/ p: typ_rcd {a [strong] T} ->
    inert_sngl T ->
    G |-#\||/ p_sel p a : T
| ty_p_sub_t : forall G p T U,
    G |-#\||/ p: T ->
    G |-# T <: U ->
    G |-#\||/ p: U
where "G '|-#\||/' p ':' T" := (ty_path_t G p T)

with subtyp_t : ctx -> typ -> typ -> Prop :=
| subtyp_top_t: forall G T,
    G |-# T <: typ_top
| subtyp_bot_t: forall G T,
    G |-# typ_bot <: T
| subtyp_refl_t: forall G T,
    G |-# T <: T
| subtyp_trans_t: forall G S T U,
    G |-# S <: T ->
    G |-# T <: U ->
    G |-# S <: U
| subtyp_and11_t: forall G T U,
    G |-# typ_and T U <: T
| subtyp_and12_t: forall G T U,
    G |-# typ_and T U <: U
| subtyp_and2_t: forall G S T U,
    G |-# S <: T ->
    G |-# S <: U ->
    G |-# S <: typ_and T U
| subtyp_fld_t: forall G a T U,
    G |-# T <: U ->
    G |-# typ_rcd { a [gen] T } <: typ_rcd { a [gen] U }
| subtyp_typ_t: forall G A S1 T1 S2 T2,
    G |-# S2 <: S1 ->
    G |-# T1 <: T2 ->
    G |-# typ_rcd { A >: S1 <: T1 } <: typ_rcd { A >: S2 <: T2 }
| subtyp_sel2_t: forall G p A T,
    G |-! trm_path p : typ_rcd { A >: T <: T } ->
    G |-# T <: typ_path p A
| subtyp_sel1_t: forall G p A T,
    G |-! trm_path p : typ_rcd { A >: T <: T } ->
    G |-# typ_path p A <: T
| subtyp_all_t: forall L G S1 T1 S2 T2,
    G |-# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 |- T1 ||^ x <: T2 ||^ x) ->
    G |-# typ_all S1 T1 <: typ_all S2 T2
| subtyp_sngl_sel1_t: forall G p q A S U,
    G |-! trm_path p: typ_sngl q ->
    G |-# trm_path q: typ_rcd { A >: S <: U } ->
    G |-# typ_path p A <: typ_path q A
| subtyp_sngl_sel2_t: forall G p q A S U,
    G |-! trm_path p: typ_sngl q ->
    G |-# trm_path q: typ_rcd { A >: S <: U } ->
    G |-# typ_path q A <: typ_path p A
| subtyp_path_t: forall G a T,
    G |-# typ_rcd { a [strong] T } <: typ_rcd { a [gen] T }
where "G '|-#' T '<:' U" := (subtyp_t G T U).

Reserved Notation "G '|-##' p ':' T" (at level 40, p at level 59).

(* Invertible typing *)

Inductive ty_path_inv : ctx -> path -> typ -> Prop :=
  (* Precise typing *)
| ty_path_i : forall G p T,
    G |-! trm_path p : T ->
    G |-## p : T
| ty_sngl_i : forall G p T,
    G |-## p: T ->
    G |-## p : typ_sngl p
  (* General term member subtyping *)
| subtyp_fld_i : forall G p a T T',
    G |-## p : typ_rcd { a [gen] T } ->
    G |-# T <: T' ->
    G |-## p : typ_rcd { a [gen] T' }
  (* Strong term member subtyping *)
| subtyp_path_i : forall G p a T,
    G |-## p : typ_rcd { a [strong] T } ->
    G |-## p : typ_rcd { a [gen] T }
  (* Type member subtyping *)
| subtyp_typ_i : forall G p A T T' U' U,
    G |-## p : typ_rcd { A >: T <: U } ->
    G |-# T' <: T ->
    G |-# U <: U' ->
    G |-## p : typ_rcd { A >: T' <: U' }
  (* Recursive Types *)
| ty_rec_intro_i : forall G x S,
    G |-## (p_var (avar_f x)) : S ||^ x ->
    G |-## (p_var (avar_f x)) : typ_bnd S
  (* Forall *)
| subtyp_all_i : forall L G p S T S' T',
    G |-## p : typ_all S T ->
    G |-# S' <: S ->
    (forall y, y \notin L ->
      G & y ~ S' |- T ||^ y <: T' ||^ y) ->
    G |-## p : typ_all S' T'
  (* And *)
| ty_and_intro_i : forall G p S T,
    G |-## p : S ->
    G |-## p : T ->
    G |-## p : typ_and S T
  (* Tight Selection *)
| subtyp_sel_i : forall G p q A S,
    G |-## p : S ->
    G |-! trm_path q : typ_rcd { A >: S <: S } ->
    G |-## p : typ_path q A
  (* Singleton type selection *)
| subtyp_sngl_i: forall G p q r A,
    G |-! trm_path p: typ_sngl r ->
    p <> r ->
    G |-## q: typ_path r A ->
    G |-## q: typ_path p A
(* Top *)
| ty_top_i : forall G p T,
    G |-## p : T ->
    G |-## p : typ_top
where "G '|-##' p ':' T" := (ty_path_inv G p T).

Reserved Notation "G '|-##v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_inv : ctx -> val -> typ -> Prop :=
  (* Precise typing *)
| ty_val_i : forall G v T,
    G |-! trm_val v : T ->
    G |-##v v : T
  (* Forall *)
| subtyp_all_v : forall L G v S T S' T',
    G |-##v v : typ_all S T ->
    G |-# S' <: S ->
    (forall y, y \notin L ->
      G & y ~ S' |- T ||^ y <: T' ||^ y) ->
    G |-##v v : typ_all S' T'
  (* Tight Selection *)
| subtyp_path_v : forall G v p A S,
    G |-##v v : S ->
    G |-! trm_path p : typ_rcd (dec_typ A S S) ->
    G |-##v v : typ_path p A
  (* Singleton types *)
| subtyp_sngl_v : forall G v r A p,
    G |-##v v: typ_path r A ->
    G |-! trm_path p : typ_sngl r ->
    G |-##v v: typ_path p A
  (* Intersection introduction *)
| ty_and_intro_v : forall G v T U,
    G |-##v v : T ->
    G |-##v v : U ->
    G |-##v v : typ_and T U
  (* Top *)
| ty_top_v : forall G v T,
    G |-##v v : T ->
    G |-##v v : typ_top
where "G '|-##v' v ':' T" := (ty_val_inv G v T).

Reserved Notation "G '~~' s" (at level 40).

Inductive wf_sto: ctx -> sto -> Prop :=
| wf_sto_empty: empty ~~ empty
| wf_sto_push: forall G s x T v,
    G ~~ s ->
    x # G ->
    x # s ->
    G |- trm_val v : T ->
    G & x ~ T ~~ s & x ~ v
where "G '~~' s" := (wf_sto G s).

(* ###################################################################### *)
(* ###################################################################### *)

(** * Infrastructure *)


(* ###################################################################### *)
(** ** Induction principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop
with   path_mut := Induction for path Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut, path_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_path_mut   := Induction for ty_path   Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_path_mut, ty_def_mut, ty_defs_mut.

Scheme tds_ty_trm_mut  := Induction for ty_trm    Sort Prop
with   tds_ty_def_mut  := Induction for ty_def    Sort Prop
with   tds_ty_defs_mut := Induction for ty_defs   Sort Prop
with   tds_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme tds_mutind from tds_ty_trm_mut, tds_ty_def_mut, tds_ty_defs_mut, tds_subtyp.

Scheme ts_ty_trm_mut  := Induction for ty_trm    Sort Prop
with   ts_path        := Induction for ty_path   Sort Prop
with   ts_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_path, ts_subtyp.

Scheme ts_ty_trm_mut_ts  := Induction for ty_trm_t    Sort Prop
with   ts_path_ts        := Induction for ty_path_t   Sort Prop
with   ts_subtyp_ts      := Induction for subtyp_t    Sort Prop.
Combined Scheme ts_mutind_ts from ts_ty_trm_mut_ts, ts_path_ts, ts_subtyp_ts.

Scheme ts_ty_trm_mut_t  := Induction for ty_trm_t    Sort Prop
with   ts_path_t        := Induction for ty_path_t   Sort Prop.
Combined Scheme ts_mutind_t from ts_ty_trm_mut_t, ts_path_t.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_path_mut   := Induction for ty_path   Sort Prop
with   rules_def_mut    := Induction for ty_def    Sort Prop
with   rules_defs_mut   := Induction for ty_defs   Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_path_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sto       => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  let K := gather_vars_with (fun x : path      => fv_path  x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(*Ltac in_empty_contradiction :=
  solve [match goal with
  | H: _ \in \{} |- _ => rewrite in_empty in H; exfalso; exact H
end].

Ltac eq_specialize :=
  repeat match goal with
  | H:                 _ = _ -> _ |- _ => specialize (H         eq_refl)
  | H: forall _      , _ = _ -> _ |- _ => specialize (H _       eq_refl)
  | H: forall _ _    , _ = _ -> _ |- _ => specialize (H _ _     eq_refl)
  | H: forall _ _ _  , _ = _ -> _ |- _ => specialize (H _ _ _   eq_refl)
  | H: forall _ _ _ _, _ = _ -> _ |- _ => specialize (H _ _ _ _ eq_refl)
  end.

Ltac crush := eq_specialize; eauto.*)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors
     ty_trm ty_def ty_defs subtyp ty_trm_t subtyp_t ty_trm_p
     ty_path ty_path_t
     ty_path_inv ty_val_inv inert_sngl inert_typ inert
     wf_sto record_has.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.
