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

Inductive path : Set :=
  | p_var : avar -> path
  | p_sel : path -> trm_label -> path.

Inductive pathmode: Set := path_strong | path_general.

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_path : path -> typ_label -> typ (* x.a1.a2. ... .an.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> pathmode -> typ -> dec (* {a: T} or {a:! T} *).

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
| dec_trm m _ _ => label_trm m
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
| rh_andl : forall T D,
  record_has (typ_and T (typ_rcd D)) D
| rh_and : forall T D D',
  record_has T D' ->
  record_has (typ_and T D) D'.

(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k)
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
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m p T => dec_trm m p (open_rec_typ k u T)
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
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_path p L   => (fv_path p)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m p T => (fv_typ T)
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

(* ###################################################################### *)
(** ** Operational Semantics *)

Inductive red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    red (trm_path (p_sel (p_var (avar_f x)) m)) s t s
| red_pvar : forall x s,
    red (trm_path (p_var (avar_f x))) s (trm_path (p_var (avar_f x))) s
| red_path : forall q m' m s,
    red (trm_path (p_sel (p_sel q m') m)) s (trm_let (trm_path (p_sel q m')) (trm_path (p_sel (p_var (avar_b 0)) m))) s
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    red (trm_app (avar_f f) (avar_f a)) s (open_trm a t) s
| red_let : forall v t s x,
    x # s ->
    red (trm_let (trm_val v) t) s (open_trm x t) (s & x ~ v)
| red_let_var : forall t s x,
    red (trm_let (trm_path (p_var (avar_f x))) t) s (open_trm x t) s
| red_let_tgt : forall t0 t s t0' s',
    red t0 s t0' s' ->
    red (trm_let t0 t) s (trm_let t0' t) s'.

Inductive eq_path : sto -> path -> var -> Prop :=
| eq_v: forall x s v,
    binds x v s ->
    eq_path s (p_var (avar_f x)) x
| eq_p: forall p x y T U ds s q a,
    eq_path s p x ->
    binds x (val_new T ds) s ->
    record_has T (dec_trm a path_strong U) ->
    defs_has (open_defs x ds) (def_trm a (trm_path q)) ->
    eq_path s q y ->
    eq_path s (p_sel p a) y.

(* ###################################################################### *)
(** ** Typing *)

Inductive tymode: Set := ty_precise | ty_general.
Inductive submode: Set := sub_tight | sub_general.

Inductive ty_trm : tymode -> ctx -> trm -> typ -> Prop :=
| ty_var : forall m1 G x T,
    binds x T G ->
    ty_trm m1 G (trm_path (p_var (avar_f x))) T
| ty_all_intro : forall L m1 G T t U,
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x t) (open_typ x U)) ->
    ty_trm m1 G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall G x z S T,
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_all S T) ->
    ty_trm ty_general G (trm_path (p_var (avar_f z)))  S ->
    ty_trm ty_general G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro : forall L m1 G T ds,
    (forall x, x \notin L ->
      ty_defs G x (open_typ x T) (open_defs x ds) (open_typ x T)) ->
    ty_trm m1 G (trm_val (val_new T ds)) (typ_bnd T)
| ty_fld_elim : forall m3 G p m T,
    ty_trm ty_general G (trm_path p) (typ_rcd (dec_trm m m3 T)) ->
    ty_trm ty_general G (trm_path (p_sel p m)) T
| ty_let : forall L G t u T U,
    ty_trm ty_general G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x u) U) ->
    ty_trm ty_general G (trm_let t u) U
| ty_rec_intro : forall G x T,
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  (open_typ x T) ->
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_bnd T)
| ty_rec_elim : forall m1 G x T,
    ty_trm m1 G (trm_path (p_var (avar_f x)))  (typ_bnd T) ->
    ty_trm m1 G (trm_path (p_var (avar_f x)))  (open_typ x T)
| ty_and_intro : forall G x T U,
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  T ->
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  U ->
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_and T U)
| ty_sub : forall m1 G t T U,
    (m1 = ty_precise -> exists x, t = trm_path (p_var (avar_f x))) ->
    ty_trm m1 G t T ->
    subtyp m1 G T U ->
    ty_trm m1 G t U

with ty_def : ctx -> var -> typ -> def -> dec -> Prop := (* Γ; z: U |= d: T U *)
| ty_def_typ : forall x G A T U,
    ty_def G x U (def_typ A T) (dec_typ A T T)
| ty_def_trm : forall x G a t T U,
    ty_trm ty_general (G & x ~ U) t T ->
    ty_def G x U (def_trm a t) (dec_trm a path_general T)
| ty_def_path : forall x G a p T U,
    ty_trm ty_general G (trm_path p) T ->
    norm G p ->
    ty_def G x U (def_trm a (trm_path p)) (dec_trm a path_strong T)
with ty_defs : ctx -> var -> typ -> defs -> typ -> Prop :=
| ty_defs_one : forall x G d D U,
    ty_def G x U d D ->
    ty_defs G x U (defs_cons defs_nil d) (typ_rcd D)
| ty_defs_cons : forall G ds d x T U D,
    ty_defs G x U ds T ->
    ty_def G x U d D ->
    defs_hasnt ds (label_of_def d) ->
    ty_defs G x U (defs_cons ds d) (typ_and T (typ_rcd D))

with norm : ctx -> path -> Prop :=
| norm_var : forall x T G,
    binds x T G ->
    norm G (p_var (avar_f x))
| norm_path : forall p T m G,
    ty_trm ty_general G (trm_path p) (typ_rcd (dec_trm m path_strong T)) ->
    norm G p ->
    norm G (p_sel p m)

with subtyp : tymode -> ctx -> typ -> typ -> Prop :=
| subtyp_top: forall G T,
    subtyp ty_general G T typ_top
| subtyp_bot: forall G T,
    subtyp ty_general G typ_bot T
| subtyp_refl: forall G T,
    subtyp ty_general G T T
| subtyp_trans: forall m1 G S T U,
    subtyp m1 G S T ->
    subtyp m1 G T U ->
    subtyp m1 G S U
| subtyp_and11: forall m1 G T U,
    subtyp m1 G (typ_and T U) T
| subtyp_and12: forall m1 G T U,
    subtyp m1 G (typ_and T U) U
| subtyp_and2: forall G S T U,
    subtyp ty_general G S T ->
    subtyp ty_general G S U ->
    subtyp ty_general G S (typ_and T U)
| subtyp_fld: forall G a T U,
    subtyp ty_general G T U ->
    subtyp ty_general G (typ_rcd (dec_trm a path_general T)) (typ_rcd (dec_trm a path_general U))
| subtyp_typ: forall G A S1 T1 S2 T2,
    subtyp ty_general G S2 S1 ->
    subtyp ty_general G T1 T2 ->
    subtyp ty_general G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2: forall G p A S T,
    ty_trm ty_general G (trm_path p)  (typ_rcd (dec_typ A S T)) ->
    norm G p ->
    subtyp ty_general G S (typ_path p A)
| subtyp_sel1: forall G p A S T,
    ty_trm ty_general G (trm_path p)  (typ_rcd (dec_typ A S T)) ->
    norm G p ->
    subtyp ty_general G (typ_path p A) T
| subtyp_all: forall L G S1 T1 S2 T2,
    subtyp ty_general G S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general (G & x ~ S2) (open_typ x T1) (open_typ x T2)) ->
    subtyp ty_general G (typ_all S1 T1) (typ_all S2 T2)
| subtyp_path: forall G a T,
    subtyp ty_general G (typ_rcd (dec_trm a path_strong T)) (typ_rcd (dec_trm a path_general T)).

Inductive wf_sto: ctx -> sto -> Prop :=
| wf_sto_empty: wf_sto empty empty
| wf_sto_push: forall G s x T v,
    wf_sto G s ->
    x # G ->
    x # s ->
    ty_trm ty_precise G (trm_val v) T ->
    wf_sto (G & x ~ T) (s & x ~ v).

Inductive ty_trm_t : tymode -> ctx -> trm -> typ -> Prop :=
| ty_var_t : forall m1 G x T,
    binds x T G ->
    ty_trm_t m1 G (trm_path (p_var (avar_f x))) T
| ty_all_intro_t : forall L m1 G T t U,
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x t) (open_typ x U)) ->
    ty_trm_t m1 G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim_t : forall G x z S T,
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_all S T) ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f z)))  S ->
    ty_trm_t ty_general G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro_t : forall L m1 G T ds,
    (forall x, x \notin L ->
      ty_defs G x (open_typ x T) (open_defs x ds) (open_typ x T)) ->
    ty_trm_t m1 G (trm_val (val_new T ds)) (typ_bnd T)
| ty_fld_elim_t : forall m3 G p m T,
    ty_trm_t ty_general G (trm_path p) (typ_rcd (dec_trm m m3 T)) ->
    ty_trm_t ty_general G (trm_path (p_sel p m)) T
| ty_let_t : forall L G t u T U,
    ty_trm_t ty_general G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x u) U) ->
    ty_trm_t ty_general G (trm_let t u) U
| ty_rec_intro_t : forall G x T,
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (open_typ x T) ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_bnd T)
| ty_rec_elim_t : forall m1 G x T,
    ty_trm_t m1 G (trm_path (p_var (avar_f x)))  (typ_bnd T) ->
    ty_trm_t m1 G (trm_path (p_var (avar_f x)))  (open_typ x T)
| ty_and_intro_t : forall G x T U,
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  T ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  U ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_and T U)
| ty_sub_t : forall m1 G t T U,
    (m1 = ty_precise -> exists x, t = trm_path (p_var (avar_f x))) ->
    ty_trm_t m1 G t T ->
    subtyp_t m1 G T U ->
    ty_trm_t m1 G t U

with subtyp_t : tymode -> ctx -> typ -> typ -> Prop :=
| subtyp_top_t: forall G T,
    subtyp_t ty_general G T typ_top
| subtyp_bot_t: forall G T,
    subtyp_t ty_general G typ_bot T
| subtyp_refl_t: forall G T,
    subtyp_t ty_general G T T
| subtyp_trans_t: forall m1 G S T U,
    subtyp_t m1 G S T ->
    subtyp_t m1 G T U ->
    subtyp_t m1 G S U
| subtyp_and11_t: forall m1 G T U,
    subtyp_t m1 G (typ_and T U) T
| subtyp_and12_t: forall m1 G T U,
    subtyp_t m1 G (typ_and T U) U
| subtyp_and2_t: forall G S T U,
    subtyp_t ty_general G S T ->
    subtyp_t ty_general G S U ->
    subtyp_t ty_general G S (typ_and T U)
| subtyp_fld_t: forall G a T U,
    subtyp_t ty_general G T U ->
    subtyp_t ty_general G (typ_rcd (dec_trm a path_general T)) (typ_rcd (dec_trm a path_general U))
| subtyp_typ_t: forall G A S1 T1 S2 T2,
    subtyp_t ty_general G S2 S1 ->
    subtyp_t ty_general G T1 T2 ->
    subtyp_t ty_general G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2_t: forall G x p A T s,
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T T)) ->
    wf_sto G s ->
    eq_path s p x ->
    subtyp_t ty_general G T (typ_path p A)
| subtyp_sel1_t: forall G x p A T s,
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T T)) ->
    wf_sto G s ->
    eq_path s p x ->
    subtyp_t ty_general G (typ_path p A) T
| subtyp_all_t: forall L G S1 T1 S2 T2,
    subtyp ty_general G S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general (G & x ~ S2) (open_typ x T1) (open_typ x T2)) ->
    subtyp_t ty_general G (typ_all S1 T1) (typ_all S2 T2)
| subtyp_path_t: forall G a T,
    subtyp_t ty_general G (typ_rcd (dec_trm a path_strong T)) (typ_rcd (dec_trm a path_general T)).
    
(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop
with   norm_mut      := Induction for norm      Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut, norm_mut.

Scheme tds_ty_trm_mut  := Induction for ty_trm    Sort Prop
with   tds_ty_def_mut  := Induction for ty_def    Sort Prop
with   tds_ty_defs_mut := Induction for ty_defs   Sort Prop
with   tds_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme tds_mutind from tds_ty_trm_mut, tds_ty_def_mut, tds_ty_defs_mut, tds_subtyp.

Scheme ts_ty_trm_mut  := Induction for ty_trm    Sort Prop
with   ts_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme ts_ty_trm_mut_t  := Induction for ty_trm_t    Sort Prop
with   ts_subtyp_t      := Induction for subtyp_t    Sort Prop.
Combined Scheme ts_mutind_t from ts_ty_trm_mut_t, ts_subtyp_t.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_def_mut    := Induction for ty_def    Sort Prop
with   rules_defs_mut   := Induction for ty_defs   Sort Prop
with   rules_norm_mut   := Induction for norm      Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_norm_mut, rules_subtyp.

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

Ltac in_empty_contradiction :=
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

Ltac crush := eq_specialize; eauto.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors
  ty_trm ty_def ty_defs subtyp ty_trm_t subtyp_t.

Hint Constructors wf_sto.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** ** Weakening *)

(* also defined for tight *)
Lemma weaken_rules:
  (forall m1 G t T, ty_trm m1 G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm m1 (G1 & G2 & G3) t T) /\
  (forall G x T d D, ty_def G x T d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ T) ->
    ty_def (G1 & G2 & G3) x T d D) /\
  (forall G x U ds T, ty_defs G x U ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ U) ->
    ty_defs (G1 & G2 & G3) x U ds T) /\
  (forall G p, norm G p -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    norm (G1 & G2 & G3) p) /\
  (forall m1 G T U, subtyp m1 G T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m1 (G1 & G2 & G3) T U).
Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; auto.
  + intros. subst.
    apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    - specialize (H z zL G1 G2 G3). apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst. apply ty_def_trm.
    rewrite <- concat_assoc. apply H; rewrite concat_assoc. reflexivity. assumption.
  + intros. subst.
    eapply norm_var. eapply binds_weaken; eassumption.
  + intros. subst.
    eapply norm_path. eapply H; eauto.
    eapply H0; auto.
  + intros. subst.
    apply_fresh subtyp_all as z.
    auto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

(* also defined for tight *)
Lemma weaken_ty_trm:  forall m1 G1 G2 t T,
    ty_trm m1 G1 t T ->
    ok (G1 & G2) ->
    ty_trm m1 (G1 & G2) t T.
Proof. 
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

(* also defined for tight *)
Lemma weaken_subtyp: forall m1 G1 G2 S U,
  subtyp m1 G1 S U ->
  ok (G1 & G2) ->
  subtyp m1 (G1 & G2) S U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_norm: forall G G' p,
  norm G p ->
  ok (G & G') ->
  norm (G & G') p.
Proof.
  introv Hn Hok.
  assert (G & G' = G & G' & empty) as EqG by (rewrite* concat_empty_r).
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity. rewrite <- EqG. assumption.
Qed.

Lemma weaken_defs: forall G1 z U ds T G2,
  ty_defs G1 z U ds T ->
  ok (G1 & G2 & z ~ U) -> 
  ty_defs (G1 & G2) z U ds T.
Proof.
  introv Hn Hok.
  assert (G1 & G2 = G1 & G2 & empty) as EqG by (rewrite* concat_empty_r).
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity. rewrite <- EqG. assumption.
Qed.

(* ###################################################################### *)
(** ** Well-formed store *)

Lemma wf_sto_to_ok_s: forall s G,
  wf_sto G s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto G s -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto G s ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) v.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
Qed.

Lemma ctx_binds_to_sto_binds_typing: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise G (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_sto_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm; eauto.
  rewrite concat_assoc.
  eapply wf_sto_to_ok_G; eauto.
Qed.

Lemma sto_binds_to_ctx_binds_raw: forall s G x v,
  wf_sto G s ->
  binds x v s ->
  exists G1 G2 T, G = G1 & (x ~ T) & G2 /\ ty_trm ty_precise G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [T0' [Eq Ty]]]].
      subst. exists G1 (G2 & x ~ T) T0'. rewrite concat_assoc. auto.
Qed.

Lemma typing_implies_bound: forall m1 G x T,
  ty_trm m1 G (trm_path (p_var (avar_f x)))  T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_path (p_var (avar_f x))) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

Lemma typing_implies_bound_t: forall m1 G x T,
  ty_trm_t m1 G (trm_path (p_var (avar_f x)))  T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_path (p_var (avar_f x)))  as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm_t; eauto];
    try solve [inversion Heqt; eapply IHty_trm_t1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

(* ###################################################################### *)
(** ** Substitution *)

Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

Fixpoint subst_path (z: var) (u: var) (p: path) : path :=
  match p with
  | p_var x   => p_var (subst_avar z u x)
  | p_sel p a => p_sel (subst_path z u p) a
  end.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_path p L   => typ_path (subst_path z u p) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L m U => dec_trm L m (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_val v        => trm_val (subst_val z u v)
  | trm_path p       => trm_path (subst_path z u p)
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

Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx := map (subst_typ z u) G.

(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_path: forall x y,
  forall p : path, x \notin fv_path p -> subst_path x y p = p.
Proof.
  intros. induction p; simpls.
  - assert (subst_avar x y a = a) as Hs. {
      apply subst_fresh_avar. assumption.
    }
    rewrite Hs. reflexivity.
  - rewrite (IHp H). reflexivity.
Qed.


Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_path.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec x y).
Definition subst_fresh_dec(x y: var) := proj2 (subst_fresh_typ_dec x y).

Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
  (apply* subst_fresh_avar || apply* subst_fresh_path || apply* subst_fresh_typ_dec).
Qed.

Definition subst_fresh_trm (x y: var) := proj41 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_val (x y: var) := proj42 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_def (x y: var) := proj43 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_defs(x y: var) := proj44 (subst_fresh_trm_val_def_defs x y).

Lemma invert_fv_ctx_types_push: forall x z T G,
  x \notin fv_ctx_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_ctx_types G).
Proof.
  introv N.
  unfold fv_ctx_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

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

Definition subst_fvar(x y z: var): var := If z = x then y else z.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a)
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

Lemma subst_open_commute_path: forall x y u,
  (forall p: path, forall n: nat,
    subst_path x y (open_rec_path n u p)
    = open_rec_path n (subst_fvar x y u) (subst_path x y p)).
Proof.
  intros. induction p.
  + unfold subst_path, open_rec_path, subst_avar, open_rec_avar, subst_fvar. destruct a.
    * repeat case_if; auto.
    * case_var*.
  + simpl; f_equal. assumption.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_path.
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_trm_val_def_defs: forall x y u,
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
  intros. apply trm_mutind; intros; simpl; f_equal*;
    (apply* subst_open_commute_avar || apply* subst_open_commute_path || apply* subst_open_commute_typ_dec).
Qed.

Lemma subst_open_commute_trm: forall x y u t,
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

Lemma subst_open_commute_defs: forall x y u ds,
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commute_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct d; simpl; reflexivity.
Qed.

Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - simpl. reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if. apply (IHds Eq).
Qed.


(* ###################################################################### *)
(** ** The substitution principle *)

Lemma subst_rules: forall y S,
  (forall m1 G t T, ty_trm m1 G t T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    m1 = ty_general ->
    ty_trm m1 (G1 & (subst_ctx x y G2)) (subst_trm x y t) (subst_typ x y T)) /\
  (forall G z T d D, ty_def G z T d D -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2 & z ~ T) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_def (G1 & (subst_ctx x y G2)) z (subst_typ x y T) (subst_def x y d) (subst_dec x y D)) /\
  (forall G z T ds U, ty_defs G z T ds U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2 & z ~ T) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_defs (G1 & (subst_ctx x y G2)) z (subst_typ x y T) (subst_defs x y ds) (subst_typ x y U)) /\
  (forall G p, norm G p -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    norm (G1 & (subst_ctx x y G2)) (subst_path x y p)) /\
  (forall m1 G T U, subtyp m1 G T U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2))  (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    m1 = ty_general ->
    subtyp m1 (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U)).
Proof.
  intros y S. apply rules_mutind; intros; subst.
  - (* ty_var *)
    simpl. case_if.
    + apply binds_middle_eq_inv in b. subst. assumption. assumption.
    + apply subst_fresh_ctx with (y:=y) in H1.
      apply binds_subst in b.
      apply ty_var. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map. assumption. assumption.
  - (* ty_all_intro *)
    simpl.
    apply_fresh ty_all_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    rewrite <- A at 3. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_all_elim *)
    simpl. rewrite subst_open_commute_typ.
    eapply ty_all_elim.
    simpl in H.
    apply H; eauto.
    apply H0; eauto.
  - (* ty_new_intro *)
    simpl.
    apply_fresh ty_new_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- A at 3. rewrite <- A at 4.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_defs.
    
    assert (subst_ctx x y G2 & z ~ subst_typ x y (open_typ z T) = subst_ctx x y (G2 & z ~ open_typ z T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    } 
    apply H; eauto.
  - (* ty_fld_elim *)
    simpl. eapply ty_fld_elim. apply H; eauto.
  - (* ty_let *)
    simpl.
    apply_fresh ty_let as z; eauto.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    apply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_rec_intro *)
    simpl. apply ty_rec_intro.
    assert (trm_path (p_var (avar_f (If x = x0 then y else x))) = subst_trm x0 y (trm_path (p_var (avar_f x))) ) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    assert (open_typ (If x = x0 then y else x) (subst_typ x0 y T) = subst_typ x0 y (open_typ x T)) as B. {
      rewrite subst_open_commute_typ. unfold subst_fvar. reflexivity.
    }
    rewrite B.
    apply H; eauto.
  - (* ty_rec_elim *)
    simpl. rewrite subst_open_commute_typ.
    apply ty_rec_elim.
    apply H; eauto.
  - (* ty_and_intro *)
    simpl.
    assert (trm_path (p_var (avar_f (If x = x0 then y else x))) = subst_trm x0 y (trm_path (p_var (avar_f x))) ) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    apply ty_and_intro; eauto.
  - (* ty_sub *)
    eapply ty_sub; eauto.
    intro Contra. inversion Contra.
  - (* ty_def_typ *)
    simpl. eapply ty_def_typ; eauto.
  - (* ty_def_trm *)
    simpl. apply ty_def_trm.
    assert (G1 & subst_ctx x0 y G2 & x ~ subst_typ x0 y U = G1 & subst_ctx x0 y (G2 & x ~ U)) as Hs. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. rewrite concat_assoc. 
      reflexivity.
    }
    rewrite Hs.
    assert (x <> x0) as Hn. {
      rewrite <- concat_assoc in H1.
      apply ok_middle_inv_r in H1. unfold not. intro Hx. subst. unfold notin in H1.
      unfold not in H1. simpl_dom.
      assert (x0 \in \{ x0} \u dom G2) as Hx. {
        rewrite in_union. left. rewrite in_singleton. reflexivity.
      }
      apply H1 in Hx. false.
    }
    apply H; auto. rewrite concat_assoc. reflexivity. rewrite concat_assoc.
    assumption.
    assert (subst_ctx x0 y (G2 & x ~ U) = (subst_ctx x0 y G2) & x ~ (subst_typ x0 y U)). {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite H0. rewrite concat_assoc. apply weaken_ty_trm.
    apply H3. 
    assert (subst_ctx x0 y G2 & x ~ subst_typ x0 y U = subst_ctx x0 y (G2 & x ~ U)) as Hsu by auto.
    rewrite <- concat_assoc. rewrite Hsu. apply ok_concat_map. rewrite <- concat_assoc in H1.
    apply ok_remove in H1. assumption.
  - (* ty_def_path *)
    simpl. apply* ty_def_path.
  - (* ty_defs_one *)
    simpl. apply* ty_defs_one.
  - (* ty_defs_cons *)
    simpl. apply* ty_defs_cons. rewrite <- subst_label_of_def. apply subst_defs_hasnt. assumption.
  - (* norm_var *)
    destruct (typing_implies_bound H2) as [U Hb].
    simpl. case_if.
    * apply* norm_var.
    * destruct (binds_concat_inv b) as [b' | [Hx  b']]; clear b. 
      + unfold subst_ctx. eapply norm_var. eauto.
      + lets Hp: (binds_push_neq_inv b' H).
        eapply norm_var. eapply binds_concat_left. eassumption.
        unfold notin. intro. unfolds subst_ctx. simpl_dom. false.
  - (* norm_path *)
    apply* norm_path. apply* H.
  - (* subtyp_top *)
    apply subtyp_top.
  - (* subtyp_bot *)
    apply subtyp_bot.
  - (* subtyp_refl *)
    apply subtyp_refl.
  - (* subtyp_trans *)
    eapply subtyp_trans; eauto.
  - (* subtyp_and11 *)
    eapply subtyp_and11; eauto.
  - (* subtyp_and12 *)
    eapply subtyp_and12; eauto.
  - (* subtyp_and2 *)
    eapply subtyp_and2; eauto.
  - (* subtyp_fld *)
    eapply subtyp_fld; eauto.
  - (* subtyp_typ *)
    eapply subtyp_typ; eauto.
  - (* subtyp_sel2 *)
    eapply subtyp_sel2; eauto.
    eapply H; eauto.
  - (* subtyp_sel1 *)
    eapply subtyp_sel1; eauto.
    eapply H; eauto.
  - (* subtyp_all *)
    simpl. apply_fresh subtyp_all as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- A at 3.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y S2 = subst_ctx x y (G2 & z ~ S2)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - constructor.
Qed.

Lemma subst_ty_trm: forall y S G x t T,
    ty_trm ty_general (G & x ~ S) t T -> 
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    ty_trm ty_general G (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_trm ty_general G (subst_trm x y t) (subst_typ x y T).
Proof.
  intros.
  apply (proj51 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H.
  unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  assumption.
  unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption.
  reflexivity.
Qed.

Lemma subst_ty_defs: forall y S G x ds z U T,
    ty_defs (G & x ~ S) z U ds T ->
    ok (G & x ~ S & z ~ U) ->
    x \notin fv_ctx_types G ->
    ty_trm ty_general G (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_defs G z (subst_typ x y U) (subst_defs x y ds) (subst_typ x y T).
Proof.
  intros.
  apply (proj53 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H.
  unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  assumption.
  unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption. 
Qed.

(* ###################################################################### *)
(** Renaming *)

Lemma ok_extend: forall E F x (v: typ),
  ok (E & F) ->
  x # (E & F) ->
  ok (E & x ~ v & F).
Proof.
  introv Hok Hn.
  induction F using env_ind; introv;
  autorewrite with rew_env_map; rew_env_concat.
  rewrite concat_empty_r in *. apply* ok_push.
  rewrite concat_assoc in *.
  apply ok_push; auto.
  intro. clear IHF. simpl_dom.
  rewrite in_union in H. destruct H. rewrite in_union in H. destruct H.
  - destruct (ok_push_inv Hok) as [_ Hnef].
    simpl_dom. rewrite notin_union in Hnef. destruct Hnef as [Hne _]. auto.
  - rewrite in_singleton in H. subst.
    rewrite notin_union in Hn. destruct Hn. apply notin_same in H. auto.
  - destruct (ok_push_inv Hok) as [_ Hnef].
    simpl_dom. rewrite notin_union in Hnef. destruct Hnef as [_ Hnf]. auto.
Qed.

Lemma fv_typ_ctx: forall x y T G,
  binds x T G ->
  y \in fv_typ T ->
  y \in fv_ctx_types G.
Proof.
  intros. induction G using env_ind.
  - false* binds_empty_inv.
  - destruct (binds_push_inv H) as [[Hx0 Hv] | [Hn Hb]];
    unfolds fv_ctx_types; unfolds fv_in_values;
    rewrite values_def, concat_def, single_def in *; simpl; subst; rewrite* in_union.
Qed.

Definition rename_var (x y z : var)  := If z = x then y else z.

Definition rename_ctx x y G := subst_ctx x y (map_keys (rename_var x y) G).


Lemma binds_destruct: forall {A} x (v:A) E,
  binds x v E ->
  exists E' E'', E = E' & x ~ v & E''.
Proof.
  introv Hb. induction E using env_ind. false* binds_empty_inv.
  destruct (binds_push_inv Hb) as [[Hx HT] | [Hn Hbx]]; subst.
  - exists E (@empty A). rewrite concat_empty_r. reflexivity.
  - apply binds_push_neq_inv in Hb. destruct (IHE Hb) as [E' [E'' HE]]. subst.
    exists E' (E'' & x0 ~ v0). rewrite concat_assoc. reflexivity. assumption.
Qed.

Lemma map_keys_notin: forall x y (G:ctx),
  x # G ->
  map_keys (rename_var x y) G = G.
Proof.
  intros. induction G using env_ind. rewrite map_keys_empty. reflexivity.
  rewrite map_keys_push. rewrite* IHG. assert (x <> x0) as Hxx0. {
    simpl_dom. rewrite notin_union in H. destruct H as [H _]. auto. 
  }
  unfold rename_var. case_if. reflexivity.
Qed.

Lemma binds_map_keys: forall x y G' (T:typ) G'',
  ok (G' & x ~ T & G'') ->
  map_keys (rename_var x y) (G' & x ~ T & G'') = G' & y ~ T & G''.
Proof.
  intros. rewrite map_keys_concat. rewrite map_keys_push.
  destruct (ok_middle_inv H) as [H1 H2]. repeat rewrite* map_keys_notin.
  unfold rename_var. case_if. reflexivity.
Qed.  

Lemma map_other_keys: forall x y z (G:ctx),
  z <> y ->
  z # G ->
  z # map_keys (rename_var x y) G.
Proof.
  intros. induction G using env_ind.
  rewrite map_keys_empty. assumption.
  rewrite map_keys_push. simpl_dom. rewrite notin_union. split.
  unfold rename_var. case_if*. auto.
Qed.

Lemma renaming_gen: forall x y,
  (forall m1 G t T, ty_trm m1 G t T ->
    ok G ->
    m1 = ty_general ->
    y # G ->
    ty_trm m1 (rename_ctx x y G) (subst_trm x y t) (subst_typ x y T)) /\
  (forall G z U d D, ty_def G z U d D ->
    ok (G & z ~ U) ->
    y # (G & z ~ U) ->
    ty_def (rename_ctx x y G) (rename_var x y z) (subst_typ x y U) 
          (subst_def x y d) (subst_dec x y D)) /\
  (forall G z U ds T, ty_defs G z U ds T ->
    ok (G & z ~ U) ->
    y # (G & z ~ U) ->
    ty_defs (rename_ctx x y G) (rename_var x y z) (subst_typ x y U) 
          (subst_defs x y ds) (subst_typ x y T)) /\
  (forall G p, norm G p ->
    ok G ->
    y # G ->
    norm (rename_ctx x y G) (subst_path x y p)) /\
  (forall m1 G T U, subtyp m1 G T U ->
    ok G ->
    m1 = ty_general ->
    y # G ->
    subtyp m1 (rename_ctx x y G) (subst_typ x y T) (subst_typ x y U)).
Proof.
  intros. apply rules_mutind; intros; subst; simpl; try (econstructor; apply* H); eauto .
  - (* ty_var *)
    constructor. unfold rename_ctx. unfold subst_ctx.
    destruct (binds_destruct b) as [G' [G'' HG]]. subst. case_if. rewrite* binds_map_keys.
    apply binds_map. rewrite map_keys_concat. rewrite map_keys_push.
    destruct (ok_middle_inv H) as [Hl Hr].
    assert (x0 <> y) as Hx0y. {
      simpl_dom. repeat rewrite notin_union in H1.  destruct H1 as [[_ Hy] _]. auto.
    }
    lets Ho: (map_other_keys Hx0y Hr (x:=x)). unfold rename_var. case_if. apply binds_middle_eq. auto.
  - (* ty_all_intro *)
    apply_fresh ty_all_intro as z. assert (z \notin L) as Lz by auto.
    specialize (H z Lz). rewrite subst_open_commute_trm in H. rewrite subst_open_commute_typ in H.
    unfold subst_fvar in H. assert (z <> x) as Hzx by auto. case_if.
    assert (rename_ctx x y G & z ~ subst_typ x y T = rename_ctx x y (G & z ~ T) ) as Hr. {
      unfold rename_ctx. unfold subst_ctx. rewrite map_keys_concat.
      assert (map_keys (rename_var x y) (z ~ T) = z ~ T) as Hm by (rewrite* map_keys_notin). rewrite Hm.
      rewrite map_push. reflexivity.
    }
    rewrite Hr. apply* H.
  - Admitted.    

Lemma renaming_def: forall G z U ds T y,
  ty_defs G z U ds T ->
  ok (G & z ~ U) ->
  y # (G & z ~ U) ->
  z \notin fv_ctx_types G ->
  ty_defs G y (subst_typ z y U) (subst_defs z y ds) (subst_typ z y T).
Proof.
  introv Hds Hok Hy Hz.
  assert (HG: G = subst_ctx z y G) by (rewrite (subst_fresh_ctx y G Hz); reflexivity).
  destruct (ok_push_inv Hok) as [_ Hn].
  assert (HG': G = (map_keys (rename_var z y) G)) by admit.
  assert (Hrg: G = rename_ctx z y G). {
    unfold rename_ctx. rewrite <- HG'. assumption.
  }    
  lets Hr: (proj53 (renaming_gen z y)). specialize (Hr G z U ds T Hds Hok Hy).
  rewrite Hrg. 
  assert (Hyz: y = (rename_var z y z)). {
    unfold rename_var. case_if. reflexivity.
  }
   rewrite <- Hyz in Hr. assumption.
Qed.

(* ###################################################################### *)
(** ** Some Lemmas *)

Lemma corresponding_types: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  ((exists S U t, binds x (val_lambda S t) s /\
                  ty_trm ty_precise G (trm_val (val_lambda S t)) (typ_all S U) /\
                  T = typ_all S U) \/
   (exists S ds, binds x (val_new S ds) s /\
                 ty_trm ty_precise G (trm_val (val_new S ds)) (typ_bnd S) /\
                 T = typ_bnd S)).
Proof.
  introv H Bi. induction H.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists T0. exists U. exists t.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * right. exists T0. exists ds.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * assert (exists x, trm_val v = trm_path (p_var (avar_f x))) as A. {
          apply H3. reflexivity.
        }
        destruct A as [? A]. inversion A.
    + specialize (IHwf_sto Bi).
      inversion IHwf_sto as [IH | IH].
      * destruct IH as [S [U [t [IH1 [IH2 IH3]]]]].
        left. exists S. exists U. exists t.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
      * destruct IH as [S [ds [IH1 [IH2 IH3]]]].
        right. exists S. exists ds.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
Qed.

Lemma unique_rec_subtyping: forall G S T,
  subtyp ty_precise G (typ_bnd S) T ->
  T = typ_bnd S.
Proof.
  introv Hsub.
  remember (typ_bnd S) as T'.
  remember ty_precise as m1.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_all_subtyping: forall G S U T,
  subtyp ty_precise G (typ_all S U) T ->
  T = typ_all S U.
Proof.
  introv Hsub.
  remember (typ_all S U) as T'.
  remember ty_precise as m1.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_lambda_typing: forall G x S U T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x)))  T ->
  T = typ_all S U.
Proof.
  introv Bi Hty.
  remember (trm_path (p_var (avar_f x)))  as t.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hty; try solve [inversion Heqt; inversion Heqm1].
  - inversions Heqt.
    unfold binds in Bi. unfold binds in H.
    rewrite H in Bi. inversion Bi.
    reflexivity.
  - specialize (IHHty Bi Heqt Heqm1).
    inversion IHHty. 
  - specialize (IHHty Bi Heqt Heqm1). destruct (H Heqm1).
    rewrite IHHty in H0. rewrite Heqm1 in H0.
    apply unique_all_subtyping in H0. apply H0.
Qed.

Lemma lambda_not_rcd: forall G x S U A T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_typ A T T)) ->
  False.
Proof.
  introv Bi Hty.
  assert (typ_rcd (dec_typ A T T) = typ_all S U) as Contra. {
    eapply unique_lambda_typing; eassumption.
  }
  inversion Contra.
Qed.

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a m T, record_dec (dec_trm a m T)
.

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
  record_typ (typ_and T (typ_rcd D)) (union ls \{l})
.

Definition record_type T := exists ls, record_typ T ls.

Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. induction H.
  - unfold open_typ. simpl.
    apply rt_one.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
Qed.

Lemma open_eq_avar: forall x i a1 a2,
  x \notin fv_avar a1 -> x \notin fv_avar a2 ->
  open_rec_avar i x a1 = open_rec_avar i x a2 ->
  a1 = a2.
Proof.
  introv Fr1 Fr2 H. induction a1; induction a2; simpl in H; inversion H.
  - case_if; case_if.
    + reflexivity.
    + inversion H. subst. reflexivity.
  - case_if.
    inversion H. subst. false.
    apply notin_same in Fr2. assumption.
  - case_if.
    inversion H. subst. false.
    apply notin_same in Fr1. assumption.
  - subst. reflexivity.
Qed.

Lemma open_eq_path: forall x i p1 p2,
  x \notin fv_path p1 -> x \notin fv_path p2 ->
  open_rec_path i x p1 = open_rec_path i x p2 ->
  p1 = p2.
Proof.
  introv Fr1 Fr2 H.
  dependent induction p1; dependent induction p2.
  - inversion H; f_equal; simpls. eapply open_eq_avar; eassumption.
  - inversion H.
  - inversion H.
  - inversion H. subst. f_equal. simpls. eapply IHp1; eassumption.
Qed.

Lemma open_eq_typ_dec: forall x,
  (forall T1, x \notin fv_typ T1 ->
   forall T2, x \notin fv_typ T2 ->
   forall i, open_rec_typ i x T1 = open_rec_typ i x T2 ->
   T1 = T2) /\
  (forall D1, x \notin fv_dec D1 ->
   forall D2, x \notin fv_dec D2 ->
   forall i, open_rec_dec i x D1 = open_rec_dec i x D2 ->
   D1 = D2).
Proof.
  intros. apply typ_mutind; intros.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal. eapply H; eauto.
  - simpl in H3; induction T2; simpl in H3; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H1; induction T2; simpl in H1; inversion H1.
    f_equal. eapply open_eq_path; eauto.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal.
    eapply H; eauto.
  - simpl in H3. induction T2; simpl in H3; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H3. induction D2; simpl in H3; inversion H3.
    subst.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H2. induction D2; simpl in H2; inversion H2.
    subst.
    f_equal.
    eapply H; eauto.
Qed.

Lemma open_eq_typ: forall x i T1 T2,
  x \notin fv_typ T1 -> x \notin fv_typ T2 ->
  open_rec_typ i x T1 = open_rec_typ i x T2 ->
  T1 = T2.
Proof.
  introv Fr1 Fr2 Heq.
  destruct (open_eq_typ_dec x) as [HT HD].
  eapply HT; eauto.
Qed.

Lemma open_record_dec_rev: forall D x,
  x \notin fv_dec D ->
  record_dec (open_dec x D) -> record_dec D.
Proof.
  introv Fr H. remember (open_dec x D) as DX.
  generalize dependent D.
  inversion H; intros.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    assert (t0 = t1) as Heq. {
      eapply open_eq_typ; eauto using notin_union_r1, notin_union_r2.
    }
    subst. constructor.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    subst. constructor.
Qed.

Lemma open_record_typ_rev: forall T x ls,
   x \notin fv_typ T ->
  record_typ (open_typ x T) ls -> record_typ T ls.
Proof.
  introv Fr H. remember (open_typ x T) as TX.
  generalize dependent T.
  induction H; intros.
  - destruct T; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_one; eauto.
    eapply open_record_dec_rev; eauto.
  - destruct T0; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    destruct T0_2; unfold open_typ in H5; simpl in H5; inversion H5.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_cons; try assumption.
    eapply IHrecord_typ; eauto using notin_union_r1.
    eapply open_record_dec_rev; eauto using notin_union_r2.
    eauto.
    rewrite <- open_dec_preserves_label in H2. apply H2.
Qed.

Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

Lemma open_record_type_rev: forall T x,
  x \notin fv_typ T ->
  record_type (open_typ x T) -> record_type T.
Proof.
  introv Fr H. destruct H as [ls H]. exists ls. eapply open_record_typ_rev; eauto.
Qed.

Lemma label_same_typing: forall G d z U D,
  ty_def  G z U d D -> label_of_def d = label_of_dec D.
Proof.
  intros. inversion H; subst; simpl; reflexivity.
Qed.

Lemma record_defs_typing_rec: forall G ds S z U,
  ty_defs  G z U ds S ->
  exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l.
Proof.
  intros. induction H.
  - eexists. split.
    apply rt_one.
    inversion H; subst; constructor.
    reflexivity.
    apply label_same_typing in H. rewrite <- H.
    intros. split; intro A.
    + unfold defs_hasnt. simpl.
      apply notin_singleton in A.
      rewrite If_r. reflexivity. eauto.
    + unfold defs_hasnt in A. unfold get_def in A.
      case_if. apply notin_singleton. eauto.
  - destruct IHty_defs as [ls [IH1 IH2]].
    eexists. split.
    apply rt_cons; try eassumption.
    inversion H0; subst; constructor.
    reflexivity.
    apply label_same_typing in H0. rewrite <- H0.
    specialize (IH2 (label_of_def d)).
    destruct IH2 as [IH2A IH2B].
    apply IH2B. assumption.
    intros. split; intro A.
    + specialize (IH2 l).
      destruct IH2 as [IH2A IH2B].
      unfold defs_hasnt. simpl.
      rewrite If_r. unfold defs_hasnt in IH2A. apply IH2A.
      apply notin_union in A. destruct A as [A1 A2]. assumption.
      apply notin_union in A. destruct A as [A1 A2]. apply notin_singleton in A2.
      apply label_same_typing in H0. rewrite <- H0 in A2. eauto.
    + apply notin_union. split.
      * specialize (IH2 l).
        destruct IH2 as [IH2A IH2B].
        apply IH2B. inversion A.
        case_if. unfold defs_hasnt. assumption.
      * apply label_same_typing in H0. rewrite <- H0.
        unfold defs_hasnt in A. unfold get_def in A.
        case_if in A.
        apply notin_singleton. eauto.
Qed.

Lemma record_defs_typing: forall G ds z U S,
  ty_defs  G z U ds S ->
  record_type S.
Proof.
  intros.
  assert (exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l) as A.
  eapply record_defs_typing_rec; eauto.
  destruct A as [ls [A1 A2]].
  exists ls. apply A1.
Qed.

Lemma record_new_typing: forall G S ds,
  ty_trm ty_precise G (trm_val (val_new S ds)) (typ_bnd S) ->
  record_type S.
Proof.
  intros.
  inversion H; subst.
  + pick_fresh x.
    apply open_record_type_rev with (x:=x).
    eauto.
    eapply record_defs_typing. eapply H3. eauto.
  + assert (exists x, trm_val (val_new S ds) = trm_path (p_var (avar_f x))) as Contra. {
      apply H0; eauto.
    }
    destruct Contra as [? Contra]. inversion Contra.
Qed.

Inductive record_sub : typ -> typ -> Prop :=
| rs_refl: forall T,
  record_sub T T
| rs_dropl: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_rcd D)
| rs_drop: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) T'
| rs_pick: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_and T' (typ_rcd D))
.

Lemma record_typ_sub_closed : forall T T' ls,
  record_sub T T' ->
  record_typ T ls ->
  exists ls', record_typ T' ls' /\ subset ls' ls.
Proof.
  introv Hsub Htyp. generalize dependent ls.
  induction Hsub; intros.
  - exists ls. split. assumption. apply subset_refl.
  - inversion Htyp; subst.
    eexists. split.
    eapply rt_one. assumption. reflexivity.
    rewrite <- union_empty_l with (E:=\{ label_of_dec D}) at 1.
    apply subset_union_2. apply subset_empty_l. apply subset_refl.
  - inversion Htyp; subst.
    specialize (IHHsub ls0 H1). destruct IHHsub as [ls' [IH1 IH2]].
    exists ls'. split. assumption.
    rewrite <- union_empty_r with (E:=ls').
    apply subset_union_2. assumption. apply subset_empty_l.
  - inversion Htyp; subst.
    specialize (IHHsub ls0 H1). destruct IHHsub as [ls0' [IH1 IH2]].
    exists (ls0' \u \{ label_of_dec D }). split.
    apply rt_cons; eauto.
    unfold "\c" in IH2. unfold "\notin". intro I.
    specialize (IH2 (label_of_dec D) I). eauto.
    apply subset_union_2. assumption. apply subset_refl.
Qed.

Lemma record_type_sub_closed : forall T T',
  record_sub T T' ->
  record_type T ->
  record_type T'.
Proof.
  introv Hsub Htype. destruct Htype as [ls Htyp].
  apply record_typ_sub_closed with (ls:=ls) in Hsub; try assumption.
  destruct Hsub as [ls' [Htyp' ?]].
  exists ls'. apply Htyp'.
Qed.

Lemma record_sub_trans: forall T1 T2 T3,
  record_sub T1 T2 ->
  record_sub T2 T3 ->
  record_sub T1 T3.
Proof.
  introv H12 H23. generalize dependent T3.
  induction H12; intros.
  - assumption.
  - inversion H23; subst. eapply rs_dropl. eassumption.
  - apply rs_drop. apply IHrecord_sub. assumption.
  - inversion H23; subst.
    + apply rs_pick. assumption.
    + eapply rs_dropl. eassumption.
    + apply rs_drop. apply IHrecord_sub. assumption.
    + apply rs_pick. apply IHrecord_sub. assumption.
Qed.

Lemma record_subtyping: forall G T T',
  subtyp ty_precise G T T' ->
  record_type T ->
  record_sub T T'.
Proof.
  introv Hsub Hr. generalize dependent Hr. dependent induction Hsub.
  - intros HS.
    apply record_sub_trans with (T2:=T).
    apply IHHsub1. apply HS.
    apply IHHsub2.
    eapply record_type_sub_closed. apply IHHsub1. apply HS. apply HS.
  - intros Htype. destruct Htype as [ls Htyp].
    inversion Htyp; subst.
    apply rs_drop. apply rs_refl.
  - intros Htype. destruct Htype as [ls Htyp].
    inversion Htyp; subst.
    eapply rs_dropl. apply rs_refl.
Qed.

Lemma record_typ_sub_label_in: forall T D ls,
  record_typ T ls ->
  record_sub T (typ_rcd D) ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Hsub. generalize dependent D. induction Htyp; intros.
  - inversion Hsub. subst. apply in_singleton_self.
  - inversion Hsub; subst.
    + rewrite in_union. right. apply in_singleton_self.
    + rewrite in_union. left. apply IHHtyp. assumption.
Qed.

Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_sub T (typ_rcd (dec_typ A T1 T1)) ->
  record_sub T (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Htype Hsub1 Hsub2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Hsub1; inversion Hsub2; subst.
  - inversion H5. subst. reflexivity.
  - inversion H9. subst. reflexivity.
  - apply record_typ_sub_label_in with (D:=dec_typ A T2 T2) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - apply record_typ_sub_label_in with (D:=dec_typ A T1 T1) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - eapply IHHtyp; eassumption.
Qed.

Lemma record_type_sub_not_rec: forall S T x,
  record_sub (open_typ x S) (typ_bnd T) ->
  record_type S ->
  False.
Proof.
  introv Hsub Htype. remember (open_typ x S) as Sx.
  apply open_record_type with (x:=x) in Htype.
  rewrite <- HeqSx in Htype. clear HeqSx.
  destruct Htype as [ls Htyp]. induction Htyp.
  - inversion Hsub.
  - inversion Hsub; subst. apply IHHtyp. assumption.
Qed.

Lemma shape_new_typing: forall G x S T,
  binds x (typ_bnd S) G ->
  record_type S ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) T ->
  T = typ_bnd S \/ record_sub (open_typ x S) T.
Proof.
  introv Bi HS Hx. dependent induction Hx.
  - unfold binds in H. unfold binds in Bi. rewrite H in Bi. inversion Bi.
    left. reflexivity.
  - assert (typ_bnd T = typ_bnd S \/ record_sub (open_typ x S) (typ_bnd T)) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + inversion A. right. apply rs_refl.
    + apply record_type_sub_not_rec in A. inversion A. assumption.
  - assert (T = typ_bnd S \/ record_sub (open_typ x S) T) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + subst. left. apply (unique_rec_subtyping H0).
    + right. eapply record_sub_trans. eassumption. apply (record_subtyping H0).
      apply (record_type_sub_closed A). apply open_record_type. assumption.
Qed.

Lemma sto_binds_to_ctx_binds: forall G s x v,
  wf_sto G s -> binds x v s -> exists S, binds x S G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  apply sto_binds_to_ctx_binds_raw with (x:=x) (v:=v) in Hwf.
  destruct Hwf as [G1 [G2 [T [EqG Hty]]]].
  subst.
  exists T.
  eapply binds_middle_eq. apply wf_sto_to_ok_G in Hwf'.
  apply ok_middle_inv in Hwf'. destruct Hwf'. assumption.
  assumption.
Qed.

Lemma val_new_typing: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise G (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis' [Ht EqT]]]]].
    false.
  - destruct H as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis.
    inversion Bis. subst.
    assumption.
Qed.

Lemma wf_sto_val_new_in_G: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [S Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [? [? [? [Bis' _]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversion Bis'.
  - destruct H as [T' [ds' [Bis' [Hty Heq]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
    assumption.
Qed.

Lemma var_new_typing: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x)))  (open_typ x T).
Proof.
  intros.
  apply ty_rec_elim. apply ty_var. eapply wf_sto_val_new_in_G; eauto.
Qed.

Lemma wf_sto_sub: forall G G' G'' s s' s'' x T v,
  wf_sto G s ->
  G = G' & x ~ T & G'' ->
  s = s' & x ~ v & s'' ->
  wf_sto (G' & x ~ T) (s' & x ~ v).
Proof.
  introv Hwf HG Hs. gen G G' s s' s''.
  induction G'' using env_ind; intros G G' HG s Hwf s' s'' Hs; destruct s'' using env_ind.
  - rewrite concat_empty_r in *. subst. assumption.
  - rewrite concat_assoc in Hs. subst. rewrite concat_empty_r in Hwf.
    assert (x <> x0) as Hxn. {
      lets Hok: (wf_sto_to_ok_s Hwf). destruct (ok_push_inv Hok) as [_ Hn].
      simpl_dom. auto.
    }
    inversion Hwf. false* empty_push_inv.
    destruct (eq_push_inv H0) as [Hx _]. destruct (eq_push_inv H) as [Hx' _]. subst. subst.
    false* Hxn.
  - rewrite concat_assoc in HG. subst. rewrite concat_empty_r in Hwf.
    assert (x <> x0) as Hxn. {
      lets Hok: (wf_sto_to_ok_G Hwf). destruct (ok_push_inv Hok) as [_ Hn].
      simpl_dom. auto.
    }
    inversion Hwf. false* empty_push_inv.
    destruct (eq_push_inv H0) as [Hx _]. destruct (eq_push_inv H) as [Hx' _]. subst. subst.
    false* Hxn.
  - assert (G' & x ~ T & G'' = G' & x ~ T & G'') as Hobv by reflexivity.
    assert (wf_sto (G' & x ~ T & G'') (s' & x ~ v & s'')) as Hwf'. {
      subst. inversion Hwf.
      * false* empty_middle_inv.
      * rewrite concat_assoc in *.
        destruct (eq_push_inv H) as [Hx [Ht Hg]]. destruct (eq_push_inv H0) as [Hx' [Hv Hs']]. 
        subst. subst. assumption.
    }
    assert (s' & x ~ v & s'' = s' & x ~ v & s'') as Hobv' by reflexivity.
    specialize (IHG'' (G' & x ~ T & G'') G' Hobv (s' & x ~ v & s'') Hwf' s' s'' Hobv').
    apply IHG''.
Qed.

Lemma wf_sto_new_typing: forall G s x T ds,
  wf_sto (G & x ~ (typ_bnd T)) (s & x ~ (val_new T ds)) ->
  ty_trm ty_precise G (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf. inversion Hwf.
  - false* empty_push_inv.
  - destruct (eq_push_inv H) as [Hx [HT HG]]. destruct (eq_push_inv H0) as [Hx' [Hv Hs]]. subst.
    assumption.
Qed.

Lemma new_ty_defs: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  exists G' G'',
    G = G' & x ~ (typ_bnd T) & G'' /\
    ty_defs G' x (open_typ x T) (open_defs x ds) (open_typ x T).
Proof.
  introv Hwf Bis.
  assert (exists s' s'', s = s' & x ~ (val_new T ds) & s'') as Hs by (apply* (binds_destruct Bis)).
  destruct Hs as [s' [s'' Hs]].
  lets Bis': (binds_push_eq x (val_new T ds) s').
  destruct (sto_binds_to_ctx_binds_raw Hwf Bis) as [G' [G'' [T0 [HG _]]]].
  exists G' G''.
  assert (T0 = typ_bnd T) as Ht. {
    lets Hb: (wf_sto_val_new_in_G Hwf Bis).
    apply wf_sto_to_ok_G in Hwf. rewrite HG in Hwf.
    assert (x # G'') as Hx by (apply* ok_middle_inv_r).
    assert (binds x T0 (G' & x ~ T0 & G'')) as Hxt by (apply* binds_middle_eq).
    rewrite <- HG in Hxt. apply (binds_func Hxt Hb).
  }
  subst T0. split. assumption.
  lets Hwf': (wf_sto_sub Hwf HG Hs).
  lets Hn: (wf_sto_new_typing Hwf').
  inversion Hn; subst. 
  - pick_fresh y. lets Hok': (wf_sto_to_ok_G Hwf'). 
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_defs with (x:=y).
    apply* renaming_def. auto. auto.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H as [? Contra]. inversion Contra.
Qed.

Lemma path_equivalence: forall G s p T,
  wf_sto G s ->
  ty_trm ty_general G (trm_path p) T ->
  norm G p ->
  exists x, (eq_path s p x /\ ty_trm ty_general G (trm_path (p_var (avar_f x))) T).
Proof.
  introv Hwf Hty Hn. gen T. induction Hn; intros.
  - exists x. split. destruct (ctx_binds_to_sto_binds_typing Hwf H) as [v [Hv _]].
    apply* eq_v. assumption.
  - inversion Hty; subst.
    * Admitted. 

Lemma path_equivalence_t: forall G s p T,
  wf_sto G s ->
  ty_trm_t ty_general G (trm_path p) T ->
  norm G p ->
  exists x, (eq_path s p x /\ ty_trm_t ty_general G (trm_path (p_var (avar_f x))) T).
Proof. Admitted.

Lemma record_has_sub: forall T D G,
  record_has T D ->
  T = typ_rcd D \/ subtyp ty_precise G T (typ_rcd D).
Proof.
  introv Hr. dependent induction Hr; auto.
  destruct IHHr as [IHHr | IHHr]; right.
  - subst. auto.
  - apply subtyp_trans with (T:=T); auto.
Qed.

Lemma path_equivalence_typing: forall p x G T s,
  wf_sto G s ->
  eq_path s p x ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) T ->
  ty_trm ty_general G (trm_path p) T.
Proof.
  introv Hwf Heq Hty. gen T.
  induction Heq; intros. auto. Admitted. (*
  lets Hv: (var_new_typing Hwf H).
  destruct (record_has_sub G H0) as [HT | Hs].
  - subst. specialize (IHHeq1 Hwf (open_typ x (typ_rcd (dec_trm a path_strong U))) Hv).
    unfold open_typ in IHHeq1. simpls.
    specialize (IHHeq2 Hwf T0 Hty). *)

Lemma precise_to_general:
  (forall m1 G t T,
     ty_trm m1 G t T ->
     m1 = ty_precise ->
     ty_trm ty_general G t T) /\
  (forall m1 G S U,
     subtyp m1 G S U ->
     m1 = ty_precise ->
     subtyp ty_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
Qed.


Lemma record_has_open: forall x T D,
  record_has T D -> record_has (open_typ x T) (open_dec x D).
Proof.
  introv H. gen D. induction T; intros; inversion H; subst; unfold open_typ; simpl; constructor. 
  apply* IHT1.
Qed.

Lemma equiv_to_norm: forall G s p x,
  wf_sto G s ->
  eq_path s p x ->
  norm G p.
Proof.
  introv Hwf Heq. induction Heq.
  lets Hs: (sto_binds_to_ctx_binds_raw Hwf H). destruct Hs as [G' [G'' [T [HG _]]]].
  apply norm_var with (T:=T). subst. apply binds_middle_eq. apply wf_sto_to_ok_G in Hwf.
  apply* ok_middle_inv_r.
  lets Hv: (var_new_typing Hwf H).
  destruct (new_ty_defs Hwf H) as [G' [G'' [HG Htd]]].
  lets Hn: (IHHeq2 Hwf).
  assert (record_has (open_typ x T) (open_dec x (dec_trm a path_strong U))) as Hrh by (apply* record_has_open).
  assert (exists U', ty_trm ty_precise G (trm_path (p_var (avar_f x)))
                              (open_typ x (typ_rcd (dec_trm a path_strong U')))) as Hx. {
    destruct (record_has_sub G' Hrh) as [Trcd | Tsub].
    - assert (exists U', T = typ_rcd (dec_trm a path_strong U')) as HU'. {
        destruct T; inversion Trcd.
        unfold open_typ in Trcd. simpl in Trcd.
        destruct d. inversion H3. inversion H3. subst. exists t0. reflexivity.
      } 
      destruct HU' as [U' HT]. exists U'. subst. auto.
    - exists U. apply ty_sub with (T:=open_typ x T). intro. exists x. reflexivity. assumption. subst.
      apply* weaken_subtyp. apply weaken_subtyp. auto.
      apply wf_sto_to_ok_G in Hwf.
      apply ok_concat_inv_l in Hwf. assumption.
  }
  destruct Hx as [U' Hx]. apply norm_path with (T:=open_typ x U').
  apply (path_equivalence_typing Hwf Heq1 Hx). auto.
Qed.

Lemma unique_eq_path: forall s p x,
  eq_path s p x ->
  (forall y, eq_path s p y ->  x = y).
Proof.
  introv Heqx.
  dependent induction Heqx; introv Heqy; inversion Heqy; subst.
  reflexivity.
  lets Heq: (IHHeqx1 x0 H4). subst x0.
  lets Hb: (binds_func H5 H). inversion Hb; subst T0 ds0.
  assert (q = q0) as Hq. {
    unfolds defs_has. simpls. remember (get_def (label_trm a) (open_defs x ds)) as g.
    rewrite H8 in H1. inversion H1. reflexivity.
  }
  subst q0.
  apply (IHHeqx2 y0 H10).
Qed.

Lemma unique_tight_bounds: forall G s x T1 T2 A,
  wf_sto G s ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Hwf Hty1 Hty2.
  assert (exists T, binds x T G) as Bi. {
    eapply typing_implies_bound. eassumption.
  }
  destruct Bi as [T Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis [Ht EqT]]]]].
    false.
    eapply lambda_not_rcd.
    subst. eassumption. eassumption.
  - destruct H as [S [ds [Bis [Ht EqT]]]]. subst.
    assert (record_type S) as Htype. {
      eapply record_new_typing. eassumption.
    }
    destruct (shape_new_typing Bi Htype Hty1) as [Contra1 | A1].
    inversion Contra1.
    destruct (shape_new_typing Bi Htype Hty2) as [Contra2 | A2].
    inversion Contra2.
    assert (record_type (open_typ x S)) as HXtype. {
      apply open_record_type. assumption.
    }
    eapply unique_rcd_typ.
    apply HXtype.
    eassumption.
    eassumption.
Qed.

Lemma tight_to_general:
  (forall m1 G t T,
     ty_trm_t m1 G t T ->
     m1 = ty_general ->
     ty_trm ty_general G t T) /\
  (forall m1 G S U,
     subtyp_t m1 G S U ->
     m1 = ty_general ->
     subtyp ty_general G S U).
Proof.
  apply ts_mutind_t; intros; subst; eauto.
  - eapply subtyp_sel2.
    lets He: (path_equivalence_typing w e t). eassumption. 
    apply* equiv_to_norm.
  - eapply subtyp_sel1.
    lets He: (path_equivalence_typing w e t). eassumption.
    apply* equiv_to_norm.
Qed.

Lemma tight_to_general_subtyping: forall G S U,
  subtyp_t ty_general G S U ->
  subtyp ty_general G S U.
Proof.
  intros. apply* tight_to_general.
Qed.

Lemma record_type_new: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  record_type (open_typ x T).
Proof.
  introv Hwf Bis.
  destruct (sto_binds_to_ctx_binds Hwf Bis) as [S Bi].
  destruct (corresponding_types Hwf Bi) as [Hlambda | Hnew].
  destruct Hlambda as [? [? [? [Bis' ?]]]].
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  destruct Hnew as [? [? [Bis' [? ?]]]]. subst.
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  apply record_new_typing in H.
  apply open_record_type. assumption.
Qed.

(* ###################################################################### *)
(** ** Narrowing *)


Definition subenv(G1 G2: ctx) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ subtyp ty_general G1 T1 T2.

Lemma subenv_push: forall G G' x T,
  subenv G' G ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T).
Proof.
  intros.
  unfold subenv. intros xb Tb Bi. apply binds_push_inv in Bi.
  destruct Bi as [Bi | Bi].
  + destruct Bi as [Bi1 Bi2]. subst.
    left. eauto.
  + destruct Bi as [Bi1 Bi2].
    unfold subenv in H. specialize (H xb Tb Bi2). destruct H as [Bi' | Bi'].
    * left. eauto.
    * right. destruct Bi' as [T' [Bi1' Bi2']].
      exists T'. split. eauto. apply weaken_subtyp. assumption. eauto.
Qed.

Lemma subenv_last: forall G x S U,
  subtyp ty_general G S U ->
  ok (G & x ~ S) ->
  subenv (G & x ~ S) (G & x ~ U).
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists S. split; eauto.
    apply weaken_subtyp; eauto.
  - destruct Bi. left. eauto.
Qed.

(* also proven for sub_general *)
Lemma narrow_rules:
  (forall m1 G t T, ty_trm m1 G t T -> forall G',
    m1 = ty_general ->
    ok G' ->
    subenv G' G ->
    ty_trm m1 G' t T)
/\ (forall G z U d D, ty_def  G z U d D -> forall G',
    ok (G' & z ~ U) ->
    subenv G' G ->
    ty_def  G' z U d D)
/\ (forall G z U ds T, ty_defs  G z U ds T -> forall G',
    ok (G' & z ~ U) ->
    subenv G' G ->
    ty_defs  G' z U ds T)
/\ (forall G p, norm G p -> forall G',
    ok G' ->
    subenv G' G ->
    norm G' p)
/\ (forall m1 G S U, subtyp m1 G S U -> forall G',
    m1 = ty_general ->
    ok G' ->
    subenv G' G ->
    subtyp m1 G' S U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. unfold subenv in H1. specialize (H1 x T b).
    destruct H1.
    + eauto.
    + destruct H as [T' [Bi Hsub]].
      eapply ty_sub; eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    eapply H; eauto. apply subenv_push; eauto.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as z. apply H; auto.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    apply H0 with (x:=y); eauto. apply subenv_push; eauto.
  - (* ty_def_path *)
    constructor. apply H; auto. apply subenv_push. assumption. assumption.
  - (* norm_var *)
    unfold subenv in H0. destruct (H0 x T b) as [Hb | [T1 [Hb Hs]]].
    econstructor. eassumption.
    econstructor. eassumption.
  - (* norm_path *)
    econstructor; eauto.
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    apply H0; eauto. apply subenv_push; eauto.
Qed. 

Lemma narrow_typing: forall G G' t T,
  ty_trm ty_general G t T ->
  subenv G' G -> ok G' ->
  ty_trm ty_general G' t T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall G G' S U,
  subtyp ty_general G S U ->
  subenv G' G -> ok G' ->
  subtyp ty_general G' S U.
Proof.
  intros. apply* narrow_rules.
Qed.

(* ###################################################################### *)
(** * Has member *)

Inductive has_member: ctx -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_any : forall G x T A S U,
  ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  T ->
  has_member_rules G x T A S U ->
  has_member G x T A S U
with has_member_rules: ctx -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_refl : forall G x A S U,
  has_member_rules G x (typ_rcd (dec_typ A S U)) A S U
| has_and1 : forall G x T1 T2 A S U,
  has_member G x T1 A S U ->
  has_member_rules G x (typ_and T1 T2) A S U
| has_and2 : forall G x T1 T2 A S U,
  has_member G x T2 A S U ->
  has_member_rules G x (typ_and T1 T2) A S U
| has_bnd : forall G x T A S U,
  has_member G x (open_typ x T) A S U ->
  has_member_rules G x (typ_bnd T) A S U
| has_sel : forall G x y p B T' A S U s,
  ty_trm ty_precise G (trm_path (p_var (avar_f y))) (typ_rcd (dec_typ B T' T')) ->
  wf_sto G s ->
  eq_path s p y ->
  has_member G x T' A S U ->
  has_member_rules G x (typ_path p B) A S U
| has_bot  : forall G x A S U,
  has_member_rules G x typ_bot A S U
.

Scheme has_mut := Induction for has_member Sort Prop
with hasr_mut := Induction for has_member_rules Sort Prop.
Combined Scheme has_mutind from has_mut, hasr_mut.

Lemma has_member_rules_inv: forall G x T A S U, has_member_rules G x T A S U ->
  (T = typ_rcd (dec_typ A S U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G x T1 A S U \/
     has_member G x T2 A S U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G x (open_typ x T') A S U) \/
  (exists p y s B T', T = typ_path p B /\
    wf_sto G s /\
    eq_path s p y /\
    ty_trm ty_precise G (trm_path (p_var (avar_f y))) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst.
  - left. eauto.
  - right. left. exists T1 T2. eauto.
  - right. left. exists T1 T2. eauto.
  - right. right. left. exists T0. eauto.
  - right. right. right. left. exists p y s B T'. split. reflexivity.
    split. assumption. split. assumption. split. assumption. assumption.
  - right. right. right. right. reflexivity.
Qed.

Lemma has_member_inv: forall G x T A S U, has_member G x T A S U ->
  (T = typ_rcd (dec_typ A S U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G x T1 A S U \/
     has_member G x T2 A S U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G x (open_typ x T') A S U) \/
  (exists p y s B T', T = typ_path p B /\
    wf_sto G s /\
    eq_path s p y /\
    ty_trm ty_precise G (trm_path (p_var (avar_f y))) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst. apply has_member_rules_inv in H1. apply H1.
Qed.

Lemma rcd_typ_eq_bounds: forall T A S U,
  record_type T ->
  record_sub T (typ_rcd (dec_typ A S U)) ->
  S = U.
Proof.
  introv Htype Hsub.
  generalize dependent U. generalize dependent S. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Hsub; subst.
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
  - apply IHHtyp with (A:=A); eauto.
Qed.

Lemma has_member_rcd_typ_sub_mut:
  (forall G x T A S U,
    has_member G x T A S U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A S U))) /\
  (forall G x T A S U,
    has_member_rules G x T A S U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A S U))).
Proof.
  apply has_mutind; intros.
  - apply H; eauto.
  - apply rs_refl.
  - inversion H0; subst. inversion H1; subst. apply rs_drop.
    apply H; eauto.
    exists ls. assumption.
  - inversion H0; subst. inversion H1; subst. inversion h; subst. inversion H3; subst.
    eapply rs_dropl. eapply rs_refl.
  - inversion H0. inversion H1.
  - inversion H0. inversion H1.
  - destruct H as [ls H]. inversion H.
Qed.

Lemma has_member_tightness: forall G s x T ds A S U,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  has_member G x (typ_bnd T) A S U ->
  S = U.
Proof.
  introv Hwf Bis Hmem.
  assert (record_type T) as Htype. {
    eapply record_new_typing. eapply val_new_typing; eauto.
  }
  assert (record_type (open_typ x T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (has_member G x (open_typ x T) A S U) as Hmemx. {
    inversion Hmem; subst. inversion H0; subst. assumption.
  }
  assert (record_sub (open_typ x T) (typ_rcd (dec_typ A S U))) as Hsub. {
    destruct has_member_rcd_typ_sub_mut as [HL _].
    eapply HL; eauto.
  }
  eapply rcd_typ_eq_bounds. eapply Htypex. eapply Hsub.
Qed.

Lemma eq_path_var: forall s x y,
  eq_path s (p_var (avar_f x)) y ->
  x = y.
Proof.
  introv Heq. inversion Heq. reflexivity.
Qed.

Lemma has_member_covariance: forall G s T1 T2 x A S2 U2,
  wf_sto G s ->
  subtyp_t ty_general G T1 T2 ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  T1 ->
  has_member G x T2 A S2 U2 ->
  exists S1 U1, has_member G x T1 A S1 U1 /\
                subtyp_t ty_general G S2 S1 /\
                subtyp_t ty_general G U1 U2.
Proof.
  introv Hwf Hsub Hty Hmem.
  generalize dependent U2.
  generalize dependent S2.
  dependent induction Hsub; subst; intros.
  - (* top *)
    inversion Hmem; subst. inversion H0.
  - (* bot *)
    exists S2 U2. split.
    apply has_any. assumption. apply has_bot.
    split; apply subtyp_refl_t.
  - (* refl *)
    exists S2 U2. eauto.
  - (* trans *)
    assert (ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  T) as HS. {
      eapply ty_sub_t. intros Hp. subst. eexists; eauto.
      eapply Hty.
      eassumption.
    }
    specialize (IHHsub2 Hwf HS S2 U2 Hmem).
    destruct IHHsub2 as [S3 [U3 [Hmem3 [Hsub31 Hsub32]]]].
    specialize (IHHsub1 Hwf Hty S3 U3 Hmem3).
    destruct IHHsub1 as [S1 [U1 [Hmem1 [Hsub11 Hsub12]]]].
    exists S1 U1. split. apply Hmem1. split; eauto.
  - (* and11 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and1. assumption.
    split; eauto.
  - (* and12 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and2. assumption.
    split; eauto.
  - (* and2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1 [T2 [Heq [Hmem | Hmem]]]]; inversions Heq.
      * specialize (IHHsub1 Hwf Hty S2 U2 Hmem). apply IHHsub1.
      * specialize (IHHsub2 Hwf Hty S2 U2 Hmem). apply IHHsub2.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [p [y [s' [B [T' [Heq _]]]]]]. inversion Heq.
    + inversion Hmem.
  - (* fld *)
    inversion Hmem; subst. inversion H0; subst.
  - (* typ *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversions Hmem.
      exists S1 T1. split.
      apply has_any. assumption. apply has_refl.
      split; assumption.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [p [y [s' [B [T' [Heq _]]]]]]. inversion Heq.
    + inversion Hmem.
  - (* sel2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [q [y [s' [B [T' [Ht [Hw [Heq [Htyb Hmem]]]]]]]]]. inversions Heq.
      inversion Htyb; subst; inversion Ht; subst.
      * apply eq_path_var in H1. subst.
        assert (T' = T) as HeqT by (apply* unique_tight_bounds). 
        subst. eauto.
      * apply eq_path_var in H1. subst. assert (T' = T) as HeqT by (apply* unique_tight_bounds).
        subst. eauto.
      * apply eq_path_var in H1. subst. assert (T' = T) as HeqT by (apply* unique_tight_bounds).
        subst. eauto.
      * inversion Ht. subst.
        subst. eauto.

    + inversion Hmem.
  - (* sel1 *)
    exists S2 U2. split.
    eapply has_any. assumption.
    apply* has_sel. admit. (* apply* path_equivalence_typing.*)
    
  - (* all *)
    inversion Hmem; subst. inversion H2; subst.
  - (* path *)
    exists S2 U2. split.
    apply has_any. assumption.
    inversions Hmem; subst. inversion H0.
    split; constructor.
Qed.

Lemma has_member_monotonicity: forall G s x T0 ds T A S U,
  wf_sto G s ->
  binds x (val_new T0 ds) s ->
  has_member G x T A S U ->
  exists T1, has_member G x (typ_bnd T0) A T1 T1 /\
             subtyp_t ty_general G S T1 /\
             subtyp_t ty_general G T1 U.
Proof.
  introv Hwf Bis Hmem. inversion Hmem; subst.
  generalize dependent U. generalize dependent S.
  dependent induction H; intros.
  - (* var *)
    destruct (corresponding_types Hwf H).
    destruct H1 as [S0 [U0 [t [Bis' _]]]]. unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversion Bis.
    destruct H1 as [S0 [ds0 [Bis' [Hty Heq]]]]. unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversions Bis'.
    assert (S = U). {
      eapply has_member_tightness. eassumption. eassumption.
      eapply has_any.
      eapply ty_var_t. eassumption.
      eassumption.
    }
    subst.
    exists U. eauto. 
  - (* rec_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversions Heq.
      apply IHty_trm_t; eauto.
      inversions H0. assumption.
      inversions H0. inversions H4. assumption.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* rec_elim *)
    apply IHty_trm_t; eauto.
    apply has_any. assumption. apply has_bnd. assumption.
    apply has_bnd. assumption.
  - (* and_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq [Hmem | Hmem]]]];
      inversions Heq; inversions H1; inversions H9.
      apply IHty_trm_t1; eauto.
      apply IHty_trm_t2; eauto. apply has_any; assumption.
      apply IHty_trm_t1; eauto. apply has_any; assumption.
      apply IHty_trm_t2; eauto.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* sub *)
    destruct (has_member_covariance Hwf H1 H0 Hmem) as [S' [U' [Hmem' [Hsub1' Hsub2']]]].
    inversion Hmem'; subst.
    specialize (IHty_trm_t Hwf Bis S' U' Hmem' H4).
    destruct IHty_trm_t as [T1 [Hmem1 [Hsub1 Hsub2]]].
    exists T1. eauto.
Qed.

(* ###################################################################### *)
(** * Tight bound completeness *)

Lemma has_member_rcd_typ_sub2_mut:
  (forall G x T A S U,
    has_member G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise G T (typ_rcd (dec_typ A S U)))  /\
  (forall G x T A S U,
    has_member_rules G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise G T (typ_rcd (dec_typ A S U))).
Proof.
  apply has_mutind; intros.
  - apply H; eauto.
  - left. reflexivity.
  - inversion H0; subst. inversion H1; subst.
    assert (record_type T1) as Htyp1. { exists ls. assumption. }
    specialize (H Htyp1). destruct H as [H | H].
    + subst. right. apply subtyp_and11.
    + right.
      eapply subtyp_trans. eapply subtyp_and11. apply H.
  - inversion H0; subst. inversion H1; subst. inversion h; subst. inversion H3; subst.
    right. eapply subtyp_and12.
  - inversion H0. inversion H1.
  - inversion H0. inversion H1.
  - destruct H as [ls H]. inversion H.
Qed.

Lemma tight_bound_completeness: forall G s x T ds A S U,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_typ A S U)) ->
  exists T1, 
    ty_trm ty_precise G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_typ A T1 T1)) /\
    subtyp_t ty_general G S T1 /\
    subtyp_t ty_general G T1 U.
Proof.
  introv Hwf Bis Hty.
  assert (has_member G x (typ_rcd (dec_typ A S U)) A S U) as Hmem. {
    apply has_any. assumption. apply has_refl.
  }
  apply has_member_monotonicity with (s:=s) (ds:=ds) (T0:=T) in Hmem.
  destruct Hmem as [T1 [Hmem [Hsub1 Hsub2]]].
  assert (has_member G x (open_typ x T) A T1 T1) as Hmemx. {
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq Hmem]]. inversions Heq. assumption.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  }
  assert (record_type T) as Htype. {
    eapply record_new_typing. eapply val_new_typing; eauto.
  }
  assert (record_type (open_typ x T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (open_typ x T = (typ_rcd (dec_typ A T1 T1)) \/ subtyp ty_precise G (open_typ x T) (typ_rcd (dec_typ A T1 T1))) as Hsub. {
    destruct has_member_rcd_typ_sub2_mut as [HE _].
    eapply HE; eauto.
  }
  assert (ty_trm ty_precise G (trm_path (p_var (avar_f x)))  (open_typ x T)) as Htypx. {
    eapply ty_rec_elim.
    eapply ty_var.
    eapply wf_sto_val_new_in_G; eauto.
  }
  exists T1. 
  destruct Hsub as [Heq | Hsub]; split*.
  - rewrite Heq in Htypx. apply Htypx.
  - assumption. 
  - assumption. 
Qed. 

(* If G ~ s, s |- x = new(x: T)d, and G |-# x: {A: S..U} then G |-# x.A <: U and G |-# S <: x.A. *)
Lemma tight_bound_completeness_sub: forall G s x T ds A S U,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_typ A S U)) ->
  subtyp_t ty_general G (typ_path (p_var (avar_f x)) A) U /\
  subtyp_t ty_general G S (typ_path (p_var (avar_f x)) A).
Proof.
  introv Hwf Bis Hty.
  destruct (tight_bound_completeness Hwf Bis Hty) as [T1 [Htyp [Hs1 Hs2]]].
  destruct (typing_implies_bound_t Hty) as [V HG]. split.
  eapply subtyp_trans_t. eapply subtyp_sel1_t. eapply Htyp. eassumption. constructor.
  assumption. apply subtyp_trans_t with (T:=T1). assumption. eapply subtyp_sel2_t. eassumption.
  eassumption. constructor.
Qed.

(* ###################################################################### *)
(** * Misc Inversions *)

Lemma all_intro_inversion: forall G S t U,
  ty_trm ty_precise G (trm_val (val_lambda S t)) U ->
  exists T, U = typ_all S T.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
Qed.

Lemma new_intro_inversion: forall G T ds U,
  ty_trm ty_precise G (trm_val (val_new T ds)) U ->
  U = typ_bnd T /\ record_type T.
Proof.
  intros. inversion H; subst.
  - apply record_new_typing in H. split; eauto.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H0 Heqm1). destruct H0. inversion H0.
Qed.

(* ###################################################################### *)
(** ** Possible types *)

(*
Definition (Possible types)

For a variable x, non-variable value v, environment G, the set Ts(G, x, v) of possible types of x defined as v in G is the smallest set SS such that:

If v = new(x: T)d then T in SS.
If v = new(x: T)d and {a = t} in d and G |- t: T' then {a: T'} in SS.
If v = new(x: T)d and {A = T'} in d and G |- S <: T', G |- T' <: U then {A: S..U} in SS.
If v = lambda(x: S)t and G, x: S |- t: T and G |- S' <: S and G, x: S' |- T <: T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then S1 & S2 in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
If S in SS then rec(x: S) in SS.
*)

Inductive possible_types: ctx -> var -> val -> typ -> Prop :=
| pt_top : forall G x v,
  possible_types G x v typ_top
| pt_new : forall G x T ds,
  possible_types G x (val_new T ds) (open_typ x T)
| pt_rcd_trm : forall G x T ds a t T',
  defs_has (open_defs x ds) (def_trm a t) ->
  ty_trm ty_general G t T' ->
  possible_types G x (val_new T ds) (typ_rcd (dec_trm a path_general T'))
| pt_rcd_path : forall G x T ds a p T',
  defs_has (open_defs x ds) (def_trm a (trm_path p)) ->
  ty_trm ty_general G (trm_path p) T' ->
  norm G p ->
  possible_types G x (val_new T ds) (typ_rcd (dec_trm a path_strong T'))
| pt_rcd_typ : forall G x T ds A T' S U,
  defs_has (open_defs x ds) (def_typ A T') ->
  subtyp ty_general G S T' ->
  subtyp ty_general G T' U ->
  possible_types G x (val_new T ds) (typ_rcd (dec_typ A S U))
| pt_lambda : forall L G x S t T S' T',
  (forall y, y \notin L ->
   ty_trm ty_general (G & y ~ S) (open_trm y t) (open_typ y T)) ->
  subtyp ty_general G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  possible_types G x (val_lambda S t) (typ_all S' T')
| pt_and : forall G x v S1 S2,
  possible_types G x v S1 ->
  possible_types G x v S2 ->
  possible_types G x v (typ_and S1 S2)
| pt_sel : forall G x v p A S s y,
  possible_types G x v S ->
  wf_sto G s ->
  eq_path s p y ->
  ty_trm ty_precise G (trm_path (p_var (avar_f y))) (typ_rcd (dec_typ A S S)) ->
  possible_types G x v (typ_path p A)
| pt_bnd : forall G x v S S',
  possible_types G x v S ->
  S = open_typ x S' ->
  possible_types G x v (typ_bnd S').


Lemma unfold_rec: 
  (forall m1 G t T, ty_trm m1 G t T -> forall G1 G2 x U,
    ok G ->
    G = G1 & x ~ open_typ x U & G2 ->
    m1 = ty_general ->
    ty_trm m1 (G1 & x ~ typ_bnd U & G2) t T) /\
  (forall G z V d D, ty_def G z V d D -> forall G1 G2 x U,
    ok (G & z ~ V) ->
    G = G1 & x ~ open_typ x U & G2 ->
    ty_def (G1 & x ~ typ_bnd U & G2) z V d D) /\
  (forall G z V ds T, ty_defs G z V ds T -> forall G1 G2 x U,
    ok (G & z ~ V) ->
    G = G1 & x ~ open_typ x U & G2 ->
    ty_defs (G1 & x ~ typ_bnd U & G2) z V ds T) /\
  (forall G p, norm G p -> forall G1 G2 x U,
    ok G ->
    G = G1 & x ~ open_typ x U & G2 ->
    norm (G1 & x ~ typ_bnd U & G2) p) /\
  (forall m1 G T V, subtyp m1 G T V -> forall G1 G2 x U,
    ok G ->
    G = G1 & x ~ open_typ x U & G2 ->
    m1 = ty_general ->
    subtyp m1 (G1 & x ~ typ_bnd U & G2) T V).
Proof.
  apply rules_mutind; intros; subst; eauto.
  - destruct (classicT (x0=x)); subst.
    * apply binds_middle_eq_inv in b. subst. apply ty_rec_elim. constructor.
      apply binds_middle_eq. apply (ok_middle_inv_r H). assumption.
    * constructor. apply binds_remove in b. apply* binds_weaken. apply* ok_middle_change.
      auto.
  - (* ty_all_intro *)
    apply_fresh ty_all_intro as z. assert (z \notin L) as Lz by auto.
    specialize (H z Lz G1 (G2 & z ~ T) x U0). repeat rewrite concat_assoc in H.
    apply* H.
  - (* ty_new_intro *)
    apply_fresh ty_new_intro as z. assert (z \notin L) as Lz by auto.
    apply* H.
  - (* ty_let *)
    apply_fresh ty_let as z; auto. assert (z \notin L) as Lz by auto.
    specialize (H0 z Lz G1 (G2 & z ~ T) x U0). repeat rewrite concat_assoc in H0. apply* H0.
  - (* ty_def_trm *)
    constructor. specialize (H G1 (G2 & x ~ U) x0 U0). repeat rewrite concat_assoc in H. 
    apply* H. 
  - destruct (classicT (x0=x)); subst.
    + apply norm_var with (T:=(typ_bnd U)). apply binds_middle_eq.
      apply (ok_middle_inv_r H). 
    + apply norm_var with (T:=T). apply binds_remove in b. apply* binds_weaken.
      apply* ok_middle_change. auto.
  - apply norm_path with (T:=T). apply* H. apply* H0.
  - apply_fresh subtyp_all as z; auto. assert (z \notin L) as Lz by auto. 
    specialize (H0 z Lz G1 (G2 & z ~ S2) x U). repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma unfold_rec_trm: forall G1 x U G2 t T,
  ok (G1 & x ~ open_typ x U & G2) ->
  ty_trm ty_general (G1 & x ~ open_typ x U & G2) t T ->
  ty_trm ty_general (G1 & x ~ typ_bnd U & G2) t T.
Proof.
  intros. apply* unfold_rec.
Qed.

Lemma pt_piece_rcd: forall G G' s x T ds d D,
  wf_sto (G & x ~ (typ_bnd T) & G') s ->
  binds x (val_new T ds) s ->
  defs_has (open_defs x ds) d ->
  ty_def G x (open_typ x T) d D ->
  possible_types (G & x ~ (typ_bnd T) & G') x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas Hdef. 
  apply wf_sto_to_ok_G in Hwf.
  inversion Hdef; subst. 
  - (* def_typ *)
    econstructor; eauto. 
  - (* def_trm *)
    apply pt_rcd_trm with (t:=t). assumption. apply* weaken_ty_trm.
    assert (G & x ~ typ_bnd T = G & x ~ typ_bnd T & (@empty typ)) as Hemp. {
      rewrite concat_empty_r. reflexivity.
    }
    assert (ok (G & x ~ open_typ x T & empty)) as Hok. {
      rewrite concat_empty_r.
      lets Hn: (ok_middle_inv_l Hwf). rewrite <- concat_assoc in Hwf. lets Hok: (ok_concat_inv_l Hwf).
      apply* ok_push.
    }
    rewrite Hemp. apply unfold_rec_trm. apply* ok_middle_change. apply ok_concat_inv_l in Hwf.
    rewrite concat_empty_r. eassumption. 
  - (* def_path *)
    apply pt_rcd_path with (p:=p). assumption. apply weaken_ty_trm. apply weaken_ty_trm. assumption.
    eapply ok_concat_inv_l; eassumption. assumption.
    apply weaken_norm. apply weaken_norm. assumption. eapply ok_concat_inv_l. eassumption.
    assumption.
Qed.

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

Lemma record_has_ty_defs: forall G z U T ds D,
  ty_defs G z U ds T ->
  record_has T D ->
  exists d, defs_has ds d /\ ty_def  G z U d D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    unfold defs_has. simpl. rewrite If_l. reflexivity. reflexivity.
    assumption.
  - inversion Hhas; subst.
    + exists d. split.
      unfold defs_has. simpl. rewrite If_l. reflexivity. reflexivity.
      assumption.
    + specialize (IHHdefs H4). destruct IHHdefs as [d' [IH1 IH2]].
      exists d'. split.
      unfold defs_has. simpl. rewrite If_r. apply IH1.
      apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      assumption.
Qed.

Lemma pt_rcd_has_piece: forall G s x T ds D,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  record_has (open_typ x T) D ->
  possible_types G x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas.
  destruct (new_ty_defs Hwf Bis) as [G' [G'' [Hg Hd]]].
  destruct (record_has_ty_defs Hd Hhas) as [d [A B]].
  subst.
  eapply pt_piece_rcd; eauto.
Qed.

Lemma pt_rcd_trm_inversion: forall G s x v a T m,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v (typ_rcd (dec_trm a m T)) ->
  exists S ds t,
    v = val_new S ds /\
    defs_has (open_defs x ds) (def_trm a t) /\
    ty_trm ty_general G t T.
Proof.
  introv Hwf Bis Hp. dependent induction Hp; subst.
  - (* pt_new *)
    induction T0; simpl in x; try solve [inversion x].
    induction d; simpl in x; try solve [inversion x].
    unfold open_typ in x. simpl in x. inversions x.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    * pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H2 y FrL).
      unfold open_typ in H2. simpl in H2. inversion H2; subst.
      destruct ds; simpl in H; try solve [inversion H].
      destruct ds; simpl in H; try solve [inversion H].
      unfold open_defs in H. simpl in H. inversions H.
      destruct d0; simpl in H5; inversion H5; subst.
      + inversion H5; subst.
        assert (ty_trm ty_general G (open_trm x0 t1) (open_typ x0 t0)) as A. {
          rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
          eapply subst_ty_trm. eapply H6.
          apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto. eauto.
          simpl. rewrite <- subst_intro_typ with (x:=y).
          lets Htyv: (var_new_typing Hwf Bis). unfold open_typ in Htyv. simpl in Htyv.
          unfold open_typ. apply Htyv.
          eauto.
          apply notin_union_r1 in Fr. apply notin_union_r2 in Fr.
          unfold fv_defs in Fr. apply notin_union_r2 in Fr. apply Fr.
          eauto.
        }
        repeat eexists.
        unfold open_defs. simpl. unfold defs_has. simpl.
        rewrite If_l. reflexivity. reflexivity.
        eapply A. 
      + exists (typ_rcd (dec_trm a path_strong t0)) (defs_cons defs_nil (def_trm a t1)) (open_trm x0 t1).
        split. reflexivity. split. unfold open_defs. simpl. unfold defs_has. simpl. case_if. reflexivity.
        rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y). apply* subst_ty_trm. 
        unfold open_trm. rewrite <- H0. apply* weaken_ty_trm. unfold open_typ. apply* precise_to_general.
        constructor. lets Hb: (wf_sto_val_new_in_G Hwf Bis).
        assert (typ_bnd (typ_rcd (dec_trm a path_strong t0)) 
               = subst_typ y x0 (typ_bnd (typ_rcd (dec_trm a path_strong t0)))) as Hsubst. {
          simpl. rewrite* subst_fresh_typ.
        }
        rewrite Hsubst in Hb. eapply Hb.
        assert (y \notin fv_defs (defs_cons defs_nil (def_trm a t1))) as Hy by auto. simpl in Hy.
        rewrite notin_union in Hy. destruct Hy as [_ Ht1]. assumption. auto.
    * assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
      specialize (H Heqm1). destruct H. inversion H.
  - (* pt_rcd_trm *)
    repeat eexists. eassumption. assumption.
  - (* pt_rcd_path *)
    repeat eexists. eassumption. eassumption.
Qed.

Lemma pt_rcd_typ_inversion: forall G s x v A S U,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v (typ_rcd (dec_typ A S U)) ->
  exists T ds T',
    v = val_new T ds /\
    defs_has (open_defs x ds) (def_typ A T') /\
    subtyp ty_general G S T' /\
    subtyp ty_general G T' U.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T; simpl in H3; try solve [inversion H3].
    induction d; simpl in H3; try solve [inversion H3].
    unfold open_typ in H3. simpl in H3. inversions H3.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H2 y FrL).
    unfold open_typ in H2. simpl in H2. inversion H2; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H5; inversion H5; subst.
    inversion H5; subst.
    assert (t2 = t0). {
      eapply open_eq_typ; eauto.
      apply notin_union_r1 in Fr. apply notin_union_r1 in Fr.
      apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. eauto. eauto.
    }
    assert (t2 = t1). {
      eapply open_eq_typ; eauto.
      apply notin_union_r1 in Fr. apply notin_union_r1 in Fr.
      apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. eauto. eauto.
    }
    subst. subst.
    repeat eexists.
    unfold open_defs. simpl. unfold defs_has. simpl.
    rewrite If_l. reflexivity. reflexivity.
    eapply subtyp_refl. eapply subtyp_refl.
    assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
  - repeat eexists. eassumption. eassumption. eassumption.
Qed.

Lemma record_sub_and: forall T T1 T2,
  record_type T ->
  T = typ_and T1 T2 ->
  record_sub T T1 /\ record_sub T T2.
Proof.
  introv Htype Heq. subst.
  destruct Htype as [ls Htyp]. inversion Htyp; subst.
  split.
  - apply rs_drop. apply rs_refl.
  - eapply rs_dropl. apply rs_refl.
Qed.

Lemma record_sub_has: forall T1 T2 D,
  record_has T2 D ->
  record_sub T1 T2 ->
  record_has T1 D.
Proof.
  introv Hhas Hsub. induction Hsub.
  - assumption.
  - inversion Hhas; subst. apply rh_andl.
  - apply rh_and. apply IHHsub. apply Hhas.
  - inversion Hhas; subst.
    + apply rh_andl.
    + apply rh_and. apply IHHsub. assumption.
Qed.

Lemma pt_record_sub_has: forall G x v T1 T2,
  (forall D, record_has T1 D -> possible_types G x v (typ_rcd D)) ->
  record_sub T1 T2 ->
  (forall D, record_has T2 D -> possible_types G x v (typ_rcd D)).
Proof.
  introv HP Hsub. intros D Hhas. apply HP; eauto using record_sub_has.
Qed.

Lemma pt_has_record: forall G x v T,
  (forall D, record_has T D -> possible_types G x v (typ_rcd D)) ->
  record_type T ->
  possible_types G x v T.
Proof.
  introv HP Htype. destruct Htype as [ls Htyp]. induction Htyp.
  - apply HP; eauto. apply rh_one.
  - apply pt_and.
    + apply IHHtyp; eauto.
      intros D0 HH0. apply HP; eauto. apply rh_and; eauto.
    + apply HP; eauto. apply rh_andl.
Qed.

Lemma pt_has_sub: forall G x v T U,
  (forall D, record_has T D -> possible_types G x v (typ_rcd D)) ->
  record_type T ->
  record_sub T U ->
  possible_types G x v U.
Proof.
  introv HP Htype Hsub. induction Hsub.
  - apply pt_has_record; eauto.
  - apply HP; eauto. apply rh_andl.
  - apply IHHsub; eauto. eapply pt_record_sub_has; eauto.
    apply rs_drop. apply rs_refl.
    eapply record_type_sub_closed; eauto.
    apply rs_drop. apply rs_refl.
  - apply pt_and.
    + apply IHHsub; eauto. eapply pt_record_sub_has; eauto.
      apply rs_drop. apply rs_refl.
      eapply record_type_sub_closed; eauto.
      apply rs_drop. apply rs_refl.
    + apply HP; eauto. apply rh_andl.
Qed.

Lemma possible_types_closure_record: forall G s x T ds U,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  record_sub (open_typ x T) U ->
  possible_types G x (val_new T ds) U.
Proof.
  introv Hwf Bis Hsub.
  apply pt_has_sub with (T:=open_typ x T).
  intros D Hhas. eapply pt_rcd_has_piece; eauto.
  apply open_record_type. eapply record_new_typing; eauto. eapply val_new_typing; eauto.
  assumption.
Qed.

Lemma pt_and_inversion: forall G s x v T1 T2,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v (typ_and T1 T2) ->
  possible_types G x v T1 /\ possible_types G x v T2.
Proof.
  introv Hwf Bis Hp. dependent induction Hp.
  - assert (record_type (open_typ x0 T)) as Htype. {
      eapply open_record_type.
      eapply record_new_typing. eapply val_new_typing; eauto.
    }
    destruct (record_sub_and Htype x) as [Hsub1 Hsub2].
    split;
    eapply possible_types_closure_record; eauto.
  - split; assumption.
Qed.

(*
Lemma (Possible types closure)

If G ~ s and G |- x: T and s |- x = v then Ts(G, x, v) is closed wrt G |- _ <: _.

Let SS = Ts(G, x, v). We first show SS is closed wrt G |-# _ <: _.

Assume T0 in SS and G |- T0 <: U0.s We show U0 in SS by an induction on subtyping derivations of G |-# T0 <: U0.
*)

Lemma possible_types_closure_tight: forall G s x v T0 U0,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v T0 ->
  subtyp_t ty_general G T0 U0 ->
  possible_types G x v U0.
Proof.
  introv Hwf Bis HT0 Hsub. dependent induction Hsub.
  - (* Top *) apply pt_top.
  - (* Bot *) inversion HT0; subst.
    lets Htype: (open_record_type x (record_new_typing (val_new_typing Hwf Bis))).
    destruct Htype as [ls Htyp]. rewrite H3 in Htyp. inversion Htyp.
  - (* Refl-<: *) assumption.
  - (* Trans-<: *)
    apply IHHsub2; try assumption.
    apply IHHsub1; assumption.
  - (* And-<: *)
    apply pt_and_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [HT HU].
    assumption.
  - (* And-<: *)
    apply pt_and_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [HT HU].
    assumption.
  - (* <:-And *)
    apply pt_and. apply IHHsub1; assumption. apply IHHsub2; assumption.
  - (* Fld-<:-Fld *)
    apply pt_rcd_trm_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [S [ds [t [Heq [Hhas Hty]]]]].
    subst.
    eapply pt_rcd_trm.
    eassumption.
    apply ty_sub with (T:=T).
    intro Contra. inversion Contra.
    assumption.
    apply tight_to_general_subtyping. assumption.
  - (* Typ-<:-Typ *)
    apply pt_rcd_typ_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [T [ds [T' [Heq [Hhas [Hsub1' Hsub2']]]]]].
    subst.
    eapply pt_rcd_typ.
    eassumption.
    eapply subtyp_trans. eapply tight_to_general_subtyping. eassumption. eassumption.
    eapply subtyp_trans. eassumption. eapply tight_to_general_subtyping. eassumption.
  - (* <:-Sel *)
    apply* pt_sel.
  - (* Sel-<: *)
    inversion HT0; subst.
    + (* pt_new *)
      assert (record_type (open_typ x T0)) as B. {
        eapply record_type_new. eapply Hwf. eassumption.
      }
      rewrite H6 in B. destruct B as [? B]. inversion B.
    + (* pt_sel *)
      assert (T = S) as B. {
        lets Hp: (path_equivalence_typing H0 H1 H).
        lets Hp': (path_equivalence_typing H5 H9 H10).
        apply* unique_tight_bounds. apply* equiv_to_norm. 
      }
      subst. assumption.
  - (* All-<:-All *)
    inversion HT0; subst.
    assert (record_type (open_typ x T)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H5 in B. destruct B as [? B]. inversion B.
    apply_fresh pt_lambda as y.
    eapply H3; eauto.
    eapply subtyp_trans. eapply tight_to_general_subtyping. auto. eauto.
    eapply subtyp_trans.
    eapply narrow_subtyping. eapply H8; eauto.
    eapply subenv_last. assumption.
    eapply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
    eapply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
    auto.
  - apply pt_rcd_trm_inversion with (s:=s) in HT0; auto.
    destruct HT0 as [S [ds [t [Hv [Hd Ht]]]]]. subst.
    apply pt_rcd_trm with (t:=t); auto.
Qed.

(*
Lemma (Possible types completeness for values)

If `G ~ s` and `x = v in s` and  `G |-! v: T` then `T in Ts(G, x, v)`.
 *)

Lemma possible_types_completeness_for_values: forall G s x v T,
  wf_sto G s ->
  binds x v s ->
  ty_trm ty_precise G (trm_val v) T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty. destruct v as [S ds | S t].
  - apply new_intro_inversion in Hty. destruct Hty as [Heq Htype]. subst.
    eapply pt_bnd. eapply pt_new. reflexivity.
  - remember Hty as Hty'. clear HeqHty'. inversion Hty'; subst.
    + apply all_intro_inversion in Hty. destruct Hty as [T' Heq]. subst.
      apply_fresh pt_lambda as y.
      eapply H4; eauto.
      apply subtyp_refl.
      apply subtyp_refl.
    + assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
      specialize (H Heqm1). destruct H. inversion H.
Qed.

(*
Lemma (Possible types completeness)

If `G ~ s` and `x = v in s` and  `G |-# x: T` then `T in Ts(G, x, v)`.

Lemma (Possible types)

If `G ~ s` and `G |- x: T` then, for some value `v`,
`s(x) = v` and `T in Ts(G, x, v)`.
*)

Lemma possible_types_completeness_tight: forall G s x T,
  wf_sto G s ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise G (trm_val v) T) as A. {
      destruct (ctx_binds_to_sto_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
      eapply wf_sto_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm_t Hwf).
    destruct IHty_trm_t as [v [Bis Hp]].
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm_t Hwf).
    destruct IHty_trm_t as [v [Bis Hp]].
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm_t1 Hwf). destruct IHty_trm_t1 as [v [Bis1 Hp1]].
    specialize (IHty_trm_t2 Hwf). destruct IHty_trm_t2 as [v' [Bis2 Hp2]].
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm_t Hwf). destruct IHty_trm_t as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure_tight; eauto.
Qed.

Lemma tight_ty_rcd_typ__new: forall G s x A S U,
  wf_sto G s ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_typ A S U)) ->
  exists T ds, binds x (val_new T ds) s.
Proof.
  introv Hwf Hty.
  destruct (possible_types_completeness_tight Hwf Hty) as [v [Bis Hpt]].
  inversion Hpt; subst; repeat eexists; eauto.
Qed.

Lemma general_to_tight: forall G0 s0,
  wf_sto G0 s0 ->
  (forall m1 G t T,
     ty_trm m1 G t T ->
     G = G0 ->
     m1 = ty_general ->
     ty_trm_t ty_general G t T) /\
  (forall m1 G S U,
     subtyp m1 G S U ->
     G = G0 ->
     m1 = ty_general ->
     subtyp_t ty_general G S U).
Proof.
  intros G s Hwf.
  apply ts_mutind; intros; subst; eauto. 
  - assert (G = G) as Hobv by reflexivity. specialize (H Hobv H1).
    destruct (path_equivalence_t Hwf H n) as [x [Heq Ht]].
    assert (exists S ds, binds x (val_new S ds) s) as Bis. {
      eapply tight_ty_rcd_typ__new. eassumption. eapply Ht.
    }
    destruct Bis as [U [ds Bis]].
    destruct (tight_bound_completeness Hwf Bis Ht) as [T1 [Htyp [Hs1 Hs2]]].
    lets Hs: (subtyp_sel2_t Htyp Hwf Heq).
    apply subtyp_trans_t with (T:=T1); auto.
  - assert (G = G) as Hobv by reflexivity. specialize (H Hobv H1).
    destruct (path_equivalence_t Hwf H n) as [x [Heq Ht]].
    assert (exists S ds, binds x (val_new S ds) s) as Bis. {
      eapply tight_ty_rcd_typ__new. eassumption. eapply Ht.
    }
    destruct Bis as [U [ds Bis]].
    destruct (tight_bound_completeness Hwf Bis Ht) as [T1 [Htyp [Hs1 Hs2]]].
    lets Hs: (subtyp_sel1_t Htyp Hwf Heq).
    apply subtyp_trans_t with (T:=T1); auto.
Qed.

Lemma general_to_tight_subtyping: forall G s S U,
   wf_sto G s ->
  subtyp ty_general G S U ->
  subtyp_t ty_general G S U.
Proof.
  intros. apply* general_to_tight.
Qed.

Lemma possible_types_closure: forall G s x v S T,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v S ->
  subtyp ty_general G S T ->
  possible_types G x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
  eapply general_to_tight_subtyping; eauto.
Qed.

Lemma possible_types_completeness: forall G s x T,
  wf_sto G s ->
  ty_trm ty_general G (trm_path (p_var (avar_f x)))  T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise G (trm_val v) T) as A. {
      destruct (ctx_binds_to_sto_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
      eapply wf_sto_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]].
    specialize (IHty_trm2 Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]].
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure; eauto.
Qed.

Lemma possible_types_lemma: forall G s x v T,
  wf_sto G s ->
  binds x v s ->
  ty_trm ty_general G (trm_path (p_var (avar_f x)))  T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G s x T U,
  wf_sto G s ->
  ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new Hwf Bis). rewrite H3 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - pick_fresh y. exists (dom G \u L). exists S0. exists t.
    split. apply Bis. split. assumption.
    intros y0 Fr0.
    eapply ty_sub.
    intros Contra. inversion Contra.
    eapply narrow_typing.
    eapply H1; eauto.
    apply subenv_last. apply H5.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    eapply H6; eauto.
Qed.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T. *)


Lemma canonical_forms_2: forall G s x a T m,
  wf_sto G s ->
  ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_trm a m T)) ->
  (exists S ds t G' G'' z,
    G = G' & z ~ typ_bnd S & G'' /\
    binds x (val_new S ds) s /\ 
    ty_defs G' z (open_typ z S) (open_defs z ds) (open_typ z S) /\ 
    defs_has (open_defs x ds) (def_trm a t) /\ 
    ty_trm ty_general G t T).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [S' [ds [t' [Heq [Hdefs Htyd]]]]]. subst.
  destruct (new_ty_defs Hwf Bis) as [G' [G'' [HG Hd]]].
  exists S' ds t' G' G'' x. split; try split; try auto.
Qed.

(* ###################################################################### *)
(** * Misc *)

Lemma val_typing: forall G v T,
  ty_trm ty_general G (trm_val v) T ->
  exists T', ty_trm ty_precise G (trm_val v) T' /\
             subtyp ty_general G T' T.
Proof.
  intros. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro with (L:=L); eauto. apply subtyp_refl.
  - destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

Lemma var_typing_implies_avar_f: forall G a T,
  ty_trm ty_general G (trm_path (p_var a)) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm.
Qed.


(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_path (p_var x))
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(*
Let G |- t: T and G ~ s. Then either

- t is a normal form, or
- there exists a store s', term t' such that s | t -> s' | t', and for any such s', t' there exists an environment G'' such that, letting G' = G, G'' one has G' |- t': T and G' ~ s'.
The proof is by a induction on typing derivations of G |- t: T.
*)

Lemma safety: forall G s t T,
  wf_sto G s ->
  ty_trm ty_general G t T ->
  (normal_form t \/ (exists s' t' G' G'', red t s t' s' /\ G' = G & G'' /\ ty_trm ty_general G' t' T /\ wf_sto G' s')).
Proof.
  introv Hwf H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 Hwf H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (open_trm z t) G (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=S).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. eauto.
  - (* New-E *) right. destruct p.
    * destruct (var_typing_implies_avar_f H) as [x Hv]. subst.
      lets C: (canonical_forms_2 Hwf H).
      destruct C as [S [ds [t [G' [G'' [z [HG [Bis [Tyds [Has Ty]]]]]]]]]].
      exists s t G (@empty typ).
      split.
      apply red_sel with (T:=S) (ds:=ds); try assumption.
      split. rewrite concat_empty_r. reflexivity.
      split. assumption. assumption.
    * exists s (trm_let (trm_path (p_sel p t)) (trm_path (p_sel (p_var (avar_b 0)) m))) G (@empty typ).
      split. constructor. split. rewrite concat_empty_r. reflexivity. split.
      + pick_fresh x. lets L:  ((((dom G \u fv_ctx_types G) \u dom s) \u fv_typ T) \u fv_path p).
        apply ty_let with (L:=L) (T:=typ_rcd (dec_trm m m3 T)). assumption.
        intros.
        assert (open_trm x0 (trm_path (p_sel (p_var (avar_b 0)) m)) = trm_path (p_sel (p_var (avar_f x0)) m)) as Hop. {
          unfold open_trm. simpl. case_if. reflexivity.
        }
        rewrite Hop. eauto.
      + assumption.
  - (* Let *) right.
    destruct t.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (s & x ~ v) (open_trm x u) (G & (x ~ T')) (x ~ T').
      split.
      apply red_let. eauto.
      split. reflexivity. split.
      apply narrow_typing with (G:=G & x ~ T).
      assumption.
      apply subenv_last. assumption.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply wf_sto_push. assumption. eauto. eauto. assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + (* Path *)
      destruct p.
      * assert (exists x, a = avar_f x) as A. {
          eapply var_typing_implies_avar_f. eassumption.
        }
        destruct A as [x A]. subst a.
        exists s (open_trm x u) G (@empty typ).
        split.
        apply red_let_var.
        split.
        rewrite concat_empty_r. reflexivity.
        split.
        pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
        rewrite subst_intro_trm with (x:=y).
        rewrite <- subst_fresh_typ with (x:=y) (y:=x).
        eapply subst_ty_trm. eapply H0.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
        rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. eauto.
      * specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
        destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
        exists s' (trm_let t' u) G' G''.
        split. apply red_let_tgt. assumption.
        split. assumption. split.
        apply ty_let with (L:=L \u dom G') (T:=T); eauto.
        intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
        rewrite IH2.
        rewrite <- IH2. eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH].
    + left. assumption.
    + right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' t' G' G''.
      split; try split; try split; try assumption.
      apply ty_sub with (T:=T).
      intro Contra. inversion Contra.
      assumption.
      rewrite IH2. apply weaken_subtyp. assumption.
      rewrite <- IH2. eapply wf_sto_to_ok_G. eassumption.
Qed.
