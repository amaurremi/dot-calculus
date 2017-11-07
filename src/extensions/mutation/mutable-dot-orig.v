Set Implicit Arguments.
Require Import LibMap LibLN.
Require Import Coq.Program.Equality.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter trm_label: Set.

Definition addr := var.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_ref  : typ -> typ (* Ref T *)
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ (* x.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> typ -> dec (* a: T *).

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_val  : val -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
  | trm_ref  : avar -> typ -> trm (* ref x T *)
  | trm_deref  : avar -> trm (* !x *)
  | trm_asg  : avar -> avar -> trm (* x := y *)
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
  | val_loc : addr -> val
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Store typing ("Sigma") *)
Definition sigma := env typ.

(** *** Value environment ("sta") *)
Definition stack := env val.

(** *** Store ("sto") *)
Definition store := LibMap.map addr var.

Definition bindsM l x sto := LibBag.binds (A:=addr) (B:=var) sto l x.

Definition emptyM : store := (@empty_impl addr var).

(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm m _ => label_trm m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.
Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k)
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_ref T      => typ_ref (open_rec_typ k u T)
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m T => dec_trm m (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_sel v m    => trm_sel (open_rec_avar k u v) m
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  | trm_ref a t    => trm_ref (open_rec_avar k u a) (open_rec_typ k u t)
  | trm_deref a    => trm_deref (open_rec_avar k u a)
  | trm_asg l r    => trm_asg (open_rec_avar k u l) (open_rec_avar k u r)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  | val_loc n      => val_loc n
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

(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_ref T      => (fv_typ T)
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv_avar x)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m T   => (fv_typ T)
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a        => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  | trm_ref a t      => (fv_avar a) \u (fv_typ t)
  | trm_deref a      => (fv_avar a)
  | trm_asg l r      => (fv_avar l) \u (fv_avar r)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
  | val_loc n       => \{}
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

Definition fv_env_types(e: env typ): vars := (fv_in_values (fun T => fv_typ T) e).

(* ###################################################################### *)
(** ** Operational Semantics *)

Inductive red : trm -> stack -> store -> trm -> stack -> store -> Prop :=
| red_sel : forall x m sta sto t T ds,
    binds x (val_new T ds) sta ->
    defs_has (open_defs x ds) (def_trm m t) ->
    red (trm_sel (avar_f x) m) sta sto t sta sto
| red_app : forall f a sta sto T t,
    binds f (val_lambda T t) sta ->
    red (trm_app (avar_f f) (avar_f a)) sta sto (open_trm a t) sta sto
| red_let : forall v t sta sto x,
    x # sta ->
    red (trm_let (trm_val v) t) sta sto (open_trm x t) (sta & x ~ v) sto
| red_let_var : forall t sta sto x,
    red (trm_let (trm_var (avar_f x)) t) sta sto (open_trm x t) sta sto
| red_let_tgt : forall t0 t sta sto t0' sta' sto',
    red t0 sta sto t0' sta' sto' ->
    red (trm_let t0 t) sta sto (trm_let t0' t) sta' sto'
| red_ref_var : forall x sta sto l T,
    l \notindom sto ->
    red (trm_ref (avar_f x) T) sta sto (trm_val (val_loc l)) sta sto[l :=  x]
| red_asgn : forall x y l sta sto,
    binds x (val_loc l) sta ->
    l \indom sto -> (* TODO is this redundant? *)
    red (trm_asg (avar_f x) (avar_f y)) sta sto (trm_var (avar_f y)) sta sto[l := y]
| red_deref : forall x y (l: addr) sta (sto: store),
    binds x (val_loc l) sta ->
    bindsM l y sto ->
    red (trm_deref (avar_f x)) sta sto (trm_var (avar_f y)) sta sto.

(* ###################################################################### *)
(** ** Typing *)

Inductive tymode: Set := ty_precise | ty_general.
Inductive submode: Set := sub_tight | sub_general.

Inductive ty_trm : tymode -> submode -> ctx -> sigma -> trm -> typ -> Prop :=
| ty_var : forall m1 m2 G S x T,
    binds x T G ->
    ty_trm m1 m2 G S (trm_var (avar_f x)) T
| ty_loc : forall m1 m2 G S l T,
    binds l T S ->
    ty_trm m1 m2 G S (trm_val (val_loc l)) (typ_ref T)
| ty_all_intro : forall L m1 m2 G S T t U,
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) S (open_trm x t) (open_typ x U)) ->
    ty_trm m1 m2 G S (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall m2 G S x z V T,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_all V T) ->
    ty_trm ty_general m2 G S (trm_var (avar_f z)) V ->
    ty_trm ty_general m2 G S (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro : forall L m1 m2 G S T ds,
    (forall x, x \notin L ->
      ty_defs (G & x ~ (open_typ x T)) S (open_defs x ds) (open_typ x T)) ->
    ty_trm m1 m2 G S (trm_val (val_new T ds)) (typ_bnd T)
| ty_new_elim : forall m2 G S x m T,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_rcd (dec_trm m T)) ->
    ty_trm ty_general m2 G S (trm_sel (avar_f x) m) T
| ty_let : forall L m2 G S t u T U,
    ty_trm ty_general m2 G S t T ->
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) S (open_trm x u) U) ->
    ty_trm ty_general m2 G S (trm_let t u) U
| ty_rec_intro : forall m2 G S x T,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (open_typ x T) ->
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_bnd T)
| ty_rec_elim : forall m1 m2 G S x T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_bnd T) ->
    ty_trm m1 m2 G S (trm_var (avar_f x)) (open_typ x T)
| ty_and_intro : forall m2 G S x T U,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) T ->
    ty_trm ty_general m2 G S (trm_var (avar_f x)) U ->
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_and T U)
| ty_sub : forall m1 m2 G S t T U,
    (m1 = ty_precise -> exists x, t = trm_var (avar_f x)) ->
    ty_trm m1 m2 G S t T ->
    subtyp m1 m2 G S T U ->
    ty_trm m1 m2 G S t U
| ty_ref_intro : forall m1 m2 G S x T,
     ty_trm m1 m2 G S (trm_var (avar_f x)) T ->
     ty_trm m1 m2 G S (trm_ref (avar_f x) T) (typ_ref T)
| ty_ref_elim : forall m1 m2 G S x T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_ref T) ->
    ty_trm m1 m2 G S (trm_deref (avar_f x)) T
| ty_asgn : forall m1 m2 G S x y T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_ref T) ->
    ty_trm m1 m2 G S (trm_var (avar_f y)) T ->
    ty_trm m1 m2 G S (trm_asg (avar_f x) (avar_f y)) T

with ty_def : ctx -> sigma -> def -> dec -> Prop :=
| ty_def_typ : forall G S A T,
    ty_def G S (def_typ A T) (dec_typ A T T)
| ty_def_trm : forall G S a t T,
    ty_trm ty_general sub_general G S t T ->
    ty_def G S (def_trm a t) (dec_trm a T)
with ty_defs : ctx -> sigma -> defs -> typ -> Prop :=
| ty_defs_one : forall G S d D,
    ty_def G S d D ->
    ty_defs G S (defs_cons defs_nil d) (typ_rcd D)
| ty_defs_cons : forall G S ds d T D,
    ty_defs G S ds T ->
    ty_def G S d D ->
    defs_hasnt ds (label_of_def d) ->
    ty_defs G S (defs_cons ds d) (typ_and T (typ_rcd D))

with subtyp : tymode -> submode -> ctx -> sigma -> typ -> typ -> Prop :=
(* sigma is not needed for subtyping but for induction *)
| subtyp_top: forall m2 G S T,
    subtyp ty_general m2 G S T typ_top
| subtyp_bot: forall m2 G S T,
    subtyp ty_general m2 G S typ_bot T
| subtyp_refl: forall m2 G S T,
    subtyp ty_general m2 G S T T
| subtyp_trans: forall m1 m2 G S V T U,
    subtyp m1 m2 G S V T ->
    subtyp m1 m2 G S T U ->
    subtyp m1 m2 G S V U
| subtyp_and11: forall m1 m2 G S T U,
    subtyp m1 m2 G S (typ_and T U) T
| subtyp_and12: forall m1 m2 G S T U,
    subtyp m1 m2 G S (typ_and T U) U
| subtyp_and2: forall m2 G S V T U,
    subtyp ty_general m2 G S V T ->
    subtyp ty_general m2 G S V U ->
    subtyp ty_general m2 G S V (typ_and T U)
| subtyp_fld: forall m2 G S a T U,
    subtyp ty_general m2 G S T U ->
    subtyp ty_general m2 G S (typ_rcd (dec_trm a T)) (typ_rcd (dec_trm a U))
| subtyp_typ: forall m2 G S A S1 T1 S2 T2,
    subtyp ty_general m2 G S S2 S1 ->
    subtyp ty_general m2 G S T1 T2 ->
    subtyp ty_general m2 G S (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2: forall G S x A V T,
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A V T)) ->
    subtyp ty_general sub_general G S V (typ_sel (avar_f x) A)
| subtyp_sel1: forall G S x A V T,
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A V T)) ->
    subtyp ty_general sub_general G S (typ_sel (avar_f x) A) T
| subtyp_sel2_tight: forall G S x A T,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general sub_tight G S T (typ_sel (avar_f x) A)
| subtyp_sel1_tight: forall G S x A T,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general sub_tight G S (typ_sel (avar_f x) A) T
| subtyp_all: forall L m2 G S S1 T1 S2 T2,
    subtyp ty_general m2 G S S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general sub_general (G & x ~ S2) S (open_typ x T1) (open_typ x T2)) ->
    subtyp ty_general m2 G S (typ_all S1 T1) (typ_all S2 T2)
| subtyp_ref: forall m2 G S T U,
    subtyp ty_general m2 G S T U ->
    subtyp ty_general m2 G S U T ->
    subtyp ty_general m2 G S (typ_ref T) (typ_ref U).

(* well-formed stack *)
Inductive wf_stack: ctx -> sigma -> stack -> Prop :=
| wf_stack_empty: wf_stack empty empty empty
| wf_stack_push: forall G S sta x T v,
    wf_stack G S sta ->
    x # G ->
    x # sta ->
    ty_trm ty_precise sub_general G S (trm_val v) T ->
    wf_stack (G & x ~ T) S (sta & x ~ v)
| wf_store_push: forall G S l T sta,
    wf_stack G S sta ->
    l # S ->
    wf_stack G (S & l ~ T) sta.

(* well-typed store *)
Inductive wt_store: ctx -> sigma -> store -> Prop :=
| wt_store_empty: wt_store empty empty emptyM
| wt_store_update: forall G S sto l x T,
    wt_store G S sto ->
    binds l T S ->
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) T ->
    wt_store G S sto[l := x]
| wt_store_new: forall G S sto l x T,
    wt_store G S sto ->
    l # S ->
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) T ->
    wt_store G (S & l ~ T) sto[l := x]
| wt_stack_push: forall G S x T sto,
    wt_store G S sto ->
    x # G ->
    wt_store (G & x ~ T) S sto.

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
with   ty_defs_mut   := Induction for ty_defs   Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut.

Scheme ts_ty_trm_mut := Induction for ty_trm    Sort Prop
with   ts_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_def_mut    := Induction for ty_def    Sort Prop
with   rules_defs_mut   := Induction for ty_defs   Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_env_types x)) in
  let D := gather_vars_with (fun x : sigma     => (dom x) \u (fv_env_types x)) in
  let E := gather_vars_with (fun x : stack     => dom x     ) in
  let F := gather_vars_with (fun x : avar      => fv_avar  x) in
  let G := gather_vars_with (fun x : trm       => fv_trm   x) in
  let H := gather_vars_with (fun x : val       => fv_val   x) in
  let I := gather_vars_with (fun x : def       => fv_def   x) in
  let J := gather_vars_with (fun x : defs      => fv_defs  x) in
  let K := gather_vars_with (fun x : typ       => fv_typ   x) in
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
  ty_trm ty_def ty_defs
  subtyp.

Hint Constructors wf_stack wt_store.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.

Lemma wt_in_dom: forall G S sto l,
  wt_store G S sto ->
  l \in dom S ->
  index sto l.
Proof.
  introv Wt. gen l. induction Wt; intros.
  - rewrite dom_empty in H. rewrite in_empty in H. false.
  - lets Hind: (IHWt l0 H1).
    lets Hdec: (classicT (l = l0)).
    lets Hinh: (prove_Inhab x).
    destruct Hdec; unfold index; simpl; subst.
    * rewrite map_indom_update. left. reflexivity. assumption.
    * rewrite map_indom_update. right. assumption. assumption.
  - lets Hdec: (classicT (l = l0)).
    lets Hinh: (prove_Inhab x).
    destruct Hdec; unfold index; simpl; subst.
    * rewrite map_indom_update. left. reflexivity. assumption.
    * rewrite map_indom_update. right.
      assert (l0 \in dom S). {
        simpl_dom. rewrite in_union in H1. destruct H1.
        + rewrite in_singleton in H1. subst. false n. reflexivity.
        + assumption.
      }
      lets Hin: (IHWt l0 H2). assumption. assumption.
  - apply IHWt in H0. assumption.
Qed.


(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules_ctx:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm m1 m2 (G1 & G2 & G3) S t T) /\
  (forall G S d D, ty_def G S d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_def (G1 & G2 & G3) S d D) /\
  (forall G S ds T, ty_defs G S ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_defs (G1 & G2 & G3) S ds T) /\
  (forall m1 m2 G S T U, subtyp m1 m2 G S T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m1 m2 (G1 & G2 & G3) S T U).
Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; eauto.
  + intros. subst.
    apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst.
    apply_fresh subtyp_all as z.
    eauto.
    eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.


Lemma weaken_rules_sigma:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_trm m1 m2 G (S1 & S2 & S3) t T) /\
  (forall G S d D, ty_def G S d D -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_def G (S1 & S2 & S3) d D) /\
  (forall G S ds T, ty_defs G S ds T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_defs G (S1 & S2 & S3) ds T) /\
  (forall m1 m2 G S T U, subtyp m1 m2 G S T U -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    subtyp m1 m2 G (S1 & S2 & S3) T U).
Proof.
  apply rules_mutind; try solve [eauto].
  intros. subst.
  eapply ty_loc. eapply binds_weaken; eauto.
Qed.


Lemma weaken_ty_trm_ctx:  forall m1 m2 G1 G2 S t T,
    ty_trm m1 m2 G1 S t T ->
    ok (G1 & G2) ->
    ty_trm m1 m2 (G1 & G2) S t T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_ctx.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_ty_trm_sigma: forall m1 m2 G S1 S2 t T,
  ty_trm m1 m2 G S1 t T ->
  ok (S1 & S2) ->
  ty_trm m1 m2 G (S1 & S2) t T.
Proof.
  intros. assert (S1 & S2 = S1 & S2 & empty) as EqS. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqS. apply* weaken_rules_sigma.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqS. assumption.
Qed.

Lemma weaken_subtyp_ctx: forall m1 m2 G1 G2 S T U,
  subtyp m1 m2 G1 S T U ->
  ok (G1 & G2) ->
  subtyp m1 m2 (G1 & G2) S T U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_ctx.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp_sigma: forall m1 m2 G S1 S2 T U,
  subtyp m1 m2 G S1 T U ->
  ok (S1 & S2) ->
  subtyp m1 m2 G (S1 & S2) T U.
Proof.
  intros.
    assert (S1 & S2 = S1 & S2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_sigma.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.


(* ###################################################################### *)
(** ** Well-formed stack *)

Lemma wf_stack_to_ok_s: forall s G S,
  wf_stack G S s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_stack_to_ok_G: forall s G S,
  wf_stack G S s -> ok G.
Proof. intros. induction H; jauto. Qed.

Lemma wf_stack_to_ok_S: forall s G S,
  wf_stack G S s -> ok S.
Proof. intros. induction H; jauto. Qed.

Lemma wt_store_to_ok_S: forall s G S,
  wt_store G S s -> ok S.
Proof.
  introv Wt. induction Wt; auto.
Qed.

Lemma wt_store_to_ok_G: forall s G S,
  wt_store G S s -> ok G.
Proof.
  introv Wt. induction Wt; auto.
Qed.


Lemma wt_notin_dom: forall G S sto l,
  wt_store G S sto ->
  l # S ->
  l \notindom sto.
Proof.
  introv Wt. gen l. induction Wt; intros.
  - unfold store. rewrite LibMap.dom_empty. auto.
  - assert (l <> l0). {
      lets Hdec: (classicT (l = l0)). destruct Hdec.
      * subst. false (binds_fresh_inv H H1).
      * assumption.
    }
    assert (LibBag.dom sto[l := x] = LibBag.dom sto). {
      apply dom_update_in.
      * apply (prove_Inhab x).
      * apply binds_get in H. apply get_some_inv in H.
        lets Hind: (wt_in_dom Wt H). assumption.
    }
    unfolds addr. rewrite H3.
    apply IHWt in H1. assumption.
  - assert (l <> l0). {
      lets Hdec: (classicT (l = l0)). destruct Hdec.
      * subst. rew_env_defs. simpl in H1. apply notin_union in H1. destruct H1.
        false (notin_same H1).
      * assumption.
    }
    unfold LibBag.notin. unfold not. intro His_in.
    assert (l0 \indom sto[l := x]) as Hindom by assumption. clear His_in.
    destruct (map_indom_update_inv Hindom) as [Hl | Hl].
    * subst. false H2. reflexivity.
    * subst.
      assert (l0 # S) as Hl0. {
        unfolds in H1.
        intro. apply H1. simpl_dom.
        assert (l0 \notin \{l } \u (dom S)) as Hdom by auto.
        apply notin_union in Hdom. destruct Hdom.
        rewrite in_union. right. assumption.
      }
    specialize (IHWt l0 Hl0).  apply IHWt in Hl. false.
    - apply IHWt in H0. assumption.
Qed.

Hint Resolve wf_stack_to_ok_s wf_stack_to_ok_G wf_stack_to_ok_S wt_store_to_ok_S wt_store_to_ok_G.

Lemma ctx_binds_to_stack_binds_raw: forall s G S x T,
  wf_stack G S s ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise sub_general G1 S (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) v.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
  + specialize (IHWf x T0 Bi). destruct IHWf as [G1 [G2 [v [HG [HB Hty]]]]].
    subst. exists G1 G2 v. split.
    - reflexivity.
    - split. assumption. apply* weaken_ty_trm_sigma.
Qed.

Lemma sigma_binds_to_store_binds_raw: forall sto G S l T,
  wt_store G S sto ->
  binds l T S ->
  exists S1 S2,
    S = S1 & (l ~ T) & S2 /\
    exists x,
    bindsM l x sto /\
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) T.
Proof.
  introv Wt. generalize l T. induction Wt; introv Bi.
  + false* binds_empty_inv.
  + lets OkS: (wt_store_to_ok_S Wt).
    apply IHWt in Bi; clear IHWt.
    destruct Bi as [S1 [S2 [HS [v0 [HBi Hty]]]]].
    exists S1 S2.
    split. assumption.
    lets Hdec: (classicT (l1 = l0)). destruct Hdec as [Hdec | Hdec].
    - subst l1. exists x. split.
      * apply binds_update_eq.
      * assert (binds l0 T1 S) as Hbi. {
          subst S. apply binds_middle_eq.
          apply ok_middle_inv in OkS. destruct OkS as [_ Hl]. assumption.
        }
        subst S. apply binds_middle_eq_inv in H.
        subst. assumption. assumption.
    - exists v0. split.
      * apply binds_update_neq; assumption.
      * assumption.
  + lets OkS: (wt_store_to_ok_S Wt).
    lets Hdec: (classicT (l1 = l0)). destruct Hdec as [Hdec | Hdec].
    - subst l1. exists S (@empty typ).
      apply binds_push_eq_inv in Bi. subst T1.
      split.
      rewrite concat_empty_r. reflexivity.
      exists x. split.
      * apply binds_update_eq.
      * apply weaken_ty_trm_sigma.
        assumption.
        constructor; assumption.
    - apply binds_push_neq_inv in Bi; try assumption.
      destruct (IHWt l1 T1 Bi) as [S1 [S2 [HS [v0 [HBiM Hty]]]]].
      exists S1 (S2 & l0 ~ T0). split.
      subst S. rewrite concat_assoc. reflexivity.
      exists v0. split.
      apply binds_update_neq; assumption.
      apply weaken_ty_trm_sigma. assumption. constructor; assumption.
  + destruct (IHWt l0 T1 Bi) as [S1 [S2 [HS [v [HBi Hty]]]]].
    exists S1 S2. split.
    assumption.
    exists v. split. assumption. apply weaken_ty_trm_ctx.
    assumption. constructor. apply wt_store_to_ok_G in Wt. assumption. assumption.
Qed.

Lemma stack_binds_to_ctx_binds_raw: forall s G S x v,
  wf_stack G S s ->
  binds x v s ->
  exists G1 G2 T, G = G1 & (x ~ T) & G2 /\ ty_trm ty_precise sub_general G1 S (trm_val v) T.
Proof.
  introv Wf Bi. gen x v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [T0' [Eq Ty]]]].
      subst. exists G1 (G2 & x ~ T) T0'. rewrite concat_assoc. auto.
  + specialize (IHWf x v Bi). destruct IHWf as [G1 [G2 [T0 [HG Hty]]]].
    exists G1 G2 T0. split.
    - assumption.
    - apply* weaken_ty_trm_sigma.
Qed.


Lemma typing_implies_bound: forall m1 m2 G S x T,
  ty_trm m1 m2 G S (trm_var (avar_f x)) T ->
  exists V, binds x V G.
Proof.
  intros. remember (trm_var (avar_f x)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

Lemma typing_implies_bound_loc: forall m1 m2 G S l T,
  ty_trm m1 m2 G S (trm_val (val_loc l)) T ->
  exists T', binds l T' S.
Proof.
  intros. remember (trm_val (val_loc l)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.


(* ###################################################################### *)
(** ** Substitution *)

Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

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

Definition subst_env (z: var) (u: var) (e: env typ) : env typ := map (subst_typ z u) e.

(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_avar.
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
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec).
Qed.

Definition subst_fresh_trm (x y: var) := proj41 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_val (x y: var) := proj42 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_def (x y: var) := proj43 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_defs(x y: var) := proj44 (subst_fresh_trm_val_def_defs x y).

Lemma invert_fv_env_types_push: forall x z T G,
  x \notin fv_env_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_env_types G).
Proof.
  introv N.
  unfold fv_env_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

Lemma subst_fresh_env: forall x y e,
  x \notin fv_env_types e -> subst_env x y e = e.
Proof.
  intros x y.
  apply (env_ind (fun e => x \notin fv_env_types e -> subst_env x y e = e)).
  + intro N. unfold subst_env. apply map_empty.
  + intros e z T IH N.
    apply invert_fv_env_types_push in N. destruct N as [N1 N2].
    unfold subst_env in *. rewrite map_push.
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

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_avar.
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec.
Qed.

Lemma subst_open_commute_dec: forall x y u D,
  subst_dec x y (open_dec u D) = open_dec (subst_fvar x y u) (subst_dec x y D).
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
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ_dec).
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

Lemma subst_rules: forall y U,
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & subst_env x y G2) (S1 & subst_env x y S2) (trm_var (avar_f y)) (subst_typ x y U) ->
    m1 = ty_general ->
    m2 = sub_general ->
    ty_trm m1 m2 (G1 & subst_env x y G2) (S1 & subst_env x y S2) (subst_trm x y t) (subst_typ x y T)) /\
  (forall G S d D, ty_def G S d D -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & subst_env x y G2) (S1 & subst_env x y S2) (trm_var (avar_f y)) (subst_typ x y U) ->
    ty_def (G1 & subst_env x y G2) (S1 & subst_env x y S2) (subst_def x y d) (subst_dec x y D)) /\
  (forall G S ds T, ty_defs G S ds T -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & subst_env x y G2) (S1 & (subst_env x y S2)) (trm_var (avar_f y)) (subst_typ x y U) ->
    ty_defs (G1 & subst_env x y G2) (S1 & subst_env x y S2) (subst_defs x y ds) (subst_typ x y T)) /\
  (forall m1 m2 G S T V, subtyp m1 m2 G S T V -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & subst_env x y G2) (S1 & subst_env x y S2) (trm_var (avar_f y)) (subst_typ x y U) ->
    m1 = ty_general ->
    m2 = sub_general ->
    subtyp m1 m2 (G1 & subst_env x y G2) (S1 & subst_env x y S2) (subst_typ x y T) (subst_typ x y V)).
Proof.
  intros y S. apply rules_mutind; intros; subst.
  - (* ty_var *)
    simpl. case_if.
    + apply binds_middle_eq_inv in b. subst. assumption. assumption.
    + apply subst_fresh_env with (y:=y) in H1.
      apply binds_subst in b.
      apply ty_var. rewrite <- H1.
      unfold subst_env. rewrite <- map_concat.
      apply binds_map. assumption. assumption.
  - (* ty_loc *)
    simpl. apply ty_loc. apply subst_fresh_env with (y:=y) in H3.
    rewrite <- H3. unfold subst_env. rewrite <- map_concat. apply binds_map. assumption.
  - (* ty_all_intro *)
    simpl.
    apply_fresh ty_all_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    rewrite <- A at 3. rewrite <- subst_open_commute_typ.
    assert (subst_env x y G2 & z ~ subst_typ x y T = subst_env x y (G2 & z ~ T)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. auto.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_env. eauto.
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
    assert (subst_env x y G2 & z ~ subst_typ x y (open_typ z T) = subst_env x y (G2 & z ~ open_typ z T)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B. rename S into V.
    apply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. auto.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_env. eauto.
  - (* ty_new_elim *)
    simpl. apply ty_new_elim.
    apply H; eauto.
  - (* ty_let *)
    simpl.
    apply_fresh ty_let as z; eauto.
    assert (subst_env x y G2 & z ~ subst_typ x y T = subst_env x y (G2 & z ~ T)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    apply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. auto.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_env. eauto.
  - (* ty_rec_intro *)
    simpl. apply ty_rec_intro.
    assert (trm_var (avar_f (If x = x0 then y else x)) = subst_trm x0 y (trm_var (avar_f x))) as A. {
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
    assert (trm_var (avar_f (If x = x0 then y else x)) = subst_trm x0 y (trm_var (avar_f x))) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    apply ty_and_intro; eauto.
  - (* ty_sub *)
    eapply ty_sub; eauto.
    intro Contra. inversion Contra.
  - (* ty_ref *)
    simpl. constructor.
    assert (trm_var (avar_f (If x = x0 then y else x)) = subst_trm x0 y (trm_var (avar_f x))) as A by (simpl; reflexivity).
    rewrite A.
    apply H; auto.
  - (* ty_ref_elim *)
    apply ty_ref_elim; eauto.
  - (* ty_asgn *)
    apply ty_asgn; eauto.
  - (* ty_def_typ *)
    simpl. apply ty_def_typ; eauto.
  - (* ty_def_trm *)
    simpl. apply ty_def_trm; eauto.
  - (* ty_defs_one *)
    simpl. apply ty_defs_one; eauto.
  - (* ty_defs_cons *)
    simpl. apply ty_defs_cons; eauto.
    rewrite <- subst_label_of_def.
    apply subst_defs_hasnt. assumption.
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
  - (* subtyp_sel2_tight *) inversion H7.
  - (* subtyp_sel1_tight *) inversion H7.
  - (* subtyp_all *)
    simpl. apply_fresh subtyp_all as z; eauto.
    assert (z \notin L) as FrL by auto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. auto.
    }
    rewrite <- A at 2. rewrite <- A at 3.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_env x y G2 & z ~ subst_typ x y S2 = subst_env x y (G2 & z ~ S2)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. auto.
    apply ok_push. apply ok_concat_map. auto. unfold subst_env. auto.
  - (* subtyp_ref *) apply subtyp_ref; auto.
Qed.


Lemma subst_ty_trm: forall y V G S x t T,
    ty_trm ty_general sub_general (G & x ~ V) S t T ->
    ok (G & x ~ V) ->
    x \notin fv_env_types G ->
    x \notin fv_env_types S ->
    ty_trm ty_general sub_general G S (trm_var (avar_f y)) (subst_typ x y V) ->
    ty_trm ty_general sub_general G S (subst_trm x y t) (subst_typ x y T).
Proof.
  intros.
  apply (proj51 (subst_rules y V)) with (G1:=G) (G2:=empty) (S1:=S) (S2:=empty) (x:=x) in H; try assumption.
  unfold subst_env in H. rewrite map_empty in H. repeat rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  rewrite concat_empty_r. reflexivity.
  unfold subst_env. rewrite map_empty. repeat rewrite concat_empty_r. assumption.
  reflexivity.
  reflexivity.
Qed.

Lemma subst_ty_defs: forall y V G S x ds T,
    ty_defs (G & x ~ V) S ds T ->
    ok (G & x ~ V) ->
    x \notin fv_env_types G ->
    x \notin fv_env_types S ->
    ty_trm ty_general sub_general G S (trm_var (avar_f y)) (subst_typ x y V) ->
    ty_defs G S (subst_defs x y ds) (subst_typ x y T).
Proof.
  intros.
  apply (proj53 (subst_rules y V)) with (G1:=G) (G2:=empty) (S1:=S) (S2:=empty) (x:=x) in H;
  try (rewrite concat_empty_r; auto).
  unfold subst_env in H. rewrite map_empty in H. repeat rewrite concat_empty_r in H.
  apply H.
  assumption. assumption.
  unfold subst_env. rewrite map_empty. repeat rewrite concat_empty_r. assumption.
Qed.

(* ###################################################################### *)
(** ** Some Lemmas *)


Lemma inversion_loc_typing: forall G S x V T,
  binds x (typ_ref V) G ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) T ->
  exists U, T = typ_ref U.
Proof. 
  introv Bi Hty.
  remember (trm_var (avar_f x)) as t.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hty; try solve [inversion Heqt; inversion Heqm1].
  - inversions Heqt.
    unfold binds in Bi. unfold binds in H.
    rewrite H in Bi. inversion Bi.
    exists V. reflexivity.
  - exists T. subst. inversion Heqt; subst.
    assert (ty_precise = ty_precise) as Hobv by reflexivity.
     assert (sub_general = sub_general) as Hobv1 by reflexivity.

specialize (IHHty Bi Heqt  Hobv Hobv1). destruct IHHty. inversion H.
  - subst. clear H.
    assert (ty_precise = ty_precise) as Hobv by reflexivity.
    assert (sub_general = sub_general) as Hobv1 by reflexivity.
    assert (trm_var (avar_f x) =  trm_var (avar_f x)) as Hobv2 by reflexivity.
    specialize (IHHty Bi Hobv2 Hobv Hobv1). destruct IHHty as [U0 HT]. 
    subst.
    clear Hobv Hobv1 Hobv2.
    dependent induction H0.
    specialize (IHsubtyp1 Bi Hty). destruct IHsubtyp1. subst.
    assert (typ_ref x0 = typ_ref x0 ) as Hobv by reflexivity.
    specialize (IHsubtyp2 Bi x0 Hobv).
    assert (ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_ref x0)) as H1. {
      apply ty_sub with (T:=typ_ref U0). intro. exists x. reflexivity. assumption.
      assumption.
    }
    apply (IHsubtyp2 H1).
Qed.

Lemma loc_intro_inversion: forall G S l T,
  ty_trm ty_precise sub_general G S (trm_val (val_loc l)) T ->
  exists U, T = typ_ref U.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H. 
Qed.

Lemma corresponding_types_ctx: forall G S s x T,
  wf_stack G S s ->
  binds x T G ->
  ((exists V U t, binds x (val_lambda V t) s /\
                  ty_trm ty_precise sub_general G S (trm_val (val_lambda V t)) (typ_all V U) /\
                  T = typ_all V U) \/
   (exists V ds, binds x (val_new V ds) s /\
                 ty_trm ty_precise sub_general G S (trm_val (val_new V ds)) (typ_bnd V) /\
                 T = typ_bnd V)) \/
   (exists V l, binds x (val_loc l) s /\
                 ty_trm ty_precise sub_general G S (trm_val (val_loc l)) (typ_ref V) /\
                 T = typ_ref V).
Proof.
  introv H Bi.
  induction H.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *.
    assert (ok G) as OkG by (apply wf_stack_to_ok_G in H; assumption).
    case_if.
    + inversions Bi. inversion H2; subst.
      * right. exists T0 l. split.
        reflexivity.
        split. apply weaken_ty_trm_ctx. assumption.
        constructor; assumption. reflexivity.
      * left. left. exists T0. exists U. exists t.
        split. auto. split.
        apply weaken_ty_trm_ctx.
        assumption.
        constructor; assumption. reflexivity.
      * left. right. exists T0. exists ds.
        split. auto. split.
        apply weaken_ty_trm_ctx. assumption. constructor; assumption. reflexivity.
      * destruct H3. reflexivity. inversion H3.
    + specialize (IHwf_stack Bi).
      inversion IHwf_stack as [IH | IH]. inversion IH as [IH' | IH']. (* todo better syntax? *)
      * destruct IH' as [V [U [t [IH1 [IH2 IH3]]]]].
        left. left. exists V. exists U t.
        split. assumption. split.
        apply weaken_ty_trm_ctx; auto. assumption.
      * destruct IH' as [V [ds [IH1 [IH2 IH3]]]].
        left. right. exists V ds.
        split. assumption. split.
        apply weaken_ty_trm_ctx; auto. assumption.
      * destruct IH as [V [l [t [IH2 IH3]]]].
        right. exists V l. split.
        assumption. split.
        apply weaken_ty_trm_ctx; auto. assumption.
  - specialize (IHwf_stack Bi).
      lets OkS: (wf_stack_to_ok_S H).
      inversion IHwf_stack as [IH | IH]. inversion IH as [IH' | IH']. (* todo better syntax? *)
      * destruct IH' as [V [U [t [IH1 [IH2 IH3]]]]].
        left. left. exists V. exists U t.
        split. assumption. split.
        apply weaken_ty_trm_sigma; auto. assumption.
      * destruct IH' as [V [ds [IH1 [IH2 IH3]]]].
        left. right. exists V ds.
        split. assumption. split.
        apply weaken_ty_trm_sigma; auto. assumption.
      * destruct IH as [V [l' [t [IH2 IH3]]]].
        right. exists V l'. split.
        assumption. split.
        apply weaken_ty_trm_sigma; auto. assumption.
Qed.


Lemma unique_rec_subtyping: forall G S V T,
  subtyp ty_precise sub_general G S (typ_bnd V) T ->
  T = typ_bnd V.
Proof.
  introv Hsub.
  remember (typ_bnd V) as T'.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1 Heqm2). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_all_subtyping: forall G S V U T,
  subtyp ty_precise sub_general G S (typ_all V U) T ->
  T = typ_all V U.
Proof.
  introv Hsub.
  remember (typ_all V U) as T'.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1 Heqm2). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.


Lemma unique_lambda_typing: forall G x S V U T,
  binds x (typ_all V U) G ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) T ->
  T = typ_all V U.
Proof.
  introv Bi Hty.
  remember (trm_var (avar_f x)) as t.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hty; try solve [inversion Heqt; inversion Heqm1].
  - inversions Heqt.
    unfold binds in Bi. unfold binds in H.
    rewrite H in Bi. inversion Bi.
    reflexivity.
  - specialize (IHHty Bi Heqt Heqm1 Heqm2).
    inversion IHHty.
  - specialize (IHHty Bi Heqt Heqm1 Heqm2).
    rewrite IHHty in H0. rewrite Heqm1 in H0. rewrite Heqm2 in H0.
    apply unique_all_subtyping in H0.
    apply H0.
Qed.

Lemma lambda_not_rcd: forall G x S V U A T,
  binds x (typ_all V U) G ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) ->
  False.
Proof.
  introv Bi Hty.
  assert (typ_rcd (dec_typ A T T) = typ_all V U) as Contra. {
    eapply unique_lambda_typing; eassumption.
  }
  inversion Contra.
Qed.

Lemma sub_top: forall G S T,
  subtyp ty_precise sub_general G S typ_top T ->
  T = typ_top.
Proof.
  introv Hsub.
  dependent induction Hsub. subst. assert (typ_top = typ_top) as Hobv by reflexivity.
  specialize (IHHsub2 Hobv). assumption.
Qed.

Lemma loc_not_rcd: forall G S x V A T,
  binds x (typ_ref V) G ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) ->
  False.
Proof.
  introv Bi Hty.
  assert (typ_rcd (dec_typ A T T) = typ_ref V) as Contra. {
    destruct (inversion_loc_typing Bi Hty) as [U H]. inversion H.
  }
  inversion Contra.
Qed.


Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T)
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
  - simpl in H2; induction T2; simpl in H2; inversion H2.
    f_equal.
    eapply H; eauto using notin_union_r1.
  - simpl in H1; induction T2; simpl in H1; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
 - simpl in H1; induction T2; simpl in H1; inversion H1.
    f_equal. eapply open_eq_avar; eauto.
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

Lemma label_same_typing: forall G S d D,
  ty_def G S d D -> label_of_def d = label_of_dec D.
Proof.
  intros. inversion H; subst; simpl; reflexivity.
Qed.

Lemma record_defs_typing_rec: forall G S ds V,
  ty_defs G S ds V ->
  exists ls, record_typ V ls /\ forall l, l \notin ls <-> defs_hasnt ds l.
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

Lemma record_defs_typing: forall G S ds V,
  ty_defs G S ds V ->
  record_type V.
Proof.
  intros.
  assert (exists ls, record_typ V ls /\ forall l, l \notin ls <-> defs_hasnt ds l) as A.
  eapply record_defs_typing_rec; eauto.
  destruct A as [ls [A1 A2]].
  exists ls. apply A1.
Qed.

Lemma record_new_typing: forall G S V ds,
  ty_trm ty_precise sub_general G S (trm_val (val_new V ds)) (typ_bnd V) ->
  record_type V.
Proof.
  intros.
  inversion H; subst.
  + pick_fresh x.
    apply open_record_type_rev with (x:=x).
    eauto.
    eapply record_defs_typing. eapply H5. eauto.
  + assert (ty_precise = ty_precise) as Hobv by reflexivity. specialize (H0 Hobv).
    destruct H0. inversion H0.
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

Lemma record_subtyping: forall G S T T',
  subtyp ty_precise sub_general G S T T' ->
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

Lemma shape_new_typing: forall G S x V T,
  binds x (typ_bnd V) G ->
  record_type V ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) T ->
  T = typ_bnd V \/ record_sub (open_typ x V) T.
Proof.
  introv Bi HS Hx. dependent induction Hx.
  - unfold binds in H. unfold binds in Bi. rewrite H in Bi. inversion Bi.
    left. reflexivity.
  - assert (typ_bnd T = typ_bnd V \/ record_sub (open_typ x V) (typ_bnd T)) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + inversion A. right. apply rs_refl.
    + apply record_type_sub_not_rec in A. inversion A. assumption.
  - assert (T = typ_bnd V \/ record_sub (open_typ x V) T) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + subst. apply unique_rec_subtyping in H0. left. assumption.
    + right. eapply record_sub_trans. eassumption.
      eapply record_subtyping. eassumption.
      eapply record_type_sub_closed. eassumption.
      eapply open_record_type. assumption.
Qed.

Lemma unique_tight_bounds: forall G S sta x T1 T2 A,
  wf_stack G S sta ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Hwf Hty1 Hty2.
  assert (exists T, binds x T G) as Bi. {
    eapply typing_implies_bound. eassumption.
  }
  destruct Bi as [T Bi].
  destruct (corresponding_types_ctx Hwf Bi) as [[Hlam | Hnew] | Hloc].
  - destruct Hlam as [V [U [t [Bis [Ht EqT]]]]].
    * false. eapply lambda_not_rcd.
      subst. eassumption. eassumption.
  - destruct Hnew as [V [ds [Bis [Ht EqT]]]]. subst.
    assert (record_type V) as Htype. {
      eapply record_new_typing. eassumption.
    }
    destruct (shape_new_typing Bi Htype Hty1) as [Contra1 | A1].
    inversion Contra1.
    destruct (shape_new_typing Bi Htype Hty2) as [Contra2 | A2].
    inversion Contra2.
    assert (record_type (open_typ x V)) as HXtype. {
      apply open_record_type. assumption.
    }
    eapply unique_rcd_typ.
    apply HXtype.
    eassumption.
    eassumption.
  - destruct Hloc as [V [l [HBi [Hty HT]]]].
    subst. false. eapply loc_not_rcd.
    subst. eassumption. eassumption.
Qed.

Lemma precise_to_general:
  (forall m1 m2 G S t T,
     ty_trm m1 m2 G S t T ->
     m1 = ty_precise ->
     m2 = sub_general ->
     ty_trm ty_general sub_general G S t T) /\
  (forall m1 m2 G S V U,
     subtyp m1 m2 G S V U ->
     m1 = ty_precise ->
     m2 = sub_general ->
     subtyp ty_general sub_general G S V U).
Proof.
  apply ts_mutind; intros; subst; eauto.
Qed.

Lemma precise_to_general_typing: forall G S t T,
  ty_trm ty_precise sub_general G S t T ->
  ty_trm ty_general sub_general G S t T.
Proof.
  intros. apply* precise_to_general.
Qed.

Lemma tight_to_general:
  (forall m1 m2 G S t T,
     ty_trm m1 m2 G S t T ->
     m1 = ty_general ->
     m2 = sub_tight ->
     ty_trm ty_general sub_general G S t T) /\
  (forall m1 m2 G S V U,
     subtyp m1 m2 G S V U ->
     m1 = ty_general ->
     m2 = sub_tight ->
     subtyp ty_general sub_general G S V U).
Proof.
  apply ts_mutind; intros; subst; eauto.
  - apply precise_to_general in t; eauto.
  - apply precise_to_general in t; eauto.
Qed.

Lemma tight_to_general_subtyping: forall G S V U,
  subtyp ty_general sub_tight G S V U ->
  subtyp ty_general sub_general G S V U.
Proof.
  intros. apply* tight_to_general.
Qed.

Lemma stack_binds_to_ctx_binds: forall G S s x v,
  wf_stack G S s -> binds x v s -> exists V, binds x V G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  apply stack_binds_to_ctx_binds_raw with (x:=x) (v:=v) in Hwf.
  destruct Hwf as [G1 [G2 [T [EqG Hty]]]].
  subst.
  exists T.
  eapply binds_middle_eq. apply wf_stack_to_ok_G in Hwf'.
  apply ok_middle_inv in Hwf'. destruct Hwf'. assumption.
  assumption.
Qed.

Lemma record_type_new: forall G S s x T ds,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  record_type (open_typ x T).
Proof.
  introv Hwf Bis.
  destruct (stack_binds_to_ctx_binds Hwf Bis) as [V Bi].
  destruct (corresponding_types_ctx Hwf Bi) as [[Hlambda | Hnew] | Hloc].
  - destruct Hlambda as [? [? [? [Bis' ?]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  - destruct Hnew as [? [? [Bis' [? ?]]]]. subst.
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
    apply record_new_typing in H.
    apply open_record_type. assumption.
  - destruct Hloc as [? [? [Bil [?]]]].
    unfold binds in *. rewrite Bil in Bis. inversion Bis.
Qed.

(* ###################################################################### *)
(** ** Narrowing *)

Definition subenv(G1 G2: ctx) (S: sigma) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ subtyp ty_general sub_general G1 S T1 T2.

Lemma subenv_push: forall G G' S x T,
  subenv G' G S ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T) S.
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
      exists T'. split. eauto. apply weaken_subtyp_ctx. assumption. eauto.
Qed.

Lemma subenv_last: forall G S x V U,
  subtyp ty_general sub_general G S V U ->
  ok (G & x ~ V) ->
  subenv (G & x ~ V) (G & x ~ U) S.
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists V. split; eauto.
    apply weaken_subtyp_ctx; eauto.
  - destruct Bi. left. eauto.
Qed.


Lemma narrow_rules:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G',
    m1 = ty_general ->
    m2 = sub_general ->
    ok G' ->
    subenv G' G S ->
    ty_trm m1 m2 G' S t T)
/\ (forall G S d D, ty_def G S d D -> forall G',
    ok G' ->
    subenv G' G S ->
    ty_def G' S d D)
/\ (forall G S ds T, ty_defs G S ds T -> forall G',
    ok G' ->
    subenv G' G S ->
    ty_defs G' S ds T)
/\ (forall m1 m2 G S V U, subtyp m1 m2 G S V U -> forall G',
    m1 = ty_general ->
    m2 = sub_general ->
    ok G' ->
    subenv G' G S ->
    subtyp m1 m2 G' S V U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. unfold subenv in H2. specialize (H2 x T b).
    destruct H2.
    + auto.
    + destruct H as [T' [Bi Hsub]].
      eapply ty_sub; eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; auto.
    apply H; auto. apply subenv_push; auto.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as y; auto.
    apply H; auto. apply subenv_push; auto.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; auto.
    apply H0 with (x:=y); auto. apply subenv_push; auto.
  - inversion H1 (* sub_tight *).
  - inversion H1 (* sub_tight *).
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; auto.
    apply H0; auto. apply subenv_push; auto.
Qed.

Lemma narrow_typing: forall G G' S t T,
  ty_trm ty_general sub_general G S t T ->
  subenv G' G S -> ok G' ->
  ty_trm ty_general sub_general G' S t T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall G G' S V U,
  subtyp ty_general sub_general G S V U ->
  subenv G' G S -> ok G' ->
  subtyp ty_general sub_general G' S V U.
Proof.
  intros. apply* narrow_rules.
Qed.

(* ###################################################################### *)
(** * Has member *)

Inductive has_member: ctx -> sigma -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_any : forall G S x T A V U,
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) T ->
  has_member_rules G S x T A V U ->
  has_member G S x T A V U
with has_member_rules: ctx -> sigma ->var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_refl : forall G S x A V U,
  has_member_rules G S x (typ_rcd (dec_typ A V U)) A V U
| has_and1 : forall G S x T1 T2 A V U,
  has_member G S x T1 A V U ->
  has_member_rules G S x (typ_and T1 T2) A V U
| has_and2 : forall G S x T1 T2 A V U,
  has_member G S x T2 A V U ->
  has_member_rules G S x (typ_and T1 T2) A V U
| has_bnd : forall G S x T A V U,
  has_member G S x (open_typ x T) A V U ->
  has_member_rules G S x (typ_bnd T) A V U
| has_sel : forall G S x y B T' A V U,
  ty_trm ty_precise sub_general G S (trm_var (avar_f y)) (typ_rcd (dec_typ B T' T')) ->
  has_member G S x T' A V U ->
  has_member_rules G S x (typ_sel (avar_f y) B) A V U
| has_bot  : forall G S x A V U,
  has_member_rules G S x typ_bot A V U.


Scheme has_mut := Induction for has_member Sort Prop
with hasr_mut := Induction for has_member_rules Sort Prop.
Combined Scheme has_mutind from has_mut, hasr_mut.

Lemma has_member_rules_inv: forall G S x T A V U, has_member_rules G S x T A V U ->
  (T = typ_rcd (dec_typ A V U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G S x T1 A V U \/
     has_member G S x T2 A V U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G S x (open_typ x T') A V U) \/
  (exists y B T', T = typ_sel (avar_f y) B /\
    ty_trm ty_precise sub_general G S (trm_var (avar_f y)) (typ_rcd (dec_typ B T' T')) /\
    has_member G S x T' A V U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst.
  - left. auto.
  - right. left. exists T1 T2. auto.
  - right. left. exists T1 T2. auto.
  - right. right. left. exists T0. auto.
  - right. right. right. left. exists y B T'. auto.
  - right. right. right. right. reflexivity.
Qed.

Lemma has_member_inv: forall G S x T A V U, has_member G S x T A V U ->
  (T = typ_rcd (dec_typ A V U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G S x T1 A V U \/
     has_member G S x T2 A V U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G S x (open_typ x T') A V U) \/
  (exists y B T', T = typ_sel (avar_f y) B /\
    ty_trm ty_precise sub_general G S (trm_var (avar_f y)) (typ_rcd (dec_typ B T' T')) /\
    has_member G S x T' A V U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst. apply has_member_rules_inv in H1. apply H1.
Qed.

Lemma val_new_typing: forall G S s x T ds,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise sub_general G S (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types_ctx Hwf Bi) as [[Hnew | Hlambda] | Hloc].
  - destruct Hnew as [V [U [t [Bis' [Ht EqT]]]]].
    false.
  - destruct Hlambda as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis.
    inversion Bis. subst.
    assumption.
  - destruct Hloc as [V [l [Bi' [Htyp]]]].
    false.
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
  (forall G S x T A V U,
    has_member G S x T A V U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A V U))) /\
  (forall G S x T A V U,
    has_member_rules G S x T A V U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A V U))).
Proof.
  apply has_mutind; intros.
  - apply H; eauto.
  - apply rs_refl.
  - inversion H0; subst. inversion H1; subst. apply rs_drop.
    apply H; auto.
    exists ls. assumption.
  - inversion H0; subst. inversion H1; subst. inversion h; subst. inversion H3; subst.
    eapply rs_dropl. apply rs_refl.
  - inversion H0. inversion H1.
  - inversion H0. inversion H1.
  - destruct H as [ls H]. inversion H.
Qed.

Lemma has_member_tightness: forall G S s x T ds A V U,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  has_member G S x (typ_bnd T) A V U ->
  V = U.
Proof.
  introv Hwf Bis Hmem.
  assert (record_type T) as Htype. {
    eapply record_new_typing. eapply val_new_typing; eauto.
  }
  assert (record_type (open_typ x T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (has_member G S x (open_typ x T) A V U) as Hmemx. {
    inversion Hmem; subst. inversion H0; subst. assumption.
  }
  assert (record_sub (open_typ x T) (typ_rcd (dec_typ A V U))) as Hsub. {
    destruct has_member_rcd_typ_sub_mut as [HL _].
    eapply HL; eauto.
  }
  eapply rcd_typ_eq_bounds. apply Htypex. apply Hsub.
Qed.

Lemma has_member_covariance: forall G S s T1 T2 x A S2 U2,
  wf_stack G S s ->
  subtyp ty_general sub_tight G S T1 T2 ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) T1 ->
  has_member G S x T2 A S2 U2 ->
  exists S1 U1, has_member G S x T1 A S1 U1 /\
                subtyp ty_general sub_tight G S S2 S1 /\
                subtyp ty_general sub_tight G S U1 U2.
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
    split; apply subtyp_refl.
  - (* refl *)
    exists S2 U2. eauto.
  - (* trans *)
    assert (ty_trm ty_general sub_tight G S (trm_var (avar_f x)) T) as HS. {
      eapply ty_sub. intros Hp. subst. eexists; eauto.
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
    + destruct Hmem as [y [B [T' [Heq _]]]]. inversion Heq.
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
    + destruct Hmem as [y [B [T' [Heq _]]]]. inversion Heq.
    + inversion Hmem.
  - (* sel2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversions Heq.
      assert (T' = T) as HeqT. {
        eapply unique_tight_bounds; eassumption.
      }
      subst. eauto.
    + inversion Hmem.
  - (* sel1 *)
    exists S2 U2. split.
    eapply has_any. assumption. eapply has_sel. eassumption. eassumption.
    eauto.
  - (* all *)
    inversion Hmem; subst. inversion H2; subst.
  - (* ref *) 
    inversion Hmem; subst. inversion H0.
Qed.

Lemma has_member_monotonicity: forall G S s x T0 ds T A V U,
  wf_stack G S s ->
  binds x (val_new T0 ds) s ->
  has_member G S x T A V U ->
  exists T1, has_member G S x (typ_bnd T0) A T1 T1 /\
             subtyp ty_general sub_tight G S V T1 /\
             subtyp ty_general sub_tight G S T1 U.
Proof.
  introv Hwf Bis Hmem. inversion Hmem; subst.
  generalize dependent U. generalize dependent V.
  dependent induction H; intros.
  - (* var *)
    destruct (corresponding_types_ctx Hwf H). destruct H1 as [Hlam | Hnew].
    * destruct Hlam as [S0 [U0 [t [Bis' _]]]].
      unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversion Bis.
    * destruct Hnew as [S0 [ds0 [Bis' [Hty Heq]]]]. unfold binds in Bis'. unfold binds in Bis.
      rewrite Bis in Bis'. inversions Bis'.
      assert (V = U). {
        eapply has_member_tightness. eassumption. eassumption.
        eapply has_any.
        eapply ty_var. eassumption.
        eassumption.
      }
      subst. exists U. eauto.
    * destruct H1 as [V0 [l [Bi' [Htyp]]]].
      unfold binds in Bis. unfold binds in Bi'. rewrite Bi' in Bis. inversion Bis.
  - (* rec_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversions Heq.
      apply IHty_trm; eauto.
      inversions H0. assumption.
      inversions H0. inversions H5. assumption.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* rec_elim *)
    apply IHty_trm; eauto.
    apply has_any. assumption. apply has_bnd. assumption.
    apply has_bnd. assumption.
  - (* and_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq [Hmem | Hmem]]]];
      inversions Heq; inversions H1; inversions H10.
      apply IHty_trm1; eauto.
      apply IHty_trm2; eauto. apply has_any; assumption.
      apply IHty_trm1; eauto. apply has_any; assumption.
      apply IHty_trm2; eauto.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* sub *)
    destruct (has_member_covariance Hwf H1 H0 Hmem) as [S' [U' [Hmem' [Hsub1' Hsub2']]]].
    inversion Hmem'; subst.
    specialize (IHty_trm Hwf Bis S' U' Hmem' H4).
    destruct IHty_trm as [T1 [Hmem1 [Hsub1 Hsub2]]].
    exists T1. eauto.
Qed.

(* ###################################################################### *)
(** * Tight bound completeness *)

Lemma has_member_rcd_typ_sub2_mut:
  (forall G S x T A V U,
    has_member G S x T A V U ->
    record_type T ->
    T = (typ_rcd (dec_typ A V U)) \/ subtyp ty_precise sub_general G S T (typ_rcd (dec_typ A V U)))  /\
  (forall G S x T A V U,
    has_member_rules G S x T A V U ->
    record_type T ->
    T = (typ_rcd (dec_typ A V U)) \/ subtyp ty_precise sub_general G S T (typ_rcd (dec_typ A V U))).
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

Lemma wf_stack_val_new_in_G: forall G S s x T ds,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [V Bi].
  destruct (corresponding_types_ctx Hwf Bi). destruct H as [Hlam | Hnew].
  - destruct Hlam as [? [? [? [Bis' _]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversion Bis'.
  - destruct Hnew as [T' [ds' [Bis' [Hty Heq]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
    assumption.
  - destruct H as [V0 [l [Bi' [Hty]]]].
    unfold binds in Bi'. unfold binds in Bis. rewrite Bi' in Bis. inversion Bis.
Qed.

(* If G, S ~ s, s |- x = new(x: T)d, and G, S |-# x: {A: V..U} then G |-# x.A <: U and G, S |-# V <: x.A. *)
Lemma tight_bound_completeness: forall G S s x T ds A V U,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_rcd (dec_typ A V U)) ->
  subtyp ty_general sub_tight G S (typ_sel (avar_f x) A) U /\
  subtyp ty_general sub_tight G S V (typ_sel (avar_f x) A).
Proof.
  introv Hwf Bis Hty.
  assert (has_member G S x (typ_rcd (dec_typ A V U)) A V U) as Hmem. {
    apply has_any. assumption. apply has_refl.
  }
  apply has_member_monotonicity with (s:=s) (ds:=ds) (T0:=T) in Hmem.
  destruct Hmem as [T1 [Hmem [Hsub1 Hsub2]]].
  assert (has_member G S x (open_typ x T) A T1 T1) as Hmemx. {
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
  assert (open_typ x T = (typ_rcd (dec_typ A T1 T1)) \/ subtyp ty_precise sub_general G S (open_typ x T) (typ_rcd (dec_typ A T1 T1))) as Hsub. {
    destruct has_member_rcd_typ_sub2_mut as [HE _].
    eapply HE; eauto.
  }
  assert (ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (open_typ x T)) as Htypx. {
    eapply ty_rec_elim.
    eapply ty_var.
    eapply wf_stack_val_new_in_G; eauto.
  }
  assert (ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T1 T1))) as Htyp. {
    destruct Hsub as [Heq | Hsub].
    - rewrite Heq in Htypx. apply Htypx.
    - eapply ty_sub.
      intro. eexists. reflexivity.
      eapply Htypx. eapply Hsub.
  }
  split.
  eapply subtyp_trans. eapply subtyp_sel1_tight. eapply Htyp. eapply Hsub2.
  eapply subtyp_trans. eapply Hsub1. eapply subtyp_sel2_tight. eapply Htyp.
  eapply Hwf. eapply Bis.
Qed.

(* ###################################################################### *)
(** * Misc Inversions *)

Lemma all_intro_inversion: forall G S V t U,
  ty_trm ty_precise sub_general G S (trm_val (val_lambda V t)) U ->
  exists T, U = typ_all V T.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
Qed.

Lemma new_intro_inversion: forall G S T ds U,
  ty_trm ty_precise sub_general G S (trm_val (val_new T ds)) U ->
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
For a variable x, non-variable value v, environment G, store typing S, the set Ts(G, S, x, v) of possible types of x defined as v in G and S is the smallest set SS such that:
If v = new(x: T)d then T in SS.
If v = new(x: T)d and {a = t} in d and G, S |- t: T' then {a: T'} in SS.
If v = new(x: T)d and {A = T'} in d and G, S |- V <: T', G |- T' <: U then {A: V..U} in SS.
If v = lambda(x: S)t and (G, x: V), S |- t: T and G, S |- V' <: V and G, x: V' |- T <: T' then all(x: V')T' in SS.
If v = loc l; G, S |- T <: U; G, S |- U <: T; and G, S |-! l: Ref T, then Ref U in SS.
If S1 in SS and S2 in SS then S1 & S2 in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
If S in SS then rec(x: S) in SS.
*)

(* todo check def of pt_loc *)
Inductive possible_types: ctx -> sigma -> var -> val -> typ -> Prop :=
| pt_top : forall G S x v,
  possible_types G S x v typ_top
| pt_new : forall G S x T ds,
  possible_types G S x (val_new T ds) (open_typ x T)
| pt_rcd_trm : forall G S x T ds a t T',
  defs_has (open_defs x ds) (def_trm a t) ->
  ty_trm ty_general sub_general G S t T' ->
  possible_types G S x (val_new T ds) (typ_rcd (dec_trm a T'))
| pt_rcd_typ : forall G S x T ds A T' V U,
  defs_has (open_defs x ds) (def_typ A T') ->
  subtyp ty_general sub_general G S V T' ->
  subtyp ty_general sub_general G S T' U ->
  possible_types G S x (val_new T ds) (typ_rcd (dec_typ A V U))
| pt_lambda : forall L G S x V t T V' T',
  (forall y, y \notin L ->
  ty_trm ty_general sub_general (G & y ~ V) S (open_trm y t) (open_typ y T)) ->
  subtyp ty_general sub_general G S V' V ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ V') S (open_typ y T) (open_typ y T')) ->
  possible_types G S x (val_lambda V t) (typ_all V' T')
| pt_loc : forall G S x l T,
  ty_trm ty_precise sub_general G S (trm_val (val_loc l)) (typ_ref T) ->
  possible_types G S x (val_loc l) (typ_ref T)
| pt_loc_sub : forall G S x l T U,
  possible_types G S x (val_loc l) (typ_ref T) ->
  subtyp ty_general sub_general G S T U ->
  subtyp ty_general sub_general G S U T ->
  possible_types G S x (val_loc l) (typ_ref U)
| pt_and : forall G S x v V1 V2,
  possible_types G S x v V1 ->
  possible_types G S x v V2 ->
  possible_types G S x v (typ_and V1 V2)
| pt_sel : forall G S x v y A V,
  possible_types G S x v V ->
  ty_trm ty_precise sub_general G S (trm_var y) (typ_rcd (dec_typ A V V)) ->
  possible_types G S x v (typ_sel y A)
| pt_bnd : forall G S x v V V',
  possible_types G S x v V ->
  V = open_typ x V' ->
  possible_types G S x v (typ_bnd V').

Lemma var_new_typing: forall G S s x T ds,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (open_typ x T).
Proof.
  intros.
  apply ty_rec_elim. apply ty_var. eapply wf_stack_val_new_in_G; eauto.
Qed.

Lemma ty_defs_has: forall G S ds T d,
  ty_defs G S ds T ->
  defs_has ds d ->
  record_type T ->
  exists D, ty_def G S d D /\ record_sub T (typ_rcd D).
Proof.
  introv Hdefs Hhas Htype. generalize dependent d. generalize dependent ds.
  inversion Htype; subst. induction H; intros.
  - exists D. split. inversion Hdefs; subst. inversion Hhas; subst.
    case_if. inversions H1. assumption. apply rs_refl.
  - inversion Hdefs; subst.
    unfold defs_has in Hhas. unfold get_def in Hhas.
    case_if.
    + inversions Hhas.
      exists D. split. inversions Hdefs; subst. assumption.
      eapply rs_dropl. eapply rs_refl.
    + assert (exists D0, ty_def G S d D0 /\ record_sub T (typ_rcd D0)) as A. {
        eapply IHrecord_typ; eauto.
        exists ls. eassumption.
      }
      destruct A as [D0 [A1 A2]].
      exists D0. split. apply A1. apply rs_drop. apply A2.
Qed.

Lemma new_ty_defs: forall G S s x T ds,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  ty_defs G S (open_defs x ds) (open_typ x T).
Proof.
  introv Hwf Bis.
  lets Htyv: (val_new_typing Hwf Bis).
  inversion Htyv; subst.
  pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H4 y FrL).
  rewrite subst_intro_defs with (x:=y). rewrite subst_intro_typ with (x:=y).
  eapply subst_ty_defs. eapply H4.
  apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto. eauto. eauto.
  rewrite <- subst_intro_typ with (x:=y).
  eapply ty_rec_elim. apply ty_var. eapply wf_stack_val_new_in_G; eauto.
  eauto. eauto. eauto.
  assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
  specialize (H Heqm1). destruct H as [? Contra]. inversion Contra. 
Qed.

Lemma pt_piece_rcd: forall G S s x T ds d D,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  defs_has (open_defs x ds) d ->
  ty_def G S d D ->
  possible_types G S x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas Hdef.
  inversion Hdef; subst; econstructor; eauto.
Qed.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
  record_has (typ_rcd D) D
| rh_andl : forall T D,
  record_has (typ_and T (typ_rcd D)) D
| rh_and : forall T D D',
  record_has T D' ->
  record_has (typ_and T D) D'.

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

Lemma record_has_ty_defs: forall G S T ds D,
  ty_defs G S ds T ->
  record_has T D ->
  exists d, defs_has ds d /\ ty_def G S d D.
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

Lemma pt_rcd_has_piece: forall G S s x T ds D,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  record_has (open_typ x T) D ->
  possible_types G S x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas.
  lets Hdefs: (new_ty_defs Hwf Bis).
  destruct (record_has_ty_defs Hdefs Hhas) as [d [A B]].
  eapply pt_piece_rcd; eauto.
Qed.

Lemma pt_rcd_trm_inversion: forall G S s x v a T,
  wf_stack G S s ->
  binds x v s ->
  possible_types G S x v (typ_rcd (dec_trm a T)) ->
  exists V ds t,
    v = val_new V ds /\
    defs_has (open_defs x ds) (def_trm a t) /\
    ty_trm ty_general sub_general G S t T.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T0; simpl in H4; try solve [inversion H4].
    induction d; simpl in H4; try solve [inversion H4].
    unfold open_typ in H4. simpl in H4. inversions H4.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H4 y FrL).
    unfold open_typ in H4. simpl in H4. inversion H4; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H3; inversion H3; subst.
    inversion H3; subst.
    assert (ty_trm ty_general sub_general G S (open_trm x t1) (open_typ x t0)) as A. {
      rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
      eapply subst_ty_trm. eapply H5.
      apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto. eauto. eauto.
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
    assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H. 
  - repeat eexists. eassumption. assumption.
Qed.

Lemma pt_rcd_typ_inversion: forall G S s x v A V U,
  wf_stack G S s ->
  binds x v s ->
  possible_types G S x v (typ_rcd (dec_typ A V U)) ->
  exists T ds T',
    v = val_new T ds /\
    defs_has (open_defs x ds) (def_typ A T') /\
    subtyp ty_general sub_general G S V T' /\
    subtyp ty_general sub_general G S T' U.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T; simpl in H4; try solve [inversion H4].
    induction d; simpl in H4; try solve [inversion H4].
    unfold open_typ in H4. simpl in H4. inversions H4.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H4 y FrL).
    unfold open_typ in H4. simpl in H4. inversion H4; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H3; inversion H3; subst.
    inversion H3; subst.
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
    subst. subst. clear H6. clear H9.
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

Lemma pt_record_sub_has: forall G S x v T1 T2,
  (forall D, record_has T1 D -> possible_types G S x v (typ_rcd D)) ->
  record_sub T1 T2 ->
  (forall D, record_has T2 D -> possible_types G S x v (typ_rcd D)).
Proof.
  introv HP Hsub. intros D Hhas. apply HP; eauto using record_sub_has.
Qed.

Lemma pt_has_record: forall G S x v T,
  (forall D, record_has T D -> possible_types G S x v (typ_rcd D)) ->
  record_type T ->
  possible_types G S x v T.
Proof.
  introv HP Htype. destruct Htype as [ls Htyp]. induction Htyp.
  - apply HP; eauto. apply rh_one.
  - apply pt_and.
    + apply IHHtyp; eauto.
      intros D0 HH0. apply HP; eauto. apply rh_and; eauto.
    + apply HP; eauto. apply rh_andl.
Qed.

Lemma pt_has_sub: forall G S x v T U,
  (forall D, record_has T D -> possible_types G S x v (typ_rcd D)) ->
  record_type T ->
  record_sub T U ->
  possible_types G S x v U.
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

Lemma possible_types_closure_record: forall G S s x T ds U,
  wf_stack G S s ->
  binds x (val_new T ds) s ->
  record_sub (open_typ x T) U ->
  possible_types G S x (val_new T ds) U.
Proof.
  introv Hwf Bis Hsub.
  apply pt_has_sub with (T:=open_typ x T).
  intros D Hhas. eapply pt_rcd_has_piece; eauto.
  apply open_record_type. eapply record_new_typing; eauto. eapply val_new_typing; eauto.
  assumption.
Qed.

Lemma pt_and_inversion: forall G S s x v T1 T2,
  wf_stack G S s ->
  binds x v s ->
  possible_types G S x v (typ_and T1 T2) ->
  possible_types G S x v T1 /\ possible_types G S x v T2.
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
If G, S ~ s and G, S |- x: T and s |- x = v then Ts(G, S, x, v) is closed wrt G, S |- _ <: _.
Let SS = Ts(G, S, x, v). We first show SS is closed wrt G, S |-# _ <: _.
Assume T0 in SS and G, S |- T0 <: U0.s We show U0 in SS by an induction on subtyping derivations of G, S |-# T0 <: U0.
*)

Lemma possible_types_closure_tight: forall G S s x v T0 U0,
  wf_stack G S s ->
  binds x v s ->
  possible_types G S x v T0 ->
  subtyp ty_general sub_tight G S T0 U0 ->
  possible_types G S x v U0.
Proof.
  introv Hwf Bis HT0 Hsub. dependent induction Hsub.
  - (* Top *) apply pt_top.
  - (* Bot *) inversion HT0; subst.
    lets Htype: (open_record_type x (record_new_typing (val_new_typing Hwf Bis))).
    destruct Htype as [ls Htyp]. rewrite H4 in Htyp. inversion Htyp.
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
    destruct HT0 as [V [ds [t [Heq [Hhas Hty]]]]].
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
  - (* <:-Sel-tight *)
    eapply pt_sel. eassumption. assumption.
  - (* Sel-<:-tight *)
    inversion HT0; subst.
    assert (record_type (open_typ x T0)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H5 in B. destruct B as [? B]. inversion B.
    assert (T = V) as B. {
      eapply unique_tight_bounds; eauto.
    }
    subst. assumption.
- (* All-<:-All *)
    inversion HT0; subst.
    assert (record_type (open_typ x T)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H6 in B. destruct B as [? B]. inversion B.
    apply_fresh pt_lambda as y.
    eapply H3; eauto.
    eapply subtyp_trans. eapply tight_to_general_subtyping. eassumption. eassumption.
    eapply subtyp_trans.
    eapply narrow_subtyping. eapply H9; eauto.
    eapply subenv_last. eapply tight_to_general_subtyping. eapply Hsub.
    eapply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
    eapply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
    eapply H; eauto.
- (* Subtyp-Ref *)
    inversion HT0; subst.
    assert (record_type (open_typ x T0)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H4 in B. destruct B as [? B]. inversion B.
    apply pt_loc_sub with (T:=T). assumption.
    apply tight_to_general_subtyping in Hsub1. assumption.
    apply tight_to_general_subtyping in Hsub2. assumption.
    apply pt_loc_sub with (T:=T). assumption.
    apply tight_to_general_subtyping in Hsub1. assumption.
    apply tight_to_general_subtyping in Hsub2. assumption.
Qed.

(*
Lemma (Possible types completeness for values)
If `G, S ~ s` and `x = v in s` and  `G, S |-! v: T` then `T in Ts(G, S, x, v)`.
 *)

Lemma possible_types_completeness_for_values: forall G S s x v T,
  wf_stack G S s ->
  binds x v s ->
  ty_trm ty_precise sub_general G S (trm_val v) T ->
  possible_types G S x v T.
Proof.
  introv Hwf Bis Hty. destruct v as [V ds | V t | V l].
  - apply new_intro_inversion in Hty. destruct Hty as [Heq Htype]. subst.
    eapply pt_bnd. eapply pt_new. reflexivity.
  - remember Hty as Hty'. clear HeqHty'. inversion Hty'; subst.
    + apply all_intro_inversion in Hty. destruct Hty as [T' Heq]. subst.
      apply_fresh pt_lambda as y.
      eapply H6; eauto.
      apply subtyp_refl.
      apply subtyp_refl.
    + assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
      specialize (H Heqm1). destruct H. inversion H. 
  - remember Hty as Hty'. clear HeqHty'. inversion Hty'; subst.
    + apply pt_loc. apply precise_to_general in Hty. assumption.
      reflexivity. reflexivity.
    + destruct (loc_intro_inversion Hty); subst.
      constructor. assumption.
Qed.

(*
Lemma (Possible types completeness)
If `G ~ s` and `x = v in s` and  `G |-# x: T` then `T in Ts(G, x, v)`.
Lemma (Possible types)
If `G ~ s` and `G |- x: T` then, for some value `v`,
`s(x) = v` and `T in Ts(G, x, v)`.
*)

Lemma possible_types_completeness_tight: forall G S s x T,
  wf_stack G S s ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G S x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G S (trm_val v) T) as A. {
      destruct (ctx_binds_to_stack_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      apply weaken_ty_trm_ctx. auto. rewrite concat_assoc.
      eapply wf_stack_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H5 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]].
    specialize (IHty_trm2 Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]].
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure_tight; eauto.
Qed.

Lemma tight_ty_rcd_typ__new: forall G S s x A V U,
  wf_stack G S s ->
  ty_trm ty_general sub_tight G S (trm_var (avar_f x)) (typ_rcd (dec_typ A V U)) ->
  exists T ds, binds x (val_new T ds) s.
Proof.
  introv Hwf Hty.
  destruct (possible_types_completeness_tight Hwf Hty) as [v [Bis Hpt]].
  inversion Hpt; subst; repeat eexists; eauto.
Qed.


Lemma general_to_tight: forall G0 S0 s0,
  wf_stack G0 S0 s0 ->
  (forall m1 m2 G S t T,
     ty_trm m1 m2 G S t T ->
     G = G0 ->
     S = S0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G S t T) /\
  (forall m1 m2 G S V U,
     subtyp m1 m2 G S V U ->
     G = G0 ->
     S = S0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     subtyp ty_general sub_tight G S V U).
Proof.
  intros G0 S0 s0 Hwf.
  apply ts_mutind; intros; subst; eauto.
  - assert (exists S ds, binds x (val_new S ds) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? [? Bis]].
    eapply proj2. eapply tight_bound_completeness; eauto.
  - assert (exists S ds, binds x (val_new S ds) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? [? Bis]].
    eapply proj1. eapply tight_bound_completeness; eauto.
Qed.

Lemma general_to_tight_subtyping: forall G S s V U,
  wf_stack G S s ->
  subtyp ty_general sub_general G S V U ->
  subtyp ty_general sub_tight G S V U.
Proof.
  intros.
  assert (forall m1 m2 G1 S1 V1 U1,
    subtyp m1 m2 G1 S1 V1 U1 ->
    G1 = G ->
    S1 = S ->
    m1 = ty_general ->
    m2 = sub_general ->
    subtyp ty_general sub_tight G1 S1 V1 U1). {
      apply* general_to_tight.
  }
  specialize (H1 ty_general sub_general G S V U). apply* H1.
Qed.


Lemma possible_types_closure: forall G S s x v V T,
  wf_stack G S s ->
  binds x v s ->
  possible_types G S x v V ->
  subtyp ty_general sub_general G S V T ->
  possible_types G S x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
  eapply general_to_tight_subtyping; eauto.
Qed.

Lemma possible_types_completeness: forall G S s x T,
  wf_stack G S s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G S x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G S (trm_val v) T) as A. {
      destruct (ctx_binds_to_stack_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      apply weaken_ty_trm_ctx. auto. rewrite concat_assoc.
      eapply wf_stack_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H5 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]].
    specialize (IHty_trm2 Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]].
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure; eauto.
Qed.

Lemma possible_types_lemma: forall G S s x v T,
  wf_stack G S s ->
  binds x v s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) T ->
  possible_types G S x v T.
Proof.
  introv Hwf Bis Hty.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.

Lemma ctx_binds_to_stack_binds_typing: forall G S sta x T,
  wf_stack G S sta ->
  binds x T G ->
  exists v, binds x v sta /\ ty_trm ty_precise sub_general G S (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_stack_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm_ctx. auto.
  rewrite concat_assoc.
  eapply wf_stack_to_ok_G; eauto.
Qed.

Lemma sigma_binds_to_store_binds_typing: forall G S sto l T,
  wt_store G S sto ->
  binds l T S ->
  exists x, bindsM l x sto /\ ty_trm ty_general sub_general G S (trm_var (avar_f x)) T.
Proof.
  introv Hwf Bi.
  lets A: (sigma_binds_to_store_binds_raw Hwf Bi).
  destruct A as [S1 [S2 [HeqG [x [Bis Hty]]]]].
  exists x. split; eauto.
Qed.

(* ###################################################################### *)
(** * Misc *)

Lemma var_typing_implies_avar_f: forall G S a T,
  ty_trm ty_general sub_general G S (trm_var a) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm.
Qed.

Lemma val_typing: forall G S v T,
  ty_trm ty_general sub_general G S (trm_val v) T ->
  exists T', ty_trm ty_precise sub_general G S (trm_val v) T' /\
             subtyp ty_general sub_general G S T' T.
Proof.
  intros. dependent induction H.
  - exists (typ_ref T). auto.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro with (L:=L); eauto. apply subtyp_refl.
  - destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G S s x T U,
  wf_stack G S s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G S T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) S (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [V Bi].
  lets A: (ctx_binds_to_stack_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - pick_fresh y. exists (dom G \u L). exists V0. exists t.
    split. apply Bis. split. assumption.
    intros y0 Fr0.
    eapply ty_sub.
    intros Contra. inversion Contra.
    eapply narrow_typing.
    eapply H1; eauto.
    apply subenv_last. apply H6.
    apply ok_push. eapply wf_stack_to_ok_G; eauto. eauto.
    apply ok_push. eapply wf_stack_to_ok_G; eauto. eauto.
    eapply H7; eauto.
Qed.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T.

*)
Lemma canonical_forms_2: forall G S s x a T,
  wf_stack G S s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  (exists V ds t, binds x (val_new V ds) s /\ ty_defs G S (open_defs x ds) (open_typ x V) /\ defs_has (open_defs x ds) (def_trm a t) /\ ty_trm ty_general sub_general G S t T).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [V Bi].
  lets A: (ctx_binds_to_stack_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [V' [ds [t' [Heq [Hdefs Htyd]]]]].
  subst.
  exists V' ds t'.
  split; try split; try split; try assumption.
  eapply new_ty_defs; eauto.
Qed.

Lemma ref_binds_typ: forall G S l T,
  ty_trm ty_precise sub_general G S (trm_val (val_loc l)) (typ_ref T) ->
  binds l T S.
Proof.
  introv Hty.
  inversion Hty.
  - assumption.
  - subst.
    apply loc_intro_inversion in H0.
    assert (ty_precise = ty_precise) as Hp by reflexivity. apply H in Hp.
    destruct Hp as [x Ht]. inversion Ht. 
Qed.

Lemma pt_loc_implies_typing: forall G S x l T,
  possible_types G S x (val_loc l) (typ_ref T) ->
  ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T).
Proof.
  introv Hp. dependent induction Hp.
  apply precise_to_general_typing. assumption.
  apply ty_sub with (T:=typ_ref T0). intro Hgp. inversion Hgp.
  assumption.
  apply subtyp_ref; assumption.
Qed.

Lemma precise_ref_subtyping: forall G S x l T sta sto,
  binds x (val_loc l) sta ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_ref T) ->
  ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T) ->
  wf_stack G S sta ->
  wt_store G S sto ->
  exists U,
  (ty_trm ty_precise sub_general G S (trm_val (val_loc l)) (typ_ref U) /\
   subtyp ty_general sub_general G S T U /\
   subtyp ty_general sub_general G S U T).
Proof.
  introv Bi Hx Hty Wf Wt. 
  destruct (typing_implies_bound_loc Hty) as [U Bi'].
  exists U.
  split. constructor. assumption.
  lets Hp: (possible_types_lemma Wf Bi Hx).
  dependent induction Hp.
  - apply ref_binds_typ in H. lets Hb: (binds_func H Bi'). subst. split; constructor.
  - assert (subtyp ty_general sub_general G S (typ_ref T) (typ_ref T0)). {
      apply subtyp_ref; assumption. 
  }
  assert (ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_ref T0)). {
      apply ty_sub with (T:=typ_ref T); try assumption. intro Hgp. inversion Hgp.
  }
  assert (ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T0)). {
   apply pt_loc_implies_typing in Hp. assumption. 
  }
  specialize (IHHp Bi H2 H3 Wf Wt Bi'). destruct IHHp.
  split; apply subtyp_trans with (T:=T0); assumption.
Qed.
    

(*
Lemma (Canonical forms 3)

If G, S ~ stack, G, S ~ store, and G, S |- x: Ref T then
  stack(x) = loc l for some address l, such that G, S |- l: Ref T, and
  there exists a value v such that
  store(l) = v and G, S |- v: T.
*)
Lemma canonical_forms_3: forall G S sta sto x T,
  wf_stack G S sta ->
  wt_store G S sto ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_ref T) ->
  exists l y,
    binds x (val_loc l) sta /\
    ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T) /\
    bindsM l y sto /\
    ty_trm ty_general sub_general G S (trm_var (avar_f y)) T.
Proof.
  introv HWfSta HWfSto Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [V Bi].
  lets A: (ctx_binds_to_stack_binds_typing HWfSta Bi). destruct A as [y [Bis Htyy]].
  lets Hp: (possible_types_lemma HWfSta Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new HWfSta Bis). rewrite H4 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - lets Bi': (typing_implies_bound_loc H4). destruct Bi' as [Tl Bi'].
    lets B: (sigma_binds_to_store_binds_typing HWfSto Bi'). destruct B as [y' [Bil Htyl]].
    exists l y'. split. assumption. split. apply precise_to_general_typing.
    assumption.
    inversion H4; subst. apply (binds_func H6) in Bi'. subst. split. assumption.
    assumption. split. assumption.
    assert (ty_precise = ty_precise) as Hpref by reflexivity. 
    destruct (H Hpref) as [x0 Htvalvar]. inversion Htvalvar.
  - lets Bi': (typing_implies_bound_loc Htyy). destruct Bi' as [Tl Bi'].
    lets B: (sigma_binds_to_store_binds_typing HWfSto Bi').
    destruct B as [y' [Bil Htyl]].
    exists l y'. split. assumption. split.
    * inversion H0; subst. 
      apply ty_sub with (T:=typ_ref T0). intro H. inversion H. apply precise_to_general_typing. assumption.
      apply subtyp_ref; assumption.
      apply pt_loc_implies_typing in Hp. assumption.
    * split. assumption.
      apply pt_loc_implies_typing in Hp. 
      destruct (precise_ref_subtyping Bis Hty Hp HWfSta HWfSto) as [U [Hl [Hsub1 Hsub2]]].
      apply ref_binds_typ in Hl. lets Hb: (binds_func Hl Bi'). subst Tl.
      apply ty_sub with (T:=U). intro Hgp; inversion Hgp.
      assumption. assumption.
Qed.


(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(*
Let G, S |- t: T,
    G, S ~ sta, and
    G, S ~ sto.
Then either
- t is a normal form, or
- there exists a stack sta', store sto', term t' such that
      sta, sto | t -> sta', sto' | t',
  and for any such sta', sto', t', there exists an environment G'' and store typing S''
  such that, letting
      G' = G, G'',
      S' = S, S'',
  one has
      G', S' |- t': T,
      G', S' ~ sta',
      G', S' ~ sto'
The proof is by a induction on typing derivations of G, S |- t: T.
*)


Lemma safety: forall G S sta sto t T,
  wf_stack G S sta ->
  wt_store G S sto ->
  ty_trm ty_general sub_general G S t T ->
  (normal_form t \/
    (exists sta' sto' t' G' G'' S' S'',
    red t sta sto t' sta' sto' /\
    G' = G & G'' /\
    S' = S & S'' /\
    ty_trm ty_general sub_general G' S' t' T
    /\ wf_stack G' S' sta'
    /\ wt_store G' S' sto')).
Proof.
  introv HWf HWt H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 HWf H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists sta sto (open_trm z t) G (@empty typ) S. exists (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto. eauto. auto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=V).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. eauto.
  - (* Fld-E *) right.
    lets C: (canonical_forms_2 HWf H).
    destruct C as [V [ds [t [Bis [Tyds [Has Ty]]]]]].
    exists sta sto t G (@empty typ) S. exists (@empty typ).
    split. apply red_sel with (T:=V) (ds:=ds); try assumption.
    split. rewrite concat_empty_r. reflexivity.
    split. rewrite concat_empty_r. reflexivity.
    split. assumption.
    split. assumption. assumption.
 - (* Let *) right.
    destruct t.
    + (* var *)
      assert (exists x, a = avar_f x) as A. {
        eapply var_typing_implies_avar_f. eassumption.
      }
      destruct A as [x A]. subst a.
      exists sta sto (open_trm x u) G (@empty typ) S. exists (@empty typ).
      split. apply red_let_var.
      split. rewrite concat_empty_r. reflexivity.
      split. rewrite concat_empty_r. reflexivity.
      split.
      pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      rewrite subst_intro_trm with (x:=y).
      rewrite <- subst_fresh_typ with (x:=y) (y:=x).
      eapply subst_ty_trm. eapply H0.
      apply ok_push. eapply wf_stack_to_ok_G. eassumption. auto. auto. auto.
      rewrite subst_fresh_typ. assumption. auto. auto. auto. auto.
    + (* val *)
      lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (sta & x ~ v) sto (open_trm x u) (G & (x ~ T')) (x ~ T') S. exists (@empty typ).
      split.
      apply red_let. auto.
      split. reflexivity. split. rewrite concat_empty_r. reflexivity.
      split. apply narrow_typing with (G:=G & x ~ T).
      assumption.
      apply subenv_last. assumption.
      apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
      apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
      split; auto.
    + (* sel *)
      specialize (IHty_trm HWf HWt). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        apply weaken_ty_trm_sigma. auto. apply (wf_stack_to_ok_S H6).
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption.
    + (* app *)
      specialize (IHty_trm HWf HWt). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        apply weaken_ty_trm_sigma. auto. apply (wf_stack_to_ok_S H6).
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption.
    + (* let *)
      specialize (IHty_trm HWf HWt). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        apply weaken_ty_trm_sigma. auto. apply (wf_stack_to_ok_S H6).
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption.
    + (* ref *)
      specialize (IHty_trm HWf HWt). destruct IHty_trm as [IH | IH].
      inversion IH. destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); auto.
      inversion H2. assumption.
      intros. rewrite IH2. eapply weaken_rules_ctx.
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        apply weaken_ty_trm_sigma. auto. apply (wf_stack_to_ok_S H6).
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption.
    + (* deref *)
      specialize (IHty_trm HWf HWt). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      inversion H2. assumption.
      intros. rewrite IH2. eapply weaken_rules_ctx.
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        apply weaken_ty_trm_sigma. auto. apply (wf_stack_to_ok_S H6).
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption.
    + (* asgn *)
      specialize (IHty_trm HWf HWt). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      inversion H2. assumption.
      intros. rewrite IH2. eapply weaken_rules_ctx.
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        apply weaken_ty_trm_sigma. auto. apply (wf_stack_to_ok_S H6).
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption.
  - (* sub *)
    specialize (IHty_trm HWf HWt). destruct IHty_trm as [IH | IH].
    + left. assumption.
    + right.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 [IH5 IH6]]]]]]]]]]]].
      exists sta' sto' t' G' G'' S'. exists S''.
      split; try split; try split; try split; try split; try assumption.
      apply ty_sub with (T:=T).
      intro Contra. inversion Contra. assumption.
      subst. apply weaken_subtyp_ctx. simpl. apply weaken_subtyp_sigma.
      assumption. apply (wf_stack_to_ok_S IH5). apply (wf_stack_to_ok_G IH5).
  - (* ref *)
    right. pick_fresh l.
    exists sta (sto[l:=x]) (trm_val (val_loc l)) G (@empty typ) (S & l ~ T). exists (l ~ T).
    split. apply* red_ref_var.
    assert (l # S) as HS by auto.
    apply (wt_notin_dom HWt HS).
    split. rewrite concat_empty_r. reflexivity.
    split. reflexivity.
    split. constructor. auto.
    split. constructor. assumption. auto.
    apply wt_store_new. assumption. auto.
    assumption.
  - (* deref *)
    right.
    lets C: (canonical_forms_3 HWf HWt H).
    destruct C as [l [y [BiLoc [_ [BiVal Htyval]]]]].
    exists sta sto (trm_var (avar_f y)) G (@empty typ) S. exists (@empty typ).
    split. apply red_deref with (l:=l). assumption. assumption.
    split. rewrite concat_empty_r. reflexivity.
    split. rewrite concat_empty_r. reflexivity.
    split. assumption. split. assumption. assumption.
  - (* asg *)
    right.
    lets C: (canonical_forms_3 HWf HWt H).

    destruct C as [l [y' [BiLoc [Hty [BiSto Htyy']]]]].
    exists sta (sto[l := y]) (trm_var (avar_f y)) G (@empty typ) S. exists (@empty typ).
    split.
    apply red_asgn with (l:=l).
    assumption.
    lets Hbd: (LibMap.binds_def sto l y'). unfold bindsM in BiSto. rewrite Hbd in BiSto.
    destruct BiSto as [His Hsto]. assumption.
    split. rewrite concat_empty_r. reflexivity.
    split. rewrite concat_empty_r. reflexivity.
    split. assumption.
    split. assumption.
    destruct (precise_ref_subtyping BiLoc H Hty HWf HWt) as [U [HU [Hs1 Hs2]]].
    clear Hs1 Hs2 IHty_trm1 IHty_trm2.
    apply wt_store_update with (T:=U); try assumption.
    apply (ref_binds_typ HU).
    lets Hp: (possible_types_lemma HWf BiLoc H).
    lets Hb: (ref_binds_typ HU).
    dependent induction Hp.
    * apply ref_binds_typ in H1. lets Hbf: (binds_func H1 Hb). subst. assumption.
    *  assert (subtyp ty_general sub_general G S (typ_ref T) (typ_ref T0)) as Hst. apply subtyp_ref; assumption.
      assert (ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_ref T0)) as HxT0. {
        apply ty_sub with (T:=typ_ref T); try assumption. intro Hgp. inversion Hgp.
      }
      assert (ty_trm ty_general sub_general G S (trm_var (avar_f y)) T0) as HyT0. {
        apply ty_sub with (T:=T); try assumption. intro Hgp. inversion Hgp.
      }
      assert (ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T0)) as HlT0. {
        apply ty_sub with (T:=typ_ref T); try assumption. intro Hgp. inversion Hgp.
      }
      assert (ty_trm ty_general sub_general G S (trm_var (avar_f y')) T0) as Hy'T0. {
        apply ty_sub with (T:=T); try assumption. intro Hgp. inversion Hgp.
      }
      specialize (IHHp HWf HWt HxT0 HyT0 BiLoc HlT0 BiSto Hy'T0 HU Hb). assumption.
 Qed.
