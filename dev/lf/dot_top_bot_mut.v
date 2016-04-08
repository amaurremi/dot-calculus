Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import LibList.
Close Scope list_scope.

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
  | avar_f : var -> avar. (* free var ("name"), refers to stack or ctx *)

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
  | trm_ref  : avar -> trm (* ref x *)
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


Definition ctx := env typ.

(* Definition sigma := loc_env typ. *)
Definition sigma := env typ.
(* todo: should I keep my own env, since I'm binding locs and not vars? *)

(** *** Value environment (s) *)
Definition stack := env val.

Definition store := env val.

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
  | trm_ref a      => trm_ref (open_rec_avar k u a)
  | trm_deref a      => trm_deref (open_rec_avar k u a)
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
  | trm_ref a        => (fv_avar a)
  | trm_deref a        => (fv_avar a)
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

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).

Definition fv_sigma_types(S: sigma): vars :=
  fold_right (fun T L => (fv_typ T) \u L) \{} (map snd S).

(* ###################################################################### *)
(** ** Operational Semantics *)

Inductive red : trm -> stack -> store -> trm -> stack -> store -> Prop :=
| red_sel : forall x m s sto t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    red (trm_sel (avar_f x) m) s sto t s sto
| red_app : forall f a s sto T t,
    binds f (val_lambda T t) s ->
    red (trm_app (avar_f f) (avar_f a)) s sto (open_trm a t) s sto
| red_let : forall v t s sto x,
    x # s ->
    red (trm_let (trm_val v) t) s sto (open_trm x t) (s & x ~ v) sto         
| red_let_var : forall t s sto x,
    red (trm_let (trm_var (avar_f x)) t) s sto (open_trm x t) s sto
| red_let_tgt : forall t0 t s sto t0' s' sto',
    red t0 s sto t0' s' sto' ->
    red (trm_let t0 t) s sto (trm_let t0' t) s' sto'
| red_ref_var : forall x v s sto l,
    binds x v s ->
    l # sto ->
    red (trm_ref (avar_f x)) s sto (trm_val (val_loc l)) s (sto & l ~ v)
| red_asgn : forall x y l v s sto,
    binds x (val_loc l) s ->
    binds y v s ->
    red (trm_asg (avar_f x) (avar_f y)) s sto (trm_val v) s (sto & l ~ v)
| red_deref : forall x l s v sto,
    binds x (val_loc l) s ->
    binds l v sto ->
    red (trm_deref (avar_f x)) s sto (trm_val v) s sto.

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
    ty_trm m1 m2 G S (trm_val (val_loc l)) T
| ty_all_intro : forall L m1 m2 G S T t U,
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) S (open_trm x t) (open_typ x U)) ->
    ty_trm m1 m2 G S (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall m2 G S x z U T,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_all U T) ->
    ty_trm ty_general m2 G S (trm_var (avar_f z)) U ->
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
| ty_ref : forall m1 m2 G S x T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) T ->
    ty_trm m1 m2 G S (trm_ref (avar_f x)) (typ_ref T)
| ty_deref : forall m1 m2 G S x T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_ref T) ->
    ty_trm m1 m2 G S (trm_deref (avar_f x)) T
| ty_asgn : forall m1 m2 G S x y T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_ref T) ->
    ty_trm m1 m2 G S (trm_var (avar_f y)) (typ_ref T) ->
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
| subtyp_sel2: forall G S x A U T,
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A U T)) ->
    subtyp ty_general sub_general G S U (typ_sel (avar_f x) A)
| subtyp_sel1: forall G S x A U T,
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A U T)) ->
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
    subtyp ty_general m2 G S (typ_all S1 T1) (typ_all S2 T2).

Inductive envmode : Set := env_stack | env_store .

Definition get_ctx (m: envmode) (env1 env2: env typ) :=
  match m with
  | env_stack => env1
  | env_store => env2
  end.

Definition get_sigma (m: envmode) (env1 env2: env typ) :=
  match m with
  | env_store => env1
  | env_stack => env2
  end.

(* generalization of well-formedness for stacks/stores
 * e1 denotes the main environment (for env_stack, it's ctx, for env_store, it's sigma),
 * and e2 the other environment *)
Inductive wf: envmode -> env typ -> env typ -> env val -> Prop :=
| wf_empty: forall m, wf m empty empty empty
| wf_push: forall m e1 e2 s x T v,
    wf m e1 e2 s ->
    x # e1 ->
    x # s ->
    ty_trm ty_precise sub_general (get_ctx m e1 e2) (get_sigma m e1 e2) (trm_val v) T ->
    wf m (e1 & x ~ T) e2 (s & x ~ v).

Definition wf_stack (G: ctx) (S: sigma) (s: stack): Prop :=
  wf env_stack G S s.

Definition wf_store (G: ctx) (S: sigma) (s: store): Prop :=
  wf env_store S G s.
    
Definition wf_stack_store(G: ctx) (S: sigma) (sta: stack) (sto: store): Prop := 
  wf_stack G S sta /\ wf_store S G sto.


Theorem wf_stack_ind
     : forall P : ctx -> sigma -> stack -> Prop,
       P empty empty empty ->
       (forall (G : ctx) (S : sigma) (s : stack) (x : var) (T : typ)
          (v : val),
        wf env_stack G S s ->
        P G S s ->
        x # G ->
        x # s ->
        ty_trm ty_precise sub_general G S (trm_val v) T ->
        P (G & x ~ T) S (s & x ~ v)) ->
       forall (c : ctx) (s : sigma) (s0 : stack), wf env_stack c s s0 -> P c s s0.
Proof.
        refine(
fun (P : ctx -> sigma -> stack -> Prop) (f : P empty empty empty)
  (f0 : forall {G : ctx} {S : sigma} {s : stack} (x : var) (T : typ)
          (v : val),
        wf_stack G S s ->
        P G S s ->
        x # G ->
        x # s ->
        ty_trm ty_precise sub_general G S (trm_val v) T ->
        P (G & x ~ T) S (s & x ~ v)) =>
fix F (c : ctx) (s : sigma) (s0 : stack) (w : wf_stack c s s0) {struct w} :
  P c s s0 :=
  (match w in (wf m c0 s1 s2) return (m = env_stack) -> (P c0 s1 s2) with
  | wf_empty m => fun _ => f
  | wf_push m G S0 s1 x T v w0 n n0 t => fun _ => _
      (* f0 G S0 s1 x T v w0 (F G S0 s1 w0) n n0 t *)
  end) (eq_refl: env_stack = env_stack)) .
  subst.
  exact (f0 G S0 s1 x T v w0 (F G S0 s1 w0) n n0 t).
Qed.

(* Best attempt at replacement of induction *)
Ltac induction_wf Wf :=
  match type of Wf with
  | (wf_stack ?G ?S ?stack0) =>
          pattern G,S,stack0; (* This causes better matching with apply. *)
          eapply wf_stack_ind;
          try eexact Wf;
          clear G S stack0 Wf
          (* When you prove store induction too, enable this *)
          (*
  | (wf_store ?G ?S ?store0) =>
          pattern G,S,store0; (* This causes better matching with apply. *)
          eapply wf_store_ind;
          try eexact Wf;
          clear G S store0 Wf
          *)
  end.

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

Combined Scheme rules_mutind2 from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp, rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : stack     => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J).

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

Hint Constructors wf.

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

Lemma weaken_rules:
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
    apply_fresh ty_all_intro as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    - specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
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

(* todo generalize the following lemmas? *)

Lemma weaken_ty_trm:  forall m1 m2 G1 G2 S t T,
    ty_trm m1 m2 G1 S t T ->
    ok (G1 & G2) ->
    ty_trm m1 m2 (G1 & G2) S t T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_ty_trm_sigma: forall m1 m2 G S1 S2 t T,
    ty_trm m1 m2 G S1 t T ->
    ok (S1 & S2) ->
    ty_trm m1 m2 G (S1 & S2) t T.
Proof.
  intros.
    assert (S1 & S2 = S1 & S2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_sigma.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp: forall m1 m2 G1 G2 S T U,
  subtyp m1 m2 G1 S T U ->
  ok (G1 & G2) ->
  subtyp m1 m2 (G1 & G2) S T U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
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
(** ** Well-formed stack and store *)

Lemma wf_env_to_ok_env: forall m e1 e2 env,
  wf m e1 e2 env -> ok env.
Proof. intros. induction H; jauto. Qed.

Lemma wf_s_to_ok_env: forall m e1 e2 s,
  wf m e1 e2 s -> ok e1.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_env_to_ok_env wf_s_to_ok_env.


(* WE STOPPED HERE *)


Lemma ctx_binds_to_stack_binds_raw: forall stack G S x T,
  wf_stack G S stack ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v stack /\ ty_trm ty_precise sub_general G1 S (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. 
  induction_wf_stack Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists e1 (@empty typ) v.
      rewrite concat_empty_r. split. auto. split. auto.
      auto.
    - simpl in H2. subst. rename e1 into G. 
    apply split_env in Bi. destruct Bi as [G' [G'']]. 
    exists G' (G'' & x ~ T).
    destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].

    specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
Qed.

Lemma sigma_binds_to_store_binds_raw: forall store G S l T,
  wf_store G S store ->
  binds l T S ->
  exists S1 S2 v, S = S1 & (l ~ T) & S2 /\ binds l v store /\ ty_trm ty_precise sub_general G S1 (trm_val v) T.
Proof.
  introv Wf Bi. gen l T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists S (@empty typ) v.
      rewrite concat_empty_r. auto.
    -  specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & l ~ T) ds'. rewrite concat_assoc. auto.
Qed.

Lemma stack_binds_to_ctx_binds_raw: forall stack G S x v,
  wf_stack G S stack ->
  binds x v stack ->
  exists G1 G2 T, G = G1 & (x ~ T) & G2 /\ ty_trm ty_precise sub_general G1 S (trm_val v) T.
Proof.
  introv Wf Bi. gen x v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [T0' [Eq Ty]]]].
      subst. exists G1 (G2 & x ~ T) T0'. rewrite concat_assoc. auto.
Qed.

Lemma store_binds_to_sigma_binds_raw: forall store G S l v,
  wf_store G S store ->
  binds l v store ->
  exists S1 S2 T, S = S1 & (l ~ T) & S2 /\ ty_trm ty_precise sub_general G S1 (trm_val v) T.
Proof.
  introv Wf Bi. gen l v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists S (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [S1 [S2 [T0' [Eq Ty]]]].
      subst. exists S1 (S2 & l ~ T) T0'. rewrite concat_assoc. auto.
Qed.

Lemma invert_wf_stack_concat: forall sta G1 G2 S,
  wf_stack (G1 & G2) S sta ->
  exists sta1 sta2, sta = sta1 & sta2 /\ wf_stack G1 S sta1.
Proof.
  introv Wf. gen_eq G: (G1 & G2). gen G1 G2. induction Wf; introv Eq; subst.
  - do 2 exists (@empty val). rewrite concat_empty_r.
    apply empty_concat_inv in Eq. destruct Eq. subst. auto.
  - destruct (env_case G2) as [Eq1 | [x' [T' [G2' Eq1]]]].
    * subst G2. rewrite concat_empty_r in Eq. subst G1.
      exists (stack0 & x ~ v) (@empty val). rewrite concat_empty_r. auto.
    * subst G2. rewrite concat_assoc in Eq. apply eq_push_inv in Eq.
      destruct Eq as [? [? ?]]. subst x' T' G. specialize (IHWf G1 G2' eq_refl).
      destruct IHWf as [s1 [s2 [Eq Wf']]]. subst.
      exists s1 (s2 & x ~ v). rewrite concat_assoc. auto.
Qed.

Lemma invert_wf_store_concat: forall sto G S1 S2,
  wf_store G (S1 & S2) sto ->
  exists sto1 sto2, sto = sto1 & sto2 /\ wf_store G S1 sto1.
Proof.
  introv Wf. gen_eq S: (S1 & S2). gen S1 S2. induction Wf; introv Eq; subst.
  - do 2 exists (@empty val). rewrite concat_empty_r.
    apply empty_concat_inv in Eq. destruct Eq. subst. auto.
  - destruct (env_case S2) as [Eq1 | [x' [T' [S2' Eq1]]]].
    * subst S2. rewrite concat_empty_r in Eq. subst S1.
      exists (store0 & l ~ v) (@empty val). rewrite concat_empty_r. auto.
    * subst S2. rewrite concat_assoc in Eq. apply eq_push_inv in Eq.
      destruct Eq as [? [? ?]]. subst x' T' S. specialize (IHWf S1 S2' eq_refl).
      destruct IHWf as [s1 [s2 [Eq Wf']]]. subst.
      exists s1 (s2 & l ~ v). rewrite concat_assoc. auto.
Qed.

Lemma stack_unbound_to_ctx_unbound: forall s G S x,
  wf_stack G S s ->
  x # s ->
  x # G.
Proof.
  introv Wf Ub_s.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub_s).
    - auto.
Qed.

Lemma store_unbound_to_sigma_unbound: forall s G S l,
  wf_store G S s ->
  l # s ->
  l # S.
Proof.
  introv Wf Ub_s.
  induction Wf.
  + auto.
  + destruct (classicT (l0 = l)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub_s).
    - auto.
Qed.

Lemma ctx_unbound_to_stack_unbound: forall s G S x,
  wf_stack G S s ->
  x # G ->
  x # s.
Proof.
  introv Wf Ub.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub).
    - auto.
Qed.

Lemma sigma_unbound_to_store_unbound: forall s G S l,
  wf_store G S s ->
  l # S ->
  l # s.
Proof.
  introv Wf Ub.
  induction Wf.
  + auto.
  + destruct (classicT (l0 = l)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub).
    - auto.
Qed.


Lemma typing_implies_bound: forall m1 m2 G S x T,
  ty_trm m1 m2 G S (trm_var (avar_f x)) T ->
  exists S, binds x S G.
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


Lemma typing_bvar_implies_false: forall m1 m2 G S a T,
  ty_trm m1 m2 G S (trm_var (avar_b a)) T ->
  False.
Proof.
  intros. remember (trm_var (avar_b a)) as t. induction H; try solve [inversion Heqt].
  eapply IHty_trm. auto.
Qed.


(* ###################################################################### *)
(** ** Extra Rec *)

Lemma extra_bnd_rules:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G1 G2 x U G',
    G = G1 & (x ~ open_typ x U) & G2 ->
    G' = G1 & (x ~ typ_bnd U) & G2 ->
    ty_trm m1 m2 G' S t T)
/\ (forall G S d D, ty_def G S d D -> forall G1 G2 x U G',
    G = G1 & (x ~ open_typ x U) & G2 ->
    G' = G1 & (x ~ typ_bnd U) & G2 ->
    ty_def G' S d D)
/\ (forall G S ds T, ty_defs G S ds T -> forall G1 G2 x U G',
    G = G1 & (x ~ open_typ x U) & G2 ->
    G' = G1 & (x ~ typ_bnd U) & G2 ->
    ty_defs G' S ds T)
/\ (forall m1 m2 G S T U, subtyp m1 m2 G S T U -> forall G1 G2 x V G',
    G = G1 & (x ~ open_typ x V) & G2 ->
    G' = G1 & (x ~ typ_bnd V) & G2 ->
    subtyp m1 m2 G' S T U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. apply binds_middle_inv in b. destruct b as [Bi | [Bi | Bi]].
    + apply ty_var. eauto.
    + destruct Bi as [Bin [Eqx EqT ]]. subst.
      apply ty_rec_elim. apply ty_var. eauto.
    + destruct Bi as [Bin [Neqx Bi]]. apply ty_var. eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H y FrL).
    specialize (H G1 (G2 & y ~ T) x U0).
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as y; eauto;
    assert (y \notin L) as FrL by eauto.
    specialize (H y FrL).
    specialize (H G1 (G2 & y ~ open_typ y T) x U).
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H0 y FrL).
    specialize (H0 G1 (G2 & y ~ T) x U0).
    eapply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H0 y FrL).
    specialize (H0 G1 (G2 & y ~ S2) x V).
    eapply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
Qed.

(* todo same for sigma *)

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
  | trm_ref x        => trm_ref (subst_avar z u x)
  | trm_deref x      => trm_ref (subst_avar z u x)
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

Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx := map (subst_typ z u) G.

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

Lemma subst_open_commute_val: forall x y u v,
  subst_val x y (open_val u v) = open_val (subst_fvar x y u) (subst_val x y v).
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

Lemma subst_intro_val: forall x u v, x \notin (fv_val v) ->
  open_val u v = subst_val x u (open_val x v).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_val.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [Q _]]. rewrite* (Q v).
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

Lemma subst_intro_dec: forall x u D, x \notin (fv_dec D) ->
  open_dec u D = subst_dec x u (open_dec x D).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_dec.
  destruct (@subst_fresh_typ_dec x u) as [_ Q]. rewrite* (Q D).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_undo_avar: forall x y,
  (forall a, y \notin fv_avar a -> (subst_avar y x (subst_avar x y a)) = a).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + unfold fv_avar in H. assert (y <> v) by auto. repeat case_if; reflexivity.
Qed.

Lemma subst_undo_typ_dec: forall x y,
   (forall T , y \notin fv_typ  T  -> (subst_typ  y x (subst_typ  x y T )) = T )
/\ (forall D , y \notin fv_dec  D  -> (subst_dec  y x (subst_dec  x y D )) = D ).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*.
  apply* subst_undo_avar.
Qed.

Lemma subst_undo_trm_val_def_defs: forall x y,
   (forall t , y \notin fv_trm  t  -> (subst_trm  y x (subst_trm  x y t )) = t )
/\ (forall v , y \notin fv_val  v  -> (subst_val  y x (subst_val  x y v )) = v )
/\ (forall d , y \notin fv_def  d  -> (subst_def  y x (subst_def  x y d )) = d )
/\ (forall ds, y \notin fv_defs ds -> (subst_defs y x (subst_defs x y ds)) = ds).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_val, fv_def, fv_defs in *; f_equal*;
    (apply* subst_undo_avar || apply* subst_undo_typ_dec).
Qed.

Lemma subst_typ_undo: forall x y T,
  y \notin fv_typ T -> (subst_typ y x (subst_typ x y T)) = T.
Proof.
  apply* subst_undo_typ_dec.
Qed.

Lemma subst_trm_undo: forall x y t,
  y \notin fv_trm t -> (subst_trm y x (subst_trm x y t)) = t.
Proof.
  apply* subst_undo_trm_val_def_defs.
Qed.

Lemma subst_idempotent_avar: forall x y,
  (forall a, (subst_avar x y (subst_avar x y a)) = (subst_avar x y a)).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + repeat case_if; reflexivity.
Qed.

Lemma subst_idempotent_typ_dec: forall x y,
   (forall T, subst_typ x y (subst_typ x y T) = subst_typ x y T)
/\ (forall D, subst_dec x y (subst_dec x y D) = subst_dec x y D).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*.
  apply* subst_idempotent_avar.
Qed.

Lemma subst_idempotent_trm_val_def_defs: forall x y,
   (forall t , subst_trm  x y (subst_trm  x y t ) = (subst_trm  x y t ))
/\ (forall v , subst_val  x y (subst_val  x y v ) = (subst_val  x y v ))
/\ (forall d , subst_def  x y (subst_def  x y d ) = (subst_def  x y d ))
/\ (forall ds, subst_defs x y (subst_defs x y ds) = (subst_defs x y ds)).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_val, fv_def, fv_defs in *; f_equal*;
    (apply* subst_idempotent_avar || apply* subst_idempotent_typ_dec).
Qed.

Lemma subst_typ_idempotent: forall x y T,
  subst_typ x y (subst_typ x y T) = subst_typ x y T.
Proof.
  apply* subst_idempotent_typ_dec.
Qed.

Lemma subst_trm_idempotent: forall x y t,
  subst_trm x y (subst_trm x y t) = subst_trm x y t.
Proof.
  apply* subst_idempotent_trm_val_def_defs.
Qed.

Lemma subst_label_of_dec: forall x y D,
  label_of_dec D = label_of_dec (subst_dec x y D).
Proof.
  intros. destruct D; simpl; reflexivity.
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
  (forall m1 m2 G t T, ty_trm m1 m2 G t T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general sub_general (G1 & (subst_ctx x y G2)) (trm_var (avar_f y)) (subst_typ x y S) ->
    m1 = ty_general ->
    m2 = sub_general ->
    ty_trm m1 m2 (G1 & (subst_ctx x y G2)) (subst_trm x y t) (subst_typ x y T)) /\
  (forall G d D, ty_def G d D -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general sub_general (G1 & (subst_ctx x y G2)) (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_def (G1 & (subst_ctx x y G2)) (subst_def x y d) (subst_dec x y D)) /\
  (forall G ds T, ty_defs G ds T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general sub_general (G1 & (subst_ctx x y G2)) (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_defs (G1 & (subst_ctx x y G2)) (subst_defs x y ds) (subst_typ x y T)) /\
  (forall m1 m2 G T U, subtyp m1 m2 G T U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general sub_general (G1 & (subst_ctx x y G2)) (trm_var (avar_f y)) (subst_typ x y S) ->
    m1 = ty_general ->
    m2 = sub_general ->
    subtyp m1 m2 (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U)).
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
    rewrite <- concat_assoc. rewrite B.
    apply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_new_elim *)
    simpl. apply ty_new_elim.
    apply H; eauto.
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
  - (* subtyp_sel2_tight *) inversion H5.
  - (* subtyp_sel1_tight *) inversion H5.
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
Qed.

Lemma subst_ty_trm: forall y S G x t T,
    ty_trm ty_general sub_general (G & x ~ S) t T -> 
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    ty_trm ty_general sub_general G (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_trm ty_general sub_general G (subst_trm x y t) (subst_typ x y T).
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
  reflexivity.
Qed.

Lemma subst_ty_defs: forall y S G x ds T,
    ty_defs (G & x ~ S) ds T ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    ty_trm ty_general sub_general G (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_defs G (subst_defs x y ds) (subst_typ x y T).
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
(** ** Some Lemmas *)

Lemma corresponding_types: forall G s x T,
  wf_stack G s ->
  binds x T G ->
  ((exists S U t, binds x (val_lambda S t) s /\
                  ty_trm ty_precise sub_general G (trm_val (val_lambda S t)) (typ_all S U) /\
                  T = typ_all S U) \/
   (exists S ds, binds x (val_new S ds) s /\
                 ty_trm ty_precise sub_general G (trm_val (val_new S ds)) (typ_bnd S) /\
                 T = typ_bnd S)).
Proof.
  introv H Bi. induction H.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists T0. exists U. exists t.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_stack_to_ok_G. eassumption. assumption.
        reflexivity.
      * right. exists T0. exists ds.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_stack_to_ok_G. eassumption. assumption.
        reflexivity.
      * assert (exists x, trm_val v = trm_var (avar_f x)) as A. {
          apply H3. reflexivity.
        }
        destruct A as [? A]. inversion A.
    + specialize (IHwf_stack Bi).
      inversion IHwf_stack as [IH | IH].
      * destruct IH as [S [U [t [IH1 [IH2 IH3]]]]].
        left. exists S. exists U. exists t.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_stack_to_ok_G. eassumption. assumption.
        assumption.
      * destruct IH as [S [ds [IH1 [IH2 IH3]]]].
        right. exists S. exists ds.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_stack_to_ok_G. eassumption. assumption.
        assumption.
Qed.

Lemma unique_rec_subtyping: forall G S T,
  subtyp ty_precise sub_general G (typ_bnd S) T ->
  T = typ_bnd S.
Proof.
  introv Hsub.
  remember (typ_bnd S) as T'.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1 Heqm2). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_all_subtyping: forall G S U T,
  subtyp ty_precise sub_general G (typ_all S U) T ->
  T = typ_all S U.
Proof.
  introv Hsub.
  remember (typ_all S U) as T'.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1 Heqm2). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_lambda_typing: forall G x S U T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) T ->
  T = typ_all S U.
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

Lemma lambda_not_rcd: forall G x S U A T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) ->
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
  - simpl in H3; induction T2; simpl in H3; inversion H3.
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

Lemma label_same_typing: forall G d D,
  ty_def G d D -> label_of_def d = label_of_dec D.
Proof.
  intros. inversion H; subst; simpl; reflexivity.
Qed.

Lemma record_defs_typing_rec: forall G ds S,
  ty_defs G ds S ->
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

Lemma record_defs_typing: forall G ds S,
  ty_defs G ds S ->
  record_type S.
Proof.
  intros.
  assert (exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l) as A.
  eapply record_defs_typing_rec; eauto.
  destruct A as [ls [A1 A2]].
  exists ls. apply A1.
Qed.

Lemma record_new_typing: forall G S ds,
  ty_trm ty_precise sub_general G (trm_val (val_new S ds)) (typ_bnd S) ->
  record_type S.
Proof.
  intros.
  inversion H; subst.
  + pick_fresh x.
    apply open_record_type_rev with (x:=x).
    eauto.
    eapply record_defs_typing. eapply H4. eauto.
  + assert (exists x, trm_val (val_new S ds) = trm_var (avar_f x)) as Contra. {
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
  subtyp ty_precise sub_general G T T' ->
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
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) T ->
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
    + subst. apply unique_rec_subtyping in H0. left. assumption.
    + right. eapply record_sub_trans. eassumption.
      eapply record_subtyping. eassumption.
      eapply record_type_sub_closed. eassumption.
      eapply open_record_type. assumption.
Qed.

Lemma unique_tight_bounds: forall G s x T1 T2 A,
  wf_stack G s ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T2 T2)) ->
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

Lemma precise_to_general:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_precise ->
     m2 = sub_general ->
     ty_trm ty_general sub_general G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_precise ->
     m2 = sub_general ->
     subtyp ty_general sub_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
Qed.

Lemma precise_to_general_typing: forall G t T,
  ty_trm ty_precise sub_general G t T ->
  ty_trm ty_general sub_general G t T.
Proof.
  intros. apply* precise_to_general.
Qed.

Lemma tight_to_general:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_general ->
     m2 = sub_tight ->
     ty_trm ty_general sub_general G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_general ->
     m2 = sub_tight ->
     subtyp ty_general sub_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
  - apply precise_to_general in t; eauto.
  - apply precise_to_general in t; eauto.
Qed.

Lemma tight_to_general_typing: forall G t T,
  ty_trm ty_general sub_tight G t T ->
  ty_trm ty_general sub_general G t T.
Proof.
  intros. apply* tight_to_general.
Qed.

Lemma tight_to_general_subtyping: forall G S U,
  subtyp ty_general sub_tight G S U ->
  subtyp ty_general sub_general G S U.
Proof.
  intros. apply* tight_to_general.
Qed.

Lemma precise_to_tight:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_precise ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_precise ->
     m2 = sub_general ->
     subtyp ty_general sub_tight G S U).
Proof.
  apply ts_mutind; intros; subst; eauto; inversion H0.
Qed.

Lemma precise_to_tight_typing: forall G t T,
  ty_trm ty_precise sub_general G t T ->
  ty_trm ty_general sub_tight G t T.
Proof.
  intros. apply* precise_to_tight.
Qed.

Lemma stack_binds_to_ctx_binds: forall G s x v,
  wf_stack G s -> binds x v s -> exists S, binds x S G.
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

Lemma ctx_binds_to_stack_binds: forall G s x T,
  wf_stack G s -> binds x T G -> exists v, binds x v s.
Proof.
  introv Hwf Bi.
  remember Hwf as Hwf'. clear HeqHwf'.
  apply ctx_binds_to_stack_binds_raw with (x:=x) (T:=T) in Hwf.
  destruct Hwf as [G1 [G2 [v [EqG [Bis Hty]]]]].
  subst.
  exists v.
  assumption.
  assumption.
Qed.

Lemma record_type_new: forall G s x T ds,
  wf_stack G s ->
  binds x (val_new T ds) s ->
  record_type (open_typ x T).
Proof.
  introv Hwf Bis.
  destruct (stack_binds_to_ctx_binds Hwf Bis) as [S Bi].
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
      binds x T1 G1 /\ subtyp ty_general sub_general G1 T1 T2.

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
  subtyp ty_general sub_general G S U ->
  ok (G & x ~ S) ->
  subenv (G & x ~ S) (G & x ~ U).
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists S. split; eauto.
    apply weaken_subtyp; eauto.
  - destruct Bi. left. eauto.
Qed.

Lemma narrow_rules:
  (forall m1 m2 G t T, ty_trm m1 m2 G t T -> forall G',
    m1 = ty_general ->
    m2 = sub_general ->
    ok G' ->
    subenv G' G ->
    ty_trm m1 m2 G' t T)
/\ (forall G d D, ty_def G d D -> forall G',
    ok G' ->
    subenv G' G ->
    ty_def G' d D)
/\ (forall G ds T, ty_defs G ds T -> forall G',
    ok G' ->
    subenv G' G ->
    ty_defs G' ds T)
/\ (forall m1 m2 G S U, subtyp m1 m2 G S U -> forall G',
    m1 = ty_general ->
    m2 = sub_general ->
    ok G' ->
    subenv G' G ->
    subtyp m1 m2 G' S U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. unfold subenv in H2. specialize (H2 x T b).
    destruct H2.
    + eauto.
    + destruct H as [T' [Bi Hsub]].
      eapply ty_sub; eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    eapply H; eauto. apply subenv_push; eauto.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as y; eauto.
    apply H; eauto. apply subenv_push; eauto.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    apply H0 with (x:=y); eauto. apply subenv_push; eauto.
  - inversion H1 (* sub_tight *).
  - inversion H1 (* sub_tight *).
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    apply H0; eauto. apply subenv_push; eauto.
Qed.

Lemma narrow_typing: forall G G' t T,
  ty_trm ty_general sub_general G t T ->
  subenv G' G -> ok G' ->
  ty_trm ty_general sub_general G' t T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall G G' S U,
  subtyp ty_general sub_general G S U ->
  subenv G' G -> ok G' ->
  subtyp ty_general sub_general G' S U.
Proof.
  intros. apply* narrow_rules.
Qed.

(* ###################################################################### *)
(** * Has member *)

Inductive has_member: ctx -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_any : forall G x T A S U,
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T ->
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
| has_sel : forall G x y B T' A S U,
  ty_trm ty_precise sub_general G (trm_var (avar_f y)) (typ_rcd (dec_typ B T' T')) ->
  has_member G x T' A S U ->
  has_member_rules G x (typ_sel (avar_f y) B) A S U
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
  (exists y B T', T = typ_sel (avar_f y) B /\
    ty_trm ty_precise sub_general G (trm_var (avar_f y)) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst.
  - left. eauto.
  - right. left. exists T1 T2. eauto.
  - right. left. exists T1 T2. eauto.
  - right. right. left. exists T0. eauto.
  - right. right. right. left. exists y B T'. eauto.
  - right. right. right. right. reflexivity.
Qed.

Lemma has_member_inv: forall G x T A S U, has_member G x T A S U ->
  (T = typ_rcd (dec_typ A S U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G x T1 A S U \/
     has_member G x T2 A S U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G x (open_typ x T') A S U) \/
  (exists y B T', T = typ_sel (avar_f y) B /\
    ty_trm ty_precise sub_general G (trm_var (avar_f y)) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst. apply has_member_rules_inv in H1. apply H1.
Qed.

Lemma val_new_typing: forall G s x T ds,
  wf_stack G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise sub_general G (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
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
  wf_stack G s ->
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

Lemma has_member_covariance: forall G s T1 T2 x A S2 U2,
  wf_stack G s ->
  subtyp ty_general sub_tight G T1 T2 ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T1 ->
  has_member G x T2 A S2 U2 ->
  exists S1 U1, has_member G x T1 A S1 U1 /\
                subtyp ty_general sub_tight G S2 S1 /\
                subtyp ty_general sub_tight G U1 U2.
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
    assert (ty_trm ty_general sub_tight G (trm_var (avar_f x)) T) as HS. {
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
Qed.

Lemma has_member_monotonicity: forall G s x T0 ds T A S U,
  wf_stack G s ->
  binds x (val_new T0 ds) s ->
  has_member G x T A S U ->
  exists T1, has_member G x (typ_bnd T0) A T1 T1 /\
             subtyp ty_general sub_tight G S T1 /\
             subtyp ty_general sub_tight G T1 U.
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
      eapply ty_var. eassumption.
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
      apply IHty_trm; eauto.
      inversions H0. assumption.
      inversions H0. inversions H4. assumption.
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
      inversions Heq; inversions H1; inversions H9.
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
  (forall G x T A S U,
    has_member G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise sub_general G T (typ_rcd (dec_typ A S U)))  /\
  (forall G x T A S U,
    has_member_rules G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise sub_general G T (typ_rcd (dec_typ A S U))).
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

Lemma wf_stack_val_new_in_G: forall G s x T ds,
  wf_stack G s ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [S Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [? [? [? [Bis' _]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversion Bis'.
  - destruct H as [T' [ds' [Bis' [Hty Heq]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
    assumption.
Qed.

(* If G ~ s, s |- x = new(x: T)d, and G |-# x: {A: S..U} then G |-# x.A <: U and G |-# S <: x.A. *)
Lemma tight_bound_completeness: forall G s x T ds A S U,
  wf_stack G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
  subtyp ty_general sub_tight G (typ_sel (avar_f x) A) U /\
  subtyp ty_general sub_tight G S (typ_sel (avar_f x) A).
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
  assert (open_typ x T = (typ_rcd (dec_typ A T1 T1)) \/ subtyp ty_precise sub_general G (open_typ x T) (typ_rcd (dec_typ A T1 T1))) as Hsub. {
    destruct has_member_rcd_typ_sub2_mut as [HE _].
    eapply HE; eauto.
  }
  assert (ty_trm ty_precise sub_general G (trm_var (avar_f x)) (open_typ x T)) as Htypx. {
    eapply ty_rec_elim.
    eapply ty_var.
    eapply wf_stack_val_new_in_G; eauto.
  }
  assert (ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T1 T1))) as Htyp. {
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

Lemma all_intro_inversion: forall G S t U,
  ty_trm ty_precise sub_general G (trm_val (val_lambda S t)) U ->
  exists T, U = typ_all S T.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
Qed.

Lemma new_intro_inversion: forall G T ds U,
  ty_trm ty_precise sub_general G (trm_val (val_new T ds)) U ->
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
  ty_trm ty_general sub_general G t T' ->
  possible_types G x (val_new T ds) (typ_rcd (dec_trm a T'))
| pt_rcd_typ : forall G x T ds A T' S U,
  defs_has (open_defs x ds) (def_typ A T') ->
  subtyp ty_general sub_general G S T' ->
  subtyp ty_general sub_general G T' U ->
  possible_types G x (val_new T ds) (typ_rcd (dec_typ A S U))
| pt_lambda : forall L G x S t T S' T',
  (forall y, y \notin L ->
   ty_trm ty_general sub_general (G & y ~ S) (open_trm y t) (open_typ y T)) ->
  subtyp ty_general sub_general G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  possible_types G x (val_lambda S t) (typ_all S' T')
| pt_and : forall G x v S1 S2,
  possible_types G x v S1 ->
  possible_types G x v S2 ->
  possible_types G x v (typ_and S1 S2)
| pt_sel : forall G x v y A S,
  possible_types G x v S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_rcd (dec_typ A S S)) ->
  possible_types G x v (typ_sel y A)
| pt_bnd : forall G x v S S',
  possible_types G x v S ->
  S = open_typ x S' ->
  possible_types G x v (typ_bnd S')
.

Lemma var_new_typing: forall G s x T ds,
  wf_stack G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (open_typ x T).
Proof.
  intros.
  apply ty_rec_elim. apply ty_var. eapply wf_stack_val_new_in_G; eauto.
Qed.

Lemma ty_defs_has: forall G ds T d,
  ty_defs G ds T ->
  defs_has ds d ->
  record_type T ->
  exists D, ty_def G d D /\ record_sub T (typ_rcd D).
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
    + assert (exists D0, ty_def G d D0 /\ record_sub T (typ_rcd D0)) as A. {
        eapply IHrecord_typ; eauto.
        exists ls. eassumption.
      }
      destruct A as [D0 [A1 A2]].
      exists D0. split. apply A1. apply rs_drop. apply A2.
Qed.

Lemma new_ty_defs: forall G s x T ds,
  wf_stack G s ->
  binds x (val_new T ds) s ->
  ty_defs G (open_defs x ds) (open_typ x T).
Proof.
  introv Hwf Bis.
  lets Htyv: (val_new_typing Hwf Bis).
  inversion Htyv; subst.
  pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
  rewrite subst_intro_defs with (x:=y). rewrite subst_intro_typ with (x:=y).
  eapply subst_ty_defs. eapply H3.
  apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto. eauto.
  rewrite <- subst_intro_typ with (x:=y).
  eapply ty_rec_elim. apply ty_var. eapply wf_stack_val_new_in_G; eauto.
  eauto. eauto. eauto.
  assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
  specialize (H Heqm1). destruct H as [? Contra]. inversion Contra.
Qed.

Lemma pt_piece_rcd: forall G s x T ds d D,
  wf_stack G s ->
  binds x (val_new T ds) s ->
  defs_has (open_defs x ds) d ->
  ty_def G d D ->
  possible_types G x (val_new T ds) (typ_rcd D).
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

Lemma record_has_ty_defs: forall G T ds D,
  ty_defs G ds T ->
  record_has T D ->
  exists d, defs_has ds d /\ ty_def G d D.
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
  wf_stack G s ->
  binds x (val_new T ds) s ->
  record_has (open_typ x T) D ->
  possible_types G x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas.
  lets Hdefs: (new_ty_defs Hwf Bis).
  destruct (record_has_ty_defs Hdefs Hhas) as [d [A B]].
  eapply pt_piece_rcd; eauto.
Qed.

Lemma pt_rcd_trm_inversion: forall G s x v a T,
  wf_stack G s ->
  binds x v s ->
  possible_types G x v (typ_rcd (dec_trm a T)) ->
  exists S ds t,
    v = val_new S ds /\
    defs_has (open_defs x ds) (def_trm a t) /\
    ty_trm ty_general sub_general G t T.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T0; simpl in H3; try solve [inversion H3].
    induction d; simpl in H3; try solve [inversion H3].
    unfold open_typ in H3. simpl in H3. inversions H3.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
    unfold open_typ in H3. simpl in H3. inversion H3; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H2; inversion H2; subst.
    inversion H2; subst.
    assert (ty_trm ty_general sub_general G (open_trm x t1) (open_typ x t0)) as A. {
      rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
      eapply subst_ty_trm. eapply H4.
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

Lemma pt_rcd_typ_inversion: forall G s x v A S U,
  wf_stack G s ->
  binds x v s ->
  possible_types G x v (typ_rcd (dec_typ A S U)) ->
  exists T ds T',
    v = val_new T ds /\
    defs_has (open_defs x ds) (def_typ A T') /\
    subtyp ty_general sub_general G S T' /\
    subtyp ty_general sub_general G T' U.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T; simpl in H3; try solve [inversion H3].
    induction d; simpl in H3; try solve [inversion H3].
    unfold open_typ in H3. simpl in H3. inversions H3.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
    unfold open_typ in H3. simpl in H3. inversion H3; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H2; inversion H2; subst.
    inversion H2; subst.
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
    subst. subst. clear H5. clear H8.
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
  wf_stack G s ->
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
  wf_stack G s ->
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
  wf_stack G s ->
  binds x v s ->
  possible_types G x v T0 ->
  subtyp ty_general sub_tight G T0 U0 ->
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
  - (* <:-Sel-tight *)
    eapply pt_sel. eassumption. assumption.
  - (* Sel-<:-tight *)
    inversion HT0; subst.
    assert (record_type (open_typ x T0)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H4 in B. destruct B as [? B]. inversion B.
    assert (T = S) as B. {
      eapply unique_tight_bounds; eauto.
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
    eapply subtyp_trans. eapply tight_to_general_subtyping. eassumption. eassumption.
    eapply subtyp_trans.
    eapply narrow_subtyping. eapply H8; eauto.
    eapply subenv_last. eapply tight_to_general_subtyping. eapply Hsub.
    eapply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
    eapply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
    eapply H; eauto.
Qed.

(*
Lemma (Possible types completeness for values)

If `G ~ s` and `x = v in s` and  `G |-! v: T` then `T in Ts(G, x, v)`.
 *)

Lemma possible_types_completeness_for_values: forall G s x v T,
  wf_stack G s ->
  binds x v s ->
  ty_trm ty_precise sub_general G (trm_val v) T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty. destruct v as [S ds | S t].
  - apply new_intro_inversion in Hty. destruct Hty as [Heq Htype]. subst.
    eapply pt_bnd. eapply pt_new. reflexivity.
  - remember Hty as Hty'. clear HeqHty'. inversion Hty'; subst.
    + apply all_intro_inversion in Hty. destruct Hty as [T' Heq]. subst.
      apply_fresh pt_lambda as y.
      eapply H5; eauto.
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
  wf_stack G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T) as A. {
      destruct (ctx_binds_to_stack_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
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
    + lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]].
    specialize (IHty_trm2 Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]].
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure_tight; eauto.
Qed.

Lemma tight_ty_rcd_typ__new: forall G s x A S U,
  wf_stack G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
  exists T ds, binds x (val_new T ds) s.
Proof.
  introv Hwf Hty.
  destruct (possible_types_completeness_tight Hwf Hty) as [v [Bis Hpt]].
  inversion Hpt; subst; repeat eexists; eauto.
Qed.


Lemma general_to_tight: forall G0 s0,
  wf_stack G0 s0 ->
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     subtyp ty_general sub_tight G S U).
Proof.
  intros G0 s0 Hwf.
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

Lemma general_to_tight_subtyping: forall G s S U,
   wf_stack G s ->
  subtyp ty_general sub_general G S U ->
  subtyp ty_general sub_tight G S U.
Proof.
  intros. apply* general_to_tight.
Qed.

Lemma possible_types_closure: forall G s x v S T,
  wf_stack G s ->
  binds x v s ->
  possible_types G x v S ->
  subtyp ty_general sub_general G S T ->
  possible_types G x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
  eapply general_to_tight_subtyping; eauto.
Qed.

Lemma possible_types_completeness: forall G s x T,
  wf_stack G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T) as A. {
      destruct (ctx_binds_to_stack_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
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
  wf_stack G s ->
  binds x v s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.

Lemma ctx_binds_to_stack_binds_typing: forall G s x T,
  wf_stack G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_stack_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm; eauto.
  rewrite concat_assoc.
  eapply wf_stack_to_ok_G; eauto.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G s x T U,
  wf_stack G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_stack_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
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
    apply ok_push. eapply wf_stack_to_ok_G; eauto. eauto.
    apply ok_push. eapply wf_stack_to_ok_G; eauto. eauto.
    eapply H6; eauto.
Qed.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T.

*)
Lemma canonical_forms_2: forall G s x a T,
  wf_stack G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  (exists S ds t, binds x (val_new S ds) s /\ ty_defs G (open_defs x ds) (open_typ x S) /\ defs_has (open_defs x ds) (def_trm a t) /\ ty_trm ty_general sub_general G t T).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_stack_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [S' [ds [t' [Heq [Hdefs Htyd]]]]].
  subst.
  exists S' ds t'.
  split; try split; try split; try assumption.
  eapply new_ty_defs; eauto.
Qed.

(* ###################################################################### *)
(** * Misc *)

Lemma var_typing_implies_avar_f: forall G a T,
  ty_trm ty_general sub_general G (trm_var a) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm.
Qed.

Lemma val_typing: forall G v T,
  ty_trm ty_general sub_general G (trm_val v) T ->
  exists T', ty_trm ty_precise sub_general G (trm_val v) T' /\
             subtyp ty_general sub_general G T' T.
Proof.
  intros. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro with (L:=L); eauto. apply subtyp_refl.
  - destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(*
Let G |- t: T and G ~ s. Then either

- t is a normal form, or
- there exists a stack s', term t' such that s | t -> s' | t', and for any such s', t' there exists an environment G'' such that, letting G' = G, G'' one has G' |- t': T and G' ~ s'.
The proof is by a induction on typing derivations of G |- t: T.
*)

Lemma safety: forall G s t T,
  wf_stack G s ->
  ty_trm ty_general sub_general G t T ->
  (normal_form t \/ (exists s' t' G' G'', red t s t' s' /\ G' = G & G'' /\ ty_trm ty_general sub_general G' t' T /\ wf_stack G' s')).
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
    apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto. eauto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=S).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. eauto.
  - (* Fld-E *) right.
    lets C: (canonical_forms_2 Hwf H).
    destruct C as [S [ds [t [Bis [Tyds [Has Ty]]]]]].
    exists s t G (@empty typ).
    split.
    apply red_sel with (T:=S) (ds:=ds); try assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    assumption.
    assumption.
  - (* Let *) right.
    destruct t.
    + (* var *)
      assert (exists x, a = avar_f x) as A. {
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
      apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto. eauto.
      rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. eauto.
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
      apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
      apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
      apply wf_stack_push. assumption. eauto. eauto. assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_stack_to_ok_G. eassumption. eauto.
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
      rewrite <- IH2. eapply wf_stack_to_ok_G. eassumption.
Qed.
