(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    Coq library by Arthur Chargueraud. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import String.

Parameter typ_label: Set.
Parameter trm_label: Set.

(** * Abstract Syntax *)

(** *** Variables ([x], [y], [z])
    The proof represents variables using the
    #<a href="http://www.chargueraud.org/softs/ln/">locally nameless representation</a>#:
    - [avar_b n] represents a variable using the de Bruijn index [n];
    - [avar_f x] represents a free variable with name [x].
    de Bruijn-indexed variables represent bound variables, whereas named variables represent free variables
    that are in the evaluation context/type environment.  *)
Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : var -> avar.

(** *** Term and type members
        Type member labels ([A], [B], [C]) and term (field) member labels ([a], [b], [c]).  *)
Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

(** *** Types
    Types ([typ], [S], [T], [U]) and type declarations ([dec], [D]):
    - [typ_top] represents [top];
    - [typ_bot] represents [bottom];
    - [typ_rcd d] represents a record type [d], where [d] is either a type or field declaration;
    - [typ_and T U] represents an intersection type [T /\ U];
    - [typ_sel x A] represents type selection [x.A];
    - [typ_bnd T] represents a recursive type [mu(x: T)]; however, since [x] is bound in the recursive type,
      it is referred to in [T] using the de Bruijn index 0, and is therefore omitted from the type representation;
      we will denote recursive types as [mu(T)];
    - [typ_all T U] represents the dependent function type [forall(x: T)U]; as in the previous case,
      [x] represents a variable bound in [U], and is therefore omitted from the representation;
      we will denote function types as [forall(T)U]. *)
Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ
  | typ_bnd  : typ -> typ
  | typ_all  : typ -> typ -> typ
(**
  - [dec_typ A S T] represents a type declaraion [{A: S..T}];
  - [dec_trm a T] represents a field declaration [{a: T}] . *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_trm  : trm_label -> typ -> dec.

(** *** Terms
  Terms ([trm], [t], [u]), values ([val], [v]),
   member definitions ([def], [d] and [defs], [ds]):
  - [trm_var x] represents a variable [x];
  - [trm_val v] represents a value [v];
  - [trm_sel x a] represents a field selection [x.a];
  - [trm_app x y] represents a function application [x y];
  - [trm_let t u] represents a let binding [let x = t in u]; since x is bound in [u],
    it is referred to in [u] using the de Bruijn index 0, and is therefore omitted from
    the let-term representation; we will denote let terms as [let t in u]. *)
Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_val  : val -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm
(**
  - [val_new T ds] represents the object [nu(x: T)ds]; the variable [x] is bound in [T]
    and [ds] and is omitted from the representation;
    we will denote new object definitions as [nu(T)ds];
  - [val_lambda T t] represents a function [lambda(x: T)t]; again, [x] is bound in [t]
    and is omitted;
    we will denote lambda terms as [lambda(T)t. *)
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
(**
  - [def_typ A T] represents a type-member definition [{A = T}];
  - [def_trm a t] represents a field definition [{a = t}]; *)
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
(**
  [defs] represents a list of definitions that are part of an intersection
  - [defs_nil] represents the empty list;
  - [defs_cons d ds] represents a concatenation of the definition [d] to the definitions [ds]. *)
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** Helper functions to retrieve labels of declarations and definitions *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm m _   => label_trm m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.

Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

(** Typing environment ([G]) *)
Definition ctx := env typ.

(** The sequence of variable-to-value let bindings, [(let x = v in)*],
     is represented as a value environment that maps variables to values: *)
Definition sto := env val.

(** * Opening *)
(** Opening takes a bound variable that is represented with a de Bruijn index [k]
    and replaces it by a named variable [u].
    The following functions define opening on variables, types, declarations, terms,
    values, and definitions.

    We will denote an identifier [X] opened with a variable [y] as [X^y]. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m T   => dec_trm m (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_sel v m    => trm_sel (open_rec_avar k u v) m
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.
Hint Unfold open_avar open_typ open_dec open_trm open_val open_def open_defs.

(** * Closing *)
(** The opposite direction of opening *)
Definition close_rec_avar k u a : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = u then avar_b k else avar_f x
  end.
Hint Unfold close_rec_avar.

Fixpoint close_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (close_rec_dec k u D)
  | typ_and T1 T2  => typ_and (close_rec_typ k u T1) (close_rec_typ k u T2)
  | typ_sel x L    => typ_sel (close_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (close_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (close_rec_typ k u T1) (close_rec_typ (S k) u T2)
  end
with close_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (close_rec_typ k u T) (close_rec_typ k u U)
  | dec_trm m T   => dec_trm m (close_rec_typ k u T)
  end.
Hint Unfold close_rec_typ close_rec_dec.


Fixpoint close_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (close_rec_avar k u a)
  | trm_val v      => trm_val (close_rec_val k u v)
  | trm_sel v m    => trm_sel (close_rec_avar k u v) m
  | trm_app f a    => trm_app (close_rec_avar k u f) (close_rec_avar k u a)
  | trm_let t1 t2  => trm_let (close_rec_trm k u t1) (close_rec_trm (S k) u t2)
  end
with close_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (close_rec_typ (S k) u T) (close_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (close_rec_typ k u T) (close_rec_trm (S k) u e)
  end
with close_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (close_rec_typ k u T)
  | def_trm m e => def_trm m (close_rec_trm k u e)
  end
with close_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (close_rec_defs k u tl) (close_rec_def k u d)
  end.
Hint Unfold close_rec_trm close_rec_val close_rec_def close_rec_defs.

Definition close_avar u a := close_rec_avar  0 u a.
Definition close_typ  u t := close_rec_typ   0 u t.
Definition close_dec  u D := close_rec_dec   0 u D.
Definition close_trm  u e := close_rec_trm   0 u e.
Definition close_val  u v := close_rec_val   0 u v.
Definition close_def  u d := close_rec_def   0 u d.
Definition close_defs u l := close_rec_defs  0 u l.
Hint Unfold close_avar close_typ close_dec close_trm close_val close_def close_defs.


(** * Free variables
      Functions that retrieve the free variables of a symbol. *)

(** Free variable in a variable. *)
Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

(** Free variables in a type or declaration. *)
Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
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

(** Free variables in a term, value, or definition. *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a       => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
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

(** Free variables in the range (types) of a context *)
Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).
Definition fv_sto_vals(e: sto): vars := (fv_in_values (fun v => fv_val v) e).

(** * Typing Rules *)

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '⊢' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '/-' d : D" (at level 40, d at level 59).
Reserved Notation "G '/-' ds :: D" (at level 40, ds at level 59).

(** ** Term typing [G ⊢ t: T] *)
Inductive ty_trm : ctx -> trm -> typ -> Prop :=

(** [G(x) = T]  #<br>#
    [――――――――]  #<br>#
    [G ⊢ x: T]  *)
| ty_var : forall G x T,
    binds x T G ->
    G ⊢ trm_var (avar_f x) : T

(** [G, x: T ⊢ t^x: U^x]     #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ lambda(T)t: forall(T)U]      *)
| ty_all_intro : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢ trm_val (val_lambda T t) : typ_all T U

(** [G ⊢ x: forall(S)T] #<br>#
    [G ⊢ z: S]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x z: T^z]     *)
| ty_all_elim : forall G x z S T,
    G ⊢ trm_var (avar_f x) : typ_all S T ->
    G ⊢ trm_var (avar_f z) : S ->
    G ⊢ trm_app (avar_f x) (avar_f z) : open_typ z T

(** [G, x: T^x ⊢ ds^x :: T^x]  #<br>#
    [x fresh]                  #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [G ⊢ nu(T)ds :: mu(T)]          *)
| ty_new_intro : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G ⊢ trm_val (val_new T ds) : typ_bnd T

(** [G ⊢ x: {a: T}] #<br>#
    [―――――――――――――] #<br>#
    [G ⊢ x.a: T]        *)
| ty_new_elim : forall G x a T,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    G ⊢ trm_sel (avar_f x) a : T

(** [G ⊢ t: T]          #<br>#
    [G, x: T ⊢ u^x: U]  #<br>#
    [x fresh]           #<br>#
    [―――――――――――――――――] #<br>#
    [G ⊢ let t in u: U]     *)
| ty_let : forall L G t u T U,
    G ⊢ t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢ trm_let t u : U

(** [G ⊢ x: T^x]   #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: mu(T)]     *)
| ty_rec_intro : forall G x T,
    G ⊢ trm_var (avar_f x) : open_typ x T ->
    G ⊢ trm_var (avar_f x) : typ_bnd T

(** [G ⊢ x: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: T^x]   *)
| ty_rec_elim : forall G x T,
    G ⊢ trm_var (avar_f x) : typ_bnd T ->
    G ⊢ trm_var (avar_f x) : open_typ x T

(** [G ⊢ x: T]     #<br>#
    [G ⊢ x: U]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: T /\ U]     *)
| ty_and_intro : forall G x T U,
    G ⊢ trm_var (avar_f x) : T ->
    G ⊢ trm_var (avar_f x) : U ->
    G ⊢ trm_var (avar_f x) : typ_and T U

(** [G ⊢ t: T]   #<br>#
    [G ⊢ T <: U] #<br>#
    [――――――――――] #<br>#
    [G ⊢ t: U]   *)
| ty_sub : forall G t T U,
    G ⊢ t : T ->
    G ⊢ T <: U ->
    G ⊢ t : U
where "G '⊢' t ':' T" := (ty_trm G t T)

(** ** Single-definition typing [G ⊢ d: D] *)
with ty_def : ctx -> def -> dec -> Prop :=
(** [G ⊢ {A = T}: {A: T..T}]   *)
| ty_def_typ : forall G A T,
    G /- def_typ A T : dec_typ A T T

(** [G ⊢ t: T]            #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢ {a = t}: {a: T}] *)
| ty_def_trm : forall G a t T,
    G ⊢ t : T ->
    G /- def_trm a t : dec_trm a T
where "G '/-' d ':' D" := (ty_def G d D)

(** ** Multiple-definition typing [G ⊢ ds :: T] *)
with ty_defs : ctx -> defs -> typ -> Prop :=
(** [G ⊢ d: D]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢ d ++ defs_nil : D] *)
| ty_defs_one : forall G d D,
    G /- d : D ->
    G /- defs_cons defs_nil d :: typ_rcd D

(** [G ⊢ ds :: T]         #<br>#
    [G ⊢ d: D]            #<br>#
    [d \notin ds]         #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢ ds ++ d : T /\ D] *)
| ty_defs_cons : forall G ds d T D,
    G /- ds :: T ->
    G /- d : D ->
    defs_hasnt ds (label_of_def d) ->
    G /- defs_cons ds d :: typ_and T (typ_rcd D)
where "G '/-' ds '::' T" := (ty_defs G ds T)

(** ** Subtyping [G ⊢ T <: U] *)
with subtyp : ctx -> typ -> typ -> Prop :=

(** [G ⊢ T <: top] *)
| subtyp_top: forall G T,
    G ⊢ T <: typ_top

(** [G ⊢ bot <: T] *)
| subtyp_bot: forall G T,
    G ⊢ typ_bot <: T

(** [G ⊢ T <: T] *)
| subtyp_refl: forall G T,
    G ⊢ T <: T

(** [G ⊢ S <: T]     #<br>#
    [G ⊢ T <: U]     #<br>#
    [――――――――――]     #<br>#
    [G ⊢ S <: U]         *)
| subtyp_trans: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ T <: U ->
    G ⊢ S <: U

(** [G ⊢ T /\ U <: T] *)
| subtyp_and11: forall G T U,
    G ⊢ typ_and T U <: T

(** [G ⊢ T /\ U <: U] *)
| subtyp_and12: forall G T U,
    G ⊢ typ_and T U <: U

(** [G ⊢ S <: T]       #<br>#
    [G ⊢ S <: U]       #<br>#
    [――――――――――――――]   #<br>#
    [G ⊢ S <: T /\ U]          *)
| subtyp_and2: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S <: U ->
    G ⊢ S <: typ_and T U

(** [G ⊢ T <: U]           #<br>#
    [――――――――――――――――――――] #<br>#
    [G ⊢ {a: T} <: {a: U}] *)
| subtyp_fld: forall G a T U,
    G ⊢ T <: U ->
    G ⊢ typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)

(** [G ⊢ S2 <: S1]                   #<br>#
    [G ⊢ T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G ⊢ {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ: forall G A S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ S <: x.A]     *)
| subtyp_sel2: forall G x A S T,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_typ A S T) ->
    G ⊢ S <: typ_sel (avar_f x) A

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ x.A <: T]     *)
| subtyp_sel1: forall G x A S T,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_typ A S T) ->
    G ⊢ typ_sel (avar_f x) A <: T

(** [G ⊢ S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]     #<br>#
    [x fresh]                     #<br>#
    [―――――――――――――――――――――――]     #<br>#
    [G ⊢ forall(S1)T1 <: forall(S2)T2]      *)
| subtyp_all: forall L G S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢ typ_all S1 T1 <: typ_all S2 T2
where "G '⊢' T '<:' U" := (subtyp G T U).

(** ** Well-formed Stores *)

(** Given a typing [G ⊢ e[t]: T], [wf_sto] establishes a correspondence
    between [G] and the store [s] that is used to define the
    evaluation context [e].
    We say that [s] is well-formed with respect to [G], denoted [G ~~ s], if
    - [G = {(xi mapsto Ti) | i = 1, ..., n}]
    - [s = {(xi mapsto vi) | i = 1, ..., n}]
    - [G ⊢ vi: Ti].
*)

Reserved Notation "G '~~' s" (at level 40).

Inductive wf_sto: ctx -> sto -> Prop :=
| wf_sto_empty: empty ~~ empty
| wf_sto_push: forall G s x T v,
    G ~~ s ->
    x # G ->
    x # s ->
    G ⊢ trm_val v : T ->
    G & x ~ T ~~ s & x ~ v
where "G '~~' s" := (wf_sto G s).

(** * Typing Relations for the Safety Proof *)
(** The following typing relations are not part of the DOT calculus, but are used
    in the proof of DOT's safety theorems. *)

Reserved Notation "G '⊢!' t ':' T" (at level 40, t at level 59).

(** ** Precise typing [G ⊢! t: T] *)
(** Precise typing is used to reason about the types of variables and values.
    Precise typing does not "modify" a variable's or value's type through subtyping.
    - For values, precise typing allows to only retrieve the "immediate" type of the value.
      It types objects with recursive types, and functions with dependent-function types. #<br>#
      For example, if a value is the object [nu(x: {a: T}){a = x.a}], the only way to type
      the object through precise typing is [G ⊢! nu(x: {a: T}){a = x.a}: mu(x: {a: T})].
    - For variables, we start out with a type [T=G(x)] (the type to which the variable is
      bound in [G]). Then we use precise typing to additionally deconstruct [T]
      by using recursion elimination and intersection elimination. #<br>#
      For example, if [G(x)=mu(x: {a: T} /\ {B: S..U})], then we can derive the following
      precise types for [x]:               #<br>#
      [G ⊢! x: mu(x: {a: T} /\ {B: S..U})] #<br>#
      [G ⊢! x: {a: T} /\ {B: S..U}]        #<br>#
      [G ⊢! x: {a: T}]                    #<br>#
      [G ⊢! x: {B: S..U}].                *)

Inductive ty_trm_p : ctx -> trm -> typ -> Prop :=

(** [G(x) = T]      #<br>#
    [―――――――――――――] #<br>#
    [G ⊢! x: T] *)
| ty_var_p : forall G x T,
    binds x T G ->
    G ⊢! trm_var (avar_f x) : T

(** [G, x: T ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⊢! lambda(T)t: forall(T) U]     *)
| ty_all_intro_p : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢! trm_val (val_lambda T t) : typ_all T U

(** [G, x: T^x ⊢ ds^x :: T^x]   #<br>#
    [x fresh]                   #<br>#
    [―――――――――――――――――――――――]   #<br>#
    [G ⊢! nu(T)ds :: mu(T)]        *)
| ty_new_intro_p : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G ⊢! trm_val (val_new T ds) : typ_bnd T

(** [G ⊢! x: mu(T)] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! x: T^x]       *)
| ty_rec_elim_p : forall G x T,
    G ⊢! trm_var (avar_f x) : typ_bnd T ->
    G ⊢! trm_var (avar_f x) : open_typ x T

(** [G ⊢! x: T /\ U] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! x: T]     *)
| ty_and1_p : forall G x T U,
    G ⊢! trm_var (avar_f x) : typ_and T U ->
    G ⊢! trm_var (avar_f x) : T

(** [G ⊢! x: T /\ U] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! x: U]     *)
| ty_and2_p : forall G x T U,
    G ⊢! trm_var (avar_f x) : typ_and T U ->
    G ⊢! trm_var (avar_f x) : U
where "G '⊢!' t ':' T" := (ty_trm_p G t T).


(** ** Tight typing *)

Reserved Notation "G '⊢#' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '⊢#' T '<:' U" (at level 40, T at level 59).

(** *** Tight term typing [G ⊢# t: T] *)
(** Tight typing is very similar to general typing, and could be obtained by replacing
    all occurrences of [⊢] with [⊢#], except for the following:
    - in the type selection subtyping rules Sel-<: and <:-Sel ([subtyp_sel1] and [subtyp_sel2]),
      the premise is precise typing of a type declaration with equal bounds;
    - whenever a typing judgement in a premise extends the environment (for example, [ty_all_intro_t]),
      it is typed under general typing [⊢] and not tight typing [⊢#]. *)

Inductive ty_trm_t : ctx -> trm -> typ -> Prop :=

(** [G(x) = T]   #<br>#
    [――――――――――] #<br>#
    [G ⊢# x: T]  *)
| ty_var_t : forall G x T,
    binds x T G ->
    G ⊢# trm_var (avar_f x) : T

(** [G, x: T ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⊢# lambda(T)t: forall(T)U]     *)
| ty_all_intro_t : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢# trm_val (val_lambda T t) : typ_all T U

(** [G ⊢# x: forall(S)T] #<br>#
    [G ⊢# z: S]     #<br>#
    [――――――――――――――] #<br>#
    [G ⊢# x z: T^z]     *)
| ty_all_elim_t : forall G x z S T,
    G ⊢# trm_var (avar_f x) : typ_all S T ->
    G ⊢# trm_var (avar_f z) : S ->
    G ⊢# trm_app (avar_f x) (avar_f z) : open_typ z T

(** [G, x: T^x ⊢ ds^x :: T^x]    #<br>#
    [x fresh]                    #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [G ⊢# nu(T)ds :: mu(T)]         *)
| ty_new_intro_t : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G ⊢# trm_val (val_new T ds) : typ_bnd T

(** [G ⊢# x: {a: T}] #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢# x.a: T]        *)
| ty_new_elim_t : forall G x a T,
    G ⊢# trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    G ⊢# trm_sel (avar_f x) a : T

(** [G ⊢# t: T]             #<br>#
    [G, x: T ⊢ u^x: U]       #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――]       #<br>#
    [G ⊢# let t in u: U]        *)
| ty_let_t : forall L G t u T U,
    G ⊢# t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢# trm_let t u : U

(** [G ⊢# x: T^x]   #<br>#
    [――――――――――――――] #<br>#
    [G ⊢# x: mu(T)] *)
| ty_rec_intro_t : forall G x T,
    G ⊢# trm_var (avar_f x) : open_typ x T ->
    G ⊢# trm_var (avar_f x) : typ_bnd T

(** [G ⊢# x: mu(T)] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢# x: T^x]       *)
| ty_rec_elim_t : forall G x T,
    G ⊢# trm_var (avar_f x) : typ_bnd T ->
    G ⊢# trm_var (avar_f x) : open_typ x T

(** [G ⊢# x: T]      #<br>#
    [G ⊢# x: U]      #<br>#
    [―――――――――――――]   #<br>#
    [G ⊢# x: T /\ U]      *)
| ty_and_intro_t : forall G x T U,
    G ⊢# trm_var (avar_f x) : T ->
    G ⊢# trm_var (avar_f x) : U ->
    G ⊢# trm_var (avar_f x) : typ_and T U

(** [G ⊢# t: T]    #<br>#
    [G ⊢# T <: U]  #<br>#
    [―――――――――――――] #<br>#
    [G ⊢# t: U]        *)
| ty_sub_t : forall G t T U,
    G ⊢# t : T ->
    G ⊢# T <: U ->
    G ⊢# t : U
where "G '⊢#' t ':' T" := (ty_trm_t G t T)

(** *** Tight subtyping [G ⊢# T <: U] *)
with subtyp_t : ctx -> typ -> typ -> Prop :=

(** [G ⊢# T <: top] *)
| subtyp_top_t: forall G T,
    G ⊢# T <: typ_top

(** [G ⊢# bot <: T] *)
| subtyp_bot_t: forall G T,
    G ⊢# typ_bot <: T

(** [G ⊢# T <: T] *)
| subtyp_refl_t: forall G T,
    G ⊢# T <: T

(** [G ⊢# S <: T]     #<br>#
    [G ⊢# T <: U]     #<br>#
    [―――――――――――――]    #<br>#
    [G ⊢# S <: U]         *)
| subtyp_trans_t: forall G S T U,
    G ⊢# S <: T ->
    G ⊢# T <: U ->
    G ⊢# S <: U

(** [G ⊢# T /\ U <: T] *)
| subtyp_and11_t: forall G T U,
    G ⊢# typ_and T U <: T

(** [G ⊢# T /\ U <: U] *)
| subtyp_and12_t: forall G T U,
    G ⊢# typ_and T U <: U

(** [G ⊢# S <: T]       #<br>#
    [G ⊢# S <: U]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢# S <: T /\ U]       *)
| subtyp_and2_t: forall G S T U,
    G ⊢# S <: T ->
    G ⊢# S <: U ->
    G ⊢# S <: typ_and T U

(** [G ⊢# T <: U]           #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢# {a: T} <: {a: U}]     *)
| subtyp_fld_t: forall G a T U,
    G ⊢# T <: U ->
    G ⊢# typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)

(** [G ⊢# S2 <: S1]                   #<br>#
    [G ⊢# T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢# {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_t: forall G A S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢# T <: x.A]         *)
| subtyp_sel2_t: forall G x A T,
    G ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G ⊢# T <: typ_sel (avar_f x) A

(** [G ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢# x.A <: T]         *)
| subtyp_sel1_t: forall G x A T,
    G ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G ⊢# typ_sel (avar_f x) A <: T

(** [G ⊢# S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⊢# forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_t: forall L G S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢# typ_all S1 T1 <: typ_all S2 T2
where "G '⊢#' T '<:' U" := (subtyp_t G T U).


(** ** Invertible typing *)

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⊢! x: {a: T}],
and [G ⊢ T <: T'], then [G ⊢## x: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). *)

(** *** Invertible typing of variables [G ⊢## x: T] *)

Reserved Notation "G '⊢##' x ':' T" (at level 40, x at level 59).

Inductive ty_var_inv : ctx -> var -> typ -> Prop :=

(** [G ⊢! x: T]  #<br>#
    [―――――――――――] #<br>#
    [G ⊢## x: T]     *)
| ty_precise_inv : forall G x T,
  G ⊢! trm_var (avar_f x) : T ->
  G ⊢## x : T

(** [G ⊢## x: {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x: {a: U}]     *)
| ty_dec_trm_inv : forall G x a T U,
  G ⊢## x : typ_rcd (dec_trm a T) ->
  G ⊢# T <: U ->
  G ⊢## x : typ_rcd (dec_trm a U)

(** [G ⊢## x: {A: T..U}]   #<br>#
    [G ⊢# T' <: T]         #<br>#
    [G ⊢# U <: U']         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## x: {A: T'..U'}]     *)
| ty_dec_typ_inv : forall G x A T T' U' U,
  G ⊢## x : typ_rcd (dec_typ A T U) ->
  G ⊢# T' <: T ->
  G ⊢# U <: U' ->
  G ⊢## x : typ_rcd (dec_typ A T' U')

(** [G ⊢## x: T^x]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## x: mu(T)] *)
| ty_bnd_inv : forall G x T,
  G ⊢## x : open_typ x T ->
  G ⊢## x : typ_bnd T

(** [G ⊢## x: forall(S)T]          #<br>#
    [G ⊢# S' <: S]            #<br>#
    [G, y: S' ⊢ T^y <: T'^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## x: forall(S')T']            *)
| ty_all_inv : forall L G x S T S' T',
  G ⊢## x : typ_all S T ->
  G ⊢# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' ⊢ open_typ y T <: open_typ y T') ->
  G ⊢## x : typ_all S' T'

(** [G ⊢## x : T]     #<br>#
    [G ⊢## x : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x : T /\ U]      *)
| ty_and_inv : forall G x S1 S2,
  G ⊢## x : S1 ->
  G ⊢## x : S2 ->
  G ⊢## x : typ_and S1 S2

(** [G ⊢## x: S]        #<br>#
    [G ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## x: y.A           *)
| ty_sel_inv : forall G x y A S,
  G ⊢## x : S ->
  G ⊢! trm_var y : typ_rcd (dec_typ A S S) ->
  G ⊢## x : typ_sel y A

(** [G ⊢## x: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## x: top]     *)
| ty_top_inv : forall G x T,
  G ⊢## x : T ->
  G ⊢## x : typ_top
where "G '⊢##' x ':' T" := (ty_var_inv G x T).

(** *** Invertible typing of values [G ⊢##v v: T] *)

Reserved Notation "G '⊢##v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_inv : ctx -> val -> typ -> Prop :=

(** [G ⊢! v: T]    #<br>#
    [―――――――――――――] #<br>#
    [G ⊢##v v: T] *)
| ty_precise_inv_v : forall G v T,
  G ⊢! trm_val v : T ->
  G ⊢##v v : T

(** [G ⊢##v v: forall(S)T]          #<br>#
    [G ⊢# S' <: S]             #<br>#
    [G, y: S' ⊢ T^y <: T'^y]    #<br>#
    [y fresh]                   #<br>#
    [――――――――――――――――――――――]    #<br>#
    [G ⊢##v v: forall(S')T']            *)
| ty_all_inv_v : forall L G v S T S' T',
  G ⊢##v v : typ_all S T ->
  G ⊢# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' ⊢ open_typ y T <: open_typ y T') ->
  G ⊢##v v : typ_all S' T'

(** [G ⊢##v v: S]       #<br>#
    [G ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢##v v: y.A]         *)
| ty_sel_inv_v : forall G v y A S,
  G ⊢##v v : S ->
  G ⊢! trm_var y : typ_rcd (dec_typ A S S) ->
  G ⊢##v v : typ_sel y A

(** [G ⊢##v v : T]        #<br>#
    [G ⊢##v v : U]        #<br>#
    [―――――――――――――]        #<br>#
    [G ⊢##v v : T /\ U]        *)
| ty_and_inv_v : forall G v T U,
  G ⊢##v v : T ->
  G ⊢##v v : U ->
  G ⊢##v v : typ_and T U

(** [G ⊢##v v: T]   #<br>#
    [――――――――――――――] #<br>#
    [G ⊢##v v: top]     *)
| ty_top_inv_v : forall G v T,
  G ⊢##v v : T ->
  G ⊢##v v : typ_top
where "G '⊢##v' v ':' T" := (ty_val_inv G v T).

(** ** Record types *)
(** In the proof, it is useful to be able to distinguish record types from
    other types. A record type is a concatenation of type declarations with equal
    bounds [{A: T..T}] and field declarations [{a: T}]. *)

(** A record declaration is either a type declaration with equal bounds,
    or a field declaration.*)
Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T).

(** Given a record declaration, a [record_typ] keeps track of the declaration's
    field member labels (i.e. names of fields) and type member labels
    (i.e. names of abstract type members). [record_typ] also requires that the
    labels are distinct.  *)
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

(** A [record_type] is a [record_typ] with an unspecified set of labels. The meaning
    of [record_type] is an intersection of type/field declarations with distinct labels. *)
Definition record_type T := exists ls, record_typ T ls.

(** Given a type [T = D1 /\ D2 /\ ... /\ Dn] and member declaration [D], [record_has T D] tells whether
    [D] is contained in the intersection of [Di]'s. *)
Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

(** ** Inert types
       A type is inert if it is either a dependent function type, or a recursive type
       whose type declarations have equal bounds (enforced through [record_type]). #<br>#
       For example, the following types are inert:
       - [lambda(x: S)T]
       - [mu(x: {a: T} /\ {B: U..U})]
       - [mu(x: {C: {A: T..U}..{A: T..U}})]
       And the following types are not inert:
       - [{a: T}]
       - [{B: U..U}]
       - [top]
       - [x.A]
       - [mu(x: {B: S..T})], where [S <> T]. *)
Inductive inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (typ_all S T)
  | inert_typ_bnd : forall T,
      record_type T ->
      inert_typ (typ_bnd T)
  | inert_typ_top : inert_typ typ_top.
  (* | inert_typ_sel :forall x A, inert_typ (typ_sel (avar_f x) A). *)

(** An inert context is a typing context whose range consists only of inert types. *)
Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_all : forall G x T,
      inert G ->
      inert_typ T ->
      x # G ->
      inert (G & x ~ T).

(** * Infrastructure *)

Hint Constructors
     inert_typ inert record_has
     ty_trm ty_def ty_defs subtyp ty_trm_p
     ty_trm_t subtyp_t ty_var_inv ty_val_inv.

(** ** Mutual Induction Principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ts_ty_trm_t_mut := Induction for ty_trm_t Sort Prop
with   ts_subtyp_t     := Induction for subtyp_t Sort Prop.
Combined Scheme ts_mutind_t from ts_ty_trm_t_mut, ts_subtyp_t.

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_def_mut    := Induction for ty_def Sort Prop
with   rules_defs_mut   := Induction for ty_defs Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.


(** * Tactics *)

(** Tactics for generating fresh variables. *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sto       => dom x \u fv_sto_vals x) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  (* let K := gather_vars_with (fun x : ec        => fv_ec    x) in *)
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J (* \u K *) ).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Ltac fresh_constructor :=
  apply_fresh ty_new_intro as z ||
  apply_fresh ty_all_intro as z ||
  apply_fresh ty_let as z ||
  apply_fresh subtyp_all as z; auto.

(** Tactics for naming cases in case analysis. *)

Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.

(** Automatically destruct premises *)
Ltac destruct_all :=
  repeat match goal with
  | [ H : exists x, _ |- _ ]  => destruct H
  | [ H : ?A /\ ?B |- _ ] => destruct H
  | [ H : ?A \/ ?B |- _ ] => destruct H
  end.
