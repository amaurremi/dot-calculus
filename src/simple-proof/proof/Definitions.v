(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    Coq library by Arthur Chargueraud. *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.

Require Export TLC.LibLN.

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

(** A stack, represented as the sequence of variable-to-value
    let bindings, [(let x = v in)*], that is represented as a value environment
    which maps variables to values.
    The operational semantics will be defined in terms of pairs [(s, t)] where
    [s] is a stack and [t] is a term.
    For example, the term [let x1 = v1 in let x2 = v2 in t] is represented as
    [({(x1 = v1), (x2 = v2)}, t)].
    *)
Definition sta := env val.

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
Definition open_typ  u T := open_rec_typ   0 u T.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.
Hint Unfold open_avar open_typ open_dec open_trm open_val open_def open_defs.

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
Definition fv_sta_vals(s: sta): vars := (fv_in_values (fun v => fv_val v) s).

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

(** * Well-typed stacks *)

(** The operational semantics is defined in terms of pairs [(s, t)], where
    [s] is a stack and [t] is a term.
    Given a typing [G ⊢ (s, t): T], [well_typed] establishes a correspondence
    between [G] and the stack [s].

    We say that [s] is well-typed with respect to [G] if
    - [G = {(xi mapsto Ti) | i = 1, ..., n}]
    - [s = {(xi mapsto vi) | i = 1, ..., n}]
    - [G ⊢ vi: Ti].

    We say that [s] is well-typed with respect to [G], denoted as [s: G]. *)

Definition well_typed (G : ctx) (s : sta) : Prop :=
  ok G /\
  ok s /\
  (dom G = dom s) /\
  (forall x T v, binds x T G ->
            binds x v s ->
            G ⊢ trm_val v : T).

(** * Infrastructure *)

Hint Unfold well_typed.
Hint Constructors
     ty_trm ty_def ty_defs subtyp.

(** ** Mutual Induction Principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_def_mut    := Induction for ty_def Sort Prop
with   rules_defs_mut   := Induction for ty_defs Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.


(** ** Tactics *)

(** Tactics for generating fresh variables. *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sta       => dom x \u fv_sta_vals x) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Ltac fresh_constructor :=
  match goal with
  | [ |- _ ⊢ trm_val (val_new _ _) : typ_bnd _ ] =>
    apply_fresh ty_new_intro as z
  | [ |- _ ⊢ trm_val (val_lambda _ _) : typ_all _ _ ] =>
    apply_fresh ty_all_intro as z
  | [ |- _ ⊢ trm_let _ _ : _ ] =>
    apply_fresh ty_let as z
  | [ |- _ ⊢ typ_all _ _ <: typ_all _ _ ] =>
    apply_fresh subtyp_all as z
  end; auto.

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

Ltac repeat_split_right :=
  match goal with
  | |- ?A /\ ?B => split; repeat_split_right
  | _ => idtac
  end.

Ltac omega := Coq.omega.Omega.omega.
