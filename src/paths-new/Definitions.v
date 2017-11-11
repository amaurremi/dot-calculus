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
Require Import String List.

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

(** The fields of a path in reverse order.
    E.g. for a path x.a1.a2...an, a list [an, ..., a2, a1]. *)
Definition fields := list trm_label.

(** todo *)
Inductive path :=
  | p_sel : avar -> fields ->  path.

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
  | typ_path : path -> typ_label -> typ
  | typ_bnd  : typ -> typ
  | typ_all  : typ -> typ -> typ
(**
  - [dec_typ A S T] represents a type declaraion [{A: S..T}];
  - [dec_trm a T] represents a field declaration [{a: T}] . *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_trm  : trm_label -> typ -> dec.

(*Notation "'{' a ':' T '}'" := (dec_trm a T) (T at level 50).*)
Notation "'{' A '>:' S '<:' T '}'" := (dec_typ A S T) (S at level 58).

(** *** Terms
  Terms ([trm], [t], [u]), values ([val], [v]),
   member definitions ([def], [d] and [defs], [ds]):
  - [trm_val v] represents a value [v];
  - [trm_app p q] represents a function application [p q];
  - [trm_let t u] represents a let binding [let x = t in u]; since x is bound in [u],
    it is referred to in [u] using the de Bruijn index 0, and is therefore omitted from
    the let-term representation; we will denote let terms as [let t in u];
  - [trm_path p] represents a path [p]. *)
Inductive trm : Set :=
  | trm_val  : val -> trm
  | trm_app  : path -> path -> trm
  | trm_let  : trm -> trm -> trm
  | trm_path : path -> trm
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

Definition pavar (x: avar) := p_sel x nil.
Definition pvar (x: var) := p_sel (avar_f x) nil.
Definition tvar (x: var) := trm_path (pvar x).
Definition sel_fields (p : path) (bs : list trm_label) :=
  match p with
  | p_sel x bs' => p_sel x (bs ++ bs')
  end.
Notation "p '•' a" := (sel_fields p (a :: nil)) (at level 5).

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

(** A list of field paths, representing a list of paths
    that start with the same variable. *)
Definition paths := list fields.

(** The sequence of variable-to-value let bindings, [(let x = v in)*],
     is represented as a value environment that maps variables to values: *)
Definition sto := env val.

(** * Opening *)
(** Opening takes a bound variable that is represented with a de Bruijn index [k]
    and replaces it by a named variable or path [u].
    The following functions define opening on paths, types, declarations, terms,
    values, and definitions.

    We will denote an identifier [X] opened with a variable [y] as [X^y]. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
end.

Definition open_rec_path (k: nat) (u: var) (p: path): path :=
  match p with
  | p_sel x bs => p_sel (open_rec_avar k u x) bs
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
  | { L >: T <: U } => { L >: open_rec_typ k u T <: open_rec_typ k u U }
  | dec_trm a T => dec_trm a (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_path p     => trm_path (open_rec_path k u p)
  | trm_app p q    => trm_app (open_rec_path k u p) (open_rec_path k u q)
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

Definition open_paths u ps := map (open_path u) ps.

(** Path opening replaces in some syntax a bound variable with dangling index (k)
    by a path p. *)

Definition open_rec_avar_p (k: nat) (u: path) (a: avar) : path :=
  match a with
  | avar_b i => If k = i then u else pavar (avar_b i)
  | avar_f x => pvar x
  end.

(* example:            (0.a.b    ^ y.c.d    == y.c.d.a.b
   our representation: (0 [b, a] ^ y [d, c] == y [b, a, d, c] *)
Definition open_rec_path_p (k: nat) (u: path) (p: path): path :=
  match p, u with
  | p_sel x bs, p_sel y cs=>
    match x with
    | avar_b i => If k = i then p_sel y (bs ++ cs) else p (* maintaining reverse order of fields *)
    | avar_f x => p
    end
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
  end
with open_rec_dec_p (k: nat) (u: path) (D: dec): dec :=
  match D with
  | { L >: T <: U } => { L >: open_rec_typ_p k u T <: open_rec_typ_p k u U }
  | dec_trm a T => dec_trm a (open_rec_typ_p k u T)
  end.

Fixpoint open_rec_trm_p (k: nat) (u: path) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val_p k u v)
  | trm_path p     => trm_path (open_rec_path_p k u p)
  | trm_app p q    => trm_app (open_rec_path_p k u p) (open_rec_path_p k u q)
  | trm_let t1 t2  => trm_let (open_rec_trm_p k u t1) (open_rec_trm_p (S k) u t2)
  end
with open_rec_val_p (k: nat) (u: path) (v: val): val :=
  match v with
  | val_new T ds => val_new (open_rec_typ_p (S k) u T) (open_rec_defs_p (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ_p k u T) (open_rec_trm_p (S k) u e)
  end
with open_rec_def_p (k: nat) (u: path) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ_p k u T)
  | def_trm m e => def_trm m (open_rec_trm_p k u e)
  end
with open_rec_defs_p (k: nat) (u: path) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs_p k u tl) (open_rec_def_p k u d)
  end.

Definition open_avar_p u a := open_rec_avar_p  0 u a.
Definition open_typ_p  u t := open_rec_typ_p   0 u t.
Definition open_dec_p  u D := open_rec_dec_p   0 u D.
Definition open_path_p u p := open_rec_path_p  0 u p.
Definition open_trm_p  u t := open_rec_trm_p   0 u t.
Definition open_val_p  u v := open_rec_val_p   0 u v.
Definition open_def_p  u d := open_rec_def_p   0 u d.
Definition open_defs_p u l := open_rec_defs_p 0 u l.


(** * Local Closure

  Our definition of [trm] accepts terms that contain de Bruijn indices that are unbound.
  A symbol [X] is considered locally closed, denoted [lc X], if all de Bruijn indices
  in [X] are bound.
   We will require a term to be locally closed in the final safety theorem. *)

(** Only named variables are locally closed. *)
Inductive lc_var : avar -> Prop :=
| lc_var_x : forall x,
    lc_var (avar_f x).

Inductive lc_path : path -> Prop :=
| lc_p: forall x bs,
    lc_var x ->
    lc_path (p_sel x bs).

(** Locally closed types and declarations. *)
Inductive lc_typ : typ -> Prop :=
| lc_typ_top : lc_typ typ_top
| lc_typ_bot : lc_typ typ_bot
| lc_typ_rcd : forall D,
    lc_dec D ->
    lc_typ (typ_rcd D)
| lc_typ_and : forall T1 T2,
    lc_typ T1 ->
    lc_typ T2 ->
    lc_typ (typ_and T1 T2)
| lc_typ_path : forall p L,
    lc_path p ->
    lc_typ (typ_path p L)
| lc_typ_bnd : forall T,
    (forall x, lc_typ (open_typ x T)) ->
    lc_typ (typ_bnd T)
| lc_typ_all : forall T1 T2,
    (forall x, lc_typ (open_typ x T2)) ->
    lc_typ T1 ->
    lc_typ (typ_all T1 T2)
with lc_dec : dec -> Prop :=
| lc_dec_typ : forall L T U,
    lc_typ T ->
    lc_typ U ->
    lc_dec (dec_typ L T U)
| lc_dec_trm : forall a T,
    lc_typ T ->
    lc_dec (dec_trm a T).

(** Locally closed terms, values, and definitions. *)
Inductive lc_trm : trm -> Prop :=
| lc_trm_path : forall p,
    lc_path p ->
    lc_trm (trm_path p)
| lc_trm_val : forall v,
    lc_val v ->
    lc_trm (trm_val v)
| lc_trm_app : forall f p,
    lc_path f ->
    lc_path p ->
    lc_trm (trm_app f p)
| lc_trm_let : forall t1 t2,
    lc_trm t1 ->
    (forall x, lc_trm (open_trm x t2)) ->
    lc_trm (trm_let t1 t2)
with lc_val : val -> Prop :=
| lc_val_new : forall T ds,
    (forall x, lc_typ (open_typ x T)) ->
    (forall x, lc_defs (open_defs x ds)) ->
    lc_val (val_new T ds)
| lc_val_lam : forall T t,
    lc_typ T ->
    (forall x, lc_trm (open_trm x t)) ->
    lc_val (val_lambda T t)
with lc_def : def -> Prop :=
| lc_def_typ : forall L T,
    lc_typ T ->
    lc_def (def_typ L T)
| lc_def_trm : forall a t,
    lc_trm t ->
    lc_def (def_trm a t)
with lc_defs : defs -> Prop :=
| lc_defs_nil : lc_defs defs_nil
| lc_defs_cons : forall ds d,
    lc_defs ds ->
    lc_def d ->
    lc_defs (defs_cons ds d).

(** Locally closed stores *)
Inductive lc_sto : sto -> Prop :=
| lc_sto_empty : lc_sto empty
| lc_sto_cons : forall x v s,
    lc_sto s ->
    lc_val v ->
    lc_sto (s & x ~ v).

(** * Free variables
      Functions that retrieve the free variables of a symbol. *)

(** Free variable in a variable. *)
Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

(** Free variable in a path. *)
Fixpoint fv_path (p: path) : vars :=
  match p with
  | p_sel x bs => fv_avar x
  end.

(** Free variables in a type or declaration. *)
Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => fv_dec D
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_path p L   => fv_path p
  | typ_bnd T      => fv_typ T
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | { L >: T <: U } => (fv_typ T) \u (fv_typ U)
  | dec_trm a T => fv_typ T
  end.

(** Free variables in a term, value, or definition. *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_val v        => (fv_val v)
  | trm_path p       => (fv_path p)
  | trm_app p q      => (fv_path p) \u (fv_path q)
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

(** ** Record types *)
(** In the proof, it is useful to be able to distinguish record types from
    other types. A record type is a concatenation of type declarations with equal
    bounds [{A: T..T}] and field declarations [{a: T}]. *)

(** A record declaration is either a type declaration with equal bounds,
    or a field declaration.*)
Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, inert_typ T -> record_dec (dec_trm a T)

(** Given a record declaration, a [record_typ] keeps track of the declaration's
    field member labels (i.e. names of fields) and type member labels
    (i.e. names of abstract type members). [record_typ] also requires that the
    labels are distinct.  *)
with record_typ : typ -> fset label -> Prop :=
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
with inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (typ_all S T)
  | inert_typ_bnd : forall T ls,
      record_typ T ls ->
      inert_typ (typ_bnd T).

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

(** A [record_type] is a [record_typ] with an unspecified set of labels. The meaning
    of [record_type] is an intersection of type/field declarations with distinct labels. *)
Definition record_type T := exists ls, record_typ T ls.

(** An inert context is a typing context whose range consists only of inert types. *)
Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_all : forall G x T,
      inert G ->
      inert_typ T ->
      x # G ->
      inert (G & x ~ T).

(** * Typing Rules *)

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '⊢' T '<:' U" (at level 40, T at level 59).
Reserved Notation "x ';' bs ';' P ';' G '⊢' d ':' D"
         (at level 40, bs at level 39, P at level 39, G at level 39, d at level 59).
Reserved Notation "x ';' bs ';' P ';' G '⊢' ds '::' D"
         (at level 40, bs at level 39, P at level 39, G at level 39, ds at level 59).
(* Reserved Notation "P '⊢' p '<' q" (at level 40, p at level 59). *)

Definition uniq := LibList.No_duplicates.

Inductive path_precedes : paths -> fields -> fields -> Prop :=
| pp: forall P P1 P2 p q,
    P = app P1 P2 ->
    uniq P ->
    In p P1 ->
    In q P2 ->
    path_precedes P p q.

(** ** Term typing [G ⊢ t: T] *)
Inductive ty_trm : ctx -> trm -> typ -> Prop :=

(** [G(x) = T]   #<br>#
    [ok G]       #<br>#
    [――――――――]   #<br>#
    [G ⊢ x: T]  *)
| ty_var : forall x T G,
    binds x T G ->
    ok G ->
    G ⊢ tvar x : T

(** [G, z: T ⊢ t^z: U^z]     #<br>#
    [z fresh]                #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ lambda(T)t: forall(T)U]      *)
| ty_all_intro : forall L G T t U,
    (forall z, z \notin L ->
      G & z ~ T ⊢ open_trm z t : open_typ z U) ->
    G ⊢ trm_val (val_lambda T t) : typ_all T U

(** [G ⊢ p: forall(S)T] #<br>#
    [G ⊢ q: S]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ p q: T^q]     *)
| ty_all_elim : forall G p q S T,
    G ⊢ trm_path p : typ_all S T ->
    G ⊢ trm_path q : S ->
    G ⊢ trm_app p q : open_typ_p p T

(** [z; P; G, z: T^z ⊢ ds^z :: T^z]    #<br>#
    [z fresh]                          #<br>#
    [―――――――――――――――――――――――――――――――]  #<br>#
    [G ⊢ nu(T)ds :: mu(T)]             *)
| ty_new_intro : forall L G T ds P,
    (forall z, z \notin L ->
      z; nil; P; G & (z ~ open_typ z T) ⊢ open_defs z ds :: open_typ z T) ->
    G ⊢ trm_val (val_new T ds) : typ_bnd T

(** [G ⊢ p: {a: T}] #<br>#
    [―――――――――――――] #<br>#
    [G ⊢ p.a: T]        *)
| ty_new_elim : forall G p a T,
    G ⊢ trm_path p : typ_rcd (dec_trm a T) ->
    G ⊢ trm_path p•a : T

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

(** [G ⊢ p: T^p]   #<br>#
    [――――――――――――] #<br>#
    [G ⊢ p: mu(T)]     *)
| ty_rec_intro : forall G p T,
    G ⊢ trm_path p : open_typ_p p T ->
    G ⊢ trm_path p : typ_bnd T

(** [G ⊢ p: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [G ⊢ p: T^p]   *)
| ty_rec_elim : forall G p T,
    G ⊢ trm_path p : typ_bnd T ->
    G ⊢ trm_path p : open_typ_p p T

(** [G ⊢ p: T]     #<br>#
    [G ⊢ p: U]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ p: T /\ U]     *)
| ty_and_intro : forall G p T U,
    G ⊢ trm_path p : T ->
    G ⊢ trm_path p : U ->
    G ⊢ trm_path p : typ_and T U

(** [G ⊢ t: T]   #<br>#
    [G ⊢ T <: U] #<br>#
    [――――――――――] #<br>#
    [G ⊢ t: U]   *)
| ty_sub : forall G t T U,
    G ⊢ t : T ->
    G ⊢ T <: U ->
    G ⊢ t : U
where "G '⊢' t ':' T" := (ty_trm G t T)

(** ** Single-definition typing [x; bs; P; G ⊢ d: D] *)
with ty_def : var -> fields -> paths -> ctx -> def -> dec -> Prop :=
(** [x; bs; G ⊢ {A = T}: {A: T..T}]   *)
| ty_def_typ : forall x bs P G A T,
    x; bs; P; G ⊢ def_typ A T : dec_typ A T T

(** [G ⊢ lambda(T)t: U]                     #<br>#
    [―――――――――――――――――――――――――――――――――――――] #<br>#
    [x; bs; P; G ⊢ {b = lambda(T)t: U}: {b: T}] *)
 | ty_def_all : forall x bs P G T t b U,
    G ⊢ trm_val (val_lambda T t) : U ->
    inert_typ U ->
    x; bs; P; G ⊢ def_trm b (trm_val (val_lambda T t)) : dec_trm b U

(** [x; (b, bs); P; G ⊢ ds^p.b: T^p.b]             #<br>#
    [―――――――――――――――――――――――――――――――――――――] #<br>#
    [x; bs; P; G ⊢ {b = nu(T)ds}: {b: T}]    *)
 | ty_def_new : forall x bs b P G ds T p,
     p = p_sel (avar_f x) bs ->
     inert_typ (typ_bnd T) ->
     x; (b :: bs); P; G ⊢ open_defs_p p•b ds :: open_typ_p p•b T ->
     x; bs; P; G ⊢ def_trm b (trm_val (val_new T ds)) : dec_trm b (typ_bnd T)

(** if [x == head(q)] then [P ⊢ (b, bs) < fields(q)] #<br>#
    [G ⊢ q: T]                                       #<br>#
    [――――――――――――――――――――――――――――――――――――――――――――――] #<br>#
    [x; bs; P; G ⊢ {a = q}: {a: T}]                  *)
 | ty_def_path : forall x bs P G q y cs b T,
    G ⊢ trm_path q: T ->
    inert_typ T ->
    q = p_sel (avar_f y) cs ->
    (x = y -> path_precedes P (b :: bs) cs) ->
    x; bs; P; G ⊢ def_trm b (trm_path q) : dec_trm b T

where "x ';' bs ';' P ';' G '⊢' d ':' D" := (ty_def x bs P G d D)

(** ** Multiple-definition typing [x; bs; P; G ⊢ ds :: T] *)
with ty_defs : var -> fields -> paths -> ctx -> defs -> typ -> Prop :=
(** [x; bs; P G ⊢ d: D]                #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [x; bs; P; G ⊢ d ++ defs_nil : D]   *)
| ty_defs_one : forall x bs P G d D,
    x; bs; P; G ⊢ d : D ->
    x; bs; P; G ⊢ defs_cons defs_nil d :: typ_rcd D

(** [x; bs; G ⊢ ds :: T]           #<br>#
    [x; bs; G ⊢ d: D]              #<br>#
    [d \notin ds]                  #<br>#
    [―――――――――――――――――――――――――――]  #<br>#
    [x; bs; G ⊢ ds ++ d : T /\ D]   *)
| ty_defs_cons : forall x bs P G d ds D T,
    x; bs; P; G ⊢ ds :: T ->
    x; bs; P; G ⊢ d : D ->
    defs_hasnt ds (label_of_def d) ->
    x; bs; P; G ⊢ defs_cons ds d :: typ_and T (typ_rcd D)
where "x ';' bs ';' P ';' G '⊢' ds '::' T" := (ty_defs x bs P G ds T)

(** ** Subtyping [ G ⊢ T <: U] *)
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
| subtyp_fld: forall G T U a,
    G ⊢ T <: U ->
    G ⊢ typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)

(** [G ⊢ S2 <: S1]                   #<br>#
    [G ⊢ T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G ⊢ {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ: forall G S1 S2 T1 T2 A,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ S <: x.A]     *)
| subtyp_sel2: forall G p A S T,
    G ⊢ trm_path p : typ_rcd (dec_typ A S T) ->
    G ⊢ S <: typ_path p A

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ x.A <: T]     *)
| subtyp_sel1: forall G p A S T,
    G ⊢ trm_path p : typ_rcd (dec_typ A S T) ->
    G ⊢ typ_path p A <: T

(** [G ⊢ S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]     #<br>#
    [x fresh]                     #<br>#
    [―――――――――――――――――――――――]     #<br>#
    [G ⊢ forall(S1)T1 <: forall(S2)T2]      *)
| subtyp_all : forall (L : fset var) (G : ctx) (S1 T1 S2 T2 : typ),
    G ⊢ S2 <: S1 ->
    (forall x : var, x \notin L -> G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
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
| wf_sto_push: forall G s x v T,
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
    [ok G]          #<br>#
    [―――――――――――――] #<br>#
    [G ⊢! x: T] *)
| ty_var_p : forall G x T,
    binds x T G ->
    ok G ->
    G ⊢! tvar x : T

(** [G, x: T ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⊢! lambda(T)t: forall(T) U]     *)
| ty_all_intro_p : forall G t T U L,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢! trm_val (val_lambda T t) : typ_all T U

(** [G, x: T^x ⊢ ds^x :: T^x]  #<br>#
    [x fresh]                  #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [G ⊢! nu(T)ds :: mu(T)]        *)
| ty_new_intro_p : forall G P ds T L,
    (forall z, z \notin L ->
      z; nil; P; G & (z ~ open_typ z T) ⊢ open_defs z ds :: open_typ z T) ->
    G ⊢! trm_val (val_new T ds) : typ_bnd T

(** [G ⊢! p: mu(T)] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! p: T^p]       *)
| ty_rec_elim_p : forall G p T,
   G ⊢! trm_path p : typ_bnd T ->
   G ⊢! trm_path p : open_typ_p p T

(** [G ⊢! p: T /\ U] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! p: T]     *)
| ty_and1_p : forall G p T U,
    G ⊢! trm_path p : typ_and T U ->
    G ⊢! trm_path p : T

(** [G ⊢! p: T /\ U] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! p: U]     *)
| ty_and2_p : forall G p T U,
    G ⊢! trm_path p : typ_and T U ->
    G ⊢! trm_path p : U
| ty_fld_elim_p : forall G p a T,
    G ⊢! trm_path p: typ_rcd (dec_trm a T) ->
    G ⊢! trm_path (p • a): T
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
    ok G ->
    G ⊢# tvar x : T

(** [G, x: T ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⊢# lambda(T)t: forall(T)U]     *)
| ty_all_intro_t : forall G t T U L,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢# trm_val (val_lambda T t) : typ_all T U

(** [G ⊢# p: forall(S)T]  #<br>#
    [G ⊢# q: S]      #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢ p q: T^q]    *)
| ty_all_elim_t : forall G p q S T,
    G ⊢# trm_path p : typ_all S T ->
    G ⊢# trm_path q : S ->
    G ⊢# trm_app p q : open_typ_p p T

(** [z; P; G, z: T^z ⊢ ds^z :: T^z]    #<br>#
    [z fresh]                          #<br>#
    [―――――――――――――――――――――――――――――――]  #<br>#
    [G ⊢# nu(T)ds :: mu(T)]             *)
| ty_new_intro_t : forall G P ds T L,
    (forall z, z \notin L ->
      z; nil; P; G & (z ~ open_typ z T) ⊢ open_defs z ds :: open_typ z T) ->
    G ⊢# trm_val (val_new T ds) : typ_bnd T

(** [G ⊢# p: {a: T}] #<br>#
    [―――――――――――――]   #<br>#
    [G ⊢# p.a: T]        *)
| ty_new_elim_t : forall G p a T,
    G ⊢# trm_path p : typ_rcd (dec_trm a T) ->
    G ⊢# trm_path p • a : T

(** [G ⊢# t: T]             #<br>#
    [G, x: T ⊢ u^x: U]       #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――]       #<br>#
    [G ⊢# let t in u: U]        *)
| ty_let_t : forall G t u T U L,
    G ⊢# t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢# trm_let t u : U

(** [G ⊢# p: T^p]   #<br>#
    [――――――――――――] #<br>#
    [G ⊢# p: mu(T)]     *)
| ty_rec_intro_t : forall G p T,
    G ⊢# trm_path p : open_typ_p p T ->
    G ⊢# trm_path p : typ_bnd T

(** [G ⊢# p: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [G ⊢# p: T^p]   *)
| ty_rec_elim_t : forall G p T,
    G ⊢# trm_path p : typ_bnd T ->
    G ⊢# trm_path p : open_typ_p p T

(** [G ⊢# p: T]     #<br>#
    [G ⊢# p: U]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢# p: T /\ U]     *)
| ty_and_intro_t : forall G p T U,
    G ⊢# trm_path p : T ->
    G ⊢# trm_path p : U ->
    G ⊢# trm_path p : typ_and T U

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
| subtyp_fld_t: forall G T U a,
    G ⊢# T <: U ->
    G ⊢# typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)

(** [G ⊢# S2 <: S1]                   #<br>#
    [G ⊢# T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢# {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_t: forall G S1 S2 T1 T2 A,
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢! p: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢# T <: p.A]         *)
| subtyp_sel2_t: forall G p A T,
    G ⊢! trm_path p : typ_rcd (dec_typ A T T) ->
    G ⊢# T <: typ_path p A

(** [G ⊢! p: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢# p.A <: T]         *)
| subtyp_sel1_t: forall G p A T,
    G ⊢! trm_path p : typ_rcd (dec_typ A T T) ->
    G ⊢# typ_path p A <: T

(** [G ⊢# S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⊢# forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_t: forall G S1 S2 T1 T2 L,
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

Reserved Notation "G '⊢##' p ':' T" (at level 40, p at level 59).

Inductive ty_var_inv : ctx -> path -> typ -> Prop :=

(** [G ⊢! p: T]  #<br>#
    [―――――――――――] #<br>#
    [G ⊢## p: T]     *)
| ty_precise_inv : forall G p T,
  G ⊢! trm_path p : T ->
  G ⊢## p : T

(** [G ⊢## p: {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p: {a: U}]     *)
| ty_dec_trm_inv : forall G p a T U,
  G ⊢## p : typ_rcd (dec_trm a T) ->
  G ⊢# T <: U ->
  G ⊢## p : typ_rcd (dec_trm a U)

(** [G ⊢## p: {A: T1..S1}]   #<br>#
    [G ⊢# T2 <: T1]         #<br>#
    [G ⊢# S1 <: S2]         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## p: {A: T2..S2}]     *)
| ty_dec_typ_inv : forall G p A T1 T2 S1 S2,
  G ⊢## p : typ_rcd (dec_typ A T1 S1) ->
  G ⊢# T2 <: T1 ->
  G ⊢# S1 <: S2 ->
  G ⊢## p : typ_rcd (dec_typ A T2 S2)

(** [G ⊢## p: T^p]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: mu(T)] *)
| ty_bnd_inv : forall G p T,
  G ⊢## p : open_typ_p p T ->
  G ⊢## p : typ_bnd T

(** [G ⊢## p: forall(S1)T1]          #<br>#
    [G ⊢# S2 <: S1]            #<br>#
    [G, y: S2 ⊢ T1^y <: T2^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## p: forall(S')T']            *)
| ty_all_inv : forall G T1 T2 S1 S2 L p,
  G ⊢## p : typ_all S1 T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢## p : typ_all S2 T2

(** [G ⊢## p : T]     #<br>#
    [G ⊢## p : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p : T /\ U]      *)
| ty_and_inv :  forall G p S1 S2,
  G ⊢## p : S1 ->
  G ⊢## p : S2 ->
  G ⊢## p : typ_and S1 S2

(** [G ⊢## p: S]        #<br>#
    [G ⊢! q: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## p: q.A           *)
| ty_path_inv : forall G p q A S,
  G ⊢## p : S ->
  G ⊢! trm_path q : typ_rcd (dec_typ A S S) ->
  G ⊢## p : typ_path q A

(** [G ⊢## p: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_inv : forall G p T,
  G ⊢## p : T ->
  G ⊢## p : typ_top
where "G '⊢##' p ':' T" := (ty_var_inv G p T).

(** *** Invertible typing of values [G ⊢##v v: T] *)

Reserved Notation "G '⊢##v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_inv : ctx -> val -> typ -> Prop :=

(** [G ⊢! v: T]    #<br>#
    [―――――――――――――] #<br>#
    [G ⊢##v v: T] *)
| ty_precise_inv_v : forall G v T,
  G ⊢! trm_val v : T ->
  G ⊢##v v : T

(** [G ⊢##v v: forall(S1)T1]          #<br>#
    [G ⊢# S2 <: S1]             #<br>#
    [G, y: S2 ⊢ T1^y <: T2^y]    #<br>#
    [y fresh]                   #<br>#
    [――――――――――――――――――――――]    #<br>#
    [G ⊢##v v: forall(S')T']            *)
| ty_all_inv_v : forall G v S1 S2 T1 T2 L,
  G ⊢##v v : typ_all S1 T1 ->
  G ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⊢ open_typ y T1 <: open_typ y T2) ->
  G ⊢##v v : typ_all S2 T2

(** [G ⊢##v v: S]       #<br>#
    [G ⊢! q: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢##v v: q.A]         *)
| ty_path_inv_v : forall G v S q A,
  G ⊢##v v : S ->
  G ⊢! trm_path q : typ_rcd (dec_typ A S S) ->
  G ⊢##v v : typ_path q A

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

(** * Infrastructure *)

Hint Constructors
     inert_typ inert record_has record_dec record_typ
     ty_trm ty_def ty_defs subtyp ty_trm_p
     ty_trm_t subtyp_t ty_var_inv ty_val_inv
     (*lc_var lc_typ lc_dec lc_trm lc_val
     lc_dec lc_defs lc_sto*).

Hint Unfold record_type.

(** ** Mutual Induction Principles *)

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

Scheme tds_ty_trm_mut  := Induction for ty_trm    Sort Prop
  with   tds_ty_def_mut  := Induction for ty_def    Sort Prop
  with   tds_ty_defs_mut := Induction for ty_defs   Sort Prop
  with   tds_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme tds_mutind from tds_ty_trm_mut, tds_ty_def_mut, tds_ty_defs_mut, tds_subtyp.

Scheme ts_ty_trm_mut  := Induction for ty_trm    Sort Prop
  with   ts_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme ts_ty_trm_mut_ts  := Induction for ty_trm_t    Sort Prop
  with   ts_subtyp_ts      := Induction for subtyp_t    Sort Prop.
Combined Scheme ts_mutind_ts from ts_ty_trm_mut_ts, ts_subtyp_ts.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
  with   rules_def_mut    := Induction for ty_def    Sort Prop
  with   rules_defs_mut   := Induction for ty_defs   Sort Prop
  with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

Scheme rcd_dec_mut := Induction for record_dec Sort Prop
  with rcd_typ_mut := Induction for record_typ Sort Prop
  with inert_mut   := Induction for inert_typ Sort Prop.
Combined Scheme rcd_mutind from rcd_dec_mut, rcd_typ_mut, inert_mut.
(*
Scheme lc_trm_mut  := Induction for lc_trm Sort Prop
with   lc_val_mut  := Induction for lc_val Sort Prop
with   lc_def_mut  := Induction for lc_def Sort Prop
with   lc_defs_mut := Induction for lc_defs Sort Prop.
Combined Scheme lc_mutind from lc_trm_mut, lc_val_mut, lc_def_mut, lc_defs_mut.

Scheme lc_typ_mut := Induction for lc_typ Sort Prop
with   lc_dec_mut := Induction for lc_dec Sort Prop.
Combined Scheme lc_typ_mutind from lc_typ_mut, lc_dec_mut.
 *)

(** * Tactics *)

(** Tactics for generating fresh variables. *)

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
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J ).

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
