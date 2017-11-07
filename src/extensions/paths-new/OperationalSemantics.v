Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding.

(** * Stack-Based Operational Semantics *)

(** * Path Lookup *)

(** Looking up a path in a stack. *)

Reserved Notation "s '∋' t" (at level 60).

Inductive lookup : sta -> path * val -> Prop :=

(** [s(x) = v  ]    #<br>#
    [――――――――――]    #<br>#
    [s ∋ (x, v)]    *)
| lookup_var : forall s x v,
    binds x v s ->
    s ∋ (pvar x, v)


where "s '∋' t" := (lookup s t)

with lookup_open : sta -> path -> defs -> Prop :=
     | lo_ds : forall s p T ds,
         s ∋ (p, val_new T ds) ->
         lookup_open s p (open_defs_p p ds).




(** [e ∋ (p, ν(T)...{ b = v }...)]    #<br>#
    [――――――――――――――――――――――――――――]    #<br>#
    [e ∋ (p.b, v)                ]    *)
| lookup_val : forall s p b T ds v,
    s ∋ (p, val_new T ds) ->
    get_def (label_trm b) ds = Some (def_trm b (trm_val v)) ->
    s ∋ (p•b, v)

(** [e ∋ (p, ν(T)...{ b = x.bs }...)] #<br>#
    [e ∋ (x.bs, v)                  ] #<br>#
    [―――――――――――――――――――――――――――――――] #<br>#
    [e ∋ (p.b, v)                   ] *)
| lookup_x : forall s p T ds b x bs v,
    s ∋ (p, val_new T ds) ->
    get_def (label_trm b) ds = Some (def_trm b (trm_path (p_sel (avar_f x) bs))) ->
    s ∋ (p_sel (avar_f x) bs, v) ->
    s ∋ (p•b, v)

(** [e ∋ (p, ν(T)...{ b = n.bs }...)] #<br>#
    [e ∋ ((p drop n).bs, v)         ] #<br>#
    [―――――――――――――――――――――――――――――――] #<br>#
    [e ∋ (p.b, v)                   ] *)
| lookup_n : forall s p T ds b x bs v cs n,
    s ∋ (p, val_new T ds) ->
    get_def (label_trm b) ds = Some (def_trm b (trm_path (p_sel (avar_b n) bs))) ->
    p = p_sel x cs ->
    (* `skipn n cs` removes the n last fields of the path, yielding the path to bs *)
    s ∋ (p_sel x (bs ++ skipn n cs), v) ->
    s ∋ (p•b, v)

Reserved Notation "t1 '|->' t2" (at level 40, t2 at level 39).

Inductive red : sta * trm -> sta * trm -> Prop :=
(** [s(x) = lambda(T)t]      #<br>#
    [―――――――――――――――――――――]  #<br>#
    [(s, x y) |-> (s, t^y)]  *)
| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    (s, trm_sel (avar_f x) m) |-> (s, t)

(** [s(x) = nu(T)...{a = t}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(s, x.a) |-> (s, t)      ]  *)
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    (s, trm_app (avar_f f) (avar_f a)) |-> (s, open_trm a t)

(** [(s, let x = v in t) |-> ((s, x = v), t^x)] *)
| red_let : forall v t s x,
    x # s ->
    (s, trm_let (trm_val v) t) |-> (s & x ~ v, open_trm x t)

(** [(s, let y = x in t) |-> (s, t^x)] *)
| red_let_var : forall t s x,
    (s, trm_let (trm_var (avar_f x)) t) |-> (s, open_trm x t)

(** [(s, t0) |-> (s', t0')]                            #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(s, let x = t0 in t) |-> (s', let x = t0' in t)]  *)
| red_let_tgt : forall t0 t s t0' s',
    (s, t0) |-> (s', t0') ->
    (s, trm_let t0 t) |-> (s', trm_let t0' t)

where "t1 '|->' t2" := (red t1 t2).

(** ** Normal forms *)

(** Paths and values are considered to be in normal form. *)
Inductive norm_form: trm -> Prop :=
| nf_path: forall p, norm_form (trm_path p)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors red norm_form.
