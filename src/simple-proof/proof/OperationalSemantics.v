Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding.

(** * Stack-Based Operational Semantics *)

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

(** [(s, t0) |-> (s', t0')]                             #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(s, let x = t0 in t) |-> (s', let x = t0' in t)]  *)
| red_let_tgt : forall t0 t s t0' s',
    (s, t0) |-> (s', t0') ->
    (s, trm_let t0 t) |-> (s', trm_let t0' t)

where "t1 '|->' t2" := (red t1 t2).

(** ** Normal forms *)
(** Variables and values are considered to be in normal form. *)
Inductive norm_form: trm -> Prop :=
| nf_var: forall x, norm_form (trm_var x)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors red norm_form.
