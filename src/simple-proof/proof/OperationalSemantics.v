Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibMap LibLN.
Require Import Definitions Binding.

(** * Stack-Based Operational Semantics *)

Reserved Notation "t1 '|->' t2" (at level 40, t2 at level 39).

Inductive red : sta * store * trm -> sta * store * trm -> Prop :=
(** [s(x) = lambda(T)t]      #<br>#
    [―――――――――――――――――――――]  #<br>#
    [(s, sigma, x y) |-> (s, sigma, t^y)]  *)
| red_sel : forall x m s sigma t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    (s, sigma, trm_sel (avar_f x) m) |-> (s, sigma, t)

(** [s(x) = nu(T)...{a = t}...]   #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(s, sigma, x.a) |-> (s, sigma, t)]  *)
| red_app : forall f a s sigma T t,
    binds f (val_lambda T t) s ->
    (s, sigma, trm_app (avar_f f) (avar_f a)) |-> (s, sigma, open_trm a t)

(** [(s, sigma, let x = v in t) |-> ((s, x = v), sigma, t^x)] *)
| red_let : forall v t s sigma x,
    x # s ->
    (s, sigma, trm_let (trm_val v) t) |-> (s & x ~ v, sigma, open_trm x t)

(** [(s, sigma, let y = x in t) |-> (s, sigma, t^x)] *)
| red_let_var : forall t s sigma x,
    (s, sigma, trm_let (trm_var (avar_f x)) t) |-> (s, sigma, open_trm x t)

(** [(s, sigma, t0) |-> (s', sigma', t0')]                     #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(s, sigma, let x = t0 in t) |-> (s', sigma', let x = t0' in t)]  *)
| red_let_tgt : forall t0 t s sigma t0' s' sigma',
    (s, sigma, t0) |-> (s', sigma', t0') ->
    (s, sigma, trm_let t0 t) |-> (s', sigma', trm_let t0' t)

(** [(s, sigma, ref x T) |-> (s', sigma[l := x], l)]  *)
| red_ref_var : forall x s sigma l T,
    l \notindom sigma ->
    (s, sigma, (trm_ref (avar_f x) T)) |-> (s, sigma[l :=  x], (trm_val (val_loc l)))

(** [s(x) = l]                   #<br>#
    [sigma(l) = y]                   #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(s, sigma, !x) |-> (s', sigma, y)]  *)
| red_deref : forall x y (l: addr) s (sigma: store),
    binds x (val_loc l) s ->
    bindsM l y sigma ->
    (s, sigma, (trm_deref (avar_f x))) |-> (s, sigma, (trm_var (avar_f y)))

(** [s(x) = l]                   #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(s, sigma, x := y) |-> (s, sigma[l:=y], y)]  *)
| red_asgn : forall x y l s sigma,
    binds x (val_loc l) s ->
    (s, sigma, (trm_asg (avar_f x) (avar_f y))) |-> (s, sigma[l := y], (trm_var (avar_f y)))

where "t1 '|->' t2" := (red t1 t2).

(** ** Normal forms *)
(** Variables and values are considered to be in normal form. *)
Inductive norm_form: trm -> Prop :=
| nf_var: forall x, norm_form (trm_var x)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors red norm_form.
