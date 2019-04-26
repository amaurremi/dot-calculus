Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions Binding Lookup.

(** * Operational Semantics *)

Reserved Notation "t1 '⤳' t2" (at level 40, t2 at level 39).

Inductive red : sta * trm -> sta * trm -> Prop :=

(** [s ∋ (p, lambda(T)t)  ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [(s, p q) ⤳ (s, t^q)]      *)
| red_app: forall s p q T t,
    s ∋ (p, λ(T) t) ->
    (s, trm_app p q) ⤳ (s, open_trm_p q t)

(** [(s, let x = v in t) ⤳ ((s, x = v), t^x)] *)
| red_let_val : forall v t s x,
    x # s ->
    (s, trm_let (trm_val v) t) ⤳ (s & x ~ v, open_trm x t)

(** [(s, let y = p in t) ⤳ (s, t^p)] *)
| red_let_path : forall t s p,
    (s, trm_let (trm_path p) t) ⤳ (s, open_trm_p p t)

(** [(s, t0) ⤳ (s', t0')]                            #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(s, let x = t0 in t) ⤳ (s', let x = t0' in t)]  *)
| red_let_tgt : forall t0 t s t0' s',
    (s, t0) ⤳ (s', t0') ->
    (s, trm_let t0 t) ⤳ (s', trm_let t0' t)

where "t1 '⤳' t2" := (red t1 t2).

(** ** Normal forms *)

(** Paths and values are considered to be in normal form. *)
Inductive norm_form: trm -> Prop :=
| nf_path: forall p, norm_form (trm_path p)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors red norm_form.
