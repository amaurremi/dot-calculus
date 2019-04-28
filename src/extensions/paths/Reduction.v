Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions Lookup Sequences.

(** * Operational Semantics *)

(** Term-reduction relation *)
Reserved Notation "t1 '⟼' t2" (at level 40, t2 at level 39).

Inductive red : sta * trm -> sta * trm -> Prop :=

(** [γ ⊢ p ⤳* lambda(T)t ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [(γ p q) ⟼ (γ, t^q)]      *)
| red_app: forall γ p q T t,
    γ ⟦ defp p ⤳* defv (λ(T) t) ⟧ ->
    (γ, trm_app p q) ⟼ (γ, open_trm_p q t)

(** [(γ, let x = v in t) ⟼ ((γ, x = v), t^x)] *)
| red_let_val : forall v t γ x,
    x # γ ->
    (γ, trm_let (trm_val v) t) ⟼ (γ & x ~ v, open_trm x t)

(** [(γ, let y = p in t) ⟼ (γ, t^p)] *)
| red_let_path : forall t γ p,
    (γ, trm_let (trm_path p) t) ⟼ (γ, open_trm_p p t)

(** [(γ, t0) ⟼ (γ', t0')]                            #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(γ, let x = t0 in t) ⟼ (γ', let x = t0' in t)]  *)
| red_let_tgt : forall t0 t γ t0' γ',
    (γ, t0) ⟼ (γ', t0') ->
    (γ, trm_let t0 t) ⟼ (γ', trm_let t0' t)

where "t1 '⟼' t2" := (red t1 t2).

(** Reflexive, transitive closure of reduction relation *)
Notation "t1 '⟼*' t2" := (star red t1 t2) (at level 40).

(** ** Normal forms *)

(** Paths and values are considered to be in normal form. *)
Inductive norm_form: trm -> Prop :=
| nf_path: forall p, norm_form (trm_path p)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors red norm_form.
