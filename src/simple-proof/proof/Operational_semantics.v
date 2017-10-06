Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.

(** * Normal Forms
A normal form is defined in the WadlerFest DOT paper as:

[n ::= x | v | let x = v in n]

This corresponds to an evaluation context of the form
[(let x = v in)* [ ]] whose hole is filled by a variable [x]
or value [v]. *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v)
| nf_let: forall v t, normal_form t -> normal_form (trm_let (trm_val v) t).

(** * Operational Semantics *)

Reserved Notation "e '[' t1 '|->' t2 ']'" (at level 60, t1 at level 39).

Inductive red : sto -> trm -> trm -> Prop :=
(** [e(x) = lambda(T)t]    #<br>#
    ―――――――――――――――――――――  #<br>#
    [e [x y] |-> e [t^y] ]  *)
| red_apply : forall x y e T t,
    lc_trm (trm_app (avar_f x) (avar_f y)) ->
    binds x (val_lambda T t) e ->
    e [ trm_app (avar_f x) (avar_f y) |-> open_trm y t ]
(** [e(x) = nu(T)...{a = t}...]  #<br>#
    ―――――――――――――――――――――――――――  #<br>#
    [e[ x.a] |-> e[t]]  *)
| red_project : forall x a e T ds t,
    lc_trm (trm_sel (avar_f x) a) ->
    binds x (val_new T ds) e ->
    defs_has (open_defs x ds) (def_trm a t) ->
    e [ trm_sel (avar_f x) a |-> t ]
(** [e[let x = y in t] |-> e[t^y]] *)
| red_let_var : forall y t e,
    lc_trm (trm_let (trm_var (avar_f y)) t) ->
    e [ trm_let (trm_var (avar_f y)) t |-> open_trm y t ]
(** [e[let x = (let y = s in t) in u] |-> e[let y = s in let x = t in u]] *)
| red_let_let : forall s t u e,
    lc_trm (trm_let (trm_let s t) u) ->
    e [ trm_let (trm_let s t) u |-> trm_let s (trm_let t u) ]
(** [e[t] |-> e[t']]                            #<br>#
    ――――――――――――――――――――――――――――――――――――――――――― #<br>#
    e[let x = t in u] |-> e[let x = t' in u]]     *)
| red_let_trm : forall e t t' u,
    lc_trm (trm_let t u) ->
    e [ t |-> t' ] ->
    e [ trm_let t u |-> trm_let t' u ]
(** [(e, x = v) [t] |-> (e, x = v) [t']]                            #<br>#
    ――――――――――――――――――――――――――――――――――――――――――― #<br>#
    e[let x = v in t] |-> e[let x = v in t']]     *)
| red_let_val: forall e t t' v L,
    lc_trm (trm_let (trm_val v) t) ->
    (forall x, x \notin L  ->
      (e & x ~ v) [ open_trm x t |-> open_trm x t' ]) ->
    e [ trm_let (trm_val v) t |-> trm_let (trm_val v) t' ]
where "e [ t |-> t' ]" := (red e t t').

Hint Constructors red normal_form.
