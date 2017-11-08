Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Precise_flow.
Require Import Inert_types.

(* ###################################################################### *)
(** ** Tight Possible types *)

(*
Definition (Tight Possible types)

For a variable x, environment G, the set TPT(G, x) of simplified possible types
of x defined as v in G is the smallest set SS such that:

If G |-! x:T then T in SS.
If {a:T} in SS and G |-# T<:T' then {a:T'} in SS.
If {A:T..U} in SS, G |-# T'<:T and G |-# U<:U' then {A:T'..U'} in SS.
If S in SS then rec(x: S) in SS.
If all(x: S)T in SS, G |-# S'<:S and G, x: S' |-# T<:T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then (S1 & S2) in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
 *)

Inductive tight_pt : ctx -> sigma -> var -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise : forall G S x T,
  ty_trm ty_precise sub_general G S (trm_var (avar_f x)) T ->
  tight_pt G S x T
  (* Term member subtyping *)
| t_pt_dec_trm : forall G S x a T T',
  tight_pt G S x (typ_rcd (dec_trm a T)) ->
  subtyp sub_tight G S T T' ->
  tight_pt G S x (typ_rcd (dec_trm a T'))
  (* Type member subtyping *)
| t_pt_dec_typ : forall G S x A T T' U' U,
  tight_pt G S x (typ_rcd (dec_typ A T U)) ->
  subtyp sub_tight G S T' T ->
  subtyp sub_tight G S U U' ->
  tight_pt G S x (typ_rcd (dec_typ A T' U'))
  (* Recursive Types *)
| t_pt_bnd : forall G x S T T',
  tight_pt G S x T ->
  T = open_typ x T' ->
  tight_pt G S x (typ_bnd T')
  (* Forall *)
| t_pt_all : forall L G S x V T V' T',
  tight_pt G S x (typ_all V T) ->
  subtyp sub_tight G S V' V ->
  (forall y, y \notin L ->
   subtyp sub_general (G & y ~ V') S (open_typ y T) (open_typ y T')) ->
  tight_pt G S x (typ_all V' T')
  (* And *)
| t_pt_and : forall G S x S1 S2,
  tight_pt G S x S1 ->
  tight_pt G S x S2 ->
  tight_pt G S x (typ_and S1 S2)
  (* Tight Selection *)
| t_pt_sel : forall G S x y A T,
  tight_pt G S x T ->
  ty_trm ty_precise sub_general G S (trm_var y) (typ_rcd (dec_typ A T T)) ->
  tight_pt G S x (typ_sel y A)
  (* Loc *)
| t_pt_loc : forall G S x T U,
  tight_pt G S x (typ_ref T) ->
  subtyp sub_tight G S T U ->
  subtyp sub_tight G S U T ->  
  tight_pt G S x (typ_ref U)
  (* Top *)
| t_pt_top : forall G S x T,
  tight_pt G S x T ->
  tight_pt G S x typ_top
.

Hint Constructors tight_pt.

Lemma tight_possible_types_closure_tight: forall G S x T U,
  inert G ->
  tight_pt G S x T ->
  subtyp sub_tight G S T U ->
  tight_pt G S x U.
Proof.
  intros G S x T U Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (inert_ty_precise_bot Hgd H).
  - inversion HT.
    + apply ty_precise_var_and_inv1 in H.
      auto.
    + auto.
  - inversion HT.
    + apply ty_precise_var_and_inv2 in H.
      auto.
    + auto.
  - inversion HT.
    + false* inert_precise_sel_inv.
    + pose proof (inert_unique_tight_bounds Hgd H H6) as Hu. subst. assumption.
Qed.

Lemma tight_possible_types_lemma :
  forall G S U x,
    inert G -> (* G inert *)
    ty_trm ty_general sub_tight G S (trm_var (avar_f x)) U -> (* G |-# x : U *)
    tight_pt G S x U (* U \in TPT(G,x,T) *).
Proof.
  intros G S U x Hgd Hty.
  dependent induction Hty.
  - auto.
  - specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    eapply t_pt_bnd.
    apply IHHty.
    reflexivity.
  - specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    inversion IHHty; subst; auto.
  - apply t_pt_and; auto.
  - eapply tight_possible_types_closure_tight; auto.
Qed.
