Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Precise_flow.
Require Import Inert_types.

(* ###################################################################### *)
(** ** Tight Possible types for values *)

(*
Definition (Tight Possible types)

For a variable v, environment G, the set TPTv(G, v) of simplified possible types
of v is the smallest set SS such that:

If G |-! v:T then T in SS.
If all(x: S)T in SS, G |-# S'<:S and G, x: S' |-# T<:T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then (S1 & S2) in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
 *)

Inductive tight_pt_v : ctx -> sigma -> val -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise_v : forall G S v T,
  ty_trm ty_precise sub_general G S (trm_val v) T ->
  tight_pt_v G S v T
  (* Forall *)
| t_pt_all_v : forall L G S v V T V' T',
  tight_pt_v G S v (typ_all V T) ->
  subtyp sub_tight G S V' V ->
  (forall y, y \notin L ->
   subtyp sub_general (G & y ~ V') S (open_typ y T) (open_typ y T')) ->
  tight_pt_v G S v (typ_all V' T')
  (* Tight Selection *)
| t_pt_sel_v : forall G S v y A V,
  tight_pt_v G S v V ->
  ty_trm ty_precise sub_general G S (trm_var y) (typ_rcd (dec_typ A V V)) ->
  tight_pt_v G S v (typ_sel y A)
| t_pt_and_v : forall G S v T U,
  tight_pt_v G S v T ->
  tight_pt_v G S v U ->
  tight_pt_v G S v (typ_and T U)
  (* Loc *)
| t_pt_loc_v : forall G S v T U,
  tight_pt_v G S v (typ_ref T) ->
  subtyp sub_tight G S T U ->
  subtyp sub_tight G S U T ->  
  tight_pt_v G S v (typ_ref U)
  (* Top *)
| t_pt_top_v : forall G S v T,
  tight_pt_v G S v T ->
  tight_pt_v G S v typ_top.

Hint Constructors tight_pt_v.

Lemma tight_possible_types_closure_tight_v: forall G S v T U,
  inert G ->
  tight_pt_v G S v T ->
  subtyp sub_tight G S T U ->
  tight_pt_v G S v U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT. inversion H.
  - inversions HT. inversion H. assumption.
  - inversions HT. inversions H. assumption.
  - inversions HT. inversions H.
  - inversions HT. inversions H.
  - inversions HT. inversions H0.
    lets Hb: (inert_unique_tight_bounds Hgd H H6). subst*.
Qed.

Lemma tight_possible_types_lemma_v : forall G S v T,
    inert G ->
    ty_trm ty_general sub_tight G S (trm_val v) T ->
    tight_pt_v G S v T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl eq_refl eq_refl).
  apply* tight_possible_types_closure_tight_v.
Qed.
