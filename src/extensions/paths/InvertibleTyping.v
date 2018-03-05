(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import List.
Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions Binding Narrowing PreciseTyping RecordAndInertTypes
               Subenvironments TightTyping Weakening.

(** ** Invertible typing *)

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⊢! x: {a: T}],
and [G ⊢ T <: T'], then [G ⊢## x: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). *)

(** ** Invertible typing of paths [G ⊢## p: T] *)

Reserved Notation "G '⊢##' p ':' T" (at level 40, p at level 59).

Inductive ty_path_inv : ctx -> path -> typ -> Prop :=

(** [G ⊢• p: qs ⪼ T]  #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## p: T]     *)
| ty_precise_inv : forall G p U T m,
  G ⊢! p : U ⪼ T // m ->
  G ⊢## p : T

(*| ty_sngl_refl_inv : forall G p T,
    G ⊢## p : T ->
    G ⊢## p : typ_sngl p*)

(** [G ⊢## p: {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## p: {a: U}]     *)
| ty_dec_trm_inv : forall G p a T U,
  G ⊢## p : typ_rcd {a ⦂ T} ->
  G ⊢# T <: U ->
  G ⊢## p : typ_rcd {a ⦂ U}

(** [G ⊢## p: {A: T1..S1}]   #<br>#
    [G ⊢# T2 <: T1]         #<br>#
    [G ⊢# S1 <: S2]         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## p: {A: T2..S2}]     *)
| ty_dec_typ_inv : forall G p A T1 T2 S1 S2,
  G ⊢## p : typ_rcd {A >: T1 <: S1} ->
  G ⊢# T2 <: T1 ->
  G ⊢# S1 <: S2 ->
  G ⊢## p : typ_rcd {A >: T2 <: S2}

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
| ty_and_inv : forall G p S1 S2,
  G ⊢## p : S1 ->
  G ⊢## p : S2 ->
  G ⊢## p : typ_and S1 S2

(** [G ⊢## p: S]        #<br>#
    [G ⊢! q: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## p: q.A           *)
| ty_sel_inv : forall G p q A S T m,
  G ⊢## p : S ->
  G ⊢! q : T ⪼ typ_rcd {A >: S <: S} // m ->
  G ⊢## p : typ_path q A

(** [G ⊢## p: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_inv : forall G p T,
  G ⊢## p : T ->
  G ⊢## p : typ_top

(* replacement rules: recursive types, selection types, singleton types *)

| ty_rec_pq1_inv : forall G p q r T,
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_bnd T ->
    G ⊢## r : typ_bnd (repl_typ p q T)

(*| ty_rec_qp2_inv : forall G p q r T,
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_bnd (repl_typ q p T) ->
    G ⊢## r : typ_bnd T*)

| ty_sel_pq1_inv : forall G p q r r' A,
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_path r' A ->
    G ⊢## r : typ_path (repl_path p q r') A

(*| ty_sel_qp2_inv : forall G p q r r' A,
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_path (repl_path q p r') A ->
    G ⊢## r : typ_path r' A*)

| ty_sngl_pq1_inv : forall G p q r r',
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_sngl r' ->
    G ⊢## r : typ_sngl (repl_path p q r')

(*| ty_sngl_qp2_inv : forall G p q r r',
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢## r : typ_sngl (repl_path q p r') ->
    G ⊢## r : typ_sngl r'*)

where "G '⊢##' p ':' T" := (ty_path_inv G p T).

Hint Constructors ty_path_inv.

(** *** Invertible to Precise Typing [|-## to |-!] *)

(** Invertible typing implies tight typing. *)
Lemma inv_to_tight: forall G p T,
    G ⊢## p: T ->
    G ⊢# trm_path p: T.
Proof.
  introv Ht. induction Ht; eauto.
  apply* precise_to_tight.
Qed.

(*
(* this is not true because the ⊢## judgment might be obtained through another path that is equal to q, i.e.
   Г(r) = q.type
   Г(q) = p.type
   ______________
   Г ⊢## p: q.type
 *)
Lemma invertible_to_precise_sngl : forall G p q,
    inert G ->
    G ⊢## p : typ_sngl q ->
    G ⊢! p : typ_sngl q ⪼ typ_sngl q.
Proof.
  introv Hi Hp. dependent induction Hp.
  - lets Ht: (pf_sngl_T Hi H). subst*.
  - specialize (IHHp1 _ Hi eq_refl). specialize (IHHp2 _ Hi eq_refl).
    unfold repl_path; destruct r', q0, p, a, f; eauto.
    case_if; destruct_all; subst.
    *

Qed.
*)

(** Invertible-to-precise typing for field declarations: #<br>#
    [G |-## p: {a: T}]            #<br>#
    [――――――――――――――――――――――]      #<br>#
    [exists T', G |-! p: {a: T'}]      #<br>#
    [G |-# T' <: T]. *)
Lemma invertible_to_precise_trm_dec: forall G p a T,
  inert G ->
  G ⊢## p : typ_rcd {a ⦂ T} ->
  exists U T' m,
    G ⊢! p: U ⪼ typ_rcd {a ⦂ T'} // m /\
    G ⊢# T' <: T.
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - repeat eexists; eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [U [T' [m' [Hp Hs]]]]. repeat eexists; eauto.
Qed.

(** Invertible-to-precise typing for function types: #<br>#
    [ok G]                        #<br>#
    [G ⊢## x: forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⊢! x: forall(S')T']  #<br>#
    [G ⊢# S <: S']               #<br>#
    [G ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma invertible_to_precise_typ_all: forall G p S T,
  inert G ->
  G ⊢## p : typ_all S T ->
  exists U m S' T' L,
    G ⊢! p : U ⪼ typ_all S' T' // m /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - exists U m S T (dom G); eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [U [m' [S' [T' [L' [Hp [Hs1 Hs]]]]]]].
    exists U m' S' T' (L \u L'). repeat split; auto. eauto. (* renaming *) admit.
Qed.

(** ** Invertible Replacement Closure *)

Lemma invertible_repl_closure_pq1 : forall G p q r T,
    inert G ->
    G ⊢## p : T ->
    G ⊢# trm_path q : typ_sngl r ->
    G ⊢## p : repl_typ q r T.
Proof.
  introv Hi Hp Hqr. gen q.
  induction Hp; introv Hq; simpl; eauto.
  - Case "ty_precise_inv".
    destruct (pf_inert Hi H) as [Hin | Hs].
    * inversions Hin.
      ** lets Heq: (pf_forall_U H). subst.
         simpl. apply ty_precise_inv in H.
         eapply ty_all_inv. apply H. apply* subtyp_sngl_pq2_t.
         introv Hy. admit. (*renaming *)
      ** destruct (pf_rec_rcd_U Hi H) as [Hp | Hp]; subst.
         + simpl. apply ty_rec_pq1_inv; eauto.
         + inversions Hp.
           gen T0. dependent induction H1; introv Hp Hr; subst; simpl; eauto.
           ++ destruct D.
              eapply ty_dec_typ_inv. apply* ty_precise_inv.
              apply* subtyp_sngl_pq2_t. apply* subtyp_sngl_pq1_t.
              eapply ty_dec_trm_inv. apply* ty_precise_inv.
              apply* subtyp_sngl_pq1_t.
           ++ constructor*. apply pf_and_destruct1 in Hp.
              destruct D.
              eauto. eauto.
              apply pf_and_destruct2 in Hp. apply ty_precise_inv in Hp.
              destruct D. apply* ty_dec_typ_inv. apply* ty_dec_trm_inv.
    * inversions Hs. lets Hs: (pf_sngl_U H). subst. simpl. constructor*.
  - Case "ty_all_inv".
    specialize (IHHp Hi _ Hq). simpls. eapply ty_all_inv. apply IHHp.
    apply subtyp_trans_t with (T:=S2); eauto.
    introv Hy. admit. (*renaming*)
Admitted.

Ltac invert_repl :=
   match goal with
  | [H: _ = repl_typ _ _ ?T |- _] =>
    destruct T; inversions H
  | [H: _ = repl_dec _ _ ?D |- _] =>
    destruct D; inversions H
  | [H: repl_typ _ _ ?T = _ |- _] =>
    destruct T; inversions H
  end.

Lemma invertible_bot : forall G p,
    inert G ->
    G ⊢## p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. false* pf_bot.
  (*destruct T; inversions x. eauto.*)
Qed.

Lemma invertible_and : forall G p T U,
    inert G ->
    G ⊢## p: typ_and T U ->
    G ⊢## p: T /\ G ⊢## p: U.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  split. apply pf_and_destruct1 in H. eauto. apply pf_and_destruct2 in H. eauto.
Qed.


(** * Replacement typing
    Whereas invertible typing does replacment for singleton types in one direction,
    replacement typing does the replacment in the other direction.

    Note that we can't simply define this using three rules:
    1) identity from invertible typing
    2) two repl subtyping rules
    The reason is that if we did that, repl typing would necessarily apply the replacement
    in all subterms of a term, whereas we want to be able to say, for example:
    Г ⊢## p: T
    Г ⊢// p: U
    __________
    Г ⊢// p: T ∧ U
*)

Reserved Notation "G '⊢//' p ':' T" (at level 40, p at level 59).

Inductive ty_repl : ctx -> path -> typ -> Prop :=

| ty_inv_r : forall G p T,
    G ⊢## p: T ->
    G ⊢// p: T

| ty_and_r : forall G p S1 S2,
  G ⊢// p : S1 ->
  G ⊢// p : S2 ->
  G ⊢// p : typ_and S1 S2

| ty_pq2_r : forall G p q r T,
    G ⊢# trm_path p : typ_sngl q ->
    G ⊢// r : repl_typ p q T ->
    G ⊢// r : T

where "G '⊢//' p ':' T" := (ty_repl G p T).

Hint Constructors ty_repl.

Lemma repl_bot : forall G p,
    inert G ->
    G ⊢// p: typ_bot -> False.
Proof.
  introv Hi Hr. dependent induction Hr; eauto. false* invertible_bot.
Qed.

Lemma repl_and : forall G p T U,
    inert G ->
    G ⊢// p: typ_and T U ->
    G ⊢// p: T /\ G ⊢// p: U.
Proof.
  introv Hi Hr. dependent induction Hr; auto.
  - split; constructor. apply (proj21 (invertible_and Hi H)). apply (proj22 (invertible_and Hi H)).
  - simpls. specialize (IHHr _ _ Hi eq_refl). destruct_all. split; apply* ty_pq2_r.
Qed.

Lemma repl_to_tight : forall G p T,
    G ⊢// p : T ->
    G ⊢# trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto. apply* inv_to_tight.
Qed.

Lemma replacement_repl_closure_pq1 : forall G p q r T,
    inert G ->
    G ⊢// p : T ->
    G ⊢# trm_path q : typ_sngl r ->
    G ⊢// p : repl_typ q r T.
Proof.
  introv Hi Hp Hqr.
(*  destruct (repl_to_inv Hi Hp Hqr) as [U [Hpu [Heq | Heq]]]; subst.
  - eapply invertible_repl_closure_pq1 in Hpu; eauto.
  - do 2 (eapply invertible_repl_closure_pq1 in Hpu; eauto).
Qed.*)


  gen q r. induction Hp; introv Hq; simpls; auto.
  - Case "ty_inv_r".
    constructor. apply* invertible_repl_closure_pq1.
  - Case "ty_pq2_r".
    specialize (IHHp Hi _ _ Hq). Admitted.

Lemma replacement_repl_closure_pq2 : forall G p q r T,
    inert G ->
    G ⊢# trm_path q : typ_sngl r ->
    G ⊢// p : repl_typ q r T ->
    G ⊢// p : T.
Proof. Admitted.

(** ** Replacment Subtyping Closure *)

 Lemma replacement_typing_closure: forall G p T U,
  inert G ->
  G ⊢// p : T ->
  G ⊢# T <: U ->
  G ⊢// p : U.
Proof.
  introv Hi HT Hsub.
  dependent induction Hsub; auto.
  - induction HT; eauto.
  - false* repl_bot.
  - lets Ha: (repl_and Hi HT). destruct_all. assumption.
  - lets Ha: (repl_and Hi HT). destruct_all. assumption.
  - clear IHHsub. dependent induction HT; simpls; auto. eauto. eauto.
  - clear IHHsub1 IHHsub2. dependent induction HT; simpls. eauto.
    all: apply repl_to_tight in HT; apply* IHHT.
  - dependent induction HT; simpls; eauto.
    * constructor. apply* invertible_repl_closure_pq1.
    * apply* replacement_repl_closure_pq1.
  - apply* replacement_repl_closure_pq2.
  - admit. (* TODO TODO TODO *)
  - admit.
  - admit.
Qed.

(** *** Tight-to-Invertible Lemma for Paths [|-# to |-##]

       [inert G]            #<br>#
       [G ⊢# x: U]         #<br>#
       [―――――――――――――――]    #<br>#
       [G ⊢## x: U] *)
Lemma tight_to_invertible : forall G U p,
    inert G ->
    G ⊢# trm_path p : U ->
    G ⊢// p : U.
Proof.
  introv Hi Hty.
  dependent induction Hty; eauto; try (specialize (IHHty _ Hi eq_refl)).
  - Case "ty_new_elim_t".
    clear Hty. dependent induction IHHty.
    * SCase "ty_precise_inv".
      dependent induction H.
      ** admit. (*apply pf_fld in H. eauto.*)
      ** specialize (IHty_path_inv _ _ eq_refl Hi). apply* replacement_typing_closure.
    * SCase "ty_dec_trm_inv".
      simpls. specialize (IHIHHty _ _ eq_refl Hi).
      apply* replacement_repl_closure_pq2.
  - Case "ty_sngl_t".
    specialize (IHHty1 _ Hi eq_refl). specialize (IHHty2 _ Hi eq_refl).
    admit.
  - Case "ty_rec_intro_t".
    admit.
  - Case "ty_rec_elim_t".
    admit.
  - Case "ty_sub_t".
    apply* replacement_typing_closure.
Qed.

(** ** Invertible Value Typing *)

(** ** Invertible typing for values [G ⊢##v v: T] *)

Reserved Notation "G '⊢##v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_inv : ctx -> val -> typ -> Prop :=

(** [G ⊢! v: T]    #<br>#
    [―――――――――――――] #<br>#
    [G ⊢##v v: T] *)
| ty_precise_inv_v : forall G v T,
  G ⊢!v v : T ->
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
| ty_path_inv_v : forall G v T S q A,
  G ⊢##v v : S ->
  G ⊢! q : T ⪼ typ_rcd {A >: S <: S} ->
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

Hint Constructors ty_val_inv.

(** *** Invertible Subtyping Closure *)

(** Invertible value typing is closed under tight subtyping. *)
Lemma invertible_typing_closure_tight_v: forall G v T U,
  inert G ->
  G ⊢##v v : T ->
  G ⊢# T <: U ->
  G ⊢##v v : U.
Proof.
  introv Hi HT Hsub.
  dependent induction Hsub; eauto; inversions HT; auto; try solve [inversion* H].
  - inversions H0.
  - lets Hb1: (pf_inert_rcd_U Hi H). lets Hb2: (pf_inert_rcd_U Hi H5).
    destruct_all. subst.
    destruct (pf_inert_rcd_U Hi H) as [U' Heq].
    destruct (pf_inert_rcd_U Hi H5) as [T0' Heq'].
    subst. inversions Heq. inversions Heq'.
    lets Heq: (p_bound_rec_unique Hi H H5). subst.
    lets Hu: (pf_record_unique_tight_bounds_rec Hi H H5). subst*.
Qed.

(** ** Tight-to-Invertible Lemma for Values

       [inert G]            #<br>#
       [G ⊢# v: T]         #<br>#
       [――――――――――――――――]   #<br>#
       [G ⊢##v v: T] *)
Lemma tight_to_invertible_v : forall G v T,
    inert G ->
    G ⊢# trm_val v : T ->
    G ⊢##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.

Lemma invertible_obj_fun_type: forall G T ds U V,
    G ⊢##v val_new T ds : (typ_all U V) -> False.
Proof.
  introv Hv. dependent induction Hv. inversion H. eauto.
Qed.

Lemma invertible_to_precise_v_obj: forall G T ds U,
    G ⊢##v val_new T ds : U ->
    inert_typ U ->
    U = typ_bnd T.
Proof.
  introv Hv Hi. dependent induction Hv; try solve [inversion Hi].
  - inversion* H.
  - false* invertible_obj_fun_type.
Qed.
