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
Require Import Definitions Binding Narrowing PreciseTyping RecordAndInertTypes SingletonTyping
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
| ty_precise_inv : forall G p qs T,
  G ⊢• p : qs ⪼ T ->
  G ⊢## p : T

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
| ty_sel_inv : forall G p q A S T,
  G ⊢## p : S ->
  G ⊢! q : T ⪼ typ_rcd {A >: S <: S} ->
  G ⊢## p : typ_path q A

(** [G ⊢## p: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## p: top]     *)
| ty_top_inv : forall G p T,
  G ⊢## p : T ->
  G ⊢## p : typ_top

(* replacement rules: recursive types, selection types, singleton types *)

| ty_rec_qp1_inv : forall G p q r T,
    G ⊢## p : typ_sngl q ->
    G ⊢## r : typ_bnd T ->
    G ⊢## r : typ_bnd (repl_typ q p T)

| ty_rec_pq2_inv : forall G p q r T,
    G ⊢## p : typ_sngl q ->
    G ⊢## r : typ_bnd (repl_typ p q T) ->
    G ⊢## r : typ_bnd T

| ty_sel_qp1_inv : forall G p q r r' A,
    G ⊢## p : typ_sngl q ->
    G ⊢## r : typ_path r' A ->
    G ⊢## r : typ_path (repl_path q p r') A

| ty_sel_pq2_inv : forall G p q r r' A,
    G ⊢## p : typ_sngl q ->
    G ⊢## r : typ_path (repl_path q p r') A ->
    G ⊢## r : typ_path r' A

| ty_sngl_qp1_inv : forall G p q r r',
    G ⊢## p : typ_sngl q ->
    G ⊢## r : typ_sngl r' ->
    G ⊢## r : typ_sngl (repl_path q p r')

| ty_sngl_pq2_inv : forall G p q r r',
    G ⊢## p : typ_sngl q ->
    G ⊢## r : typ_sngl (repl_path q p r') ->
    G ⊢## r : typ_sngl r'

where "G '⊢##' p ':' T" := (ty_path_inv G p T).

Hint Constructors ty_path_inv.

(** *** Invertible to Precise Typing [|-## to |-!] *)

(** Invertible typing implies tight typing. *)
Lemma inv_to_tight: forall G p T,
    G ⊢## p: T ->
    G ⊢# trm_path p: T.
Proof.
  introv Ht. induction Ht; eauto.
  - dependent induction H; eauto. apply precise_to_tight in H.
    destruct_all. auto.
  - apply ty_sub_t with (T:=repl_typ p q (typ_bnd T)); eauto.
  - apply ty_sub_t with (T:=repl_typ q p (typ_path r' A)); eauto.
  - apply ty_sub_t with (T:=repl_typ q p (typ_sngl r')); eauto.
(*
    lets Hst: (sngl_to_tight H). eapply ty_sub_t. apply IHHt.
    destruct qs.
    inversions H. eauto. destruct (List.app_eq_nil _ _ H0). inversion H2.
    lets Hsp: (sngl_precise H). destruct Hsp as [U Hp].
    apply subtyp_trans_t with (T:=typ_path p0 A). apply* subtyp_sel2_t.
    apply sngl_tight_paths in H.
    assert (typ_path q A = repl_typ p0 q (typ_path p0 A)) as Heq by admit.
    rewrite Heq. eauto.
 *)
Qed.

(* this is not true because the ⊢## judgment might be obtained through another path that is equal to q, i.e.
   Г(r) = q.type
   Г(p) = p.type
   ______________
   Г ⊢## p: q.type
 *)
(*Lemma invertible_to_precise_sngl : forall G p q,
    inert G ->
    G ⊢## p : typ_sngl q ->
    exists qs, G ⊢• p : qs ⪼ typ_sngl q.
Proof.
  introv Hi Hp. dependent induction Hp.
  - Case "ty_precise_inv".
    eauto.
  - Case "ty_repl_inv".
    destruct T; inversions x. specialize (IHHp2 _ Hi eq_refl). specialize (IHHp1 _ Hi eq_refl).
    destruct IHHp1 as [q0s IH1]. destruct IHHp2 as [p0s IH2]. (* the problem is here *)
  - Case "ty_sngl_inv".
    specialize (IHHp2 _ Hi eq_refl). eauto.
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
  exists qs T',
    G ⊢• p: qs ⪼ typ_rcd {a ⦂ T'} /\
    G ⊢# T' <: T.
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - repeat eexists; eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [qs [T' [Hp Hs]]]. repeat eexists; eauto.
(*  - destruct T0; inversions x. destruct d; inversions H0. specialize (IHHinv2 _ _ Hi eq_refl).
    destruct IHHinv2 as [qs [T' [Ht Hs]]]. repeat eexists. apply Ht.
    apply subtyp_trans_t with (T:=t0); auto. apply inv_to_tight in Hinv1.
    eauto.*)
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
  exists qs S' T' L,
    G ⊢• p : qs ⪼ typ_all S' T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hinv.
  dependent induction Hinv.
  - exists qs S T (dom G); eauto.
  - specialize (IHHinv _ _ Hi eq_refl). destruct IHHinv as [qs [S' [T' [L' [Hp [Hs1 Hs]]]]]].
    exists qs S' T' (L \u L'). repeat split; auto. eauto. (* renaming *) admit.
(*  - destruct T0; inversions x. specialize (IHHinv2 _ _ Hi eq_refl).
    destruct IHHinv2 as [qs [S' [T' [L [Hr [Hs Hs2]]]]]].
    exists qs S' T' L. split; auto. split. apply subtyp_trans_t with (T:=T0_1); auto.
    apply inv_to_tight in Hinv1. eauto. (* renaming *) admit.*)
Qed.

Lemma invertible_bot : forall G p,
    inert G ->
    G ⊢## p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. false* sngl_bot.
  (*destruct T; inversions x. eauto.*)
Qed.

Lemma invertible_and : forall G p T U,
    inert G ->
    G ⊢## p: typ_and T U ->
    G ⊢## p: T /\ G ⊢## p: U.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - split; apply sngl_and in H; destruct_all; eauto.
  (*- destruct T0; inversions x. specialize (IHHp2 _ _ Hi eq_refl). destruct_all.
    split*.*)
Qed.

(** ** Invertible Replacement Closure *)

Lemma invertible_repl_closure : forall G p q r T,
    inert G ->
    G ⊢## p : T ->
    G ⊢## q : typ_sngl r ->
    G ⊢## p : repl_typ q r T.
Proof.
  introv Hi Hp. gen q. induction Hp; introv Hq; eauto.
  - destruct (sngl_inertsngl Hi H) as [[His | His] | His].
    * inversions His.
    + simpl. eapply ty_all_inv. apply* ty_precise_inv.
      auto. introv Hy.
      assert (open_typ y (repl_typ q r T0) = repl_typ q r (open_typ y T0)) as Heq by admit.
      rewrite Heq. apply tight_to_general in Hq. apply weaken_subtyp. auto. apply* ok_push.
    + simpl. apply* ty_repl_rec_inv.


    gen q r. induction H; introv Hpr.
    * gen q r. induction H; introv Hpr; admit.
    * specialize (IHty_path_sngl1 _ _ Hpr). specialize (IHty_path_sngl2 _ _ Hpr).



(** ** Invertible Subtyping Closure *)

(** Invertible typing is closed under tight subtyping. *)
Lemma invertible_typing_closure_tight: forall G p T U,
  inert G ->
  G ⊢## p : T ->
  G ⊢# T <: U ->
  G ⊢## p : U.
Proof.
  intros G x T U Hi HT Hsub. rename x into r.
  dependent induction Hsub; eauto.
  - false* invertible_bot.
  - lets Ha: (invertible_and Hi HT). destruct_all. assumption.
  - lets Ha: (invertible_and Hi HT). destruct_all. assumption.
  - gen p q. induction HT; introv Hp; eauto.
    * (* NEXT: try to prove this by induction on H, and induction on the underlying precise typing *)
  - (* need mutual induction to get that G ⊢## p: q.type *)
    assert (G ⊢## p : typ_sngl q) as Hp by admit. admit.
  - assert (G ⊢## p : typ_sngl q) as Hp by admit. admit.
  - admit.
  -
    dependent induction HT.
    + false* pf_psel_false.
    + lets Hu: (pf_inert_rcd_U Hi H). lets Hu': (pf_inert_rcd_U Hi H0). destruct_all. subst.
      lets Heq: (p_bound_rec_unique Hi H H0). subst.
      lets Heq: (pf_record_unique_tight_bounds_rec Hi H H0). subst. eauto.
    + destruct T; inversions x. specialize (IHHT2 Hi _ _ eq_refl). clear IHHT1.
      unfold repl_path in H. destruct p1, p0, a.
      * apply precise_to_general in H. apply typed_paths_named in H. inversion H. destruct_all. inversion* H0.
      * destruct f. admit. case_if.
        ** destruct q. destruct_all. subst.
           rename v into q'_x. rename f0 into q'_bs. rename a into q_x. rename f1 into q_bs.
           rename t into bs.
           lets Hp: (ty_repl1_inv HT1 HT2).
           lets Hpr: (invertible_to_precise_sngl Hi HT1).
           remember (p_sel (avar_f q'_x) q'_bs) as q'. remember (p_sel q_x q_bs) as q.
           remember (p_sel (avar_f q'_x) (bs :: q'_bs)%list) as q'bs.
           remember (p_sel q_x (bs :: q_bs)%list) as qbs.
           destruct (classicT (q'=q)).
           *** rewrite e in *. clear e Hpr.
               assert (repl_typ q q (typ_path q'bs A) = typ_path q'bs A) as Heq by admit.
               rewrite Heq in Hp. clear Heq.
               subst. inversions Heqq. apply* IHHT2.
           *** specialize (Hpr n).
        Admitted.

(** *** Tight-to-Invertible Lemma for Paths [|-# to |-##]

       [inert G]            #<br>#
       [G ⊢# x: U]         #<br>#
       [―――――――――――――――]    #<br>#
       [G ⊢## x: U] *)
Lemma tight_to_invertible : forall G U p,
    inert G ->
    G ⊢# trm_path p : U ->
    G ⊢## p : U.
Proof.
  intros G U x Hi Hty.
  dependent induction Hty; eauto; try (specialize (IHHty _ Hi eq_refl)).
  - Case "ty_new_elim_t".
    clear Hty. dependent induction IHHty.
    * SCase "ty_precise_inv".
      apply pf_fld in H. eauto.
    * SCase "ty_dec_trm_inv".
      apply invertible_typing_closure_tight with (T:=T0); auto.
    * SCase "ty_repl1_inv".
      destruct T0; inversions x. destruct d; inversions H0.
      specialize (IHIHHty2 _ _ eq_refl Hi).
      eapply invertible_typing_closure_tight. assumption. eassumption.
      eapply subtyp_sngl1_t. apply* inv_to_tight.
    * SCase "ty_repl2_inv"simpls.
      apply* IHIHHty2. repeat f_equal.
  - Case "ty_sngl_t".
    specialize (IHHty1 _ Hi eq_refl). specialize (IHHty2 _ Hi eq_refl).
    destruct x. destruct f. apply tight_to_general in Hty1. apply typed_paths_named in Hty1.
    inversions Hty1. destruct H as [bs Heq]. inversions Heq.
    apply (invertible_sngl_var Hi) in IHHty1. subst. assumption.
    assert (p_sel a (t :: f)%list = (p_sel a f) • t) as Heq by auto.
    rewrite Heq in *. (*
    apply ( invertible_to_precise_sngl _ _ Hi) in IHHty1. rename t into a'.
    clear Hty1 Hty2 Heq.
    induction IHHty2; eauto.
    * SCase "ty_precise_inv". admit.
    * specialize (IHIHHty2 IHHty1 Hi). *) admit.
  - Case "ty_rec_elim_t".
    inversion IHHty; subst; eauto.
  - Case "ty_sub_t".
    eapply invertible_typing_closure_tight; eauto.
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
