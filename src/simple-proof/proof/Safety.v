Set Implicit Arguments.

Require Import LibBag LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Binding CanonicalForms Definitions TightTyping GeneralToTight InvertibleTyping Narrowing
            OperationalSemantics PreciseTyping RecordAndInertTypes Substitution Weakening.

(** For the purposes of our evaluation semantics, a term is a
 The typing of a term with a stack *)
Inductive sta_trm_typ : sta * store * trm -> typ -> Prop :=
| sta_trm_typ_c : forall G Sigma s sigma t T,
    inert G ->
    well_typed G Sigma s ->
    wt_store G Sigma sigma ->
    G ⋆ Sigma ⊢ t : T ->
    sta_trm_typ (s, sigma, t) T.

Hint Constructors sta_trm_typ.

Notation "'⊢' t ':' T" := (sta_trm_typ t T) (at level 40, t at level 59).

(** * Preservation *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.15 in the paper. *)
Lemma val_typing: forall G Sigma v T,
  G ⋆ Sigma ⊢ trm_val v : T ->
  exists T', G ⋆ Sigma ⊢! trm_val v : T' /\
        G ⋆ Sigma ⊢ T' <: T.
Proof.
  intros G Sigma v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl). destruct_all. eauto.
Qed.

(** Helper tactics for proving Preservation *)

Ltac binds_eq :=
  match goal with
  | [Hb1: binds ?x _ ?G,
     Hb2: binds ?x _ ?G |- _] =>
     apply (binds_func Hb1) in Hb2; inversions Hb2
  end.

Ltac invert_red :=
  match goal with
  | [Hr: (_, _, _) |-> (_, _, _) |- _] => inversions Hr
  end.

Ltac solve_IH :=
  match goal with
  | [IH: well_typed _ _ _ ->
         wt_store _ _ _ ->
         inert _ ->
         forall t', (_, _, _) |-> (_, _, _) -> _,
       Wf: well_typed _ _ _,
       Ws: wt_store _ _ _,
       In: inert _,
       Hr: (_, _, _) |-> (_, _, ?t') |- _] =>
    specialize (IH Wf Ws In t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⋆ _ & ?Sigma' ⊢ _ : _ |- _] =>
    exists G' Sigma'; repeat split; auto
  end.

Ltac solve_let :=
  invert_red; solve_IH; fresh_constructor; eauto; try (apply weaken_ty_trm_sigma; eauto); apply* weaken_rules.

(** [s: G]                  #<br>#
    [inert [G]              #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [G ⊢ t: T]              #<br>#
    [―――――――――――――――――――]   #<br>#
    [exists G', inert G']        #<br>#
    [s': G, G']             #<br>#
    [G, G' ⊢ t': T]         *)
Lemma preservation_helper: forall G Sigma s sigma t s' sigma' t' T,
    well_typed G Sigma s ->
    wt_store G Sigma sigma ->
    inert G ->
    (s, sigma, t) |-> (s', sigma', t') ->
    G ⋆ Sigma ⊢ t : T ->
    exists G' Sigma', inert G' /\
          well_typed (G & G') (Sigma & Sigma') s' /\
          wt_store (G & G') (Sigma & Sigma') sigma' /\
          G & G' ⋆ Sigma & Sigma' ⊢ t' : T.
Proof.
  introv Hwf Hws Hin Hred Ht. gen t'.
  dependent induction Ht; intros; try solve [invert_red].
  - Case "ty_all_elim".
    match goal with
    | [Hx: _ ⋆ _ ⊢ trm_var (avar_f _) : typ_all _ _ |- _] =>
        pose proof (canonical_forms_fun Hin Hwf Hx) as [L [T' [t [Bis [Hsub Hty]]]]];
          inversions Hred;
          binds_eq
    end.
    exists (@empty typ) (@empty typ). rewrite? concat_empty_r. repeat split; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    eapply renaming_typ; eauto.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hin Hwf Ht) as [?S [ds [t [Bis [Has Ty]]]]].
    invert_red. binds_eq.
    exists (@empty typ) (@empty typ). rewrite? concat_empty_r. repeat split; auto.
    match goal with
    | [Hd: defs_has _ (def_trm _ ?t') |- G ⋆ Sigma ⊢ t': T] =>
      rewrite* <- (defs_has_inv Has Hd)
    end.
  - Case "ty_let".
    destruct t; try solve [solve_let].
    + SCase "[t = (let x = a in u)] where a is a variable".
      repeat invert_red.
      exists (@empty typ) (@empty typ). rewrite? concat_empty_r. repeat split; auto.
      apply* renaming_fresh.
    + SCase "[t = (let x = v in u)] where v is a value".
      repeat invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (well_typed_notin_dom Hwf Hn) as ?Hng
      end.
      pose proof (val_typing Ht) as [V [Hv Hs]].
      exists (x ~ V) (@empty typ). rewrite? concat_empty_r. repeat split.
      * rewrite <- concat_empty_l. eauto.
      * constructor~. apply~ precise_to_general.
      * auto.
      * eapply renaming_fresh with (L:=L \u dom G \u \{x}).
        auto.
        intros. apply~ weaken_rules.
        apply~ ty_sub. apply~ weaken_subtyp.
  - Case "ty_sub".
    solve_IH.
    match goal with
    | [Hs: _ ⋆ _ ⊢ _ <: _,
       Hg: _ & ?G' ⋆ _ & ?Sigma' ⊢ _: _ |- _] =>
      apply weaken_subtyp with (G2:=G') in Hs;
      apply weaken_subtyp_sigma with (Sigma2:=Sigma') in Hs;
      eauto
    end.
  - Case "ty_ref_intro".
    invert_red.
    pose proof (wt_store_fresh_in_Sigma Hws H0).
    exists (@empty typ) (l ~ T). rewrite? concat_empty_r. repeat split; auto.
  - Case "ty_ref_elim".
    pose proof (canonical_forms_ref Hin Hwf Hws Ht) as [?l [?y [? [? [? ?]]]]].
    invert_red.
    exists (@empty typ) (@empty typ). rewrite? concat_empty_r. repeat split; auto.
    congruence.
  - Case "ty_assgn".
    invert_red.
    exists (@empty typ) (@empty typ). rewrite? concat_empty_r. repeat split; auto.
    pose proof (canonical_forms_ref Hin Hwf Hws Ht1) as [?l [?y [? [? [? ?]]]]].
    assert (l0 = l) by congruence; subst l0. clear H.
    pose proof (val_typ_ref_to_loc Hin H1) as [?l [?T [? [? ?]]]].
    assert (l0 = l) by congruence; subst l0; clear H.
    eapply wt_store_update; auto.
    + apply H4.
    + destruct_all. apply tight_to_general.
      pose proof (general_to_tight_typing Hin Ht2).
      eapply ty_sub_t; eauto.
Qed.

(** ** Preservation Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [⊢ (s', t'): T]         *)
Theorem preservation : forall s s' sigma sigma' t t' T,
    ⊢ (s, sigma, t) : T ->
    (s, sigma, t) |-> (s', sigma', t') ->
    ⊢ (s', sigma', t') : T.
Proof.
  introv Ht Hr. destruct Ht as [* Hi Hwf Hws Ht].
  lets Hp: (preservation_helper Hwf Hws Hi Hr Ht). destruct Hp as [G' [Sigma' [Hi' [Hwf' [Hws' Ht']]]]].
  apply sta_trm_typ_c with (G:=G & G') (Sigma:=Sigma & Sigma'); auto. apply* inert_concat.
Qed.

(** * Progress *)

(** Helper tactic for proving progress *)
Ltac solve_let_prog :=
  match goal with
      | [IH: ⊢ (?s, ?sigma, ?t) : ?T ->
             inert _ ->
             well_typed _ _ _ ->
             wt_store _ _ _ ->
             _,
         Hi: inert _,
         Hwt: well_typed _ _ _,
         Hws: wt_store _ _ _ |- _] =>
        assert (⊢ (s, sigma, t): T) as Hs by eauto;
        specialize (IH Hs Hi Hwt Hws) as [IH | [s' [sigma' [t' Hr]]]];
        eauto; inversion IH
      end.

(** ** Progress Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [t] is in normal form   #<br>#
    or [exists s', t'] such that [(s, t) |-> (s', t')] *)
Theorem progress: forall s sigma t T,
    ⊢ (s, sigma, t) : T ->
    norm_form t \/ exists s' sigma' t', (s, sigma, t) |-> (s', sigma', t').
Proof.
  introv Ht. inversion Ht as [G Sigma s' sigma' t' T' Hi Hwt Hws HT]. subst.
  induction HT; eauto.
  - Case "ty_all_elim".
    pose proof (canonical_forms_fun Hi Hwt HT1). destruct_all. right*.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hi Hwt HT). destruct_all. right*.
  - Case "ty_let".
    right. destruct t; try solve [solve_let_prog].
    + pose proof (var_typing_implies_avar_f HT) as [x A]. subst*.
    + pick_fresh x. exists (s & x ~ v) sigma (open_trm x u). auto.
  - Case "ty_ref_intro".
    right.
    pick_fresh l.
    exists s (sigma[l:=x]) (trm_val (val_loc l)).
    apply* red_ref_var.
    eauto using wt_store_notindom.
  - Case "ty_ref_elim".
    pose proof (canonical_forms_ref Hi Hwt Hws HT) as [?l [?y ?]]. destruct_all. right*.
  - Case "ty_asgn".
    pose proof (canonical_forms_ref Hi Hwt Hws HT1) as [?l [?y ?]]. destruct_all. right.
    pose proof (binds_dom H1).
    exists s (sigma[l:=y]) (trm_var (avar_f y)); auto.
Qed.
