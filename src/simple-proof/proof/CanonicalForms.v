(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibBag LibMap LibLN.
Require Import Definitions.
Require Import RecordAndInertTypes.
Require Import Subenvironments.
Require Import Narrowing.
Require Import PreciseTyping.
Require Import TightTyping.
Require Import InvertibleTyping.
Require Import GeneralToTight.
Require Import Substitution.
Require Import Weakening.

(** * Simple Implications of Typing *)

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G Sigma x T,
  G ⋆ Sigma ⊢ trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
Qed.

(** * Well-typedness *)

(** If [e: G], the variables in the domain of [e] are distinct. *)
Lemma well_typed_to_ok_G: forall G Sigma e,
    well_typed G Sigma e -> ok G.
Proof.
  introv H. induction H; jauto.
Qed.
Hint Resolve well_typed_to_ok_G.

Lemma well_typed_to_ok_S: forall G Sigma e,
    well_typed G Sigma e -> ok Sigma.
Proof.
  introv H. induction H; jauto.
Qed.
Hint Resolve well_typed_to_ok_S.

Lemma wt_store_to_ok_S : forall G Sigma s,
    wt_store G Sigma s -> ok Sigma.
  introv H. induction H; jauto.
Qed.
Hint Resolve wt_store_to_ok_S.

Lemma wt_store_to_ok_G : forall G Sigma s,
    wt_store G Sigma s -> ok G.
  introv H. induction H; jauto.
Qed.
Hint Resolve wt_store_to_ok_G.

Lemma well_typed_notin_dom: forall G Sigma s x,
    well_typed G Sigma s ->
    x # s -> x # G.
Proof.
  intros. induction H; auto.
Qed.

Lemma notindom_update: forall A B (x y : A) (v : B) m,
    x \notindom m[y:=v] ->
    x \notindom m /\ x <> y.
Proof.
  introv.
  unfold LibBag.notin.
  intros. split.
  + unfold not; intros. apply H.
    rewrite indom_update; auto.
  + unfold not. intros. apply H.
    subst. apply indom_update_self; auto.
Qed.

Lemma wt_store_fresh_in_Sigma: forall G Sigma sigma l,
    wt_store G Sigma sigma ->
    l \notindom sigma ->
    l # Sigma.
Proof.
  intros.
  induction H;
    match goal with
    | [H: LibBag.notin ?l (LibBag.dom ?s [?l1 := ?v]) |- _] =>
      pose proof (notindom_update H) as [? ?]
    | _ => idtac
    end;
    auto.
Qed.

Lemma wt_store_notindom: forall G Sigma s l,
  wt_store G Sigma s ->
  l # Sigma ->
  l \notindom s.
Proof.
  introv Hws. induction Hws.
  - intros. unfold LibBag.notin, not.
    intros. eapply LibMap.in_dom_empty.
    apply H0.
  - intros. unfold LibBag.notin, not.
    intros.
    apply indom_update_inv in H2; auto.
    destruct_all; subst.
    eauto using binds_fresh_inv.
    apply IHHws; auto.
  - intros. unfold LibBag.notin, not.
    intros.
    apply indom_update_inv in H2; auto.
    destruct_all; subst.
    pose proof (binds_push_eq l0 T (Sigma & l0 ~ T)).
    eauto using binds_fresh_inv.
    apply IHHws; auto.
  - auto.
Qed.

(** [e: G]              #<br>#
    [G(x) = T]          #<br>#
    [―――――――――――――]     #<br>#
    [exists v, e(x) = v]     #<br>#
    [G ⋆ Sigma ⊢ v: T]          *)
Lemma corresponding_types: forall G Sigma e x T,
    well_typed G Sigma e ->
    binds x T G ->
    (exists v, binds x v e /\
          G ⋆ Sigma ⊢ trm_val v : T).
Proof.
  introv Hwt BiG. induction Hwt.
  - false* binds_empty_inv.
  - destruct (classicT (x = x0)).
    + subst. apply binds_push_eq_inv in BiG. subst.
      exists v. repeat split~. apply~ weaken_ty_trm.
      apply* ok_push.
    + apply binds_push_neq_inv in BiG; auto.
      specialize (IHHwt BiG) as [v' [Bis Ht]].
      exists v'. repeat split~. apply~ weaken_ty_trm.
      apply* ok_push.
  - destruct (IHHwt BiG) as [v [? ?]]. exists v; split~.
    apply~ weaken_ty_trm_sigma; auto.
    apply* ok_push.
Qed.

(** [G ⋆ Sigma ⊢##v v: forall(S)T]                 #<br>#
    [inert G]                          #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [exists S', T', G ⋆ Sigma ⊢! v: forall(S')T']      #<br>#
    [G ⋆ Sigma ⊢ S <: S']                      #<br>#
    [forall fresh y, G, y: S ⋆ Sigma ⊢ T'^y <: T^y] *)
Lemma invertible_val_to_precise_lambda: forall G Sigma v T U,
    G ⋆ Sigma ⊢##v v : typ_all T U ->
    inert G ->
    exists L T' U',
      G ⋆ Sigma ⊢! trm_val v : typ_all T' U' /\
      G ⋆ Sigma ⊢ T <: T' /\
      (forall y, y \notin L ->
                 G & y ~ T ⋆ Sigma ⊢ open_typ y U' <: open_typ y U).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) T U. split*.
  - destruct (IHHt _ _ eq_refl Hg) as [L' [T1 [U1 [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) T1 U1. split. assumption. split. apply subtyp_trans with (U:=S1).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ T)) as Hok. {
      apply* ok_push.
    }
    apply subtyp_trans with (U:=open_typ y T0).
    eapply narrow_subtyping. apply* Hst. apply subenv_last.
    apply* tight_to_general.
    all: auto.
Qed.

(** This lemma corresponds to Lemma 3.7 ([forall] to [G(x)]) in the paper.

    [inert G]            #<br>#
    [G ⋆ Sigma ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U',]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G ⋆ Sigma ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⋆ Sigma ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G Sigma x T U,
    inert G ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G ⋆ Sigma ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⋆ Sigma ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [L [Htp [Hs1 Hs2]]]]].
  exists L T' U'. repeat split.
  - apply* inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

(** This lemma corresponds to Lemma 3.8 ([forall] to [lambda]) in the paper.

    [inert G]                       #<br>#
    [G ⋆ Sigma ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                       #<br>#
    [v = lambda(T')t]              #<br>#
    [G ⋆ Sigma ⊢ T <: T']                   #<br>#
    [forall fresh y, G, y: T ⋆ Sigma ⊢ t^y: U^y] *)
Lemma val_typ_all_to_lambda: forall G Sigma v T U,
    inert G ->
    G ⋆ Sigma ⊢ trm_val v : typ_all T U ->
    (exists L T' t,
        v = val_lambda T' t /\
        G ⋆ Sigma ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⋆ Sigma ⊢ (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_v Hin Htt).
  destruct (invertible_val_to_precise_lambda Hinv Hin) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H3 y HL0).
  eapply ty_sub; eauto. eauto using narrow_typing.
Qed.

(** * Canonical Forms for Functions

    [inert G]            #<br>#
    [e: G]               #<br>#
    [G ⋆ Sigma ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――――――] #<br>#
    [e(x) = lambda(T')t] #<br>#
    [G ⋆ Sigma ⊢ T <: T']        #<br>#
    [G, x: T ⋆ Sigma ⊢ t: U]          *)
Lemma canonical_forms_fun: forall G Sigma e x T U,
  inert G ->
  well_typed G Sigma e ->
  G ⋆ Sigma ⊢ trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_lambda T' t) e /\ G ⋆ Sigma ⊢ T <: T' /\
  (forall y, y \notin L -> G & y ~ T ⋆ Sigma ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hwt Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S' [T' [BiG [Hs1 Hs2]]]]].
  destruct (corresponding_types Hwt BiG) as [v [Bis Ht]].
  destruct (val_typ_all_to_lambda Hin Ht) as [L' [S'' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S'' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    + eapply ty_sub; eauto.
Qed.

(** [d1 isin ds]             #<br>#
    [label(d2) \notin ds]     #<br>#
    [―――――――――――――――――――――]  #<br>#
    [label(d1) <> label(d2)]  *)
Lemma defs_has_hasnt_neq: forall ds d1 d2,
  defs_has ds d1 ->
  defs_hasnt ds (label_of_def d2) ->
  label_of_def d1 <> label_of_def d2.
Proof.
  introv Hhas Hhasnt.
  unfold defs_has in Hhas.
  unfold defs_hasnt in Hhasnt.
  induction ds.
  - simpl in Hhas. inversion Hhas.
  - simpl in Hhasnt. simpl in Hhas. case_if; case_if.
    + inversions Hhas. assumption.
    + apply IHds; eauto.
Qed.

(** [G ⋆ Sigma ⊢ ds :: ... /\ D /\ ...]       #<br>#
    [―――――――――――――――――――――――]       #<br>#
    [exists d, ds = ... /\ d /\ ...]       #<br>#
    [G ⋆ Sigma ⊢ d: D]                      *)
Lemma record_has_ty_defs: forall G Sigma T ds D,
  G ⋆ Sigma /- ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ G ⋆ Sigma /- d : D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    + unfold defs_has. simpl. rewrite If_l; reflexivity.
    + assumption.
  - inversion Hhas; subst.
    + destruct (IHHdefs H4) as [d' [H1 H2]].
      exists d'. split.
      * unfold defs_has. simpl. rewrite If_r. apply H1.
        apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      * assumption.
    + exists d. split.
      * unfold defs_has. simpl. rewrite If_l; reflexivity.
      * inversions* H4.
Qed.

(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⋆ Sigma ⊢ x: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⋆ Sigma ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G Sigma x a T,
    inert G ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (exists S' T',
        binds x (typ_bnd S') G /\
        record_has (open_typ x S') (dec_trm a T') /\
        G ⋆ Sigma ⊢ T' <: T).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S' BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [T' [Htp Hs]].
  destruct (precise_flow_lemma Htp) as [U Pf].
  destruct (pf_inert_rcd_U Hin Pf) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Pf). apply pf_binds in Pf.
  exists U' T'. split. assumption. split. assumption. apply* tight_to_general.
Qed.

(** This lemma corresponds to Lemma 3.10 ([mu] to [nu]) in the paper.

    [inert G]                  #<br>#
    [G ⋆ Sigma ⊢ v: mu(T)]             #<br>#
    [G ⋆ Sigma ⊢ x: T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⋆ Sigma ⊢ t: U] *)
Lemma val_mu_to_new: forall G Sigma v T U a x,
    inert G ->
    G ⋆ Sigma ⊢ trm_val v: typ_bnd T ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : open_typ x T ->
    record_has (open_typ x T) (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs x ds) (def_trm a t) /\
      G ⋆ Sigma ⊢ t: U.
Proof.
  introv Hi Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi Htt).
  inversions Hinv. inversions H.
  pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H4 z Hz).
  assert (G ⋆ Sigma /- open_defs x ds :: open_typ x T) as Hds by apply* renaming_def.
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]]. inversions Hd.
  exists t ds. split*.
Qed.

(** * Canonical Forms for Objects

    [inert G]                    #<br>#
    [e: G]                       #<br>#
    [G ⋆ Sigma ⊢ x: {a:T}]          #<br>#
    [――――――――――――――――――――――――――] #<br>#
    [exists S, ds, t,]                #<br>#
    [e(x) = nu(S)ds]             #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⋆ Sigma ⊢ t: T] *)
Lemma canonical_forms_obj: forall G Sigma e x a T,
  inert G ->
  well_typed G Sigma e ->
  G ⋆ Sigma ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  (exists S' ds t, binds x (val_new S' ds) e /\ defs_has (open_defs x ds) (def_trm a t) /\ G ⋆ Sigma ⊢ t : T).
Proof.
  introv Hi Hwt Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [S' [T' [Bi [Hr Hs]]]].
  destruct (corresponding_types Hwt Bi) as [v [Bis Ht]].
  apply ty_var with (Sigma:=Sigma) in Bi. apply ty_rec_elim in Bi.
  destruct (val_mu_to_new Hi Ht Bi Hr) as [t [ds [Heq [Hdefs Ht']]]].
  subst. exists S' ds t. repeat split~. eapply ty_sub; eauto.
Qed.

(** * Canonical Forms for References

    [inert G]            #<br>#
    [e: G ⋆ S]          #<br>#
    [G ⋆ Sigma ⊢ x: {a:T}]  #<br>#
    [――――――――――――――――――] #<br>#
    [exists S, ds, t,] #<br>#
    [e(x) = nu(S)ds] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⋆ Sigma ⊢ t: T] *)

(*
Lemma var_typ_ref_to_binds: forall G Sigma x T,
    inert G ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : typ_ref T ->
        binds x (typ_ref T) G.
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_ref (inert_ok Hin) Hinv) as [T' [Htp [Hs1 Hs2]]].
  exists T'. split.
*)

Lemma var_typ_ref_to_binds: forall G Sigma x T,
    inert G ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : typ_ref T ->
    (exists T',
        binds x (typ_ref T') G /\
        G ⋆ Sigma ⊢ T <: T' /\
        G ⋆ Sigma ⊢ T' <: T).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_ref (inert_ok Hin) Hinv) as [T' [Htp [Hs1 Hs2]]].
  exists T'. split.
  - apply* inert_precise_ref_inv.
  - split; apply~ tight_to_general.
Qed.

Lemma sigma_binds_to_store_binds_typing: forall sto G Sigma l T,
  wt_store G Sigma sto ->
  binds l T Sigma ->
  exists x, bindsM l x sto /\ G ⋆ Sigma ⊢ (trm_var (avar_f x)) : T.
Proof.
  introv Hwt. gen l T.
  induction Hwt; introv Bi.
  - false* binds_empty_inv.
  - pose proof (IHHwt _ _ Bi) as [?x [HBi Hty]]; clear IHHwt.
    lets Hdec: (classicT (l = l0)). destruct Hdec as [Hdec | Hdec].
    + subst l0. exists x. split.
      * apply binds_update_eq.
      * rewrite (binds_func Bi H); auto.
    + exists x0. split.
      * apply binds_update_neq; auto.
      * auto.
  - lets OkS: (wt_store_to_ok_S Hwt).
    lets Hdec: (classicT (l = l0)). destruct Hdec as [Hdec | Hdec].
    + subst l0. exists x. split.
      * apply binds_update_eq.
      * rewrite (binds_push_eq_inv Bi); auto using weaken_ty_trm_sigma.
    + apply not_eq_sym in Hdec.
      pose proof (binds_push_neq_inv Bi Hdec).
      pose proof (IHHwt _ _ H1) as [?x [HBi Hty]]; clear IHHwt.
      exists x0. split.
      * apply binds_update_neq; auto.
      * auto using weaken_ty_trm_sigma.
  - pose proof (IHHwt _ _ Bi) as [?x [HBi Hty]].
    exists x0. split; auto.
    lets OkG: (wt_store_to_ok_G Hwt).
    apply weaken_ty_trm; auto.
Qed.

Lemma invertible_val_to_precise_ref: forall G Sigma v T,
    inert G ->
    G ⋆ Sigma ⊢##v v : typ_ref T ->
    exists T',
      G ⋆ Sigma ⊢! trm_val v : typ_ref T' /\
      G ⋆ Sigma ⊢# T <: T' /\
      G ⋆ Sigma ⊢# T' <: T.
Proof.
  introv Hin Ht. dependent induction Ht.
  - exists T; auto.
  - pose proof (IHHt _ Hin eq_refl) as [T' [? [? ?]]].
    exists T'. eauto.
Qed.

Lemma val_typ_ref_to_loc: forall G Sigma v T,
    inert G ->
    G ⋆ Sigma ⊢ trm_val v : typ_ref T ->
    exists l T',
      v = val_loc l /\
      binds l T' Sigma /\
      G ⋆ Sigma ⊢# T <: T' /\ G ⋆ Sigma ⊢# T' <: T.
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_v Hin Htt).
  pose proof (invertible_val_to_precise_ref Hin Hinv) as [T' [Htp ?]].
  inversions Htp.
  exists l T'. auto.
Qed.

Lemma canonical_forms_ref: forall G Sigma e s x T,
  inert G ->
  well_typed G Sigma e ->
  wt_store G Sigma s ->
  G ⋆ Sigma ⊢ trm_var (avar_f x) : typ_ref T ->
  (exists l y, binds x (val_loc l) e /\
          (G ⋆ Sigma ⊢ (trm_val (val_loc l)) : (typ_ref T)) /\
          bindsM l y s /\
          (G ⋆ Sigma ⊢ (trm_var (avar_f y)) : T)).
Proof.
  introv Hi Hwt Hws Hty.
  destruct (var_typ_ref_to_binds Hi Hty) as [T' [Bi [Hr Hs]]].
  destruct (corresponding_types Hwt Bi) as [v [Bis Ht]].
  pose proof (val_typ_ref_to_loc Hi Ht) as [l [?T [Hv [HBi [Hs1 Hs2]]]]].
  pose proof (sigma_binds_to_store_binds_typing Hws HBi) as [?x [? ?]].
  exists l x0.
  split.
  - rewrite <- Hv. auto.
  - split.
    + eapply ty_sub.
      * rewrite <- Hv. apply Ht.
      * eapply subtyp_ref; auto.
    + split; auto. eapply ty_sub; try eassumption.
      apply tight_to_general in Hs2.
      eapply subtyp_trans.
      * eapply Hs2.
      * eauto.
Qed.
