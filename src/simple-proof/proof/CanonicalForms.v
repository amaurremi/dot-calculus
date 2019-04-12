(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import TLC.LibLN.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        GeneralToTight Subenvironments Weakening Narrowing Substitution.

(** * Simple Implications of Typing *)

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G ⊢ trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
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

(** [G ⊢ ds :: ... /\ D /\ ...]       #<br>#
    [―――――――――――――――――――――――]       #<br>#
    [exists d, ds = ... /\ d /\ ...]       #<br>#
    [G ⊢ d: D]                      *)
Lemma record_has_ty_defs: forall G T ds D,
  G /- ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ G /- d : D.
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

(** * Functions under Inert Contexts *)
(** This lemma corresponds to Lemma 3.7 ([forall] to [G(x)]) in the paper.

    [inert G]            #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U',]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G x T U,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V' [L [Htp [Hs1 Hs2]]]]]].
  exists L T' U'. repeat split.
  - apply* inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

(** This lemma corresponds to Lemma 3.8 ([forall] to [lambda]) in the paper.

    [inert G]                       #<br>#
    [G ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                       #<br>#
    [v = lambda(T')t]              #<br>#
    [G ⊢ T <: T']                   #<br>#
    [forall fresh y, G, y: T ⊢ t^y: U^y] *)
Lemma val_typ_all_to_lambda: forall G v T U,
    inert G ->
    G ⊢ trm_val v : typ_all T U ->
    (exists L T' t,
        v = val_lambda T' t /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_v Hin Htt).
  destruct (invertible_val_to_precise_lambda Hin Hinv) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H2 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H2; eauto.
Qed.

(** * Objects under Inert Contexts *)
(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⊢ x: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G x a T,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open_typ x S) (dec_trm a T') /\
        G ⊢ T' <: T).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [T' [U [Htp Hs]]].
  destruct (pf_inert_rcd_U Hin Htp) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp). apply pf_binds in Htp.
  exists U' T'. split. assumption. split. assumption. apply* tight_to_general.
Qed.

(** This lemma corresponds to Lemma 3.10 ([mu] to [nu]) in the paper.

    [inert G]                  #<br>#
    [G ⊢ v: mu(T)]             #<br>#
    [G ⊢ x: T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U] *)
Lemma val_mu_to_new: forall G v T U a x,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ trm_var (avar_f x) : open_typ x T ->
    record_has (open_typ x T) (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs x ds) (def_trm a t) /\
      G ⊢ t: U.
Proof.
  introv Hi Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi Htt).
  inversions Hinv. inversions H.
  pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H3 z Hz).
  assert (G /- open_defs x ds :: open_typ x T) as Hds. {
    apply* renaming_def; eauto.
  }
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]]. inversions Hd.
  exists t ds. split*.
Qed.

(** * Well-typedness *)

(** If [s: G], the variables in the domain of [s] are distinct. *)
Lemma well_typed_to_ok_G: forall s G,
    well_typed G s -> ok G.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve well_typed_to_ok_G.

Lemma well_typed_to_ok_s: forall s G,
    well_typed G s -> ok s.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve well_typed_to_ok_s.

(** [s: G]       #<br>#
    [x ∉ dom(G)] #<br>#
    [――――――――――] #<br>#
    [x ∉ dom(s)] *)
Lemma well_typed_notin_dom: forall G s x,
    well_typed G s ->
    x # s ->
    x # G.
Proof.
  introv Hwt. destruct Hwt as [? [? [?Hdom ?]]].
  unfold notin. rewrite Hdom.
  auto.
Qed.

Lemma well_typed_empty:
    well_typed empty empty.
Proof.
  repeat split; auto.
  - simpl_dom; auto.
  - introv B. exfalso; apply* binds_empty_inv.
Qed.
Hint Resolve well_typed_empty.

Lemma well_typed_push: forall G s x T v,
    well_typed G s ->
    x # G ->
    x # s ->
    G ⊢ trm_val v : T ->
    well_typed (G & x ~ T) (s & x ~ v).
Proof.
  intros. unfold well_typed in *.
  destruct_all.
  repeat split; auto.
  - simpl_dom. fequal. auto.
  - intros x0 T0 v0 BxG. gen v0.
    destruct (binds_push_inv BxG) as [[?Heqx ?HeqT] | [?Hneq ?HB]].
    + subst x0 T0. introv Bxv. apply binds_push_eq_inv in Bxv.
      subst v0. apply weaken_ty_trm; auto.
    + intros.
      assert (binds x0 T0 G) by eauto using binds_push_neq_inv.
      assert (binds x0 v0 s) by eauto using binds_push_neq_inv.
      apply weaken_ty_trm; eauto.
Qed.
Hint Resolve well_typed_push.

(** [s: G]              #<br>#
    [G(x) = T]          #<br>#
    [―――――――――――――]     #<br>#
    [exists v, s(x) = v]     #<br>#
    [G ⊢ v: T]          *)
Lemma corresponding_types: forall G s x T,
    well_typed G s ->
    binds x T G ->
    (exists v, binds x v s /\
          G ⊢ trm_val v : T).
Proof.
  introv Hwt BiG. destruct Hwt as [?HokG [?HokS [?HdomEq ?]]].
  pose proof (get_some_inv BiG) as HinDom.
  symmetry in HdomEq.
  pose proof (get_some (Logic.eq_ind_r _ HinDom HdomEq)) as [?v Bis].
  exists v. split.
  - apply Bis.
  - eauto.
Qed.

(** * Canonical Forms for Functions

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――――――] #<br>#
    [s(x) = lambda(T')t] #<br>#
    [G ⊢ T <: T']        #<br>#
    [G, x: T ⊢ t: U]          *)
Lemma canonical_forms_fun: forall G s x T U,
  inert G ->
  well_typed G s ->
  G ⊢ trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_lambda T' t) s /\ G ⊢ T <: T' /\
  (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hwt Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  destruct (corresponding_types Hwt BiG) as [v [Bis Ht]].
  destruct (val_typ_all_to_lambda Hin Ht) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    + eapply ty_sub; eauto.
Qed.

(** * Canonical Forms for Objects

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x: {a:T}]       #<br>#
    [――――――――――――――――――] #<br>#
    [exists S, ds, t,] #<br>#
    [s(x) = nu(S)ds] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: T] *)
Lemma canonical_forms_obj: forall G s x a T,
  inert G ->
  well_typed G s ->
  G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  (exists S ds t, binds x (val_new S ds) s /\ defs_has (open_defs x ds) (def_trm a t) /\ G ⊢ t : T).
Proof.
  introv Hi Hwt Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [S [T' [Bi [Hr Hs]]]].
  destruct (corresponding_types Hwt Bi) as [v [Bis Ht]].
  apply ty_var in Bi. apply ty_rec_elim in Bi.
  destruct (val_mu_to_new Hi Ht Bi Hr) as [t [ds [Heq [Hdefs Ht']]]].
  subst. exists S ds t. repeat split~. eapply ty_sub; eauto.
Qed.
