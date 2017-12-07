(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import LibLN.
Require Import Binding Definitions GeneralToTight InvertibleTyping Narrowing PreciseTyping
         RecordAndInertTypes Substitution Subenvironments TightTyping Weakening.

(** * Well-typedness *)

(** If [e: G], the variables in the domain of [e] are distinct. *)
Lemma well_typed_to_ok_G: forall s G,
    well_typed G s -> ok G.
Proof.
  intros. induction H; jauto.
Qed.
Hint Resolve well_typed_to_ok_G.

(** [s: G]       #<br>#
    [x ∉ dom(G)] #<br>#
    [――――――――――] #<br>#
    [x ∉ dom(s)] *)
Lemma well_typed_notin_dom: forall G s x,
    well_typed G s ->
    x # s ->
    x # G.
Proof.
  intros. induction H; auto.
Qed.

Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢!v v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl). destruct_all. eauto.
Qed.

Lemma record_has_trm_dec : forall G p T U T' U' a,
    G ⊢ trm_path p: T ->
    G ⊢ T <: U ->
    record_type T ->
    record_type U ->
    record_has T (dec_trm a T') ->
    (record_has U (dec_trm a U') /\ G ⊢ T' <: U').
Proof.
  introv Hp Hs HrT HrU Ha. Admitted.

Lemma record_has_ty_dec : forall G p T U T' A,
    G ⊢ trm_path p: T ->
    G ⊢ T <: U ->
    record_type T ->
    record_type U ->
    record_has T (dec_typ A T' T') ->
    record_has U (dec_typ A T' T').
Proof.
  introv Hp Hs HrT HrU HA. Admitted.

Lemma val_typing_sub: forall G v T U p,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ open_typ_p p T <: open_typ_p p U ->
    G ⊢ trm_path p: open_typ_p p T ->
    record_type T ->
    record_type U ->
    G ⊢ trm_val v: typ_bnd U.
Proof.
  introv Hi Hv Hs Hp HT HU.
  apply (general_to_tight_typing Hi) in Hv.
  apply (tight_to_invertible_v Hi) in Hv.
  inversions Hv. inversions H. pick_fresh x. assert (x \notin L) as Hx by auto.
  specialize (H3 x Hx). assert (HT' := HT). assert (HU' := HU).
  destruct HT as [lsT HT]. destruct HU as [lsU HU].
  induction HT; subst.
  - destruct D. inversions H. apply open_record_type_p with (p:=p) in HT'.
    apply open_record_type_p with (p:=p) in HU'.
    assert (record_has (open_typ_p p (typ_rcd {t >: t1 <: t1})) (open_dec_p p {t >: t1 <: t1})) as Hrh. {
      unfold open_typ_p, open_dec_p. simpl. auto.
    }
   lets Hr: (record_has_ty_dec Hp Hs HT' HU' Hrh).
Admitted.

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
Lemma record_has_ty_defs: forall z bs P G T ds D,
  z; bs; P; G ⊢ ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ z; bs; P; G ⊢ d : D.
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

Lemma stack_typing : forall G s v p ps,
    well_typed G s ->
    s ∋ (p, v) // ps ->
    exists T, G ⊢ trm_val v: T.
Proof.
  introv Hwt Hs.
Admitted.

(** [G ~ s]                             #<br>#
    [s ∋ (p, ν(U)...{a = q}...) // ps]  #<br>#
    [――――――――――――――――――――――――――――――――]  #<br>#
    [exists T, Г ⊢ q: T]                         *)
Lemma stack_path_typing : forall ps G s U ds a q p r,
    well_typed G s ->
    s ∋ (p, val_new U ds) // ps ->
    defs_has (open_defs_p r ds) (def_trm a (trm_path q)) ->
    exists T, G ⊢ trm_path q: T.
Proof.
  introv Hwt Hs Hd.
  destruct (stack_typing Hwt Hs) as [T Ht].
  (* apply [stack_typing] to say that [val_new U ds] is typed in [G], and therefore, [q] can be typed. *)
Admitted.

(** [G ~ s]                 #<br>#
    [G ⊢ p: T]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [exists P v, P ⊢ s ∋ (p, v)] *)
Lemma typed_path_lookup : forall G s p T,
    well_typed G s ->
    G ⊢ trm_path p: T ->
    exists v ps, s ∋ (p, v) // ps.
Proof.
  introv Hwt Hp. Admitted.

Lemma path_lookup :
    (forall s t ps,
        s ∋ t // ps -> forall G p T ds a q r,
        well_typed G s ->
        t = (p, val_new T ds) ->
        defs_has (open_defs_p r ds) (def_trm a (trm_path q)) ->
        exists v ps', s ∋ (q, v) // ps') /\
    (forall s p ds ps,
        s ↓ p == ds // ps -> forall G a q,
        well_typed G s ->
        defs_has ds (def_trm a (trm_path q)) ->
        exists v ps', s ∋ (q, v) // ps').
Proof.
  apply lookup_mutind; intros; eauto.
  - Case "lookup_var".
    lets Hl: (lookup_var ps b). inversions H0.
    destruct (stack_path_typing r H Hl H1) as [U Hq].
    destruct (typed_path_lookup H Hq) as [P' [v Hs]].
    eauto.
  - Case "lookup_val".
    inversions H1.
    lets Hl: (lookup_val l d).
    destruct (stack_path_typing r H0 Hl H2) as [U Hq].
    destruct (typed_path_lookup H0 Hq) as [P' [v Hs]].
    eauto.
  - Case "lookup_path".
    inversions H2. inversions l.
    specialize (H _ _ _ H1 d). destruct H as [v [P' Hs]].
    destruct (named_path_lookup_l H2) as [z [ds Heq]]. inversions Heq.
    apply* H0.
Qed.

(** [G ~ s]                          #<br>#
    [P ⊢ s ∋ (p, ν(T)...{a = q}...]  #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [exists v P', P' ⊢ s ∋ (q, v)]        *)
Lemma path_lookup_l : forall G s p T ds a q ps,
    well_typed G s ->
    s ∋ (p, val_new T ds) // ps ->
    defs_has (open_defs_p p ds) (def_trm a (trm_path q)) ->
    exists v ps', s ∋ (q, v) // ps'.
Proof.
  intros. apply* path_lookup.
Qed.

(** [G ~ s]          #<br>#
    [P ⊢ s ∋ (p, v)] #<br>#
    [G ⊢! p: T]      #<br>#
    [――――――――――――――] #<br>#
    [G ⊢ v: T]       *)
Lemma path_lookup_typing: forall G s p ps v T T',
    inert G ->
    well_typed G s ->
    s ∋ (p, v) // ps ->
    G ⊢! p : T ⪼ T' ->
    G ⊢ trm_val v: T.
Proof.
  introv Hi Hwt Hs Hp. gen T' T v p. induction Hwt; introv Hs Hp.
  - false* lookup_empty.
  - destruct p as [y bs].
    (* showing that y is named *)
    lets Hg: (precise_to_general Hp). apply typed_paths_named in Hg. inversions Hg.
    destruct_all. inversions H2.
    destruct (classicT (x = x0)).
    * subst. rename x1 into bs. gen v0 v. dependent induction Hp; introv Hv Hs.
      + Case "pf_bind".
        apply binds_push_eq_inv in H1. subst.
        assert (p_sel (avar_f x0) nil = pvar x0) as Heq by auto. rewrite Heq in Hs.
        apply lookup_push_eq_inv_var in Hs. subst. apply* weaken_ty_trm.
      + Case "pf_fld".
        unfolds sel_fields. destruct p. inversions x.
        specialize (IHHp f x0 H0 T G Hi Hwt H IHHwt eq_refl JMeq_refl).
        unfolds sel_fields. simpls.
        inversions Hs.
        ++ SCase "lookup_val".
           unfolds sel_fields. destruct p as [x bs]. simpls. inversions H1.
           inversions H4. specialize (IHHp _ _ Hv H1).
           (* from
              [Г, x0: T ⊢ ν(T1)ds0: T0]
              [T0 inert]
              get
              [T0 = μ(T1)] *)
           (* from
              [Г, x0: T ⊢ ν(T1)ds0: μ(T1)]
              get
              [Г, x0: T, y: T1 ⊢ ds0^y: T1^y] *)
           (* from that and
              [Г, x0: T ⊢ x0.f: T1]
              get through substitution of [y] by [x0.f] that
              [Г, x0: T ⊢ ds0^x0.f : T1^x0.f] *)
           (* from that and
              [ds0^x0.f = ...{a = v0}...]
              [T0 = ...{a: U}...]
              get
              [Г, x0: T ⊢ v0: U] *)
           admit.
        ++ SCase "lookup_path".
           unfolds sel_fields. destruct p. inversions H1.
           destruct (pf_inert_rcd_U Hi Hp) as [V Heq]. subst.
           lets Hrh: (precise_flow_record_has Hi Hp). simpls.
           inversions H3. admit.
      + Case "pf_open".
        eauto.
      + Case "pf_and1".
        eauto.
      + Case "pf_and2".
        eauto.
   * apply pf_strengthen in Hp; auto.
     assert (inert G) as Hi' by apply* inert_prefix.
     lets Hn: (lookup_strengthen Hs n). apply* weaken_ty_trm.
Qed.

Lemma corresponding_types: forall G s p T T',
    inert G ->
    well_typed G s ->
    G ⊢! p: T ⪼ T' ->
    (exists v ps, s ∋ (p, v) // ps /\
            G ⊢ trm_val v : T).
Proof.
  introv Hi Hwt Hp.
  apply pf_precise_U in Hp.
  lets Hg: (precise_to_general Hp).
  destruct (typed_path_lookup Hwt Hg) as [P [v Hs]].
  lets Hi': (pf_inert_T Hi Hp).
  lets Ht: (path_lookup_typing Hi Hwt Hs Hp). eauto.
Qed.

(** [G ⊢##v v: forall(S)T]                 #<br>#
    [inert G]                          #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [exists S', T', G ⊢! v: forall(S')T']      #<br>#
    [G ⊢ S <: S']                      #<br>#
    [forall fresh y, G, y: S ⊢ T'^y <: T^y] *)
Lemma invertible_val_to_precise_lambda: forall G v S T,
    G ⊢##v v : typ_all S T ->
    inert G ->
    exists L S' T',
      G ⊢!v v : typ_all S' T' /\
      G ⊢ S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt _ _ eq_refl Hg) as [L' [S' [T' [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S' T'. split. assumption. split. apply subtyp_trans with (T:=S1).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok by apply* ok_push.
    apply subtyp_trans with (T:=open_typ y T1).
    * eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general. auto.
    * apply* H0.
Qed.

(** [forall] to [G(x)]        #<br>#
    [inert G]            #<br>#
    [G ⊢ p: forall(T)U]       #<br>#
    [――――――――――――――--]   #<br>#
    [exists T', U',]          #<br>#
    [G ∋ (p, forall(T')U')]   #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G p T U,
    inert G ->
    G ⊢ trm_path p : typ_all T U ->
    (exists L V T' U',
        G ⊢! p : typ_all T' U' ⪼ V /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V [L [Htp [Hs1 Hs2]]]]]].
  exists L V T' U'. repeat split.
  lets Hv: (pf_inert_lambda_U Hin Htp). subst*. apply* tight_to_general. eauto.
Qed.

(** [forall] to [lambda]                 #<br>#
    [inert G]                       #<br>#
    [G ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                      #<br>#
    [v = lambda(T')t]               #<br>#
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
  destruct (invertible_val_to_precise_lambda Hinv Hin) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H2 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H2; eauto.
Qed.

(** * Canonical Forms for Functions

    [inert G]              #<br>#
    [s: G]                 #<br>#
    [G ⊢ p: forall(T)U]         #<br>#
    [――――――――――――――――――――] #<br>#
    [s ∋ (p, lambda(T')t)] #<br>#
    [G ⊢ T <: T']          #<br>#
    [G, y: T ⊢ t: U]          *)
Lemma canonical_forms_fun: forall G s p T U,
  inert G ->
  well_typed G s ->
  G ⊢ trm_path p : typ_all T U ->
                   (exists L T' t ps, s ∋ (p, val_lambda T' t) // ps /\
                    G ⊢ T <: T' /\
                    (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hwt Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [V [S [T' [Hp [Hs1 Hs2]]]]]].
  destruct (corresponding_types Hin Hwt Hp) as [v [P [Bis Ht]]].
  destruct (val_typ_all_to_lambda Hin Ht) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S' t P. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    eapply ty_sub; eauto.
Qed.

(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⊢ p: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^p = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G p a T,
    inert G ->
    G ⊢ trm_path p : typ_rcd (dec_trm a T) ->
    (exists S T' V,
        G ⊢! p : typ_bnd S ⪼ V /\
        record_has (open_typ_p p S) (dec_trm a T') /\
        G ⊢ T' <: T).
Proof.
  introv Hin Ht.
  lets Hn: (typed_paths_named Ht). destruct Hn as [x [bs Heq]]. subst.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [T' [V [Htp Hs]]].
  destruct (pf_inert_rcd_U Hin Htp) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp).
  apply tight_to_general in Hs. repeat eexists; eauto.
Qed.

(** [mu] to [nu])

    [inert G]                    #<br>#
    [G ⊢ v: mu(T)]               #<br>#
    [G ⊢ p: T^p]                 #<br>#
    [T^p = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds      ] #<br>#
    [ds^p = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U] *)
Lemma val_mu_to_new: forall G v T U a p,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ trm_path p : open_typ_p p T ->
    record_has (open_typ_p p T) (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs_p p ds) (def_trm a t) /\
      G ⊢ t: U.
Proof.
  introv Hi Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi Htt).
  inversions Hinv. inversions H.
  pick_fresh z.
  assert (z \notin L) as Hz by auto.
  specialize (H3 z Hz).
  destruct p as [x bs].
  lets Hv: (typed_paths_named Hx). inversions Hv. destruct_all.
  assert (x0; bs; P; G ⊢
    open_defs_p (p_sel (avar_f x0) bs) ds :: open_typ_p (p_sel (avar_f x0) bs) T)
    as Hds by admit. (*apply* renaming_def.*)
  inversions H.
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]].
  inversions Hd; eauto.
  Case "ty_def_new".
  exists (trm_val (val_new T0 ds0)) ds. repeat split*.
  fresh_constructor. simpls. lets Hrs: (record_has_sel_typ Hx Hr). apply ty_rec_elim in Hrs.
  Admitted. (*
  apply* renaming_def'.
Qed.
  *)

(** * Canonical Forms for Objects

    [inert G]            #<br>#
    [s: G]             #<br>#
    [G ⊢ x: {a:T}]             #<br>#
    [――――――――――――――――――] #<br>#
    [exists S, ds, t,] #<br>#
    [s(x) = nu(S)ds] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: T] *)
Lemma canonical_forms_obj: forall G s p a T,
  inert G ->
  well_typed G s ->
  G ⊢ trm_path p: typ_rcd (dec_trm a T) ->
               (exists ps S ds t,
                   s ∋ (p, val_new S ds) // ps /\
                   defs_has (open_defs_p p ds) (def_trm a t) /\
                   G ⊢ t : T).
Proof.
  introv Hi Hwt Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [S [T' [V [Bi [Hr Hs]]]]].
  destruct (corresponding_types Hi Hwt Bi) as [v [P [Bis Ht]]].
  lets Bieq: (pf_precise_U Bi).
  lets Bi': (precise_to_general Bieq). apply ty_rec_elim in Bi'.
  destruct (val_mu_to_new Hi Ht Bi' Hr) as [t [ds [Heq [Hdefs Ht']]]].
  subst. exists P S ds t. repeat split~. eapply ty_sub; eauto.
Qed.
