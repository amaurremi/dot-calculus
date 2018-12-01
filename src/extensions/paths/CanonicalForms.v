(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import Binding Definitions GeneralToTight InvertibleTyping Lookup Narrowing PreciseTyping
        Replacement ReplacementTyping RecordAndInertTypes Substitution Subenvironments TightTyping
        Weakening.
Require Import Sequences.

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

Definition deftrm t : trm :=
  match t with
  | defp p => trm_path p
  | defv v => trm_val v
  end.

(** * Lemmas to prove that [γ ⟦ p ↦ t ⟧] and [Γ ⊢! p: T] imply [Γ ⊢ t: T] *)

Lemma repl_composition_sub G T U :
  repl_composition_qp G T U ->
  G ⊢ T <: U /\ G ⊢ U <: T.
Proof.
  intros Hr. dependent induction Hr; eauto.
  destruct H as [q [r [n [Hq%precise_to_general Hrt]]]]. destruct_all.
  split.
  - eapply subtyp_trans. apply* subtyp_sngl_qp. auto.
  - eapply subtyp_trans. apply H0. apply repl_swap in Hrt. eauto.
Qed.

Lemma defs_invert_trm x bs P G d a T :
  x; bs; P; G ⊢ d : {a ⦂ T} ->
  exists t, d = {a := t}.
Proof.
  intros Hd. inversion Hd; eauto.
Qed.

Lemma path_field_typing x bs P G a p T :
  x; bs; P; G ⊢ {a :=p p} : {a ⦂ T} ->
  T = typ_sngl p.
Proof.
  inversion 1; subst; eauto.
Qed.

Lemma val_field_typing x bs P G a v T :
  x; bs; P; G ⊢ {a :=v v} : {a ⦂ T} ->
  G ⊢ trm_path (p_sel (avar_f x) bs) • a : T ->
  G ⊢ trm_val v : T.
Proof.
  intros Hd Hp. inversions Hd. eauto.
  fresh_constructor.
  Admitted. (* tricky *)

Lemma typ_bnd_record_has_typing G p T D :
  G ⊢ trm_path p : T ->
  record_has T D ->
  G ⊢ trm_path p : typ_rcd D.
Proof.
  induction 2; eauto.
Qed.

Lemma rename_defs G x P T ds px pbs :
  x; nil; P; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T ->
  G ⊢ trm_path (p_sel (avar_f px) pbs) : open_typ_p (p_sel (avar_f px) pbs) T ->
  px \notin fv_defs ds ->
  px; pbs; P; G ⊢ open_defs_p (p_sel (avar_f px) pbs) ds :: open_typ_p (p_sel (avar_f px) pbs) T.
Proof.
  Admitted.


Lemma object_typing G ds a t p px pbs T V :
  inert G ->
  G ⊢!v val_new T ds : typ_bnd T ->
  defs_has ds {a := t} ->
  G ⊢ trm_path p : typ_bnd T ->
  p = p_sel (avar_f px) pbs ->
  px \notin fv_defs ds ->
  record_has (open_typ_p p T) {a ⦂ V} ->
  (exists v, t = defv v /\ G ⊢ open_trm_p p (trm_val v) : V) \/
  (exists q S, t = defp q /\ V = typ_sngl (open_path_p p q) /\ G ⊢ trm_path (open_path_p p q) : S).
Proof.
  intros Hi Hv Hds Hp Heq Hn Hr.
  inversion Hv. subst G0 T0 ds0.
  pick_fresh x. assert (x \notin L) as Hx by auto.
  specialize (H1 x Hx).
  assert (px; pbs; P; G ⊢ open_defs_p p ds :: open_typ_p p T) as Hds_p by (subst; apply* rename_defs).
  destruct (record_has_ty_defs Hds_p Hr) as [d [Hdh Hdt]].
  apply (defs_has_open p) in Hds. destruct (defs_invert_trm Hdt) as [t' ->].
  unfold open_def_p in Hds. simpl in *.
  pose proof (defs_has_inv Hds Hdh) as <-. destruct t as [q | v]; simpl in *.
  - inversion* Hdt.
  - left. eexists; split; eauto. apply* val_field_typing.
    constructor. apply ty_rec_elim in Hp. eapply typ_bnd_record_has_typing; subst*.
Admitted.

Lemma object_typing' G ds a t p px pbs T U V :
  inert G ->
  G ⊢ trm_val (val_new T ds) : typ_bnd U ->
  defs_has ds {a := t} ->
  G ⊢! p : typ_bnd U ⪼ typ_rcd {a ⦂ V} ->
  p = p_sel (avar_f px) pbs ->
  px \notin fv_defs ds ->
  (exists v, t = defv v /\ G ⊢ open_trm_p p (trm_val v) : V) \/
  (exists q r r' S, t = defp q /\
               V = typ_sngl r /\
               repl_composition_qp G (typ_sngl r') (typ_sngl r) /\
               repl_composition_qp G (typ_sngl r') (typ_sngl (open_path_p p q)) /\
               G ⊢ trm_path (open_path_p p q) : S).
Proof.
  intros Hi Hv Hds Hp Heq Hn. proof_recipe.
  lets Hr: (pf_record_has_U Hi Hp).
  lets Hp': (precise_to_general (pf_TT Hp)). apply ty_sub with (U:=typ_bnd T) in Hp'.
  - lets Hrc1: (repl_composition_open p Hrc). lets Hrc2: (repl_composition_open p Hrc').
    destruct (repl_comp_record_has2 Hrc1 Hr) as [V1 [Hrv1 Hrcv1]].
    destruct (repl_comp_record_has1 Hrc2 Hrv1) as [V2 [Hrv2 Hrcv2]].
    destruct (object_typing Hi Hv Hds Hp' Heq Hn Hrv2) as [[w [-> Hw]] | [q [S [-> [-> Hq]]]]].
    * left. eexists. split. eauto.
      apply ty_sub with (T:=V1).
      { apply ty_sub with (T:=V2); auto. apply* repl_composition_sub. }
      apply repl_composition_sub in Hrcv1 as [? _]. auto.
    * right. destruct (repl_comp_sngl_inv1 Hrcv2) as [q1 ->].
      destruct (repl_comp_sngl_inv2 Hrcv1) as [q2 ->]. repeat eexists; eauto.
  - apply repl_comp_bnd in Hrc'. apply repl_comp_bnd in Hrc.
    apply repl_composition_sub in Hrc'. apply repl_composition_sub in Hrc. destruct_all. eauto.
Qed.

Lemma lookup_step_preservation_prec1: forall G s p t T U,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢! p : T ⪼ U ->
    (exists v, t = defv v /\ G ⊢ trm_val v : T) \/
    (exists q r r', t = defp q /\
               T = typ_sngl r /\
               repl_composition_qp G (typ_sngl r') (typ_sngl r) /\
               repl_composition_qp G (typ_sngl r') (typ_sngl q)).
Proof.
  introv Hi Hwt. gen p t T U.
  (** induction on well-formedness **)
  induction Hwt; introv Hs Hp.
  - Case "G is empty".
    false* lookup_empty.
  - Case "G is not empty".
    destruct p as [y bs].
    (* showing that y is named *)
    assert (exists x0, y = avar_f x0) as [x0 ->] by admit. (* later when we figure out how to make env closed *)
    destruct (classicT (x = x0)) as [-> | Hn].
    * SCase "x = x0".
      (** induction on ⟦⟼⟧ **)
      gen T U T0.
      dependent induction Hs; introv Hi Hv; introv Hp; try simpl_dot; try rewrite proj_rewrite in *.
      + SSCase "lookup_var".
        apply binds_push_eq_inv in H as ->.
        left. exists v.
        lets Hb: (pf_binds Hi Hp). pose proof (binds_push_eq_inv Hb) as ->.
        apply binds_inert in Hb; auto. repeat split*. apply* weaken_ty_trm.
      + SSCase "lookup_sel_p".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ _ JMeq_refl eq_refl Hwt H0 H IHHwt _ Hi Hv _ _ Hp')
          as [[_ [[=] _]] | [? [? [? [[= ->] [-> [? ?]]]]]]].
        apply pf_sngl_U in Hp'. inversion Hp'.
      + SSCase "lookup_sel_v".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ _ JMeq_refl eq_refl Hwt H0 H1 IHHwt _ Hi Hv _ _ Hp')
          as [[v' [[= <-] Hv']] | [? [? [? [[= ->] [-> [? [? ?]]]]]]]].
        pose proof (pf_bnd_T2 Hi Hp') as [T' ->].
        destruct (object_typing' Hi Hv' H Hp' eq_refl)
          as [[w [-> Hvt]] | [q1 [r1 [r1' [S' [-> [-> [Hrc1 [Hrc1' Hst]]]]]]]]]. {
          admit. (* adjust definition of well formedness *)
        }
        ++ left. eexists. split*.
        ++ right. exists (open_path_p (p_sel (avar_f x0) f) q1) r1 r1'. repeat split*.
    * SCase "x <> x0".
      apply pf_strengthen in Hp; auto. apply lookup_strengthen in Hs; auto.
      specialize (IHHwt (inert_prefix Hi) _ _ _ _ Hs Hp)
        as [[w [[= ->] Hw]] | [? [? [? [[= ->] [-> [? ?]]]]]]].
      + left. eexists; split*. apply* weaken_ty_trm.
      + right. exists x1 x2 x3. repeat split*; apply* repl_composition_weaken.
Admitted.

Lemma lookup_step_preservation_prec2: forall G s p t T,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!! p : T ->
    (exists v U, t = defv v /\ G ⊢ trm_val v : U /\ G ⊢! p : U ⪼ T) \/
    (exists q r r', t = defp q /\
               T = typ_sngl r /\
               repl_composition_qp G (typ_sngl r') (typ_sngl r) /\
               repl_composition_qp G (typ_sngl r') (typ_sngl q)).
Proof.
  introv Hi Hwt Hs Hp. gen s t. induction Hp; introv Hwt; introv Hs.
  - destruct (lookup_step_preservation_prec1 Hi Hwt Hs H)
      as [[v' [-> Hv']] | [? [? [? [[= ->] [-> [? ?]]]]]]].
     * left. eauto.
    * pose proof (pf_sngl_U H) as ->. right. repeat eexists; eauto.
  - clear IHHp2. specialize (IHHp1 Hi _ Hwt).
    gen q U. dependent induction Hs; simpl_dot; introv Hp IHHp1 Hv.
    * specialize (IHHp1 _ Hs) as [[? [? [[= ->] ?]]] | [q' [r [r' [[= <-] [<- [Hrc1 Hrc2]]]]]]].
      right. exists (q • a) (q0 • a). eexists.
      repeat split; apply* repl_composition_fld_elim; admit.
    (* for that we need to fix named-var problem *)
    * specialize (IHHp1 _ Hs) as [[w [V [[= <-] [Hw Hp']]]] | [? [? [? [[= <-] ?]]]]].
      proof_recipe. apply (pf_sngl_T Hi) in Hp' as ->. false* repl_to_invertible_val_sngl.
Admitted.

Lemma lookup_step_preservation_prec3: forall G s p T t,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!!! p : T ->
    inert_typ T ->
    G ⊢ deftrm t : T.
Proof.
  introv Hi Hwt Hs Hp. gen t. dependent induction Hp; introv Hs Hin;
    destruct (lookup_step_preservation_prec2 Hi Hwt Hs H)
                                as [[v' [U' [-> [Hv' Hp']]]] | [q' [r [r' [-> [[= ->] [Hrc1 Hrc2]]]]]]]; simpl.
  - inversions Hin.
    * apply pf_forall_T in Hp' as ->; auto.
    * apply pf_bnd_T in Hp' as ->; auto.
  - inversion Hin.
  - apply pf_sngl_T in Hp' as ->; auto. proof_recipe. false* repl_to_invertible_val_sngl.
  - clear IHHp.
    assert (exists V, G ⊢!!! q' : V) as [V Hq'] by admit. (* naming stuff *)
    pose proof (repl_composition_sngl Hi Hrc1 Hp) as [-> | Ht1];
      pose proof (repl_composition_sngl Hi Hrc2 Hq') as [-> | Ht]; clear Hrc1 Hrc2 Hq'; apply* precise_to_general3.
    * apply* pt3_sngl_trans3.
    * apply* pt3_inert_sngl_invert.
    * apply* pt3_sngl_trans3. apply* pt3_inert_sngl_invert.
Qed.

(** * Lemmas to prove that [Γ ~ γ] and [Γ ⊢! p: T] imply [γ ∋ (p, v)] *)

Lemma path_lookup_inside_value_typing G x bs P ds T a t U :
  inert G ->
  x; bs; P; G ⊢ ds :: T ->
  defs_has ds {a := t} ->
  record_has T {a ⦂ U} ->
  exists V, G ⊢ trm_path (p_sel (avar_f x) bs)•a : V /\ inert_typ V.
Proof. Admitted.

Lemma typed_path_lookup1 : forall G s p T U,
    inert G ->
    well_typed G s ->
    G ⊢! p: T ⪼ U ->
    exists v, s ∋ (p, v).
Proof.
  introv Hi Hwt. gen p T U. induction Hwt; introv Hp.
  (*******************************)
  (* induction on well-typedness *)
  (*******************************)
  - Case "G is empty".
    apply precise_to_general in Hp. false* typing_empty_false.
  - Case "G is not empty".
    destruct p as [y bs].
    (* showing that y is named *)
    assert (exists x0, y = avar_f x0) as [x0 ->] by admit. (* later when we figure out how to make env closed *)
    destruct (classicT (x = x0)) as [-> | Hn].
    * SCase "x = x0".
      clear IHHwt. dependent induction Hp; try simpl_dot.
      + eexists. constructor. apply star_one. constructor. eauto.
      + specialize (IHHp _ _ _ _ JMeq_refl eq_refl Hi _ _ Hwt H0 H H1) as [w Hs].

(* continue here *)

Lemma typed_path_lookup1 : forall G s p T U,
    inert G ->
    well_typed G s ->
    G ⊢! p: T ⪼ U ->
    exists v, (inert_typ T /\ s ⟦ p ⟼ defv v ⟧) \/ (is_sngl T /\ s ∋ (p, v)).
Proof.
  introv Hi Hwt. gen p T U. induction Hwt; introv Hp.
  (*******************************)
  (* induction on well-typedness *)
  (*******************************)
  - Case "G is empty".
    apply precise_to_general in Hp. false* typing_empty_false.
  - Case "G is not empty".
    destruct p as [y bs].
    (* showing that y is named *)
    assert (exists x0, y = avar_f x0) as [x0 ->] by admit. (* later when we figure out how to make env closed *)
    destruct (classicT (x = x0)) as [-> | Hn].
    * SCase "x = x0".
      clear IHHwt. dependent induction Hp; try simpl_dot.
      + eexists. left. split. eapply binds_inert. apply H0. apply Hi. constructor*.
      + specialize (IHHp _ _ _ _ JMeq_refl eq_refl Hi _ _ Hwt H0 H H1) as [w [[Hit Hs] | Hs]].
        ++ assert (well_typed (G & x0 ~ T) (s & x0 ~ v)) as Hwt' by constructor*.
           destruct (lookup_step_preservation_prec1 Hi Hwt' Hs Hp)
             as [[v' [[= ->] Hw]] | [? [? [? [[= ->] [-> [? ?]]]]]]].
           pose proof (pf_bnd_T2 Hi Hp) as [V ->]. proof_recipe.
           inversions Hw. pick_fresh z. assert (z \notin L) as Hz by auto.
           specialize (H5 z Hz).
           pose proof (repl_composition_open (p_sel (avar_f x0) f) Hrc) as Hrc1.
           pose proof (repl_composition_open (p_sel (avar_f x0) f) Hrc') as  Hrc1'.
           pose proof (repl_composition_sub Hrc1) as [_ Hs1].
           pose proof (repl_composition_sub Hrc1') as [Hs2 _].
           pose proof (ty_rec_elim (precise_to_general (pf_TT Hp))) as Hp'.
           pose proof (ty_sub Hp' Hs1) as Hp'1.
           pose proof (ty_sub Hp'1 Hs2) as Hp'2.
           assert (x0 \notin fv_defs ds) as Hx0 by admit. (* not sure that this is true *)
           pose proof (rename_defs _ _ H5 Hp'2 Hx0) as Hdefs.
           pose proof (pf_record_has_U Hi Hp) as Hr.
           pose proof (repl_comp_record_has2 Hrc1 Hr) as [V' [Hrh Hrc2]].
           pose proof (repl_comp_record_has1 Hrc1' Hrh) as [V'' [Hrh' Hrc2']].
           pose proof (record_has_ty_defs Hdefs Hrh') as [d [Hdh Hd]].
           pose proof (defs_invert_trm Hd) as [t ->].
           pose proof (path_lookup_inside_value_typing Hi Hdefs Hdh Hrh')
             as [S [Hpa Hins]].




Admitted.

(** [G ~ s]                 #<br>#
    [G ⊢ p: T]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [exists P v, P ⊢ s ∋ (p, v)] *)
Lemma typed_path_lookup : forall G s p T,
    inert G ->
    well_typed G s ->
    G ⊢ trm_path p: T ->
    exists v, s ∋ (p, v).
Proof.
  introv Hi Hwt. gen p T. induction Hwt; introv Hp.
  (*******************************)
  (* induction on well-typedness *)
  (*******************************)
  - false* typing_empty_false.
  - proof_recipe.
    dependent induction Hp; eauto. dependent induction H2; eauto.
    (****************************************)
    (* induction on ## typing of the path p *)
    (****************************************)

    admit. (*
    * destruct (binds_push_inv H0) as [[Heq1 Heq2] | [Hneq Hb]].
      subst. exists v. constructor. apply star_one. constructor*.
      apply inert_prefix in Hi. lets Hok': (inert_ok Hi).
      lets Ht: (ty_var Hb Hok'). unfolds tvar.  specialize (IHHwt Hi _ _ Ht).
      destruct_all. exists x1. constructor. apply* lookup_push_neq. inversion* H4.
    * specialize (IHprecise_flow _ _ _ JMeq_refl H0 Hi Hwt H H1 IHHwt Hok).
      destruct IHprecise_flow as [v' Hl].
      inversions Hl. gen U T0 a.
      assert (exists q, s & x ~ v ⟦ defp p ⟼* defp q ⟧ /\
                       s & x ~ v ⟦ q ⟼ defv v' ⟧) as Hex by admit.
      destruct Hex as [q [Hpq Hqv]].
      assert (well_typed (G & x ~ T) (s & x ~ v)) as Hwt' by constructor*.
      dependent induction Hpq; introv Hpt; clear H5.
      (******************************)
      (* induction on s ⟦ p ⟼* q ⟧ *)
      (*******************************)
      + lets Hpr: (lookup_step_preservation_prec Hi Hwt' Hqv Hpt).
        destruct (pf_inert_rcd_U Hi Hpt) as [S Heq]. subst.
        apply (general_to_tight_typing Hi) in Hpr.
        apply (tight_to_invertible_v Hi) in Hpr. inversions Hpr.
        inversions H2.
        lets Hrh: (precise_flow_record_has Hi Hpt).
        pick_fresh z. assert (z \notin L) as Hz by auto. specialize (H6 z Hz).
        eexists. constructor.
        assert (exists U', record_has (open_typ z S) {a ⦂ U'}) as Hex by admit.
        destruct Hex as [U' Hrh'].
        destruct (record_has_ty_defs H6 Hrh') as [d [Hd Ht]].
        destruct (defs_has_typing Ht) as [t Heq]. subst.
         (* idea:
           we need an induction hypothesis that says that if we have
           definitions [ds] which have a record {a = p}, then p also can be looked
           up in the store.
           for this, we need to formulate this whole lemma using mutual induction
           and to have a case
           z; bs; P; G ⊢ {a = p} : {a : p.type}
           ____________________________________
           exists v, s ∋ (p, v) *)
        admit.
      + destruct (lookup_path_inv Hpq) as [r Heq]. subst.
        assert (s & x ~ v ⟦ defp r ⟼* defv v' ⟧) as Hrv'. {
          eapply star_trans. apply Hpq. apply* star_one.
        }
        specialize (IHHpq _ H0 Hi Hwt H H1 IHHwt Hok Hrv' _ eq_refl eq_refl Hqv Hwt').
        lets Hprl: (lookup_step_preservation_prec Hi Hwt' H2 Hpt).
        destruct (pf_inert_rcd_U Hi Hpt) as [S Heq]. subst.
        assert (exists U', G & x ~ T ⊢ trm_path r : typ_rcd { a ⦂ U' }) as Hex by admit.
        destruct Hex as [U' Hr]. clear Hok. proof_recipe.
        specialize (IHHpq _ _ _ Hpr). destruct IHHpq as [w Hw].



        (* attempt : lets delete stuff *)
        clear Hpq IHHwt Hqv Hwt' Hpt Hrv' Hprl Hr Hpr Hspr Tpr Upr Hok Hwt Hi H1 q U S U' H G
              T v'.
        inversions Hw.
        assert (exists  q, s & x ~ v ⟦ defp r • a ⟼* defp q ⟧ /\
                          s & x ~ v ⟦ q ⟼ defv w ⟧) as Hex by admit.
        destruct Hex as [q [Hraq Hqw]]. clear H3.
        gen w p. dependent induction Hraq; introv Hqw; introv Hpr.
        (*****************************************************)
        (* induction on s ⟦ r.a ⟼* q ⟧, where s ⟦ p ⟼ r ⟧ *)
        (*****************************************************)
        ++ eexists. constructor. inversions Hqw; unfold sel_fields in H.
           destruct r. inversion H.
           destruct p0, r. inversions H. destruct p.
           rename a0 into x1. rename f into bs1. rename a2 into x2. rename f0 into bs2.
           admit.
           (* todo: we need to define the lookup closure through mutual
                    induction as well, otherwise it is not true that if
                    { p = r } and { r = ν{a = v} }
                    then we can say p.a *)
        ++ admit.*)
Admitted.

(** * Lemmas to Prove Canonical Forms for Functions *)

Lemma lookup_preservation_typ_all : forall G s t u T S,
    inert G ->
    well_typed G s ->
    star (lookup_step s) t u ->
    G ⊢ deftrm t : typ_all S T ->
    G ⊢ deftrm u: typ_all S T.
Proof.
  introv Hi Hwt Hl Hp. dependent induction Hl; auto.
  assert (exists q, a = defp q) as [q ->] by (inversions H; eauto).
  proof_recipe.
  apply repl_to_precise_typ_all in Hp as [S' [T' [? [Hpr [? ?]]]]]; auto.
  apply IHHl.
  lets Hb: (lookup_step_preservation_prec3 Hi Hwt H Hpr).
  apply ty_sub with (T:=typ_all S' T'); auto; fresh_constructor; apply* tight_to_general.
Qed.

Lemma corresponding_types_fun: forall G s p S T,
    inert G ->
    well_typed G s ->
    G ⊢!!! p: typ_all S T ->
    (exists v, s ∋ (p, v) /\
            G ⊢ trm_val v : typ_all S T).
Proof.
  introv Hi Hwt Hp.
  lets Hg: (precise_to_general3 Hp).
  destruct (typed_path_lookup Hi Hwt Hg) as [v Hs].
  inversions Hs.
  lets Ht: (lookup_preservation_typ_all Hi Hwt H1 Hg). eauto.
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
Lemma path_typ_all_to_binds: forall G p T U,
    inert G ->
    G ⊢ trm_path p : typ_all T U ->
    (exists L T' U',
        G ⊢!!! p : typ_all T' U' /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hrepl: (replacement_closure Hin Htt).
  destruct (repl_to_precise_typ_all Hin Hrepl) as [T' [U' [L [Hs1 [Hs2 Hs3]]]]].
  exists L T' U'. repeat split; auto.
  apply* tight_to_general.
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
  introv Hin Ht. proof_recipe. inversions  Ht.
  destruct (invertible_val_to_precise_lambda H Hin) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H3 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H3; eauto.
Qed.

(** ** Canonical Forms for Functions

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
                   (exists L T' t, s ∋ (p, val_lambda T' t) /\
                    G ⊢ T <: T' /\
                    (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hwt Hty.
  destruct (path_typ_all_to_binds Hin Hty) as [L [S [T' [Hp [Hs1 Hs2]]]]].
  destruct (corresponding_types_fun Hin Hwt Hp) as [v [P Hv]].
  destruct (val_typ_all_to_lambda Hin Hv) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    eapply ty_sub; eauto.
Qed.
