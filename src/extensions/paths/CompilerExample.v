Require Import ExampleTactics.

Section CompilerExample.

Variables DottyCore Tpe Symbol : typ_label.
Variables dottyCore types typeRef symbols symbol symb tpe denotation srcPos : trm_label.

Notation TpeImpl := (μ(typ_rcd {denotation ⦂ Id})).
Notation SymbolImpl := (μ(typ_rcd {srcPos ⦂ Id})).

Hypothesis TS: types <> symbols.
Hypothesis ST: symb <> denotation.
Hypothesis TS': tpe <> srcPos.

Notation typesType tpe_lower tpe_upper :=
  (typ_rcd {Tpe >: tpe_lower <: tpe_upper} ∧
     typ_rcd {typeRef ⦂ ∀(super•symbols↓Symbol)
                         (super↓Tpe ∧ (typ_rcd {symb ⦂ ssuper•symbols↓Symbol}))}).
Notation symbolsType symb_lower symb_upper :=
  (typ_rcd {Symbol >: symb_lower <: symb_upper} ∧
   typ_rcd {symbol ⦂ ∀(super•types↓Tpe)
                      (super↓Symbol ∧ (typ_rcd {tpe ⦂ ssuper•types↓Tpe}))}).
Notation DottyCorePackage tpe_lower tpe_upper symb_lower symb_upper :=
  (typ_rcd {types ⦂ μ(typesType tpe_lower tpe_upper)} ∧
   typ_rcd {symbols ⦂ μ(symbolsType symb_lower symb_upper)}).

Notation DottyCoreAbstract := (DottyCorePackage ⊥ ⊤ ⊥ ⊤).
Notation DottyCoreTight := (DottyCorePackage TpeImpl TpeImpl SymbolImpl SymbolImpl).

Definition t := (trm_val
(ν(typ_rcd {DottyCore >: μ DottyCoreAbstract <: μ DottyCoreAbstract} ∧
   typ_rcd {dottyCore ⦂ Lazy (super ↓ DottyCore)})
  defs_nil Λ
  {DottyCore ⦂= μ DottyCoreAbstract} Λ
  {dottyCore :=
     lazy (let_trm (trm_val (ν(DottyCoreTight)
                              defs_nil Λ
                              {types :=
                                 defv (ν(typesType TpeImpl TpeImpl)
                                        defs_nil Λ
                                        {Tpe ⦂= TpeImpl} Λ
                                        {typeRef :=
                                           defv (λ(super•symbols↓Symbol)
                                                  (let_trm (trm_val (ν(typ_rcd {symb ⦂ ({{ super }}) } ∧
                                                                       typ_rcd {denotation ⦂ Id})
                                                                      defs_nil Λ
                                                                      {symb := defp super} Λ
                                                                      {denotation := defv id})))) }) } Λ
                              {symbols :=
                                 defv (ν(symbolsType SymbolImpl SymbolImpl)
                                        defs_nil Λ
                                        {Symbol ⦂= SymbolImpl} Λ
                                        {symbol :=
                                           defv (λ(super•types↓Tpe)
                                                  (let_trm (trm_val (ν(typ_rcd {tpe ⦂ {{ super }}} ∧
                                                                       typ_rcd {srcPos ⦂ Id})
                                                                      defs_nil Λ
                                                                      {tpe := defp super} Λ
                                                                      {srcPos := defv id}))))})})))})).

Notation T :=
  (μ(typ_rcd {DottyCore >: μ DottyCoreAbstract <: μ DottyCoreAbstract} ∧
     typ_rcd {dottyCore ⦂ Lazy (super ↓ DottyCore)})).

Lemma compiler_typecheck :
  empty ⊢ t : T.
Proof.
  fresh_constructor. repeat apply ty_defs_cons; crush.
  - Case "dottyCore".
    constructor. fresh_constructor. crush.
    fresh_constructor.
    + fresh_constructor. crush.
      apply ty_defs_cons; crush.
      * SCase "types".
        apply ty_defs_one. eapply ty_def_new; eauto.
        { econstructor. constructor*. simpl. apply notin_singleton. intros [=]. }
        crush. apply ty_defs_cons; crush.

        constructor. fresh_constructor. crush. fresh_constructor.
        *** remember_ctx G.
            fresh_constructor. crush.
            apply ty_defs_cons; crush.
            **** apply ty_defs_one.
                 econstructor.
                 eapply ty_sub.
                 ***** rewrite HeqG. constructor*.
                 ***** eapply subtyp_sel1. rewrite proj_rewrite.
                 constructor. apply ty_rcd_intro.
                 eapply ty_sub. apply ty_rec_elim. constructor.
                 eapply ty_sub. rewrite HeqG. constructor*. eauto.
                 crush.
                 ***** eauto.
            **** constructor. fresh_constructor. crush. constructor*.
        *** match goal with
            | H: _ |- _ & ?y0 ~ ?T0' & ?y1 ~ ?T1' & ?y2 ~ ?T2' ⊢ _ : _ =>
              remember T0' as T0; remember T1' as T1; remember T2' as T2
            end.
            remember_ctx G.
            assert (binds y2 T2 G) as Hb%ty_var by rewrite* HeqG. crush.
            apply ty_and_intro.
            **** rewrite proj_rewrite. eapply ty_sub.
                 2: {
                   eapply subtyp_sel2. eapply ty_sub. apply ty_rec_elim. constructor.
                   assert (binds y0 T0 G) as Hb'%ty_var by rewrite* HeqG.
                   rewrite HeqT0 in Hb'. eapply ty_sub; eauto.
                   unfold open_typ_p. rewrite HeqT1. simpl. eauto.
                 }
                 apply ty_rec_intro. crush.
                 rewrite HeqT2 in Hb. apply ty_rec_elim in Hb.
                 eapply ty_sub. eauto. crush.
            **** assert (binds y0 T0 G) as Hb' by rewrite* HeqG.
                 rewrite HeqT0 in Hb'. apply ty_var in Hb'.
                 match goal with
                 | H: _ ⊢ tvar y0 : ?T0''' ∧ ?T0'' |- _ =>
                   remember T0'' as T0'; remember T0''' as T01
                 end.
                 rewrite HeqT2 in Hb.
                 apply ty_rec_elim in Hb. unfold open_typ_p in Hb.
                 simpl in *. rewrite HeqT1. rewrite proj_rewrite.
                 apply ty_rcd_intro.
                 eapply ty_sub.
                 2: {
                   eapply subtyp_sel2.
                   assert (G ⊢ tvar y0 : T0') as Hy0 by eauto.
                   rewrite HeqT0' in Hy0. apply ty_new_elim in Hy0.
                   apply ty_rec_elim in Hy0. unfold open_typ_p in Hy0. simpl in *.
                   eapply ty_sub. apply Hy0. crush.
                 }
                 eapply ty_sub. eapply ty_sngl. constructor. eapply ty_sub. apply Hb.
                 eauto. rewrite HeqG. constructor*. rewrite HeqT1.
                 eapply subtyp_sel1.
                 assert (G ⊢ tvar y0 : T0') as Hy0 by eauto.
                 rewrite HeqT0' in Hy0. apply ty_new_elim, ty_rec_elim in Hy0.
                 unfold open_typ_p in Hy0. simpl in *. eapply ty_sub.
                 apply Hy0. eauto.
      * eapply ty_def_new; eauto.
        { repeat econstructor. simpl. intros Hin.
          rewrite in_singleton in Hin. inversion Hin. }
        crush. apply ty_defs_cons; crush.
        constructor. fresh_constructor. crush.
        fresh_constructor.
        *** remember_ctx G.
            fresh_constructor. crush.
            apply ty_defs_cons; crush.
            **** apply ty_defs_one.
                 econstructor.
                 eapply ty_sub.
                 ***** rewrite HeqG. constructor*.
                 ***** eapply subtyp_sel1. rewrite proj_rewrite.
                 constructor. apply ty_rcd_intro.
                 eapply ty_sub. apply ty_rec_elim. constructor.
                 eapply ty_sub. rewrite HeqG. constructor*. eauto. crush.
                 ***** eauto.
            **** constructor. fresh_constructor. crush. constructor*.
        *** match goal with
            | H: _ |- _ & ?y0 ~ ?T0' & ?y1 ~ ?T1' & ?y2 ~ ?T2' ⊢ _ : _ =>
              remember T0' as T0; remember T1' as T1; remember T2' as T2
            end.
            remember_ctx G.
            assert (binds y2 T2 G) as Hb%ty_var by rewrite* HeqG. crush.
            apply ty_and_intro.
            **** rewrite proj_rewrite. eapply ty_sub.
                 2: {
                   eapply subtyp_sel2. eapply ty_sub. apply ty_rec_elim. constructor.
                   assert (binds y0 T0 G) as Hb'%ty_var by rewrite* HeqG.
                   rewrite HeqT0 in Hb'. eapply ty_sub; eauto. crush.
                 }
                 apply ty_rec_intro. crush.
                 rewrite HeqT2 in Hb. apply ty_rec_elim in Hb.
                 eapply ty_sub. eauto. crush.
            **** assert (binds y0 T0 G) as Hb' by rewrite* HeqG.
                 rewrite HeqT0 in Hb'. apply ty_var in Hb'.
                 match goal with
                 | H: _ ⊢ tvar y0 : ?T0''' ∧ ?T0'' |- _ =>
                   remember T0'' as T01; remember T0''' as T0'
                 end.
                 rewrite HeqT2 in Hb.
                 apply ty_rec_elim in Hb. unfold open_typ_p in Hb.
                 simpl in *. rewrite HeqT1. rewrite proj_rewrite.
                 apply ty_rcd_intro.
                 eapply ty_sub.
                 2: {
                   eapply subtyp_sel2.
                   assert (G ⊢ tvar y0 : T0') as Hy0 by eauto.
                   rewrite HeqT0' in Hy0. apply ty_new_elim in Hy0.
                   apply ty_rec_elim in Hy0. unfold open_typ_p in Hy0. simpl in *.
                   eapply ty_sub. apply Hy0. case_if. eauto.
                 }
                 eapply ty_sub. eapply ty_sngl. constructor. eapply ty_sub. apply Hb.
                 eauto. rewrite HeqG. constructor*. rewrite HeqT1.
                 eapply subtyp_sel1.
                 assert (G ⊢ tvar y0 : T0') as Hy0 by eauto.
                 rewrite HeqT0' in Hy0. apply ty_new_elim, ty_rec_elim in Hy0.
                 unfold open_typ_p in Hy0. simpl in *. eapply ty_sub.
                 apply Hy0. eauto.
    + unfold open_trm. simpl. case_if.
      match goal with
      | H: _ |- ?G' & _ ~ ?T0' ⊢ _ : _ =>
        remember G' as G; remember T0' as T0
      end.
      assert (binds y0 T0 (G & y0 ~ T0)) as Hb%ty_var by auto.
      rewrite HeqT0 in Hb. apply ty_rec_elim in Hb.
      eapply ty_sub. 2: {
        repeat rewrite <- concat_assoc in HeqG.
        rewrite concat_empty_l in HeqG.
        match goal with
        | H: G = z ~ ?Tz' & _ |- _ =>
          remember Tz' as Tz
        end.
        assert (binds z Tz (G & y0 ~ T0)) as Hz%ty_var. {
          rewrite HeqG. repeat eapply binds_concat_left; auto. apply binds_single_eq.
        }
        eapply subtyp_sel2. unfold tvar in Hz. rewrite HeqTz in Hz.
        eapply ty_sub. apply Hz. eauto.
      }
      apply ty_rec_intro.
      unfold open_typ_p in *. simpl in *. repeat case_if.
      match goal with
      | H: _ ⊢ trm_path (pvar y0) : ?U' ∧ ?U'' |- _ =>
        remember U' as S; remember U'' as U
      end.
      apply ty_and_intro.
      * assert (G & y0 ~ T0 ⊢ tvar y0 : S) as Ht. {
          rewrite HeqS, HeqT0. eapply ty_sub. apply Hb. rewrite HeqS. eauto.
        }
        rewrite HeqS in Ht. unfold tvar in Ht. apply ty_rcd_intro.
        apply ty_new_elim in Ht. apply ty_rec_intro. apply ty_rec_elim in Ht.
        unfold open_typ_p in *. simpl in *. case_if.
        apply ty_and_intro.
        ** eapply ty_sub.
           2: {
             apply subtyp_typ. apply subtyp_bot. apply subtyp_top.
           }
           eapply ty_sub. apply Ht. eauto.
        ** eapply ty_sub. apply Ht. eauto.
      * assert (G & y0 ~ T0 ⊢ tvar y0 : U) as Ht. {
          rewrite HeqU, HeqT0. eapply ty_sub. apply Hb. rewrite HeqU. eauto.
        }
        rewrite HeqU in Ht. unfold tvar in Ht. apply ty_rcd_intro.
        apply ty_new_elim in Ht. apply ty_rec_intro. apply ty_rec_elim in Ht.
        unfold open_typ_p in *. simpl in *. case_if.
        apply ty_and_intro.
        ** eapply ty_sub.
           2: {
             apply subtyp_typ. apply subtyp_bot. apply subtyp_top.
           }
           eapply ty_sub. apply Ht. eauto.
        ** eapply ty_sub. apply Ht. eauto.
Qed.

End CompilerExample.
