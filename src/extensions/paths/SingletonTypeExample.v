Require Import ExampleTactics.

Section SingletonTypeExample.

Variables C D : typ_label.
Variables d incr decr : trm_label.

Hypothesis CD: C <> D.
Hypothesis di: incr <> decr.

Notation t :=
  (trm_let (trm_val
              (ν(typ_rcd {C >: μ(typ_rcd {incr ⦂ {{ this }} })
                          <: μ(typ_rcd {incr ⦂ {{ this }} })} ∧
                 typ_rcd {D >: μ(super↓C ∧ typ_rcd {decr ⦂ {{ this }} })
                          <: μ(super↓C ∧ typ_rcd {decr ⦂ {{ this }} })} ∧
                 typ_rcd {d ⦂ Lazy (super↓D)})
                defs_nil Λ
                {C ⦂= μ(typ_rcd {incr ⦂ {{ this }} }) } Λ
                {D ⦂= μ(super↓C ∧ typ_rcd {decr ⦂ {{ this }} })} Λ
                {d := lazy (let_trm (trm_val
                                       (ν(typ_rcd {incr ⦂ {{ this }} } ∧ typ_rcd {decr ⦂ {{ this }} })
                                         defs_nil Λ {incr :=p this} Λ {decr :=p this})))}))
           (trm_let (trm_app this•d this)
                    (trm_path this•incr•decr))).

Notation T := (μ(typ_rcd {incr ⦂ {{ this }} } ∧ typ_rcd {decr ⦂ {{ this }} })).

Lemma typecheck : empty ⊢ t : T.
Proof.
  fresh_constructor.
  - fresh_constructor. crush. repeat apply ty_defs_cons; crush.
    constructor. fresh_constructor. crush. fresh_constructor.
    + fresh_constructor. crush.
      match goal with
      | H: _ |- _; _; ?G' & ?y ~ ?T' ⊢ _ :: _ =>
        remember T' as T; remember (G' & y ~ T) as G
      end.
      assert (binds y0 T G) as Hb%ty_var by rewrite* HeqG.
      assert (T = open_typ_p (pvar y0) T) as HeqT' by rewrite* HeqT.
      rewrite HeqT' in Hb. apply ty_rec_intro in Hb. unfold pvar in Hb.
      rewrite HeqT', HeqT. crush.
      repeat apply ty_defs_cons; crush.
      * apply ty_defs_one. econstructor. apply Hb. rewrite HeqT. econstructor.
        econstructor; eauto. simpl. intros Hin. rewrite in_singleton in Hin. false*.
      * econstructor. apply Hb. rewrite HeqT. econstructor.
        econstructor; eauto. simpl. intros Hin. rewrite in_singleton in Hin. false*.
    + crush.
      match goal with
        | [H: _ |- _ & z ~ ?Tz' & _ ~ _ & y0 ~ ?Ty0' ⊢ _ : _ ] =>
          remember Tz' as Tz; remember Ty0' as Ty0
      end.
      remember_ctx G.
      assert (binds z Tz G) as Hb by rewrite* HeqG.
      rewrite HeqTz in Hb. apply ty_var in Hb.
      assert (binds y0 Ty0 G) as Hb' by rewrite* HeqG. apply ty_var in Hb'. rewrite HeqTy0 in Hb'.
      apply ty_rec_elim in Hb'. unfold open_typ_p in *. simpl in *. repeat case_if.
      eapply ty_sub.
      2: {
        eapply subtyp_sel2. eapply ty_sub. apply Hb. eapply subtyp_trans.
        apply subtyp_and11. eauto.
      }
      apply ty_rec_intro. crush. apply ty_and_intro.
      * eapply ty_sub.
        2: {
          eapply subtyp_sel2. eapply ty_sub. apply Hb. eapply subtyp_trans.
          apply subtyp_and11. eauto.
        }
       apply ty_rec_intro. crush. eapply ty_sub; eauto.
      * eapply ty_sub; eauto.
  - crush.
    match goal with
    | [ H: _ |- _ & (z ~ μ(?T1' ∧ ?T2') ∧ ?T3') ⊢ _ : _] =>
      remember T1' as T1; remember T2' as T2; remember T3' as T3;
        remember (μ(T1 ∧ T2) ∧ T3) as Tz
    end.
    remember_ctx G.
    assert (binds z Tz G) as Hb by rewrite* HeqG. apply ty_var in Hb. rewrite HeqTz in Hb.
    apply ty_rec_elim in Hb. unfold open_typ_p in *. simpl in *. repeat case_if.
    rewrite proj_rewrite.
    assert (G ⊢ tvar z : open_typ_p (pvar z) T2) as Hz. {
      eapply ty_sub. apply Hb. eauto.
    }
    fresh_constructor; eauto.
    + econstructor.
      * apply ty_new_elim. eapply ty_sub. apply Hb. rewrite HeqT3. crush.
      * eapply ty_sub; eauto.
    + crush.
      assert (G & y ~ ((pvar z)↓D) ⊢ tvar y : μ((pvar z↓C) ∧ typ_rcd {decr ⦂ {{this}}})) as Hy. {
        eapply ty_sub. eauto. eapply subtyp_sel1. rewrite HeqT2 in Hb. eapply ty_sub.
        apply weaken_ty_trm; eauto. rewrite* HeqG. rewrite HeqT2. crush.
      }
      rewrite proj_rewrite. apply ty_rec_elim in Hy. unfold open_typ_p in *. simpl in *. case_if.
      pose proof (ty_sub Hy (subtyp_and11 _ _ _)) as Hy'.
      unfold pvar in *.
      eapply ty_sub in Hy'.
      2: {
        eapply subtyp_sel1. rewrite HeqT1 in Hb. simpl in *. case_if. apply weaken_ty_trm.
        eapply ty_sub. apply Hb. eauto. rewrite* HeqG.
      }
      apply ty_rec_elim in Hy'. unfold open_typ_p in *. simpl in *. case_if.
      eapply ty_sngl.
      * repeat rewrite proj_rewrite. apply ty_new_elim.
        eapply ty_sngl; eauto.
      * apply ty_rec_intro. crush. apply ty_and_intro; eauto.
Qed.

End SingletonTypeExample.
