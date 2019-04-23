Require Import ExampleTactics.
Require Import String.

Section ListExample.

Variables A List : typ_label.
Variables Nil Cons head tail : trm_label.

Hypothesis NC: Nil <> Cons.
Hypothesis HT: head <> tail.

Notation ListTypeA list_level A_lower A_upper A_level :=
  (typ_rcd { A >: A_lower <: A_upper } ∧
   typ_rcd { head ⦂ Lazy (super↓A) } ∧
   typ_rcd { tail ⦂ Lazy (list_level↓List ∧ typ_rcd { A >: ⊥ <: A_level↓A }) }).
Notation ListType list_level := (ListTypeA list_level ⊥ ⊤ super).

Notation ListObjType :=
  (typ_rcd { List >: μ (ListType ssuper) <: μ (ListType ssuper) } ∧
   typ_rcd { Nil  ⦂ ∀(typ_rcd { A >: ⊥ <: ⊤ }) (super↓List ∧ (typ_rcd { A >: ⊥ <: ⊥ })) } ∧
   typ_rcd { Cons ⦂ ∀(typ_rcd { A >: ⊥ <: ⊤ })                       (* x: {A} *)
                    ∀(this↓A)                                        (* y: x.A *)
                    ∀(ssuper↓List ∧ typ_rcd { A >: ⊥ <: super↓A })   (* ys: sci.List ∧ {A <: x.A} *)
                     (sssuper↓List ∧ typ_rcd { A >: ⊥ <: ssuper↓A }) }).

Definition t :=
 trm_val (ν (ListObjType)
            defs_nil Λ
            { List ⦂= μ (ListType ssuper) } Λ
            { Nil := defv (λ(typ_rcd { A >: ⊥ <: ⊤ })
                            let_trm (trm_val (ν(ListTypeA sssuper ⊥ ⊥ super)
                                               defs_nil Λ
                                               { A ⦂= ⊥ } Λ
                                               { head := defv (λ(⊤) trm_app super•head this) } Λ
                                               { tail := defv (λ(⊤) trm_app super•tail this) }))) } Λ
            { Cons := defv (λ(typ_rcd { A >: ⊥ <: ⊤ })
                   trm_val (λ(this↓A)
                   trm_val (λ(ssuper↓List ∧ typ_rcd { A >: ⊥ <: super↓A })
                             let_trm (trm_val (ν(ListTypeA sssssuper (sssuper↓A) (sssuper↓A) ssssuper)
                                        defs_nil Λ
                                        { A ⦂= sssuper↓A } Λ
                                        { head := lazy (trm_path sssuper) } Λ
                                        { tail := lazy (trm_path ssuper)}))))) }).

Lemma list_typing :
  empty ⊢ t : μ ListObjType.
Proof.
  fresh_constructor. repeat apply ty_defs_cons; crush.
  - Case "Nil"%string.
    constructor. fresh_constructor. crush.
    (* ⊢ let result = ν(ListType){A}{head}{tail} in result : List ∧ {A <:} *)
    fresh_constructor.
    + (* ⊢ ν(ListType){A}{head}{tail} in result : μ(ListType) *)
      fresh_constructor. repeat apply ty_defs_cons; crush.
      * SCase "head"%string.
        constructor. fresh_constructor. crush.
        assert (p_sel (avar_f y0) nil ↓ A = open_typ_p (p_sel (avar_f y1) nil) (p_sel (avar_f y0) nil ↓ A))
          as Heq by crush.
        rewrite Heq. eapply ty_all_elim.
        ** rewrite proj_rewrite. apply ty_new_elim.
           eapply ty_sub; try solve [constructor*].
           eapply subtyp_trans.
           { apply subtyp_and11. }
           apply subtyp_and12.
        ** eapply ty_sub.
           { constructor*. }
           auto.
      * SCase "tail"%string.
        constructor. fresh_constructor. crush.
        assert ((p_sel (avar_f z) nil ↓ List) ∧ typ_rcd {A >: ⊥ <: p_sel (avar_f y0) nil ↓ A} =
                open_typ_p (p_sel (avar_f y1) nil)
                           ((p_sel (avar_f z) nil ↓ List) ∧ typ_rcd {A >: ⊥ <: p_sel (avar_f y0) nil ↓ A}))
          as Heq by (unfold open_typ_p; auto).
        rewrite Heq. eapply ty_all_elim.
        ** rewrite proj_rewrite. apply ty_new_elim.
           eapply ty_sub; try solve [constructor*].
        ** eapply ty_sub.
           { constructor*. }
           auto.
    + (* y0: ListType ⊢ y0: List ∧ {A<:} *)
     remember_ctx G.
     unfold open_trm. simpl. case_if.
     remember (p_sel (avar_f y0) nil) as py0.
     assert (G ⊢ trm_path py0 : typ_rcd {A >: ⊥ <: ⊥}) as Hpy1. {
       rewrite Heqpy0, HeqG.
       eapply ty_sub. apply ty_rec_elim. constructor*. crush.
       eapply subtyp_trans; apply subtyp_and11.
     }
     assert (G ⊢ trm_path py0 : typ_rcd { head ⦂ Lazy (p_sel (avar_f y0) nil ↓ A) }) as Hpy2. {
       rewrite Heqpy0, HeqG.
       eapply ty_sub. apply ty_rec_elim. constructor*.
       crush. eapply subtyp_trans. apply subtyp_and11. eauto.
     }
     assert (G ⊢ trm_path py0 : typ_rcd {tail ⦂ Lazy ((p_sel (avar_f z) nil ↓ List) ∧
                                                      typ_rcd {A >: ⊥ <: p_sel (avar_f y0) nil ↓ A})}) as Hpy3. {
       rewrite Heqpy0, HeqG.
       eapply ty_sub. apply ty_rec_elim. constructor*.
       crush.
     }
     apply ty_and_intro.
     * apply ty_sub with (T:=μ ListType (p_sel (avar_f z) nil)).
       ** apply ty_rec_intro. crush.
          apply ty_and_intro.
          { apply ty_and_intro.
            - apply (ty_sub Hpy1). eauto.
            - rewrite Heqpy0 in *. auto.
          }
          rewrite Heqpy0 in *. auto.
       ** eapply subtyp_sel2.
          eapply ty_sub.
          {
            rewrite HeqG.
            constructor*.
          }
          eapply subtyp_trans; apply subtyp_and11.
     * eapply ty_sub. apply Hpy1. apply subtyp_typ; auto.
  - Case "Cons"%string.
    constructor. do 3 (fresh_constructor; crush). fresh_constructor.
    (* ⊢ let result = ν(ListType){A}{head}{tail} in result : List ∧ {A <:} *)
    + (* ⊢ ν(ListType){A}{head}{tail} in result : μ(ListType) *)
      fresh_constructor. repeat apply ty_defs_cons; crush.
      * SCase "head"%string.
        constructor. fresh_constructor. crush.
        eapply ty_sub.
        { constructor*. }
        eapply subtyp_sel2. eapply ty_sub.
        constructor*. eapply subtyp_trans. apply subtyp_and11. eauto.
      * SCase "tail"%string.
        constructor. fresh_constructor. crush.
    + (* y2: ListType ⊢ y2: List ∧ {A<:} *)
      remember_ctx G. crush.
      remember (p_sel (avar_f y2) nil) as py0.
      assert (G ⊢ trm_path py0 : typ_rcd {A >: p_sel (avar_f y) nil ↓ A <: p_sel (avar_f y) nil ↓ A}) as Hpy1. {
        rewrite Heqpy0, HeqG.
        eapply ty_sub. apply ty_rec_elim. constructor*.
        crush. eapply subtyp_trans; apply subtyp_and11.
      }
      assert (G ⊢ trm_path py0 : typ_rcd { head ⦂ Lazy (p_sel (avar_f y2) nil ↓ A) }) as Hpy2. {
        rewrite Heqpy0, HeqG.
        eapply ty_sub. apply ty_rec_elim. constructor*.
        crush. eapply subtyp_trans. apply subtyp_and11. eauto.
      }
      assert (G ⊢ trm_path py0 : typ_rcd {tail ⦂ Lazy ((p_sel (avar_f z) nil ↓ List) ∧
                                                       typ_rcd {A >: ⊥ <: p_sel (avar_f y) nil ↓ A})}) as Hpy3. {
        rewrite Heqpy0, HeqG.
        eapply ty_sub. apply ty_rec_elim. constructor*.
        crush.
      }
      apply ty_and_intro.
      * apply ty_sub with (T:=μ ListType (p_sel (avar_f z) nil)).
        ** rewrite Heqpy0 in *. apply ty_rec_intro. crush.
           apply ty_and_intro.
           { apply ty_and_intro; auto. apply (ty_sub Hpy1). eauto. }
           eapply ty_sub. apply Hpy3.
           constructor. fresh_constructor.
           crush. apply subtyp_and2.
           *** apply subtyp_and11.
           *** eapply subtyp_trans. apply subtyp_and12. apply subtyp_typ. auto.
               eapply subtyp_sel2. apply* weaken_ty_trm. rewrite HeqG. repeat apply* ok_push.
        ** rewrite HeqG in *.
           eapply subtyp_sel2. eapply ty_sub. constructor*.
           eapply subtyp_trans. apply subtyp_and11. eapply subtyp_and11.
      * eapply ty_sub. apply Hpy1. apply subtyp_typ; auto.
Qed.

End ListExample.
