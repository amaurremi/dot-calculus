Require Import Definitions Binding.
Require Import List.

Section ListExample.

Variables A List : typ_label.
Variables Nil Cons head tail : trm_label.

Hypothesis NC: Nil <> Cons.
Hypothesis HT: head <> tail.


Notation this := (p_sel (avar_b 0) nil).
Notation super := (p_sel (avar_b 1) nil).
Notation ssuper := (p_sel (avar_b 2) nil).
Notation sssuper := (p_sel (avar_b 3) nil).
Notation ssssuper := (p_sel (avar_b 4) nil).

Notation lazy t := (defv (λ(⊤) t)).
Notation Lazy T := (∀(⊤) T).

Notation ListTypeA list_level A_lower A_upper :=
  (typ_rcd { A >: A_lower <: A_upper } ∧
   typ_rcd { head ⦂ Lazy (super↓A) } ∧
   typ_rcd { tail ⦂ Lazy (list_level↓List ∧ typ_rcd { A >: ⊥ <: super↓A }) }).
Notation ListType list_level := (ListTypeA list_level ⊥ ⊤).

Notation "d1 'Λ' d2" := (defs_cons d1 d2) (at level 40).

Notation ListObjType :=
  (typ_rcd { List >: μ (ListType ssuper) <: μ (ListType ssuper) } ∧
   typ_rcd { Nil  ⦂ ∀(typ_rcd { A >: ⊥ <: ⊤ }) (super↓List ∧ (typ_rcd { A >: ⊥ <: this↓A })) } ∧
   typ_rcd { Cons ⦂ ∀(typ_rcd { A >: ⊥ <: ⊤ })                       (* x: {A} *)
                    ∀(this↓A)                                        (* y: x.A *)
                    ∀(ssuper↓List ∧ typ_rcd { A >: ⊥ <: super↓A })   (* ys: sci.List ∧ {A <: x.A} *)
                     (sssuper↓List ∧ typ_rcd { A >: ⊥ <: ssuper↓A }) }).

Definition t :=
 trm_val (ν (ListObjType)
            defs_nil Λ
            { List ⦂= μ (ListType ssuper) } Λ
            { Nil := defv (λ(typ_rcd { A >: ⊥ <: ⊤ })
                            trm_let (* result = *)
                            (trm_val (ν(ListTypeA sssuper (ssuper↓A) (ssuper↓A))
                                       defs_nil Λ
                                       { A ⦂= ssuper↓A } Λ
                                       { head := lazy (trm_app super•head this) } Λ
                                       { tail := lazy (trm_app super•tail this) }))
                            (trm_path this)) } Λ
            { Cons := defv (λ(typ_rcd { A >: ⊥ <: ⊤ })
                   trm_val (λ(this↓A)
                   trm_val (λ(ssuper↓List ∧ typ_rcd { A >: ⊥ <: super↓A })
                             trm_let (* result = *)
                             (trm_val (ν(ListTypeA ssssuper (sssuper↓A) (sssuper↓A))
                                        defs_nil Λ
                                        { A ⦂= sssuper↓A } Λ
                                        { head := lazy (trm_path sssuper) } Λ
                                        { tail := lazy (trm_path ssuper)}))
                             (trm_path this)))) }).


Lemma list_typing :
  empty ⊢ t : μ ListObjType.
Proof.
  fresh_constructor. repeat apply ty_defs_cons; auto; try rewrite concat_empty_l.
  - Case "Nil".
    constructor. fresh_constructor. simpl. repeat case_if.
    unfold open_trm, open_typ. simpl. repeat case_if.
    fresh_constructor.
    + fresh_constructor. repeat apply ty_defs_cons; simpl; auto.
      * SCase "head".
        constructor. fresh_constructor. case_if. unfold open_trm, open_typ. simpl. repeat case_if. simpl. case_if.
        assert (p_sel (avar_f y0) nil ↓ A = open_typ_p (p_sel (avar_f y1) nil) (p_sel (avar_f y0) nil ↓ A))
          as Heq by (unfold open_typ_p; auto).
        rewrite Heq. eapply ty_all_elim.
        ** rewrite proj_rewrite. apply ty_new_elim.
           eapply ty_sub; try solve [constructor*].
           eapply subtyp_trans.
           { apply subtyp_and11. }
           apply subtyp_and12.
        ** eapply ty_sub.
           { constructor*. }
           auto.
      * unfold defs_hasnt. simpl. case_if*.
      * SCase "tail".
        repeat case_if. constructor. fresh_constructor.
        unfold open_trm, open_typ. simpl. repeat case_if.
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
      * unfold defs_hasnt. simpl. repeat case_if; auto.
    + unfold open_trm. simpl. case_if. apply ty_and_intro.
      * eapply ty_sub.
        { constructor*. }
        eapply subtyp_sel2.





End ListExample.
