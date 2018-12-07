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

Lemma object_typing G x bs P ds T a t V :
  inert G ->
  x; bs; P; G ⊢ ds :: T ->
  defs_has ds {a := t} ->
  record_has T {a ⦂ V} ->
  (exists U u, t = defv (val_lambda U u) /\ G ⊢ deftrm t : V) \/
  (exists U ds', t = defv (val_new U ds') /\
            x; (a :: bs); P; G ⊢ open_defs_p (p_sel (avar_f x) (a :: bs)) ds' ::
                                 open_typ_p (p_sel (avar_f x) (a :: bs)) U /\
            V = typ_bnd U) \/
  (exists q S, t = defp q /\ V = typ_sngl q /\ G ⊢ trm_path q : S).
Proof.
  intros Hi Hds Hdh Hr.
  destruct (record_has_ty_defs Hds Hr) as [? [Hdh' Hdt]].
  destruct (defs_invert_trm Hdt) as [t' ->].
  pose proof (defs_has_inv Hdh Hdh') as <-. destruct t as [q | v]; simpl in *.
  - inversion* Hdt.
  - destruct v.
    * right. left. inversions Hdt.
      simpl in *. repeat eexists; auto.
    * left. inversions Hdt. eauto.
Qed.

Lemma lookup_step_preservation_prec1: forall G s p t T U,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢! p : T ⪼ U ->
    (exists S u, t = defv (val_lambda S u) /\ G ⊢ deftrm t : T) \/
    (exists S ds px pbs W T' P, t = defv (val_new S ds) /\
                           p = p_sel (avar_f px) pbs /\
                           T = typ_bnd T' /\
                           px ; pbs ; P ; G ⊢ open_defs_p p ds :: open_typ_p p S /\
                           repl_composition_qp G W S /\
                           repl_composition_qp G W T') \/
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
        lets Hb: (pf_binds Hi Hp). pose proof (binds_push_eq_inv Hb) as ->.
        apply binds_inert in Hb; auto.
        destruct v as [S ds | S u].
        ++ right. left.
           lets Hi': (inert_prefix Hi).
           inversions Hb; proof_recipe. { inversion Hvpr. }
           inversions Hv. pick_fresh z. assert (z \notin L) as Hz by auto.
           apply H4 in Hz. do 6 eexists. exists P. repeat split*. apply open_env_last_defs; auto.
           apply narrow_defs with (G:=G & x0 ~ open_typ x0 S).
           assert (open_defs_p (p_sel (avar_f x0) nil) ds = open_defs x0 ds) as -> by rewrite* open_var_defs_eq.
           assert (open_typ_p (p_sel (avar_f x0) nil) S = open_typ x0 S) as -> by rewrite* open_var_typ_eq.
           apply* rename_defs. apply subenv_last; auto. apply (repl_composition_open (pvar x0)) in Hrc.
           eapply (repl_composition_open (pvar x0)) in Hrc'.
           apply subtyp_trans with (T:=open_typ x0 U');
             apply repl_composition_sub in Hrc'; apply repl_composition_sub in Hrc; destruct_all;
               repeat rewrite open_var_typ_eq in *; unfold pvar in *; auto. all: apply* repl_composition_weaken.
        ++ left. repeat eexists. apply* weaken_ty_trm.
      + SSCase "lookup_sel_p".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ _ JMeq_refl eq_refl Hwt H0 H IHHwt _ Hi Hv _ _ Hp')
          as [[? [? [[=]]]] |
              [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
               [? [? [? [[= ->] [-> [? ?]]]]]]]].
        apply pf_sngl_U in Hp'. inversion Hp'.
      + SSCase "lookup_sel_v".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ _ JMeq_refl eq_refl Hwt H0 H1 IHHwt _ Hi Hv _ _ Hp')
          as [[? [? [[=]]]] |
              [[S [ds' [x [pbs [W [T'' [P [[= -> ->] [[= -> ->] [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
               [? [? [? [[= ->] [-> [? ?]]]]]]]]. clear IHHwt.
        lets H': (defs_has_open (p_sel (avar_f x) pbs) H). simpl in *.
        assert (exists V W, record_has (open_typ_p (p_sel (avar_f x) pbs) S) {a ⦂ V} /\
                       repl_composition_qp (G & x ~ T0) W V /\
                       repl_composition_qp (G & x ~ T0) W T1)
          as [V [W' [Hrh [Hrc1' Hrc2']]]]. {
          lets Hr: (pf_record_has_U Hi Hp').
          apply (repl_composition_open (p_sel (avar_f x) pbs) ) in Hrc1.
          apply (repl_composition_open (p_sel (avar_f x) pbs) ) in Hrc2.
          destruct (repl_comp_record_has2 Hrc2 Hr) as [? [Hrh1 ?]].
          destruct* (repl_comp_record_has1 Hrc1 Hrh1).
        }
        assert (G & x ~ T0 ⊢ V <: T1 /\ G & x ~ T0 ⊢ T1 <: V) as [HVT HTV]. {
          apply repl_composition_sub in Hrc2'. apply repl_composition_sub in Hrc1'.
          destruct_all.
          split; apply subtyp_trans with (T:=W'); eauto.
        }
        destruct (object_typing Hi Hds H' Hrh) as [[U' [u [Heq Ht']]] |
                                                   [[U' [ds'' [Heq [Hds'' ->]]]] | [q [V' [Heq1 [-> Hq]]]]]].
        ++ destruct t; inversions Heq. destruct v0; inversions H3.
           left. repeat eexists. eauto.
        ++ destruct t as [|]; inversions Heq. destruct v0 as [X ds |]; inversions H3. fold open_rec_defs_p in Hds''.
           right. left.
           pose proof (repl_comp_bnd_inv1 Hrc1') as [Y ->]. pose proof (repl_comp_bnd_inv2 Hrc2') as [Z ->].
           repeat eexists; eauto.
           +++ apply repl_comp_bnd' in Hrc1'. apply Hrc1'.
           +++ apply repl_comp_bnd' in Hrc2'. auto.
        ++ destruct t; inversions Heq1. right. right.
           pose proof (repl_comp_sngl_inv1 Hrc1') as [r ->]. pose proof (repl_comp_sngl_inv2 Hrc2') as [r' ->].
           repeat eexists; eauto.
    * SCase "x <> x0".
      apply pf_strengthen in Hp; auto. apply lookup_strengthen in Hs; auto.
      specialize (IHHwt (inert_prefix Hi) _ _ _ _ Hs Hp)
        as [[? [? [[= ->]]]] |
              [[? [? [? [? [? [? [? [[= ->] [[= -> ->] [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
               [? [? [? [[= ->] [-> [? ?]]]]]]]].
      + left. repeat eexists. apply* weaken_ty_trm.
      + right. left. repeat eexists. apply* weaken_ty_defs. all: apply* repl_composition_weaken.
      + right. right. repeat eexists; apply* repl_composition_weaken.
Qed.

Lemma lookup_step_preservation_prec2: forall G s p t T,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!! p : T ->
    (exists S U u, t = defv (val_lambda S u) /\ G ⊢ deftrm t : U /\ G ⊢! p : U ⪼ T) \/
    (exists S ds px pbs W U P, t = defv (val_new S ds) /\
                           p = p_sel (avar_f px) pbs /\
                           G ⊢! p : typ_bnd U ⪼ T /\
                           px ; pbs ; P ; G ⊢ open_defs_p p ds :: open_typ_p p S /\
                           repl_composition_qp G W S /\
                           repl_composition_qp G W U) \/
    (exists q r r', t = defp q /\
               T = typ_sngl r /\
               repl_composition_qp G (typ_sngl r') (typ_sngl r) /\
               repl_composition_qp G (typ_sngl r') (typ_sngl q)).
Proof.
  introv Hi Hwt Hs Hp. gen s t. induction Hp; introv Hwt; introv Hs.
  - destruct (lookup_step_preservation_prec1 Hi Hwt Hs H)
      as [[? [? [[= ->]]]] |
          [[S [ds' [z [pbs [W [T'' [P [[= ->] [[= ->] [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
           [? [? [? [[= ->] [-> [? ?]]]]]]]].
    * left. repeat eexists; eauto.
    * right. left. repeat eexists; eauto.
    * pose proof (pf_sngl_U H) as ->. right. right. repeat eexists; eauto.
  - clear IHHp2. specialize (IHHp1 Hi _ Hwt).
    gen q U. dependent induction Hs; simpl_dot; introv Hp IHHp1 Hv.
    * specialize (IHHp1 _ Hs) as [[? [? [? [[=] ?]]]] |
                                  [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
                                   [q' [r [r' [[= <-] [<- [Hrc1 Hrc2]]]]]]]].
      right. right. exists (q • a) (q0 • a) (r' • a).
      repeat split; apply* repl_composition_fld_elim; admit.
    (* for that we need to fix named-var problem *)
    * specialize (IHHp1 _ Hs) as [[? [? [? [[= ->] ?]]]] |
                                  [[? [? [? [? [? [? [? [[= -> ->] [[= -> ->] [[=]%pf_sngl_T ?]]]]]]]]]] |
                                   [? [? [? [[=] ?]]]]]]; auto.
Admitted.

Lemma lookup_step_preservation_prec3: forall G s p T t,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!!! p : T ->
    inert_typ T ->
    (exists S U, T = typ_all S U /\ G ⊢ deftrm t : typ_all S U) \/
    (exists U, T = typ_bnd U /\
          ((exists S ds px pbs W P, t = defv (val_new S ds) /\
                               p = p_sel (avar_f px) pbs /\
                               px; pbs; P; G ⊢ open_defs_p p ds :: open_typ_p p S /\
                               repl_composition_qp G W S /\
                               repl_composition_qp G W U) \/
           (exists q, t = defp q /\ G ⊢!!! q : T))).
Proof.
  introv Hi Hwt Hs Hp. gen t. dependent induction Hp; introv Hs Hit;
    destruct (lookup_step_preservation_prec2 Hi Hwt Hs H)
                                as [[S' [U [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [px [pbs [W [U [P [[= ->] [-> [Hp' [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
                                     [q' [r [r' [[= ->] [<- [Hrc1 Hrc2]]]]]]]]; simpl.
  - left. simpl in *. inversions Hit.
    * apply (pf_forall_T Hi) in Hp' as ->. repeat eexists; eauto.
    * apply (pf_bnd_T Hi) in Hp' as ->. proof_recipe. inversion Hv.
  - right. inversions Hit.
    * apply (pf_forall_T Hi) in Hp' as [=].
    * apply (pf_bnd_T Hi) in Hp' as [= ->]. eexists. split*. left. repeat eexists; eauto.
  - apply repl_comp_sngl_inv2 in Hrc1 as [q [= ->]]. inversion Hit.
  - apply pf_sngl_T in Hp' as ->; auto. proof_recipe. false* repl_to_invertible_val_sngl.
  - apply (pf_sngl_T Hi) in Hp' as [=].
  - clear IHHp.
    assert (exists V, G ⊢!!! q' : V) as [V Hq'] by admit. (* naming stuff *)
    pose proof (repl_composition_sngl Hi Hrc1 Hp) as [-> | Ht1];
      pose proof (repl_composition_sngl Hi Hrc2 Hq') as [-> | Ht]; clear Hrc1 Hrc2 Hq'; inversions Hit;
        try solve [left; repeat eexists; apply* precise_to_general3;
                   try solve [apply* pt3_sngl_trans3]; apply* pt3_inert_sngl_invert].
    * right. eexists. split*.
    * right. eexists. split*. right. eexists. split*. apply* pt3_sngl_trans3.
    * right. eexists. split*. right. eexists. split*. apply* pt3_inert_sngl_invert.
    * left. repeat eexists.
      pose proof (pt3_inert_sngl_invert Hi Hp Ht1 (inert_typ_all _ _)) as Hr'. apply* precise_to_general3.
      apply* pt3_sngl_trans3.
    * right. eexists. split*. right. eexists. split*.
      apply* pt3_sngl_trans3. apply* pt3_inert_sngl_invert.
Qed.

Lemma lookup_step_preservation_prec3_fun G s p T S t :
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!!! p : typ_all T S ->
    G ⊢ deftrm t : typ_all T S.
Proof.
  intros Hi Hwt Hs Hp.
  destruct (lookup_step_preservation_prec3 Hi Hwt Hs Hp) as
      [[? [? [-> Ht]]] | [? [[=] ?]]]; auto.
Qed.

Lemma lookup_step_preservation_prec3_bnd G s p T q :
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ defp q ⟧ ->
    G ⊢!!! p : typ_bnd T ->
    G ⊢!!! q : typ_bnd T.
Proof.
  introv Hi Hwt Hs Hp.
  assert (inert_typ (typ_bnd T)) as Hit. {
    apply (pf3_inertsngl Hi) in Hp. inversions Hp; inversions H; auto; inversion H0; inversion H.
  }
  destruct (lookup_step_preservation_prec3 Hi Hwt Hs Hp) as
      [[? [? [[=] ?]]] | [U [[= ->] [[? [? [? [? [? [? [[=] ?]]]]]]] | [? [[= ->] ?]]]]]]; auto.
Qed.

(* TODO !!!
   it might be that we will have to select specific px and pbs and not just arbitrary ones *)
Lemma lookup_preservation G s p t T :
  inert G ->
  well_typed G s ->
  s ⟦ defp p ⟼* t ⟧ ->
  G ⊢!!! p : T ->
  inert_typ T ->
  t = defp p \/
  (exists S U, T = typ_all S U /\ G ⊢ deftrm t : typ_all S U) \/
  (exists U, T = typ_bnd U /\
        ((exists S ds px pbs W P, t = defv (val_new S ds) /\
                             px; pbs; P; G ⊢ open_defs_p (p_sel (avar_f px) pbs) ds ::
                                             open_typ_p (p_sel (avar_f px) pbs) S /\
                             repl_composition_qp G W S /\
                             repl_composition_qp G W U) \/
         (exists q, t = defp q /\ G ⊢!!! q : T))).
Proof.
  intros Hi Hwt Hs. gen T. dependent induction Hs; introv Hp Hit.
  - left*.
  - right.
    pose proof (lookup_step_preservation_prec3 Hi Hwt H Hp Hit)
      as [[S [U [[= ->] Ht]]] |
          [U [[= ->] [[S [ds [px [pbs [W [P [[= ->] [Heq [Hds [Hrc1 Hrc2]]]]]]]]]] |
                     [q [[= ->] Hq]]]]]].
    + left. destruct b as [q | v].
      * simpl in *. proof_recipe.
        specialize (IHHs _ Hi Hwt eq_refl _ Hpr (inert_typ_all _ _))
          as [-> |
              [[S' [U' [[= ->] Ht']]] |
               [? [[= ->] [[? [? [? [? [? [? [[= ->] ?]]]]]]] |
                     [? [[= ->] ?]]]]]]]; repeat eexists; simpl.
        ** eapply ty_sub. apply* precise_to_general3.
           eapply subtyp_all. apply* tight_to_general. eauto.
        ** eapply ty_sub. apply Ht'. eapply subtyp_all. apply* tight_to_general.
           subst. apply Hspr2.
      * apply lookup_val_inv in Hs as ->. simpl in *. repeat eexists. auto.
    + right. eexists. split*.
      apply lookup_val_inv in Hs as ->. left. repeat eexists; subst; eauto.
    + right. eexists. split*.
      specialize (IHHs _ Hi Hwt eq_refl _ Hq Hit)
        as [-> |
            [[S' [U' [[= ->] Ht']]] |
             [U' [[= ->] [[S [ds [qx [qbs [W [P [-> [Hds [Hrc1 Hrc2]]]]]]]]] |
                        [? [[= ->] ?]]]]]]]; eauto.
      left. repeat eexists; eauto.
Qed.



(** * Lemmas to prove that [Γ ~ γ] and [Γ ⊢! p: T] imply [γ ∋ (p, v)] *)

Lemma typ_to_lookup1 G s p T U :
  inert G ->
  well_typed G s ->
  G ⊢! p : T ⪼ U ->
  exists t, s ⟦ p ⟼ t ⟧.
Proof.
  intros Hi Hwt Hp. gen p T U. induction Hwt; introv Hp.
  (** induction on ⟦~⟧ **)
  - false. dependent induction Hp; eauto. apply* binds_empty_inv.
  - assert (exists y bs, p = p_sel (avar_f y) bs) as [y [bs ->]] by admit.
    (* later when we figure out how to make env closed *)
    destruct (classicT (x = y)) as [-> | Hn].
    * SCase "x = y".
      (** induction on ⟦⊢!⟧ **)
      dependent induction Hp; try simpl_dot.
      + eexists. apply* lookup_var.
      + specialize (IHHp _ _ H0 _ _ Hi Hwt H H1 IHHwt JMeq_refl eq_refl) as [t Hs].
        pose proof (pf_bnd_T2 Hi Hp) as [V ->].
        destruct (lookup_step_preservation_prec1 Hi (well_typed_push Hwt H H0 H1) Hs Hp)
          as [[S [u [-> Ht]]] |
              [[S [ds' [z [pbs [W [T'' [P [-> [[= -> ->] [[= ->] [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
               [? [? [? [? [[=] [? ?]]]]]]]].
        ++ proof_recipe. inversion Ht.
        ++ assert (exists u, defs_has ds' {a := u}) as [u Hu] by admit. (* annoying easy stuff *)
           eexists. rewrite proj_rewrite. eauto.
      + eauto.
      + eauto.
      + eauto.
    * SCase "x <> y".
      apply pf_strengthen in Hp; auto. specialize (IHHwt (inert_prefix Hi) _ _ _ Hp) as [t Hs].
      eexists. apply* lookup_step_push_neq.
Qed.

Lemma typ_to_lookup2 G s p T :
  inert G ->
  well_typed G s ->
  G ⊢!! p : T ->
  exists t, s ⟦ p ⟼ t ⟧.
Proof.
  intros Hi Hwt Hp. induction Hp.
  - apply* typ_to_lookup1.
  - specialize (IHHp1 Hi Hwt) as [u1 Hs1]. specialize (IHHp2 Hi Hwt) as [u2 Hs2].
    destruct (lookup_step_preservation_prec2 Hi Hwt Hs1 Hp1)
                                as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [px [pbs [W [U' [P [[= ->] [-> [Hp' [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
                                     [q' [r [r' [[= ->] [<- [Hrc1 Hrc2]]]]]]]]; simpl.
    + pose proof (pf_sngl_T Hi Hp') as ->. proof_recipe. inversions Hv. inversions H. inversions H0.
    + pose proof (pf_sngl_T Hi Hp') as [=].
    + eauto.
Qed.

Lemma sngl_path_lookup1 G s p q U :
  inert G ->
  well_typed G s ->
  G ⊢! p : typ_sngl q ⪼ U ->
  exists r r', s ⟦ p ⟼ defp r ⟧
          /\ repl_composition_qp G (typ_sngl r') (typ_sngl r)
          /\ repl_composition_qp G (typ_sngl r') (typ_sngl q).
Proof.
  intros Hi Hwt Hp. destruct (typ_to_lookup1 Hi Hwt Hp) as [t Hs].
  destruct (lookup_step_preservation_prec1 Hi Hwt Hs Hp)
          as [[? [? [-> ?]]] |
              [[? [? [? [? [? [? [? [-> [[= ->] [[= ->] ?]]]]]]]]]] |
               [? [? [? [-> [[= ->] [? ?]]]]]]]]; eauto.
  proof_recipe. inversions H. inversions H0. inversion H.
Qed.

Lemma object_lookup1 G s p T U :
  inert G ->
  well_typed G s ->
  G ⊢! p : typ_bnd T ⪼ U ->
  exists S ds W px pbs P, s ⟦ p ⟼ defv (val_new S ds) ⟧ /\
                   p = p_sel (avar_f px) pbs /\
                   px; pbs; P; G ⊢ open_defs_p p ds :: open_typ_p p S /\
                   repl_composition_qp G W S /\
                   repl_composition_qp G W T.
Proof.
  intros Hi Hwt Hp. destruct (typ_to_lookup1 Hi Hwt Hp) as [t Hs].
  destruct (lookup_step_preservation_prec1 Hi Hwt Hs Hp)
          as [[? [? [-> ?]]] |
              [[? [? [? [? [? [? [? [-> [[= ->] [[= ->] [? [? ?]]]]]]]]]]]] |
               [? [? [? [-> [[=] ?]]]]]]]; eauto.
  - proof_recipe. inversion H.
  - repeat eexists; eauto.
Qed.

Lemma lookup_step_fld_star s p q a :
  s ⟦ defp p ⟼* defp q ⟧ ->
  s ⟦ defp p • a ⟼* defp q • a ⟧.
Proof.
  intros Hs. dependent induction Hs.
  - apply star_refl.
  - pose proof (lookup_path_inv Hs) as [r ->]. specialize (IHHs _ _ eq_refl eq_refl).
    eapply star_trans. apply star_one. apply* lookup_sel_p. auto.
Qed.

Lemma sngl_path_lookup2 G s p q :
  inert G ->
  well_typed G s ->
  G ⊢!! p : typ_sngl q ->
   exists r r', s ⟦ defp p ⟼* defp r ⟧
          /\ repl_composition_qp G (typ_sngl r') (typ_sngl r)
          /\ repl_composition_qp G (typ_sngl r') (typ_sngl q).
Proof.
  intros Hi Hwt Hpq. dependent induction Hpq.
  - pose proof (pf_sngl_T Hi H) as ->.
    destruct (sngl_path_lookup1 Hi Hwt H) as [r [r' [Hs [Hrc1 Hrc2]]]].
    repeat eexists. apply* star_one. eauto. eauto.
  - specialize (IHHpq1 _ Hi Hwt eq_refl) as [r [r' [Hs [Hrc1 Hrc2]]]].
    repeat eexists. apply* lookup_step_fld_star.
    all: apply* repl_composition_fld_elim; admit. (* named typing stuff *)
Admitted.

Lemma blah G s p T V :
  well_typed G s ->
  inert G ->
  G ⊢! p : T ⪼ V ->
  exists U, G ⊢!!! p : U /\ inert_typ U.
Proof.
  intros Hwt Hi Hp. gen p T V. induction Hwt; introv Hp.
  - admit.
  - assert (exists px pbs, p = p_sel (avar_f px) pbs) as [px [pbs Heq]] by admit.
    assert (x = px) as -> by admit.
    dependent induction Hp; eauto.
    * inversions Heq. assert (T = T0) as <- by admit.
      admit.
    * simpl_dot. clear IHHp.
      pose proof (pf_bnd_T2 Hi Hp) as [S ->]. specialize (IHHwt (inert_prefix Hi)).


Lemma lookup_path_order G s p px pbs qx qbs :
  well_typed G s ->
  p = p_sel (avar_f px) pbs ->
  q = p_sel (avar_f qx) qbs ->
  G ⊢!!! p: T ->


Lemma defs_paths_precise G px pbs ds T P a q qx qbs :
  inert G ->
  px; pbs; P; G ⊢ ds :: T ->
  q = p_sel (avar_f qx) qbs ->
  defs_has ds {a := defp q} ->
  record_has T {a ⦂ typ_sngl q} ->
  exists U, G ⊢!! q : U.
Proof. Admitted.

Lemma


Lemma typed_path_lookup1 G s p T U :
    inert G ->
    well_typed G s ->
    G ⊢! p: T ⪼ U ->
    exists v, s ∋ (p, v).
Proof.
  introv Hi Hwt. gen p T U. induction Hwt; introv Hp.
  - Case "G is empty".
    apply precise_to_general in Hp. false* typing_empty_false.
  - Case "G is not empty".
    destruct p as [y bs].
    (* showing that y is named *)
    assert (exists x0, y = avar_f x0) as [x0 ->] by admit. (* later when we figure out how to make env closed *)
    destruct (classicT (x = x0)) as [-> | Hn].
    * SCase "x = x0".
      dependent induction Hp; try simpl_dot.
      + SSCase "pf_bind".
      eexists. constructor. apply star_one. constructor. eauto.
      + SSCase "pf_fld".
        specialize (IHHp _ _ _ _ JMeq_refl eq_refl Hi _ _ Hwt H0 H H1 IHHwt) as [w Hs].
        lets Hwt': (well_typed_push Hwt H H0 H1). pose proof (pf_bnd_T2 Hi Hp) as [V ->].
        pose proof (object_lookup1 Hi Hwt' Hp) as [X [ds [Y [px [pbs [P [Hl [[= -> ->] [Hds [Hrc1 Hrc2]]]]]]]]]].
        pose proof (pf_record_has_U Hi Hp) as Hr.
        assert (exists Z, record_has X {a ⦂ Z}) as [Z Hr'] by admit.

      + SSCase "pf_open".
        eauto.
      + SSCase "pf_and1".
        eauto.
      + SSCase "pf_and2".
        eauto.
    * apply pf_strengthen in Hp; auto. specialize (IHHwt (inert_prefix Hi) _ _ _ Hp) as [t Hs].
      eexists. constructor. apply* lookup_push_neq. inversion* Hs.
Admitted.

Lemma typed_path_lookup2 G s p T :
    inert G ->
    well_typed G s ->
    G ⊢!! p: T ->
    exists v, s ∋ (p, v).
Proof.
  introv Hi Hwt Hp. induction Hp.
  - apply* typed_path_lookup1.
  - specialize (IHHp1 Hi Hwt) as [v1 Hs1]. specialize (IHHp2 Hi Hwt) as [v2 Hs2].
    eexists. constructor. apply star_trans with (b:=defp q • a).
    * pose proof (sngl_path_lookup2 Hi Hwt Hp1) as [r [r' [Hs [Hrc1 Hrc2]]]].
      (* todo tricky but maybe similar to typed_path_lookup1 cycle case *) admit.
    * inversion* Hs2.
Admitted.

Lemma typed_path_lookup3 G s p T :
    inert G ->
    well_typed G s ->
    G ⊢!!! p: T ->
    exists v, s ∋ (p, v).
Proof.
  induction 3; apply* typed_path_lookup2.
Qed.

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
  apply repl_to_precise_typ_all in Hp as [S' [T' [? [Hpr' [? ?]]]]]; auto.
  apply IHHl.
  pose proof (lookup_step_preservation_prec3 Hi Hwt H Hpr') as [[S1 [T1 [[= -> ->] Ht]]] | [? [[=] ?]]]; auto.
  apply ty_sub with (T:=typ_all S1 T1); auto; fresh_constructor; apply* tight_to_general.
Qed.

Lemma corresponding_types_fun: forall G s p S T,
    inert G ->
    well_typed G s ->
    G ⊢!!! p: typ_all S T ->
    (exists v, s ∋ (p, v) /\
            G ⊢ trm_val v : typ_all S T).
Proof.
  introv Hi Hwt Hp.
  destruct (typed_path_lookup3 Hi Hwt Hp) as [v Hs].
  inversions Hs.
  lets Ht: (lookup_preservation_typ_all Hi Hwt H1 (precise_to_general3 Hp)). eauto.
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
  introv Hin Ht. proof_recipe. inversions Hvpr.
  exists (L1 \u L \u (dom G)) S1 t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L1) by auto.
  specialize (HS2 y HL0).
  specialize (H2 y HL).
  eapply ty_sub; eauto. eapply narrow_typing in H2; eauto.
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
