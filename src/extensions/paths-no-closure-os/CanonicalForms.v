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

Definition deftrm t : trm :=
  match t with
  | defp p => trm_path p
  | defv v => trm_val v
  end.

(** * Lemmas to prove that [γ ⟦ p ↦ t ⟧] and [Γ ⊢! p: T] imply [Γ ⊢ t: T] *)

Lemma repl_composition_sub G T U :
  G ⊢ T ⟿ U ->
  G ⊢ U <: T /\ G ⊢ T <: U.
Proof.
  intros Hr. dependent induction Hr; eauto.
  destruct H as [q [r [n [S [Hq%precise_to_general [Hq' Hrt]]]]]]. destruct_all.
  split.
  - eapply subtyp_trans. apply* subtyp_sngl_qp. apply* precise_to_general2. eauto.
  - eapply subtyp_trans. apply H0. apply repl_swap in Hrt. eapply subtyp_sngl_pq; eauto. apply* precise_to_general2.
Qed.

Lemma defs_invert_trm x bs G d a T :
  x; bs; G ⊢ d : {a ⦂ T} ->
  exists t, d = {a := t}.
Proof.
  intros Hd. inversion Hd; eauto.
Qed.

Lemma object_typing G x bs ds T a t V :
  inert G ->
  x; bs; G ⊢ ds :: T ->
  defs_has ds {a := t} ->
  record_has T {a ⦂ V} ->
  (exists U u, t = defv (λ(U) u) /\ G ⊢ deftrm t : V) \/
  (exists U ds', t = defv (ν(U) ds') /\
            x; (a :: bs); G ⊢ open_defs_p (p_sel (avar_f x) (a :: bs)) ds' ::
                                 open_typ_p (p_sel (avar_f x) (a :: bs)) U /\
            V = μ U) \/
  (exists q S, t = defp q /\ V = {{ q }} /\ G ⊢ trm_path q : S).
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

Lemma pt3_exists G p T :
  inert G ->
  G ⊢ trm_path p : T ->
  exists U, G ⊢!!! p : U.
Proof.
  intros Hi Hp. apply (general_to_tight_typing Hi) in Hp.
  apply tight_to_prec_exists in Hp as [? ?]; eauto.
Qed.

Lemma lookup_step_preservation_prec1: forall G s p px pbs t T U,
    inert G ->
    wf_env G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢! p : T ⪼ U ->
    p = p_sel (avar_f px) pbs ->
    (exists S u, t = defv (λ(S) u) /\ G ⊢ deftrm t : T) \/
    (exists S ds W T' G1 G2 pT,
        t = defv (ν(S) ds) /\
        T = μ T' /\
        G = G1 & px ~ pT & G2 /\
        px ; pbs; G ⊢ open_defs_p p ds :: open_typ_p p S /\
        G1 ⊩ S ⟿ W ⬳ T') \/
    (exists q r r' G1 G2 pT,
        t = defp q /\
        T = {{ r }} /\
        G = G1 & px ~ pT & G2 /\
        (r = r' \/ G1 ⊢!!! r : {{ r' }}) /\ (q = r' \/ G1 ⊢!!! q : {{ r' }})).
Proof.
  introv Hi Hwf Hwt. gen p px pbs t T U.
  (** induction on well-formedness **)
  induction Hwt; introv Hs Hp Heq.
  - Case "G is empty".
    false* lookup_empty.
  - Case "G is not empty".
    pose proof (typed_paths_named (precise_to_general Hp)) as [px' [bs ->]].
    destruct (classicT (x = px')) as [-> | Hn].
    * SCase "x = px".
      (** induction on ⟦⟼⟧ **)
      gen T U T0 px pbs.
      dependent induction Hs; introv Hwf Hi Hv; introv Hp; introv [= -> <-];
        try simpl_dot; try rewrite proj_rewrite in *.
      + SSCase "lookup_var".
        apply binds_push_eq_inv in H1 as ->.
        lets Hb: (pf_binds Hi Hp). pose proof (binds_push_eq_inv Hb) as ->.
        apply binds_inert in Hb; auto.
        destruct v as [S ds | S u].
        ++ right. left.
           lets Hi': (inert_prefix Hi). lets Hwf': (wf_env_prefix Hwf).
           inversions Hb; proof_recipe. { inversion Hvpr. }
           inversions Hv. pick_fresh z. assert (z \notin L) as Hz by auto.
           apply H4 in Hz. repeat eexists.
           +++ rewrite concat_empty_r. eauto.
           +++ apply open_env_last_defs; auto.
               apply narrow_defs with (G:=G & px ~ open_typ px S). {
                 assert (open_defs_p (p_sel (avar_f px) nil) ds = open_defs px ds) as -> by rewrite* open_var_defs_eq.
                 assert (open_typ_p (p_sel (avar_f px) nil) S = open_typ px S) as -> by rewrite* open_var_typ_eq.
                 apply rename_defs with (x := z); auto.
               }
               apply subenv_last; auto. apply (repl_composition_open (pvar px)) in Hrc.
               eapply (repl_composition_open (pvar px)) in Hrc'.
               apply subtyp_trans with (T:=open_typ px U');
                 apply repl_composition_sub in Hrc'; apply repl_composition_sub in Hrc; destruct_all;
                   repeat rewrite open_var_typ_eq in *; unfold pvar in *; auto. all: auto.
           +++ eauto.
           +++ eauto.
        ++ left. repeat eexists. apply* weaken_ty_trm.
      + SSCase "lookup_sel_p".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ Hwt IHHwt _ H0 H JMeq_refl eq_refl _ Hwf Hi Hv _ _ Hp' _ _ eq_refl)
          as [[? [? [[=] ?]]] |
              [[? [? [? [? [? [? [? [[=]]]]]]]]] |
               [? [? [? [? [? [? [[= ->] [-> [[= ->] ?]]]]]]]]]]].
        apply pf_sngl_U in Hp'. inversion Hp'.
      + SSCase "lookup_sel_v".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ Hwt IHHwt _ H0 H JMeq_refl eq_refl _ Hwf Hi Hv _ _ Hp' _ _ eq_refl)
          as [[? [? [[=] ?]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [[= -> ->] [[= ->] [Heq [Hds Hrc]]]]]]]]]]] |
               [? [? [? [? [? [? [[= ->] [-> [[= ->] ?]]]]]]]]]]].
        lets H': (defs_has_open (p_sel (avar_f px) f) H1). simpl in *.
        lets Hr: (pf_record_has_U Hi Hp').
        rewrite Heq in Hi, Hwf.
        pose proof (repl_comp_trans_open (p_sel (avar_f px) f)
                                         (inert_prefix (inert_prefix Hi))
                                         Hrc) as Hrc_op.
        pose proof (repl_comp_trans_record_has Hrc_op Hr) as [V [W' [Hrh [Hrc1' Hrc2']]]].
        rewrite <- concat_empty_r in Heq at 1.
        assert (G2 = empty) as ->. {
          eapply env_ok_inv. eauto. rewrite concat_empty_r. rewrite <- Heq, concat_empty_r in Hi. auto.
        }
        repeat rewrite concat_empty_r in *. apply eq_push_inv in Heq as [_ [<- <-]].
        assert (G & px ~ T0 ⊢ V <: T1 /\ G & px ~ T0 ⊢ T1 <: V) as [HVT HTV]. {
          apply repl_composition_sub in Hrc2'. apply repl_composition_sub in Hrc1'.
          destruct_all.
          split; apply weaken_subtyp; eauto.
        }
        destruct (object_typing Hi Hds H' Hrh) as [[U' [u [Heq Ht']]] |
                                                   [[U' [ds'' [Heq [Hds'' ->]]]] | [q [V' [Heq1 [-> Hq]]]]]].
        ++ destruct t; inversions Heq. destruct v0; inversions H3.
           left. repeat eexists. eauto.
        ++ destruct t as [|]; inversions Heq. destruct v0 as [X ds |]; inversions H3. fold open_rec_defs_p in Hds''.
           right. left.
           pose proof (repl_comp_bnd_inv1 Hrc1') as [Y ->]. pose proof (repl_comp_bnd_inv2 Hrc2') as [Z ->].
           repeat eexists; eauto.
           +++ apply repl_comp_bnd' in Hrc1'. rewrite concat_empty_r. eauto.
           +++ apply repl_comp_bnd' in Hrc1'. apply Hrc1'.
           +++ apply* repl_comp_bnd'.
        ++ destruct t; inversions Heq1. right. right.
           pose proof (repl_comp_sngl_inv1 Hrc1') as [r ->]. pose proof (repl_comp_sngl_inv2 Hrc2') as [r' ->].
           pose proof (pf_sngl_U Hp) as ->.
           pose proof (sngl_typed Hi Hwf Hp) as [V Hr'%pt3].
           pose proof (pt3_exists Hi Hq) as [V'' Hp3].
           pose proof (repl_comp_to_prec' Hi Hwf Hrc2' Hr')
             as [-> | Hpr];
             pose proof (repl_comp_to_prec' Hi Hwf Hrc1' Hp3)
             as [<- | Hpr']; clear Hrc1' Hrc2';
               repeat eexists; try rewrite concat_empty_r; eauto.
    * SCase "x <> x0".
      apply pf_strengthen in Hp; auto. apply lookup_strengthen_one in Hs; auto.
      inversions Heq.
      specialize (IHHwt (inert_prefix Hi) (wf_env_prefix Hwf) _ _ _ _ _ _ Hs Hp eq_refl)
        as [[? [? [[= ->]]]] |
              [[? [? [? [? [? [? [? [-> [-> [-> [Hds [? ?]]]]]]]]]]]] |
               [? [? [? [? [? [? [[= ->] [[= ->] [-> [? ?]]]]]]]]]]]].
      + left. repeat eexists. apply* weaken_ty_trm.
      + right. left. repeat eexists. rewrite concat_assoc. eauto.
        apply* weaken_ty_defs. all: eauto.
      + right. right. repeat eexists. rewrite concat_assoc. all: eauto.
Qed.
Lemma lookup_step_preservation_prec2 G s p px pbs t T :
    inert G ->
    wf_env G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!! p : T ->
    p = p_sel (avar_f px) pbs ->
    (exists S U u, t = defv (λ(S) u) /\ G ⊢ deftrm t : U /\ G ⊢! p : U ⪼ T) \/
    (exists S ds W U G1 G2 pT,
        t = defv (ν(S) ds) /\
        G ⊢! p : μ U ⪼ T /\
        G = G1 & px ~ pT & G2 /\
        px ; pbs; G ⊢ open_defs_p p ds :: open_typ_p p S /\
        G1 ⊩ S ⟿ W ⬳ U) \/
    (exists q r r' G1 G2 pT,
        t = defp q /\
        T = {{ r }} /\
        G = G1 & px ~ pT & G2 /\
        (r = r' \/ G1 ⊢!!! r : {{ r' }}) /\ (r' = q \/ G1 ⊢!!! q : {{ r' }})).
Proof.
  introv Hi Hwf Hwt Hs Hp Heq. gen s t px pbs. induction Hp; introv Hwt; introv Hs; introv Heq.
  - destruct (lookup_step_preservation_prec1 Hi Hwf Hwt Hs H Heq)
      as [[? [? [[= ->]]]] |
          [[S [ds' [W [T'' [G1 [G2 [pT [-> [-> [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
           [? [? [? [? [? [? [-> [-> [-> [? ?]]]]]]]]]]]].
    * left. repeat eexists; eauto.
    * right. left. repeat eexists; eauto.
    * pose proof (pf_sngl_U H) as ->. right. right. repeat eexists; eauto.
      destruct_all; eauto.
  - clear IHHp2. simpl_dot. specialize (IHHp1 Hi Hwf _ Hwt).
    gen q U. dependent induction Hs; simpl_dot; introv Hp IHHp1 Hv.
    * specialize (IHHp1 _ Hs _ _ eq_refl) as [[? [? [? [[=] ?]]]] |
                                  [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
                                   [q' [r [r' [G1 [G2 [pT [[= <-] [[= ->] [-> [Hrc1 Hrc2]]]]]]]]]]]].
      right. right. exists (q • a) (r • a).
      pose proof (inert_prefix (inert_prefix Hi)) as Hi'.
      pose proof (wf_env_prefix (wf_env_prefix Hwf)) as Hwf'.
      destruct Hrc1 as [-> | Hr1]; destruct Hrc2 as [-> | Hr2].
      ** repeat eexists; eauto.
      ** repeat eexists; eauto. right. apply* pt3_field_elim_p.
         apply* pt3_trans2.
         pose proof (sngl_typed3 Hi' Hwf' Hr2) as [_ [T Ht]%pt2_exists].
         constructor. rewrite <- concat_assoc in *. apply* pt2_fld_strengthen.
      ** repeat eexists. right. apply* pt3_field_elim_p.
         rewrite <- concat_assoc in *. apply* pt3_fld_strengthen.
         left*.
      ** pose proof (field_elim_q3) as Hf.
         rewrite <- concat_assoc in *.
         pose proof (pt3_weaken (inert_ok Hi) Hr1).
         specialize (Hf _ _ _ _ _ Hi H (pt3 Hv)) as [S Ht].
         repeat eexists. rewrite* concat_assoc.
         right. apply* pt3_field_elim_p.
         apply* pt3_fld_strengthen.
         right. apply* pt3_field_elim_p. apply* pt3_fld_strengthen.
         eapply pt3_trans2. eapply pt3_weaken. apply* inert_ok. apply Hr2.
         eapply pt3_weaken in Hr1. apply Ht. apply* inert_ok.
    * specialize (IHHp1 _ Hs) as [[? [? [? [[= ->] ?]]]] |
                                  [[? [? [? [? [? [? [? [? [[=]%pf_sngl_T [[=] [HH [HHH ?]]]]]]]]]]]] |
                                   [? [? [? [? [? [? [[=] ?]]]]]]]]]; auto.
Qed.
Lemma lookup_step_preservation_inert_prec3: forall G s p T t,
    inert G ->
    wf_env G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!!! p : T ->
    inert_typ T ->
    (exists S U, T = ∀(S) U /\ G ⊢ deftrm t : ∀(S) U) \/
    (exists U, T = μ U /\
          ((exists S ds px pbs W, t = defv (ν(S) ds) /\
                               p = p_sel (avar_f px) pbs /\
                               px; pbs; G ⊢ open_defs_p p ds :: open_typ_p p S /\
                               G ⊩ S ⟿ W ⬳ U) \/
           (exists q, t = defp q /\ G ⊢!!! q : T))).
Proof.
  introv Hi Hwf Hwt Hs Hp. gen t.
  pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs Heq]].
  dependent induction Hp; introv Hs Hit;
    destruct (lookup_step_preservation_prec2 Hi Hwf Hwt Hs H Heq)
                                as [[S' [U [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [W [U [G1 [G2 [pT [[= ->] [Hp' [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
                                     [q' [r [r' [G1 [G2 [pT [[= ->] [[= ->] [Heq' [Hrc1 Hrc2]]]]]]]]]]]]; simpl.
  - left. simpl in *. inversions Hit.
    * apply (pf_forall_T Hi) in Hp' as ->. repeat eexists; eauto.
    * apply (pf_bnd_T Hi) in Hp' as ->. proof_recipe. inversion Hv.
  - right. inversions Hit.
    * apply (pf_forall_T Hi) in Hp' as [=].
    * apply (pf_bnd_T Hi) in Hp' as [= ->]. eexists. split*. left. repeat eexists; eauto;
      repeat apply* repl_composition_weaken; apply* inert_ok; apply* inert_prefix.
  - inversion Hit.
  - apply pf_sngl_T in Hp' as ->; auto. proof_recipe. false* repl_to_invertible_val_sngl.
  - apply (pf_sngl_T Hi) in Hp' as [=].
  - clear IHHp.
    assert (exists V, G ⊢!!! q' : V) as [V Hq']. {
      destruct Hrc1 as [-> | Hr]; destruct Hrc2 as [-> | Hr']; subst; rewrite <- concat_assoc in *; eauto.
      - eexists. apply* pt3_weaken.
      - apply sngl_typed3 in Hr as [S Ht]. eexists. apply* pt3_weaken. apply* inert_prefix. apply* wf_env_prefix.
      - eexists. apply* pt3_weaken.
    }
    lets Hok: (inert_ok Hi). rewrite Heq' in Hok.
    destruct Hrc1 as [-> | Hr]; destruct Hrc2 as [-> | Hr']; inversions Hit.
    + left; repeat eexists; apply* precise_to_general3.
    + right. eexists. split*.
    + left. repeat eexists. apply* precise_to_general3. apply* pt3_sngl_trans3.
      repeat apply* pt3_weaken.
    + right. eexists. split*. right. eexists. split*.
      apply* pt3_sngl_trans3. repeat apply* pt3_weaken.
    + left. repeat eexists.
      do 2 eapply pt3_weaken in Hr.
      pose proof (pt3_inert_sngl_invert Hi Hp Hr (inert_typ_all _ _)) as Hr'.
      apply* precise_to_general3. all: eauto; apply* inert_ok. apply* inert_prefix.
    + right. eexists. split*. right. eexists. split*.
      do 2 eapply pt3_weaken in Hr.
      apply* (pt3_inert_sngl_invert Hi Hp Hr).
      all: eauto; apply* inert_ok. apply* inert_prefix.
    + left. repeat eexists. apply precise_to_general3.
      eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
      apply* pt3_inert_sngl_invert. repeat apply* pt3_weaken.
    + right. eexists. split*. right. eexists. split*.
      eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
      apply* pt3_inert_sngl_invert. repeat apply* pt3_weaken.
Qed.
Lemma lookup_step_preservation_prec3_fun G s p T S t :
  inert G ->
  wf_env G ->
  well_typed G s ->
  s ⟦ p ⟼ t ⟧ ->
  G ⊢!!! p : ∀(T) S ->
  G ⊢ deftrm t : ∀(T) S.
Proof.
  intros Hi Hwf Hwt Hs Hp.
  destruct (lookup_step_preservation_inert_prec3 Hi Hwf Hwt Hs Hp) as
      [[? [? [-> Ht]]] | [? [[=] ?]]]; auto.
Qed.

(** * Lemmas to prove that [Γ ~ γ] and [Γ ⊢! p: T] imply [γ ∋ (p, v)] *)
Lemma typ_to_lookup1 G s p T U :
  inert G ->
  wf_env G ->
  well_typed G s ->
  G ⊢! p : T ⪼ U ->
  exists t, s ⟦ p ⟼ t ⟧.
Proof.
  intros Hi Hwf Hwt Hp. gen p T U. induction Hwt; introv Hp.
  (** induction on ⟦~⟧ **)
  - false. dependent induction Hp; eauto. apply* binds_empty_inv.
  - pose proof (typed_paths_named (precise_to_general Hp)) as [y [bs ->]].
    (* later when we figure out how to make env closed *)
    destruct (classicT (x = y)) as [-> | Hn].
    * SCase "x = y".
      (** induction on ⟦⊢!⟧ **)
      dependent induction Hp; try simpl_dot.
      + eexists. apply* lookup_var.
      + specialize (IHHp _ _ H0 _ _ Hwf Hi Hwt H H1 IHHwt JMeq_refl eq_refl) as [t Hs].
        pose proof (pf_bnd_T2 Hi Hp) as [V ->].
        destruct (lookup_step_preservation_prec1 Hi Hwf (well_typed_push Hwt H H0 H1) Hs Hp eq_refl)
          as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [-> [[= ->] ?]]]]]]]]] |
               [? [? [? [? [? [? [? [[=] [? ?]]]]]]]]]]].
        ++ proof_recipe. inversion Ht.
        ++ assert (exists u, defs_has ds' {a := u}) as [u Hu]. {
             destruct H3 as [Heq [Hds Hrc]].
             apply pf_record_has_U in Hp; auto.
             eapply repl_comp_trans_open in Hrc.
             eapply repl_comp_trans_record_has in Hrc as [V [X [Hr _]]]; try apply Hp.
             eapply record_has_ty_defs in Hds as [d [Hdh Hds]]; eauto.
             eapply defs_invert_trm in Hds as [t ->]. unfold defs_has in *.
             simpl in *. apply* defs_has_open'. rewrite  Heq in Hi, Hwf.
             repeat apply* inert_prefix.
           }
           eexists. rewrite proj_rewrite. eauto.
      + eauto.
      + eauto.
      + eauto.
    * SCase "x <> y".
      apply pf_strengthen in Hp; auto. specialize (IHHwt (inert_prefix Hi) (wf_env_prefix Hwf) _ _ _ Hp) as [t Hs].
      eexists. apply* lookup_step_weaken_one.
Qed.
Lemma typ_to_lookup2 G s p T :
  inert G ->
  wf_env G ->
  well_typed G s ->
  G ⊢!! p : T ->
  exists t, s ⟦ p ⟼ t ⟧.
Proof.
  intros Hi Hwf Hwt Hp. induction Hp.
  - apply* typ_to_lookup1.
  - specialize (IHHp1 Hi Hwf Hwt) as [u1 Hs1]. specialize (IHHp2 Hi Hwf Hwt) as [u2 Hs2].
    pose proof (typed_paths_named (precise_to_general2 Hp1)) as [px [pbs ->]].
    destruct (lookup_step_preservation_prec2 Hi Hwf Hwt Hs1 Hp1 eq_refl)
                                as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [W [U' [G1 [G2 [pT [-> [Hp' [Heq [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
                                     [? [? [? [? [? [? [-> [[= ->] ?]]]]]]]]]].
    + pose proof (pf_sngl_T Hi Hp') as ->. proof_recipe. inversions Hv. inversions H. inversions H0.
    + pose proof (pf_sngl_T Hi Hp') as [=].
    + eauto.
Qed.
Lemma typ_to_lookup3 G s p T :
  inert G ->
  wf_env G ->
  well_typed G s ->
  G ⊢!!!p : T ->
  exists t, s ⟦ p ⟼ t ⟧.
Proof.
  intros Hi Hwf Hwt Hp. induction Hp; apply* typ_to_lookup2.
Qed.
