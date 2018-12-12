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
  G ⊢ T ⟿ U ->
  G ⊢ U <: T /\ G ⊢ T <: U.
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

Lemma env_ok_inv {A} (G1 G2 G1' G2' : env A) x x' T T' :
  G1 & x ~ T & G2 = G1' & x' ~ T' & G2' ->
  ok (G1' & x' ~ T' & G2') ->
  G1 = G1' /\ x = x' /\ T = T' /\ G2 = G2'.
Proof.
  gen G2'. induction G2 using env_ind; introv Heq Hn.
  - assert (G2' = empty) as ->. {
      destruct G2' using env_ind; auto. rewrite concat_assoc in Heq.
(*      rewrite concat_empty_r in *.
      pose proof (eq_push_inv Heq) as [-> ?]. rewrite Heq in Hi. apply inert_ok in Hi.
      rewrite <- concat_assoc in Hi. apply ok_middle_inv_r in Hi. simpl_dom.
      apply notin_union in Hi as [Contra ?].  false* notin_same.*)
  Admitted.

Lemma lookup_step_preservation_prec1: forall G s p px pbs t T U,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢! p : T ⪼ U ->
    p = p_sel (avar_f px) pbs ->
    (exists S u, t = defv (val_lambda S u) /\ G ⊢ deftrm t : T) \/
    (exists S ds W T' P G1 G2 pT,
        t = defv (val_new S ds) /\
        T = typ_bnd T' /\
        G = G1 & px ~ pT & G2 /\
        px ; pbs ; P ; G ⊢ open_defs_p p ds :: open_typ_p p S /\
        G1 ⊩ S ⟿ W ⬳ T') \/
    (exists q r r' G1 G2 pT,
        t = defp q /\
        T = typ_sngl r /\
        G = G1 & px ~ pT & G2 /\
        G1 ⊩ r ⟿' r' ⬳ q).
Proof.
  introv Hi Hwt. gen p px pbs t T U.
  (** induction on well-formedness **)
  induction Hwt; introv Hs Hp Heq.
  - Case "G is empty".
    false* lookup_empty.
  - Case "G is not empty".
    destruct p as [y bs].
    (* showing that y is named *)
    assert (exists x0, y = avar_f x0) as [x0 ->] by admit. (* later when we figure out how to make env closed *)
    destruct (classicT (x = x0)) as [-> | Hn].
    * SCase "x = x0".
      (** induction on ⟦⟼⟧ **)
      gen T U T0 px pbs.
      dependent induction Hs; introv Hi Hv; introv Hp; introv [= -> <-]; try simpl_dot; try rewrite proj_rewrite in *.
      + SSCase "lookup_var".
        apply binds_push_eq_inv in H1 as ->.
        lets Hb: (pf_binds Hi Hp). pose proof (binds_push_eq_inv Hb) as ->.
        apply binds_inert in Hb; auto.
        destruct v as [S ds | S u].
        ++ right. left.
           lets Hi': (inert_prefix Hi).
           inversions Hb; proof_recipe. { inversion Hvpr. }
           inversions Hv. pick_fresh z. assert (z \notin L) as Hz by auto.
           apply H4 in Hz. do 4 eexists. exists P. repeat eexists.
           rewrite concat_empty_r. eauto.
           apply open_env_last_defs; auto.
           apply narrow_defs with (G:=G & px ~ open_typ px S).
           assert (open_defs_p (p_sel (avar_f px) nil) ds = open_defs px ds) as -> by rewrite* open_var_defs_eq.
           assert (open_typ_p (p_sel (avar_f px) nil) S = open_typ px S) as -> by rewrite* open_var_typ_eq.
           apply* rename_defs. apply subenv_last; auto. apply (repl_composition_open (pvar px)) in Hrc.
           eapply (repl_composition_open (pvar px)) in Hrc'.
           apply subtyp_trans with (T:=open_typ px U');
             apply repl_composition_sub in Hrc'; apply repl_composition_sub in Hrc; destruct_all;
               repeat rewrite open_var_typ_eq in *; unfold pvar in *; auto. all: eauto.
        ++ left. repeat eexists. apply* weaken_ty_trm.
      + SSCase "lookup_sel_p".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ Hwt IHHwt _ H0 H JMeq_refl eq_refl _ Hi Hv _ _ Hp' _ _ eq_refl)
          as [[? [? [[=] ?]]] |
              [[? [? [? [? [? [? [? [? [[=]]]]]]]]]] |
               [? [? [? [? [? [? [[= ->] [-> [[= ->] ?]]]]]]]]]]].
        apply pf_sngl_U in Hp'. inversion Hp'.
      + SSCase "lookup_sel_v".
        destruct (pf_invert_fld _ _ Hp) as [V Hp'].
        specialize (IHHs _ _ _ Hwt IHHwt _ H0 H JMeq_refl eq_refl _ Hi Hv _ _ Hp' _ _ eq_refl)
          as [[? [? [[=] ?]]] |
              [[S [ds' [W [T'' [P [G1 [G2 [pT [[= -> ->] [[= ->] [Heq [Hds Hrc]]]]]]]]]]]] |
               [? [? [? [? [? [? [[= ->] [-> [[= ->] ?]]]]]]]]]]].
        lets H': (defs_has_open (p_sel (avar_f px) f) H1). simpl in *.
        lets Hr: (pf_record_has_U Hi Hp').
        pose proof (repl_comp_trans_open (p_sel (avar_f px) f) Hrc) as Hrc_op.
        pose proof (repl_comp_trans_record_has Hrc_op Hr) as [V [W' [Hrh [Hrc1' Hrc2']]]].
        rewrite <- concat_empty_r in Heq at 1.
        assert (G2 = empty) as ->. {
          eapply env_ok_inv. eauto. rewrite concat_empty_r. auto.
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
           repeat eexists; eauto. rewrite concat_empty_r. eauto.
    * SCase "x <> x0".
      apply pf_strengthen in Hp; auto. apply lookup_strengthen in Hs; auto.
      inversions Heq.
      specialize (IHHwt (inert_prefix Hi) _ _ _ _ _ _ Hs Hp eq_refl)
        as [[? [? [[= ->]]]] |
              [[? [? [? [? [? [? [? [? [-> [-> [-> [Hds [? ?]]]]]]]]]]]]] |
               [? [? [? [? [? [? [[= ->] [[= ->] [-> [? ?]]]]]]]]]]]].
      + left. repeat eexists. apply* weaken_ty_trm.
      + right. left. repeat eexists. rewrite concat_assoc. eauto.
        apply* weaken_ty_defs. all: eauto.
      + right. right. repeat eexists. rewrite concat_assoc. eauto. eauto. auto.
Qed.

Lemma lookup_step_preservation_prec2 G s p px pbs t T :
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!! p : T ->
    p = p_sel (avar_f px) pbs ->
    (exists S U u, t = defv (val_lambda S u) /\ G ⊢ deftrm t : U /\ G ⊢! p : U ⪼ T) \/
    (exists S ds W U P G1 G2 pT,
        t = defv (val_new S ds) /\
        G ⊢! p : typ_bnd U ⪼ T /\
        G = G1 & px ~ pT & G2 /\
        px ; pbs ; P ; G ⊢ open_defs_p p ds :: open_typ_p p S /\
        G1 ⊩ S ⟿ W ⬳ U) \/
    (exists q r r' G1 G2 pT,
        t = defp q /\
        T = typ_sngl r /\
        G = G1 & px ~ pT & G2 /\
        G1 ⊩ r ⟿' r' ⬳ q).
Proof.
  introv Hi Hwt Hs Hp Heq. gen s t px pbs. induction Hp; introv Hwt; introv Hs; introv Heq.
  - destruct (lookup_step_preservation_prec1 Hi Hwt Hs H Heq)
      as [[? [? [[= ->]]]] |
          [[S [ds' [W [T'' [P [G1 [G2 [pT [-> [-> [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]]] |
           [? [? [? [? [? [? [-> [-> [-> [? ?]]]]]]]]]]]].
    * left. repeat eexists; eauto.
    * right. left. repeat eexists; eauto.
    * pose proof (pf_sngl_U H) as ->. right. right. repeat eexists; eauto.
  - clear IHHp2. simpl_dot. specialize (IHHp1 Hi _ Hwt).
    gen q U. dependent induction Hs; simpl_dot; introv Hp IHHp1 Hv.
    * specialize (IHHp1 _ Hs _ _ eq_refl) as [[? [? [? [[=] ?]]]] |
                                  [[? [? [? [? [? [? [? [? [[=] ?]]]]]]]]] |
                                   [q' [r [r' [G1 [G2 [pT [[= <-] [<- [-> [Hrc1 Hrc2]]]]]]]]]]]].
      right. right. exists (q • a) (q0 • a) (r' • a). repeat eexists;
      apply* repl_composition_fld_elim; admit.
    (* for that we need to fix named-var problem *)
    * specialize (IHHp1 _ Hs) as [[? [? [? [[= ->] ?]]]] |
                                  [[? [? [? [? [? [? [? [? [? [[=]%pf_sngl_T [[=] [HH [HHH ?]]]]]]]]]]]]] |
                                   [? [? [? [? [? [? [[=] ?]]]]]]]]]; auto.
Admitted.

Lemma lookup_step_preservation_inert_prec3: forall G s p T t,
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
                               G ⊩ S ⟿ W ⬳ U) \/
           (exists q, t = defp q /\ G ⊢!!! q : T))).
Proof.
  introv Hi Hwt Hs Hp. gen t.
  assert (exists px pbs, p = p_sel (avar_f px) pbs) as [px [pbs Heq]] by admit.
  dependent induction Hp; introv Hs Hit;
    destruct (lookup_step_preservation_prec2 Hi Hwt Hs H Heq)
                                as [[S' [U [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [W [U [P [G1 [G2 [pT [[= ->] [Hp' [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]]] |
                                     [q' [r [r' [G1 [G2 [pT [[= ->] [<- [Heq' [Hrc1 Hrc2]]]]]]]]]]]]; simpl.
  - left. simpl in *. inversions Hit.
    * apply (pf_forall_T Hi) in Hp' as ->. repeat eexists; eauto.
    * apply (pf_bnd_T Hi) in Hp' as ->. proof_recipe. inversion Hv.
  - right. inversions Hit.
    * apply (pf_forall_T Hi) in Hp' as [=].
    * apply (pf_bnd_T Hi) in Hp' as [= ->]. eexists. split*. left. repeat eexists; eauto;
      repeat apply* repl_composition_weaken; apply* inert_ok; apply* inert_prefix.
  - apply repl_comp_sngl_inv2 in Hrc1 as [q [= ->]]. inversion Hit.
  - apply pf_sngl_T in Hp' as ->; auto. proof_recipe. false* repl_to_invertible_val_sngl.
  - apply (pf_sngl_T Hi) in Hp' as [=].
  - clear IHHp.
    assert (exists V, G ⊢!!! q' : V) as [V Hq'] by admit. (* naming stuff *)
    lets Hok: (inert_ok Hi). rewrite Heq' in Hok.
    apply repl_composition_weaken with (G':=(px ~ pT & G2)) in Hrc1;
    apply repl_composition_weaken with (G':=(px ~ pT & G2)) in Hrc2;
    rewrite concat_assoc in *; auto. rewrite <- Heq' in *.
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
  destruct (lookup_step_preservation_inert_prec3 Hi Hwt Hs Hp) as
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
  destruct (lookup_step_preservation_inert_prec3 Hi Hwt Hs Hp) as
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
                             G ⊩ S ⟿ W ⬳ U) \/
         (exists q, t = defp q /\ G ⊢!!! q : T))).
Proof.
  intros Hi Hwt Hs. gen T. dependent induction Hs; introv Hp Hit.
  - left*.
  - right.
    pose proof (lookup_step_preservation_inert_prec3 Hi Hwt H Hp Hit)
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

Lemma typing_lookup1 G s p q T U :
    inert G ->
    well_typed G s ->
    s ⟦ defp p ⟼* defp q ⟧ ->
    G ⊢! p : T ⪼ U ->
    exists r r', T = typ_sngl r /\ G ⊩ r ⟿' r' ⬳ q /\ s ⟦ defp q ⟼* defp r' ⟧ /\ s ⟦ defp r ⟼* defp r' ⟧.
Proof.
  intros Hi Hwt Hs Hp. gen p T U q. induction Hwt; introv Hp; introv Hs.
  (** induction on ⟦~⟧ **)
  - apply precise_to_general in Hp. false* typing_empty_false.
  - assert (exists y bs, p = p_sel (avar_f y) bs) as [y [bs ->]] by admit.
    (* later when we figure out how to make env closed *)
    destruct (classicT (x = y)) as [-> | Hn].
    * SCase "x = y".
      (** induction on ⟦⊢!⟧ **)
      gen q. dependent induction Hp; introv Hs; try simpl_dot; eauto.
      + admit.
      + specialize (IHHp _ _ H0 _ _ Hi Hwt H H1 IHHwt JMeq_refl eq_refl).
        admit.
        * SCase "x <> y". admit.
Abort.


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
        destruct (lookup_step_preservation_prec1 Hi (well_typed_push Hwt H H0 H1) Hs Hp eq_refl)
          as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [P [G1 [G2 [pT [-> [[= ->] ?]]]]]]]]]] |
               [? [? [? [? [? [? [? [[=] [? ?]]]]]]]]]]].
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
    assert (exists px pbs, p = p_sel (avar_f px) pbs) as [px [pbs ->]] by admit.
    destruct (lookup_step_preservation_prec2 Hi Hwt Hs1 Hp1 eq_refl)
                                as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [W [U' [P [G1 [G2 [pT [-> [Hp' [Heq [Hds [Hrc1 Hrc2]]]]]]]]]]]]] |
                                     [? [? [? [? [? [? [-> [[= ->] ?]]]]]]]]]].
    + pose proof (pf_sngl_T Hi Hp') as ->. proof_recipe. inversions Hv. inversions H. inversions H0.
    + pose proof (pf_sngl_T Hi Hp') as [=].
    + eauto.
Qed.

Lemma typ_to_lookup3 G s p T :
  inert G ->
  well_typed G s ->
  G ⊢!!!p : T ->
  exists t, s ⟦ p ⟼ t ⟧.
Proof.
  intros Hi Hwt Hp. induction Hp; apply* typ_to_lookup2.
Qed.

Lemma prec_to_repl_comp1 G p q T :
  G ⊢! p : typ_sngl q ⪼ T ->
  G ⊢ p ⟿' q.
Proof.
  intros Hp. dependent induction Hp; eauto.
  - admit.
  - econstructor. econstructor. apply pf_fld in Hp. exists q 0. split. apply Hp.
    apply repl_intro_sngl. apply star_refl.
Qed.

Lemma prec_to_repl_comp2 G p q :
  inert G ->
  G ⊢!! p : typ_sngl q ->
  G ⊢ p ⟿' q.
Proof.
  intros Hi Hp. dependent induction Hp.
  - pose proof (pf_sngl_T Hi H) as ->. apply* prec_to_repl_comp1.
  - specialize (IHHp1 _ Hi eq_refl). apply* repl_composition_fld_elim.
Qed.

Lemma prec_to_repl_comp3 G p q :
  inert G ->
  G ⊢!!! p : typ_sngl q ->
  G ⊢ p ⟿' q.
Proof.
  intros Hi Hp. dependent induction Hp.
  - apply* prec_to_repl_comp2.
  - specialize (IHHp _ Hi eq_refl). pose proof (prec_to_repl_comp2 Hi H) as Hp'.
    eapply star_trans. apply* IHHp. eauto.
Qed.

Lemma sngl_path_lookup1 G s p q U :
  inert G ->
  well_typed G s ->
  G ⊢! p : typ_sngl q ⪼ U ->
  exists r r', s ⟦ p ⟼ defp r ⟧ /\ G ⊩ r ⟿' r' ⬳ q.
Proof.
  intros Hi Hwt Hp. destruct (typ_to_lookup1 Hi Hwt Hp) as [t Hs].
  assert (exists px pbs, p = p_sel (avar_f px) pbs) as [px [pbs ->]] by admit.
  destruct (lookup_step_preservation_prec1 Hi Hwt Hs Hp eq_refl)
           as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [P [G1 [G2 [pT [-> [[= ->] ?]]]]]]]]]] |
               [? [? [? [G1 [G2 [pT [-> [[= -> ] [-> [Hrc1 Hrc2]]]]]]]]]]]].
  - proof_recipe. inversions Ht. inversions H. inversion H0.
  - pose proof (inert_ok Hi) as Hok%ok_concat_inv_l.
    repeat eexists. eauto. all: do 2 apply* repl_composition_weaken.
Qed.

Lemma lookup_step_preservation_sngl_prec3: forall G s p q t Q1 Q2 Q3,
    inert G ->
    well_typed G s ->
    s ⟦ p ⟼ t ⟧ ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢! q : typ_all Q1 Q2 ⪼ Q3 ->
    exists r r', t = defp r /\ G ⊩ q ⟿' r' ⬳ r.
Proof. Admitted. (*
  introv Hi Hwt Hs Heq Hp. gen t px pbs.
  dependent induction Hp; introv Hs; introv Heq Hq;
    destruct (lookup_step_preservation_prec2 Hi Hwt Hs H Heq)
                                as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [W [U' [P [G1 [G2 [pT [-> [Hp' [Heq' [Hds [Hrc1 Hrc2]]]]]]]]]]]]] |
                                     [q' [r [r' [G1 [G2 [pT [-> [[= ->] [Heq' [Hrc1 Hrc2]]]]]]]]]]]].
  - pose proof (pf_sngl_T Hi Hp') as ->. pose proof (sngl_path_lookup1 Hi Hwt Hp') as [? [? [Hl ?]]].
    pose proof (lookup_step_func Hl Hs) as [=].
  - pose proof (pf_sngl_T Hi Hp') as [=].
  - do 5 eexists; split*.
  - pose proof (pf_sngl_T Hi Hp') as ->. pose proof (sngl_path_lookup1 Hi Hwt Hp') as [? [? [Hl ?]]].
    pose proof (lookup_step_func Hl Hs) as [=].
  - pose proof (pf_sngl_T Hi Hp') as [=].
  - pose proof (typ_to_lookup3 Hi Hwt Hp) as [t Hl].
    assert (exists rx rbs, r = p_sel (avar_f rx) rbs) as [rx [rbs ->]] by admit.
    specialize (IHHp _ Hi Hwt eq_refl _ Hl _ _ eq_refl Hq) as [r1 [r2 [G1' [G2' [pT' [Heq'' [-> [Hrq1 Hrq2]]]]]]]].
    rewrite Heq'' in Heq'.
    pose proof (env_ok_inv Heq') as [-> [-> [-> ->]]]. {
      rewrite Heq'' in Hi. rewrite Heq' in Hi. auto.
    }
    assert (inert (G1 & px ~ pT)) as Hi' by (subst; apply* inert_prefix).
    pose proof (inert_prefix Hi') as Hi''.
    pose proof (repl_comp_to_prec Hi Hrq1 (pt3 (pt2 Hq))) as [-> | Hq']; clear Hrq1.
    + assert (exists R, G ⊢!!! r1 : R) as [R Hr1] by admit.
      pose proof (repl_comp_to_prec Hi Hrq2' Hr1) as [-> | Hq']; clear Hrq2 Hr1.
      * assert (exists R', G ⊢!!! q' : R') as [R' Hrt] by admit.
        pose proof (repl_comp_to_prec Hi Hrc1' Hp) as [<- | Hp'];
          pose proof (repl_comp_to_prec Hi Hrc2' Hrt) as [-> | Hp''];
          do 5 eexists; split*; clear Hrc1 Hrc2; subst.
        ** split; eauto. split.  constructor. apply* prec_to_repl_comp3. apply Hp.
        ** split. constructor. eapply star_trans; apply* prec_to_repl_comp3.
        ** split. constructor.
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1 [[= ->] [-> | ?]]]]; try solve [apply* prec_to_repl_comp3].
           *** constructor.
           *** false* pt1_inert_pt3_sngl_false.
        ** split. constructor.
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1 [[= ->] [-> | ?]]]]; try solve [apply* prec_to_repl_comp3].
           *** eapply star_trans; apply* prec_to_repl_comp3.
           *** false* pt1_inert_pt3_sngl_false.
      * assert (exists R', G ⊢!!! q' : R') as [R' Hrt] by admit.
        pose proof (repl_comp_to_prec Hi Hrc1 Hp) as [-> | Hp'];
          pose proof (repl_comp_to_prec Hi Hrc2 Hrt) as [-> | Hp'']; do 2 eexists; split*; clear Hrc1 Hrc2.
        ** split. constructor. apply* prec_to_repl_comp3.
        ** split. constructor. eapply star_trans. apply (prec_to_repl_comp3 Hi Hp). apply* prec_to_repl_comp3.
        ** split. constructor.
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1' [[= ->] [-> | ?]]]]; try solve [apply* prec_to_repl_comp3].
           *** constructor.
           *** false* pt1_inert_pt3_sngl_false.
        ** split. constructor.
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1' [[= ->] [-> | HHH]]]]; try solve [apply* prec_to_repl_comp3].
           *** eapply star_trans; apply* prec_to_repl_comp3.
           *** false* pt1_inert_pt3_sngl_false.
    + false* (pt2_inert_pt3_sngl_false Hi (pt2 Hq) Hq').
      apply pf_forall_U in Hq as ->. auto.
Qed.*)

Lemma object_lookup1 G s p T U :
  inert G ->
  well_typed G s ->
  G ⊢! p : typ_bnd T ⪼ U ->
  exists S ds W px pbs P, s ⟦ p ⟼ defv (val_new S ds) ⟧ /\
                   p = p_sel (avar_f px) pbs /\
                   px; pbs; P; G ⊢ open_defs_p p ds :: open_typ_p p S /\
                   G ⊩ S ⟿ W ⬳ T.
Proof.
  intros Hi Hwt Hp. destruct (typ_to_lookup1 Hi Hwt Hp) as [t Hs]. Admitted.
 (*  destruct (lookup_step_preservation_prec1 Hi Hwt Hs Hp)
          as [[? [? [-> ?]]] |
              [[? [? [? [? [? [? [? [-> [[= ->] [[= ->] [? [? ?]]]]]]]]]]]] |
               [? [? [? [-> [[=] ?]]]]]]]; eauto.
  - proof_recipe. inversion H.
  - repeat eexists; eauto.
Qed.*)

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
   exists r r', s ⟦ defp p ⟼* defp r ⟧ /\ G ⊩ r ⟿' r' ⬳ q.
Proof.
  intros Hi Hwt Hpq. dependent induction Hpq.
  - pose proof (pf_sngl_T Hi H) as ->.
    destruct (sngl_path_lookup1 Hi Hwt H) as [? [? [? [? ?]]]].
    repeat eexists. apply* star_one. eauto. eauto.
  - specialize (IHHpq1 _ Hi Hwt eq_refl) as [? [? [? ?]]].
    repeat eexists. apply* lookup_step_fld_star.
    all: apply* repl_composition_fld_elim; admit. (* named typing stuff *)
Admitted.

Lemma repl_comp_in_env G p q :
  G ⊢ p ⟿' q ->
  p = q \/ (exists px pbs qx qbs T U,
              p = p_sel (avar_f px) pbs /\
              q = p_sel (avar_f qx) qbs /\
              binds px T G /\ binds qx U G).
Proof.
  intros Hp. dependent induction Hp; auto.
  assert (exists r, b = typ_sngl r) as [r ->]. {
    inversions H. destruct_all. inversions H0. eauto.
  }
  destruct H as [r' [r'' [n [Hr Hrt]]]].
  invert_repl.
  specialize (IHHp _ _ eq_refl eq_refl)
    as [-> | [px [pbs [qx [qbs [T [U [HH [HHH [Hb Hb']]]]]]]]]].
  - admit.
  - simpl_dot. right. assert (exists rx rbs, r'' = p_sel (avar_f rx) rbs) as [rx [rbs ->]] by admit.
    assert (exists V, binds rx V G) as [V Hb''] by admit.
    do 6 eexists. split. auto. split. Focus 2. split. apply Hb. apply Hb''.




Lemma lookup_same_var_same_type G s x bs cs T:
  inert G ->
  well_typed G s ->
  s ⟦ p_sel (avar_f x) bs ⟼ defp (p_sel (avar_f x) cs) ⟧ ->
  G ⊢!! p_sel (avar_f x) bs : T ->
  exists ds, T = typ_sngl (p_sel (avar_f x) ds).
Proof.
  intros Hi Hwt. gen x bs cs T. induction Hwt; introv Hs Ht.
  - Case "s is empty".
    false* lookup_empty.
  - Case "G is not empty".
    destruct (classicT (x = x0)) as [<- | Hn].
    + SCase "x = x0".
      pose proof (lookup_step_preservation_prec2 Hi (well_typed_push Hwt H H0 H1) Hs Ht eq_refl)
        as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
            [[S' [ds [W [U' [P [G1 [G2 [pT [[=] [Hp' [Heq [Hds [Hrc1 Hrc2]]]]]]]]]]]]] |
             [r [r' [r'' [G1 [G2 [pT [[= <-] [-> [Heq [Hrc1 Hrc2]]]]]]]]]]]].
      rewrite <- concat_empty_r in Heq at 1.
      apply eq_sym in Heq.
      apply env_ok_inv in Heq as [<- [_ [<- ->]]]; try rewrite concat_empty_r in *; auto.
      pose proof (repl_comp_in_env Hrc2)
      pose proof (repl_comp_sngl_inv2 Hrc1) as [q ->].


      Admitted.




(*
  intros Hi Hwt. gen x bs cs T. induction Hwt; introv Hs Ht.
  - Case "s is empty".
    false* lookup_empty.
  - Case "G is not empty".
    destruct (classicT (x = x0)) as [<- | Hn].
    + SCase "x = x0".
      gen T0. dependent induction Hs; introv Ht.
      * SSCase "lookup_sel_p".
        assert (exists px pbs, p = p_sel (avar_f px) pbs) as [px [pbs ->]] by admit.
        simpl in *. simpl_dot. inversions x1. rewrite proj_rewrite in *.
        pose proof (pt2_backtrack _ _ Ht) as [T' Ht'].
        specialize (IHHs _ _ _ H1 _ Hwt IHHwt _ Hi H H0 JMeq_refl eq_refl eq_refl _ Ht') as [ds ->].
        exists (a :: ds). repeat rewrite proj_rewrite.
        pose proof (lookup_step_preservation_prec2 Hi (well_typed_push Hwt H H0 H1) Hs Ht')
          as [[? [? [? [[=] ?]]]] |
              [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
               [r [r' [r'' [[= <-] [<- Hrc]]]]]]].
        inversions Ht.
        ** apply pf_invert_fld in H2 as [V Hp%pt2]. apply (pt2_sngl_unique' Hi Ht') in Hp as [=].
        ** simpl_dot. apply (pt2_sngl_unique' Hi H3) in Ht' as [= ->]. auto.
      * SSCase "lookup_sel_v".
         pose proof (lookup_step_preservation_prec2 Hi (well_typed_push Hwt H H0 H1) Hs Ht)
          as [[? [? [? [[=] ?]]]] |
              [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
               [r [r' [r'' [[= <-] [<- Hrc]]]]]]].
        simpl_dot.

*)



Lemma typed_path_lookup_helper G s p r S T V :
  inert G ->
  well_typed G s ->
  G ⊢!!! p : typ_sngl r ->
  G ⊢! r : typ_all S T ⪼ V->
  s ⟦ defp p ⟼* defp r ⟧.
Proof.
  intros Hi Hwt. gen p r S T V. induction Hwt; introv Hp Hr.
  - Case "G is empty".
    apply precise_to_general in Hr. false* typing_empty_false.
  - Case "G is not empty".
    destruct p as [x' bs].
    (* showing that y is named *)
    assert (exists px, x' = avar_f px) as [px Heq] by admit.
    destruct (classicT (x = px)) as [-> | Hn].
    + SCase "x = px".
      lets Hwt': (well_typed_push Hwt H H0 H1).
      pose proof (typ_to_lookup3 Hi Hwt' Hp) as [t Hlt].
      pose proof (lookup_step_preservation_sngl_prec3 Hi Hwt' Hlt Hp Hr) as [r1 [r2 [-> Hrc]]].
      assert (exists y cs, r1 = p_sel (avar_f y) cs) as [y [cs Heq']] by admit.
      destruct (classicT (px = y)) as [-> | Hn].
      * SSCase "px = y".
        subst. pose proof (lookup_same_var_same_type Hi Hwt' Hlt) as [ds Hds].



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
        pose proof (object_lookup1 Hi Hwt' Hp) as [X [ds [Y [px [pbs [P [Hl [[= -> ->] [Hds Hrc]]]]]]]]].
        pose proof (pf_record_has_U Hi Hp) as Hr.
        assert (exists Z, record_has X {a ⦂ Z}) as [Z Hr'] by admit. admit.
      + SSCase "pf_open".
        eauto.
      + SSCase "pf_and1".
        eauto.
      + SSCase "pf_and2".
        eauto.
    * apply pf_strengthen in Hp; auto. specialize (IHHwt (inert_prefix Hi) _ _ _ Hp) as [t Hs].
      eexists. constructor. apply* lookup_push_neq. inversion* Hs.
Abort.
(*
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
Abort.

Lemma typed_path_lookup3 G s p T :
    inert G ->
    well_typed G s ->
    G ⊢!!! p: T ->
    exists v, s ∋ (p, v).
Proof.
  induction 3; apply* typed_path_lookup2.
Qed.*)



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

Inductive well_typed_prec : ctx -> sta -> Prop :=
  | well_typed_prec_empty :
    well_typed_prec empty empty
  | well_typed_prec_push : forall (G : ctx) (s : sta) (x : var) (T : typ) (v : val),
      well_typed_prec G s ->
      x # G ->
      x # s ->
      G ⊢!v v : T ->
      well_typed_prec (G & x ~ T) (s & x ~ v).

Hint Constructors well_typed_prec.

Lemma inert_narrow G G' :
  inert G ->
  G' ⪯ G ->
  inert G'.
Proof.
  intros Hi. gen G'. induction Hi; introv HG.
  - inversions HG; auto. false* empty_push_inv.
  - inversions HG; eauto. apply eq_push_inv in H1 as [<- [<- <-]].
    constructor; auto. Abort.

Lemma narrow_notin G G' x :
  G' ⪯ G ->
  x # G ->
  x # G'.
Proof.
  induction 1; auto.
Qed.

Lemma narrow_ok G G' :
  G' ⪯ G ->
  ok G ->
  ok G'.
Proof.
  induction 1; auto.
Qed.

(*Lemma repl_comp_record:
  (forall D, record_dec D ->
        forall G D', G ⊢ typ_rcd D ⟿ typ_rcd D' -> record_dec D') /\
  (forall T ls , record_typ T ls ->
        forall G T', G ⊢ T ⟿ T' -> record_typ T' ls) /\
  (forall T, inert_typ T ->
        forall G T', G ⊢ T ⟿ T' -> inert_typ T').
Proof.
  apply rcd_mutind; intros; eauto.
  - apply repl_comp_typ_rcd in H as [T' [U' [= ->]]]. apply rd_typ.

Lemma record_typ_repl_comp T U G :
  record_type T ->
  G ⊢ T ⟿ U ->
  record_type U.
Proof.
  intros Hr. gen U. inversions Hr. induction H; introv Hc; subst; econstructor.
  -

Lemma well_typed_precise G s :
  inert G ->
  well_typed G s ->
  exists G', inert G' /\ G' ⪯ G /\ well_typed_prec G' s.
Proof.
  intros Hi. induction 1; eauto.
  pose proof (inert_prefix Hi) as Hi'.
  specialize (IHwell_typed Hi') as [G' [HiG' [HG' Hwt']]].
  eapply narrow_typing in H2; eauto.
  pose proof (narrow_notin HG' H0) as Hni.
  destruct (inert_last Hi) as [S T | T]; proof_recipe.
  - exists (G' & x ~ typ_all S1 T1). repeat split; eauto.
  - exists (G' & x ~ typ_bnd U''). repeat split; eauto.

*)

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
