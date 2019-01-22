Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import Sequences.
Require Import Binding CanonicalForms Definitions GeneralToTight InvertibleTyping Lookup Narrowing
            OperationalSemantics PreciseTyping RecordAndInertTypes Subenvironments Substitution Weakening.

Module Safety.
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

(** The typing of a term with a stack *)
Inductive sta_trm_typ : sta * trm -> typ -> Prop :=
| sta_trm_typ_c : forall G s t T,
    inert G ->
    wf_env G ->
    well_typed G s ->
    G ⊢ t : T ->
    sta_trm_typ (s, t) T.

Hint Constructors sta_trm_typ.

Notation "'⊢' t ':' T" := (sta_trm_typ t T) (at level 40, t at level 59).

(** * Preservation *)

Lemma pf_sngl G x bs T U a :
  inert G ->
  G ⊢! (p_sel (avar_f x) bs) • a : T ⪼ U ->
  exists S V, G ⊢! pvar x : typ_bnd S ⪼ V.
Proof.
  intros Hi Hp. gen G x a T U. induction bs; introv Hi; introv Hp.
  - simpl in Hp. rewrite proj_rewrite in *. apply pf_invert_fld in Hp as [V Hp].
    pose proof (pf_bnd_T2 Hi Hp) as [S ->]. eauto.
  - pose proof (pf_invert_fld _ _ Hp) as [V Hp']. eauto.
Qed.

Lemma def_typing_sngl_rhs z bs P G a t q :
  z; bs; P; G ⊢ {a := t} : {a ⦂ typ_sngl q} ->
  exists T, G ⊢ trm_path q : T.
Proof.
  intros Hd. dependent induction Hd; eauto.
Qed.

Lemma defs_typing_sngl_rhs z bs P G ds T a q :
  z; bs; P; G ⊢ ds :: T ->
  record_has T {a ⦂ typ_sngl q} ->
  exists T, G ⊢ trm_path q : T.
Proof.
  induction 1; intros Hr.
  - destruct D; inversions Hr. inversions H. apply* def_typing_sngl_rhs.
  - inversions Hr; auto. inversions H5. inversions H0. eauto.
Qed.

Reserved Notation "x '==>' T '=' bs '=>' U" (at level 40, T at level 20).

Inductive lookup_fields_typ : var -> typ -> list trm_label -> typ -> Prop :=
| lft_empty : forall x T,
    x ==> T =nil=> T
| lft_cons : forall T bs U x a S,
    x ==> T =bs=> typ_bnd U ->
    record_has (open_typ_p (p_sel (avar_f x) bs) U) {a ⦂ S} ->
    x ==> T =a::bs=> S

where "x '==>' T '=' bs '=>' U" := (lookup_fields_typ x T bs U).

Hint Constructors lookup_fields_typ.

Lemma inert_record_has T p a U :
  inert_typ (typ_bnd T) ->
  record_has (open_typ_p p T) {a ⦂ U} ->
  inert_sngl U.
Proof.
  intros Hi Hr. dependent induction Hr.
  - destruct T; inversions x. destruct d; inversions H0. inversions Hi. inversions H0.
    inversions H1. left. apply* open_record_p. right. eexists. simpl. eauto.
  - destruct T; inversions x. inversions Hi. inversions H0. apply* IHHr.
  - destruct T; inversions x. inversions Hi. inversions H0.
    specialize (IHHr U a p (typ_rcd D)). eauto.
Qed.

Lemma lft_inert x T bs U :
  inert_typ T ->
  x ==> T =bs=> typ_bnd U ->
  inert_typ (typ_bnd U).
Proof.
  intros Hi Hl. gen x U. induction bs; introv Hl; inversions Hl; eauto.
  specialize (IHbs _ _ H3).
  apply (inert_record_has _ IHbs) in H5 as [Hin | [? [=]]]. auto.
Qed.

Lemma lft_unique x S bs T U :
  inert_typ S ->
  x ==> S =bs=> T ->
  x ==> S =bs=> U ->
  T = U.
Proof.
  intros Hi Hl1. gen U. induction Hl1; introv Hl2.
  - inversion Hl2; auto.
  - inversions Hl2. specialize (IHHl1 Hi _ H4) as [= ->].
    pose proof (lft_inert Hi Hl1). inversions H0.
    eapply unique_rcd_trm. apply* open_record_type_p. eauto. eauto.
Qed.

Lemma lft_typ_all_inv x S bs cs V T U:
  inert_typ S ->
  x ==> S =bs=> typ_all T U ->
  x ==> S =cs++bs=> V ->
  cs = nil.
Proof.
  gen x S bs T U V. induction cs; introv Hin Hl1 Hl2; auto.
  rewrite <- app_comm_cons in Hl2.
  inversions Hl2. specialize (IHcs _ _ _ _ _ _ Hin Hl1 H3) as ->.
  rewrite app_nil_l in H3.
  pose proof (lft_unique Hin Hl1 H3) as [= <-].
Qed.

Lemma lft_typ_sngl_inv x S bs p cs V :
  inert_typ S ->
  x ==> S =bs=> typ_sngl p ->
  x ==> S =cs++bs=> V ->
  cs = nil.
Proof.
  gen x S bs p V. induction cs; introv Hin Hl1 Hl2; auto.
  rewrite <- app_comm_cons in Hl2.
  inversions Hl2. specialize (IHcs _ _ _ _ _ Hin Hl1 H3) as ->.
  rewrite app_nil_l in H3.
  pose proof (lft_unique Hin Hl1 H3) as [= <-].
Qed.

Lemma lfs_defs_typing : forall cs z bs P G ds T S U,
  z; bs; P; G ⊢ ds :: open_typ_p (p_sel (avar_f z) bs) T ->
  inert_typ S ->
  z ==> S =bs=> typ_bnd T ->
  z ==> S =cs++bs=> typ_bnd U ->
  exists ds', z; (cs++bs); P; G ⊢ ds' :: open_typ_p (p_sel (avar_f z) (cs++bs)) U.
Proof.
  induction cs; introv Hds Hin Hl1 Hl2.
  - rewrite app_nil_l in*. pose proof (lft_unique Hin Hl1 Hl2) as [= ->]. eauto.
  - rewrite <- app_comm_cons in *. inversions Hl2.
    specialize (IHcs _ _ _ _ _ _ _ _ Hds Hin Hl1 H3) as [ds' Hds'].
    pose proof (record_has_ty_defs Hds' H5) as [d [Hdh Hd]].
    inversions Hd. eauto.
Qed.

Lemma def_typing_rhs z bs P G d a q U S cs T b V :
  z; bs; P; G ⊢ d : {b ⦂ V} ->
  inert_typ S ->
  z ==> S =bs=> typ_bnd T ->
  record_has (open_typ_p (p_sel (avar_f z) bs) T) {b ⦂ V} ->
  z ==> S =cs++b::bs=> typ_bnd U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++b::bs)) U) {a ⦂ typ_sngl q} ->
  exists W, G ⊢ trm_path q : W.
Proof.
  intros Hds Hin Hl1 Hrd Hl2 Hr. inversions Hds.
  - Case "def_all".
    eapply lft_cons in Hl1; eauto.
    pose proof (lft_typ_all_inv _ Hin Hl1 Hl2) as ->.
    rewrite app_nil_l in *.
    pose proof (lft_unique Hin Hl1 Hl2) as [=].
  - Case "def_new".
    pose proof (ty_def_new _ eq_refl H7 H8).
    assert (z ==> S =b::bs=> typ_bnd T0) as Hl1'. {
        eapply lft_cons. eauto. eauto.
    }
    pose proof (lfs_defs_typing _ H8 Hin Hl1' Hl2) as [ds' Hds'].
    pose proof (record_has_ty_defs Hds' Hr) as [d [Hdh Hd]].
    inversions Hd. eauto.
  - Case "def_path".
    eapply lft_cons in Hl1; eauto.
    pose proof (lft_typ_sngl_inv _ Hin Hl1 Hl2) as ->.
    rewrite app_nil_l in *.
    pose proof (lft_unique Hin Hl1 Hl2) as [=].
Qed.

Lemma defs_typing_rhs z bs P G ds T a q U S cs T' b V :
  z; bs; P; G ⊢ ds :: T ->
  inert_typ S ->
  z ==> S =bs=> typ_bnd T' ->
  record_has (open_typ_p (p_sel (avar_f z) bs) T') {b ⦂ V} ->
  record_has T {b ⦂ V} ->
  z ==> S =cs++b::bs=> typ_bnd U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++b::bs)) U) {a ⦂ typ_sngl q} ->
  exists V, G ⊢ trm_path q : V.
Proof.
  intros Hds Hin Hl1 Hr1 Hr2 Hl2 Hr.
  gen S a q U cs T' b V. dependent induction Hds; introv Hin; introv Hl1; introv Hl2; introv Hr Hr1 Hr2.
  - inversions Hr2. eapply def_typing_rhs; eauto.
  - specialize (IHHds _ Hin _ _ _ _ _ Hl1 _ Hl2 Hr _ Hr1).
    inversions Hr2; auto.
    inversions H4. clear IHHds.
    eapply def_typing_rhs; eauto.
Qed.

Lemma pf_sngl_to_lft G x T bs W V :
  inert (G & x ~ typ_bnd T) ->
  G & x ~ typ_bnd T ⊢! p_sel (avar_f x) bs : W ⪼ V ->
  bs = nil \/
  exists b c bs' bs'' U V,
    bs = c :: bs' /\
    bs = bs'' ++ b :: nil /\
    x ==> typ_bnd T =bs'=> typ_bnd U /\
    record_has (open_typ x T) {b ⦂ V} /\
    record_has (open_typ_p (p_sel (avar_f x) bs') U) {c ⦂ W}.
Proof.
  intros Hi Hp. dependent induction Hp; eauto.
  simpl_dot. right. specialize (IHHp _ _ _ _ Hi JMeq_refl eq_refl)
    as [-> | [b [c [bs' [bs'' [S [V [-> [Hl [Hl2 [Hr1 Hr2]]]]]]]]]]].
  - Case "pf_bind".
    pose proof (pf_binds Hi Hp) as ->%binds_push_eq_inv. repeat eexists; eauto.
    simpl. rewrite app_nil_l. eauto. rewrite open_var_typ_eq. eapply pf_record_has_T; eauto.
    apply* pf_record_has_T.
  - Case "pf_fld".
    pose proof (pf_bnd_T2 Hi Hp) as [W ->].
    rewrite Hl.
    exists b a. eexists. exists (a :: bs''). repeat eexists; eauto.
    rewrite <- Hl. econstructor; eauto. rewrite <- Hl.
    apply* pf_record_has_T.
Qed.

Lemma val_typing G x v T :
  inert G ->
  wf_env G ->
  G ⊢ trm_val v : T ->
  x # G ->
  exists T', G ⊢!v v : T' /\
        G ⊢ T' <: T /\
        inert_typ T' /\
        wf_env (G & x ~ T').
Proof.
  intros Hi Hwf Hv Hx. dependent induction Hv; eauto.
  - exists (typ_all T U). repeat split*. constructor; eauto. introv Hp.
    assert (binds x (typ_all T U) (G & x ~ typ_all T U)) as Hb by auto. apply pf_bind in Hb; auto.
    destruct bs as [|b bs].
    + apply pf_binds in Hp; auto. apply binds_push_eq_inv in Hp as [=].
    + apply pf_sngl in Hp as [? [? [=]%pf_binds%binds_push_eq_inv]]; auto.
  - exists (typ_bnd T). assert (inert_typ (typ_bnd T)) as Hin. {
      apply ty_new_intro_p in H. apply* pfv_inert.
    }
    repeat split*. pick_fresh z. assert (z \notin L) as Hz by auto.
    specialize (H z Hz). assert (z # G) as Hz' by auto.
    constructor*. introv Hp.
    assert (exists W, G & x ~ typ_bnd T ⊢ trm_path q : W) as [W Hq]. {
      assert (inert (G & x ~ typ_bnd T)) as Hi' by eauto.
      pose proof (pf_sngl_to_lft Hi' Hp) as [-> | [b [c [bs' [bs'' [U [V [-> [Hl1 [Hl2 [Hr1 Hr2]]]]]]]]]]].
      { apply pf_binds in Hp as [=]%binds_push_eq_inv; auto. }
      assert (x; nil; P; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T)
        as Hdx%open_env_last_defs by admit; auto.
      destruct bs'' as [|bs'h bs't].
      + rewrite app_nil_l in *. inversions Hl1. inversions Hl2.
        eapply defs_typing_sngl_rhs. apply Hdx. rewrite* open_var_typ_eq.
      + rewrite <- app_comm_cons in Hl1. inversions Hl1.
        eapply defs_typing_rhs.
        apply Hdx.
        apply Hin.
        eauto.
        rewrite open_var_typ_eq in Hr1. apply Hr1.
        auto.
        apply Hl2.
        apply Hr2.
    }
    admit.
  - specialize (IHHv _ Hi Hwf eq_refl Hx). destruct_all. eexists; split*.
Qed.

(** Helper tactics for proving Preservation *)

Ltac lookup_eq :=
  match goal with
  | [Hl1: ?s ∋ ?t1,
     Hl2: ?s ∋ ?t2 |- _] =>
     apply (lookup_func Hl1) in Hl2; inversions Hl2
  end.

Ltac invert_red :=
  match goal with
  | [Hr: (_, _) |-> (_, _) |- _] => inversions Hr
  end.

Ltac solve_IH :=
  match goal with
  | [IH: well_typed _ _ ->
         inert _ ->
         wf_env _ ->
         forall t', (_, _) |-> (_, _) -> _,
       Wt: well_typed _ _,
       In: inert _,
       Wf: wf_env _,
       Hr: (_, _) |-> (_, ?t') |- _] =>
    specialize (IH Wt In Wf t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
    exists G'; repeat split; auto
  end.

Ltac solve_let :=
  invert_red; solve_IH; fresh_constructor; eauto; apply* weaken_rules.

(** [s: G]                  #<br>#
    [inert G]               #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [G ⊢ t: T]              #<br>#
    [―――――――――――――――――――]   #<br>#
    [exists G', inert G']        #<br>#
    [s': G, G']             #<br>#
    [G, G' ⊢ t': T]         *)
Lemma preservation_helper: forall G s t s' t' T,
    well_typed G s ->
    inert G ->
    wf_env G ->
    (s, t) |-> (s', t') ->
    G ⊢ t : T ->
    exists G', inert G' /\
          wf_env (G & G') /\
          well_typed (G & G') s' /\
          G & G' ⊢ t' : T.
Proof.
  introv Hwt Hi Hwf Hred Ht. gen t'.
  induction Ht; intros; try solve [invert_red].
  - Case "ty_all_elim".
    match goal with
    | [Hp: _ ⊢ trm_path _ : typ_all _ _ |- _] =>
        pose proof (canonical_forms_fun Hi Hwf Hwt Hp) as [L [T' [t [Hl [Hsub Hty]]]]];
        inversions Hred
    end.
    lookup_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    eapply renaming_typ; eauto. eauto. eauto.
  - Case "ty_let".
    destruct t; try solve [solve_let].
     + SCase "[t = (let x = v in u)] where v is a value".
      repeat invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (well_typed_notin_dom Hwt Hn) as Hng
      end.
      pose proof (val_typing Hi Hwf Ht Hng) as [V [Hv [Hs [Hin Hwf']]]].
      exists (x ~ V). repeat split; auto.
      ** rewrite <- concat_empty_l. constructor~.
      ** constructor~. apply (precise_to_general_v Hv).
      ** rewrite open_var_trm_eq. eapply renaming_fresh with (L:=L \u dom G \u \{x}). apply* ok_push.
         intros. apply* weaken_rules. apply ty_sub with (T:=V); auto. constructor*. apply* weaken_subtyp.
    + SCase "[t = (let x = p in u)] where a is p variable".
      repeat invert_red.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      apply* renaming_fresh.
  - Case "ty_sub".
    solve_IH.
    match goal with
    | [Hs: _ ⊢ _ <: _,
       Hg: _ & ?G' ⊢ _: _ |- _] =>
      apply weaken_subtyp with (G2:=G') in Hs;
      eauto
    end.
Qed.

(** ** Preservation Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [⊢ (s', t'): T]         *)
Theorem preservation : forall s s' t t' T,
    ⊢ (s, t) : T ->
    (s, t) |-> (s', t') ->
    ⊢ (s', t') : T.
Proof.
  introv Ht Hr. destruct Ht as [* Hi Hwf Hwt Ht].
  lets Hp: (preservation_helper Hwt Hi Hwf Hr Ht). destruct Hp as [G' [Hi' [Hwf' [Hwt' Ht']]]].
  apply sta_trm_typ_c with (G:=G & G'); auto. apply* inert_concat.
Qed.

(** * Progress *)

(** Helper tactic for proving progress *)
Ltac solve_let_prog :=
  match goal with
      | [IH: ⊢ (?s, ?t) : ?T ->
             inert _ ->
             wf_env _ ->
             well_typed _ _ -> _,
         Hi: inert _,
         Hwf: wf_env _,
         Hwt: well_typed _ _ |- _] =>
        assert (⊢ (s, t): T) as Hs by eauto;
        specialize (IH Hs Hi Hwf Hwt) as [IH | [s' [t' Hr]]];
        eauto; inversion IH
      end.

(** ** Progress Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [t] is in normal form   #<br>#
    or [exists s', t'] such that [(s, t) |-> (s', t')] *)
Theorem progress: forall s t T,
    ⊢ (s, t) : T ->
    norm_form t \/ exists s' t', (s, t) |-> (s', t').
Proof.
  introv Ht. inversion Ht as [G s' t' T' Hi Hwf Hwt HT]. subst.
  induction HT; unfold tvar; eauto.
  - Case "ty_all_elim".
    pose proof (canonical_forms_fun Hi Hwf Hwt HT1). destruct_all. right*.
  - Case "ty_let".
    right. destruct t; try solve [solve_let_prog].
    pick_fresh x. exists (s & x ~ v) (open_trm x u). auto.
Qed.


(** * Safety *)

Theorem safety_helper G t1 t2 s1 s2 T :
  G ⊢ t1 : T ->
  inert G ->
  wf_env G ->
  well_typed G s1 ->
  star red (s1, t1) (s2, t2) ->
  (exists s3 t3, (s2, t2) |-> (s3, t3)) \/ norm_form t2.
Proof.
  intros Ht Hi Hwf Hwt Hr. gen G T. dependent induction Hr; introv Hi Hwf Hwt; introv Ht.
  - assert (⊢ (s2, t2) : T) as Ht' by eauto.
    destruct (progress Ht'); eauto.
  - destruct b as [s12 t12]. specialize (IHHr _ _ _ _ eq_refl eq_refl).
    assert (⊢ (s1, t1) : T) as Ht1 by eauto.
    lets Hpr: (preservation Ht1 H). inversions Hpr.
    dependent induction H; eauto.
Qed.

Theorem safety t u s T :
  empty ⊢ t : T ->
  star red (empty, t) (s, u) ->
  (exists s' u', (s, u) |-> (s', u')) \/ norm_form u.
Proof.
  intros Ht Hr. apply* safety_helper. constructor.
Qed.

End Safety.
