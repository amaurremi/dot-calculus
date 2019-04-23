Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Sequences.
Require Import Binding CanonicalForms Definitions GeneralToTight InvertibleTyping Lookup Narrowing
        OperationalSemantics PreciseTyping RecordAndInertTypes ReplacementTyping
        Subenvironments Substitution TightTyping Weakening.

Close Scope string_scope.

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

(** The typing of a term with a store *)
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
  exists S V, G ⊢! pvar x : μ S ⪼ V.
Proof.
  intros Hi Hp. gen G x a T U. induction bs; introv Hi; introv Hp.
  - simpl in Hp. rewrite proj_rewrite in *. apply pf_invert_fld in Hp as [V Hp].
    pose proof (pf_bnd_T2 Hi Hp) as [S ->]. eauto.
  - pose proof (pf_invert_fld _ _ Hp) as [V Hp']. eauto.
Qed.

Lemma def_typing_sngl_rhs z bs G a t q :
  z; bs; G ⊢ {a := t} : {a ⦂ {{ q }}} ->
  exists T, G ⊢ trm_path q : T.
Proof.
  intros Hd. dependent induction Hd; eauto.
Qed.

Lemma defs_typing_sngl_rhs z bs G ds T a q :
  z; bs; G ⊢ ds :: T ->
  record_has T {a ⦂ {{ q }}} ->
  exists T, G ⊢ trm_path q : T.
Proof.
  induction 1; intros Hr.
  - destruct D; inversions Hr. inversions H. eauto.
  - inversions Hr; auto. inversions H5. inversions H0. eauto.
Qed.

Reserved Notation "x '==>' T '=' bs '=>' U" (at level 40, T at level 20).

Inductive lookup_fields_typ : var -> typ -> list trm_label -> typ -> Prop :=
| lft_empty : forall x T,
    x ==> T =nil=> T
| lft_cons : forall T bs U x a S,
    x ==> T =bs=> μ U ->
    record_has (open_typ_p (p_sel (avar_f x) bs) U) {a ⦂ S} ->
    x ==> T =a::bs=> S

where "x '==>' T '=' bs '=>' U" := (lookup_fields_typ x T bs U).

Hint Constructors lookup_fields_typ.

Lemma inert_record_has T p a U :
  inert_typ (μ T) ->
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
  x ==> T =bs=> μ U ->
  inert_typ (μ U).
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
  x ==> S =bs=> ∀(T) U ->
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
  x ==> S =bs=> {{ p }} ->
  x ==> S =cs++bs=> V ->
  cs = nil.
Proof.
  gen x S bs p V. induction cs; introv Hin Hl1 Hl2; auto.
  rewrite <- app_comm_cons in Hl2.
  inversions Hl2. specialize (IHcs _ _ _ _ _ Hin Hl1 H3) as ->.
  rewrite app_nil_l in H3.
  pose proof (lft_unique Hin Hl1 H3) as [= <-].
Qed.

Lemma lfs_defs_typing : forall cs z bs G ds T S U,
  z; bs; G ⊢ ds :: open_typ_p (p_sel (avar_f z) bs) T ->
  inert_typ S ->
  z ==> S =bs=> μ T ->
  z ==> S =cs++bs=> μ U ->
  exists ds', z; (cs++bs); G ⊢ ds' :: open_typ_p (p_sel (avar_f z) (cs++bs)) U.
Proof.
  induction cs; introv Hds Hin Hl1 Hl2.
  - rewrite app_nil_l in*. pose proof (lft_unique Hin Hl1 Hl2) as [= ->]. eauto.
  - rewrite <- app_comm_cons in *. inversions Hl2.
    specialize (IHcs _ _ _ _ _ _ _ Hds Hin Hl1 H3) as [ds' Hds'].
    pose proof (record_has_ty_defs Hds' H5) as [d [Hdh Hd]].
    inversions Hd. eauto.
Qed.

Lemma def_typing_rhs z bs G d a q U S cs T b V :
  z; bs; G ⊢ d : {b ⦂ V} ->
  inert_typ S ->
  z ==> S =bs=> μ T ->
  record_has (open_typ_p (p_sel (avar_f z) bs) T) {b ⦂ V} ->
  z ==> S =cs++b::bs=> μ U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++b::bs)) U) {a ⦂ {{ q }}} ->
  exists W, G ⊢ trm_path q : W.
Proof.
  intros Hds Hin Hl1 Hrd Hl2 Hr. inversions Hds.
  - Case "def_all"%string.
    eapply lft_cons in Hl1; eauto.
    pose proof (lft_typ_all_inv _ Hin Hl1 Hl2) as ->.
    rewrite app_nil_l in *.
    pose proof (lft_unique Hin Hl1 Hl2) as [=].
  - Case "def_new"%string.
    pose proof (ty_def_new _ _ eq_refl H6 H7).
    assert (z ==> S =b::bs=> μ T0) as Hl1'. {
        eapply lft_cons. eauto. eauto.
    }
    pose proof (lfs_defs_typing _ H7 Hin Hl1' Hl2) as [ds' Hds'].
    pose proof (record_has_ty_defs Hds' Hr) as [d [Hdh Hd]].
    inversions Hd. eauto.
  - Case "def_path"%string.
    eapply lft_cons in Hl1; eauto.
    pose proof (lft_typ_sngl_inv _ Hin Hl1 Hl2) as ->.
    rewrite app_nil_l in *.
    pose proof (lft_unique Hin Hl1 Hl2) as [=].
Qed.

Lemma defs_typing_rhs z bs G ds T a q U S cs T' b V :
  z; bs; G ⊢ ds :: T ->
  inert_typ S ->
  z ==> S =bs=> μ T' ->
  record_has (open_typ_p (p_sel (avar_f z) bs) T') {b ⦂ V} ->
  record_has T {b ⦂ V} ->
  z ==> S =cs++b::bs=> μ U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++b::bs)) U) {a ⦂ {{ q }}} ->
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
  inert (G & x ~ μ T) ->
  G & x ~ (μ T) ⊢! p_sel (avar_f x) bs : W ⪼ V ->
  bs = nil \/
  exists b c bs' bs'' U V,
    bs = c :: bs' /\
    bs = bs'' ++ b :: nil /\
    x ==> (μ T) =bs'=> (μ U) /\
    record_has (open_typ x T) {b ⦂ V} /\
    record_has (open_typ_p (p_sel (avar_f x) bs') U) {c ⦂ W}.
Proof.
  intros Hi Hp. dependent induction Hp; eauto.
  simpl_dot. right. specialize (IHHp _ _ _ _ Hi JMeq_refl eq_refl)
    as [-> | [b [c [bs' [bs'' [S [V [-> [Hl [Hl2 [Hr1 Hr2]]]]]]]]]]].
  - Case "pf_bind"%string.
    pose proof (pf_binds Hi Hp) as ->%binds_push_eq_inv. repeat eexists; eauto.
    simpl. rewrite app_nil_l. eauto. rewrite open_var_typ_eq. eapply pf_record_has_T; eauto.
    eapply pf_record_has_T; eauto.
  - Case "pf_fld"%string.
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
  - exists (∀(T) U). repeat split*. constructor; eauto. introv Hp.
    assert (binds x (∀(T) U) (G & x ~ ∀(T) U)) as Hb by auto. apply pf_bind in Hb; auto.
    destruct bs as [|b bs].
    + apply pf_binds in Hp; auto. apply binds_push_eq_inv in Hp as [=].
    + apply pf_sngl in Hp as [? [? [=]%pf_binds%binds_push_eq_inv]]; auto.
  - exists (μ T). assert (inert_typ (μ T)) as Hin. {
      apply ty_new_intro_p in H. apply* pfv_inert.
    }
    repeat split*. pick_fresh z. assert (z \notin L) as Hz by auto.
    specialize (H z Hz). assert (z # G) as Hz' by auto.
    constructor*. introv Hp.
    assert (exists W, G & x ~ (μ T) ⊢ trm_path q : W) as [W Hq]. {
      assert (inert (G & x ~ μ T)) as Hi' by eauto.
      pose proof (pf_sngl_to_lft Hi' Hp) as [-> | [b [c [bs' [bs'' [U [V [-> [Hl1 [Hl2 [Hr1 Hr2]]]]]]]]]]].
      { apply pf_binds in Hp as [=]%binds_push_eq_inv; auto. }
      assert (x; nil; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T)
        as Hdx%open_env_last_defs. {
        apply rename_defs with (x:=z); auto.
      }
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
      + auto.
    }
    apply pt3_exists in Hq as [? Hq'%pt2_exists]; auto.
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
  | [Hr: (_, _) |=> (_, _) |- _] => inversions Hr
  end.

Ltac solve_IH :=
  match goal with
  | [IH: well_typed _ _ ->
         inert _ ->
         wf_env _ ->
         forall t', (_, _) |=> (_, _) -> _,
       Wt: well_typed _ _,
       In: inert _,
       Wf: wf_env _,
       Hr: (_, _) |=> (_, ?t') |- _] =>
    specialize (IH Wt In Wf t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
    exists G'; repeat split; auto
  end.


Lemma inv_to_general G p T :
  G ⊢## p : T ->
  G ⊢ trm_path p : T.
Proof.
  induction 1;
    try match goal with
        | [H: _ ⊢# _ <: _ |- _] => apply tight_to_general in H
        end.
  - apply* precise_to_general3.
  - apply* ty_sub.
  - eapply ty_sub. eauto. constructor. apply* tight_to_general. auto.
  - eapply ty_sub. eauto. fresh_constructor.
  - eauto.
  - eauto.
  - eauto.
  - eapply ty_sub. eauto. apply rbnd in H2. eapply subtyp_sngl_pq. apply* precise_to_general.
    apply*  precise_to_general2. eauto.
  - eapply ty_sub. eauto. eapply subtyp_sngl_pq. apply* precise_to_general.
    apply*  precise_to_general2. eauto.
  - eapply ty_sub. eauto. eapply subtyp_sngl_pq. apply* precise_to_general.
    apply*  precise_to_general2. eauto.
Qed.

Lemma repl_to_general G p T :
  G ⊢// p : T ->
  G ⊢ trm_path p : T.
Proof.
  induction 1; auto.
  - apply* inv_to_general.
  - eapply ty_sub. eauto. eapply subtyp_sel2. apply* precise_to_general.
  - eapply ty_sub. eauto. apply rbnd in H2. eapply subtyp_sngl_qp. apply* precise_to_general.
    apply*  precise_to_general2. eauto.
  - eapply ty_sub. eauto. eapply subtyp_sngl_qp. apply* precise_to_general.
    apply*  precise_to_general2. eauto.
  - eapply ty_sub. eauto. eapply subtyp_sngl_qp. apply* precise_to_general.
    apply*  precise_to_general2. eauto.
Qed.

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
    (s, t) |=> (s', t') ->
    G ⊢ t : T ->
    exists G', inert G' /\
          wf_env (G & G') /\
          well_typed (G & G') s' /\
          G & G' ⊢ t' : T.
Proof.
  introv Hwt Hi Hwf Hred Ht. gen t'.
  induction Ht; intros; try solve [invert_red].
  - Case "ty_all_elim"%string.
    match goal with
    | [Hp: _ ⊢ trm_path _ : ∀(_) _ |- _] =>
        pose proof (canonical_forms_fun Hi Hwf Hwt Hp) as [L [T' [t [Hl [Hsub Hty]]]]];
        inversions Hred
    end.
    lookup_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    eapply renaming_typ; eauto. eauto. eauto.
  - Case "ty_let"%string.
    destruct t; try solve [solve_let].
     + SCase "[t = (let x = v in u)] where v is a value"%string.
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
         intros. apply* weaken_rules. apply ty_sub with (T:=V); auto. apply* weaken_subtyp.
    + SCase "[t = (let x = p in u)] where a is p variable"%string.
      repeat invert_red.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      apply* renaming_fresh.
  - Case "ty_sub"%string.
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
    (s, t) |=> (s', t') ->
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
    norm_form t \/ exists s' t', (s, t) |=> (s', t').
Proof.
  introv Ht. inversion Ht as [G s' t' T' Hi Hwf Hwt HT]. subst.
  induction HT; eauto.
  - Case "ty_all_elim"%string.
    pose proof (canonical_forms_fun Hi Hwf Hwt HT1). destruct_all. right*.
  - Case "ty_let"%string.
    right. destruct t; try solve [solve_let_prog].
    pick_fresh x. exists (s & x ~ v) (open_trm x u). auto.
Qed.


(** * Safety *)

Theorem safety_helper G t1 t2 s1 s2 T :
  G ⊢ t1 : T ->
  inert G ->
  wf_env G ->
  well_typed G s1 ->
  star red' (s1, t1) (s2, t2) ->
  (exists s3 t3 G3, (s2, t2) |=> (s3, t3) /\ G3 ⊢ t3 : T /\ well_typed G3 s3) \/
  (exists G2, norm_form t2 /\ G2 ⊢ t2 : T /\ well_typed G2 s2).
Proof.
  intros Ht Hi Hwf Hwt Hr. gen G T. dependent induction Hr; introv Hi Hwf Hwt; introv Ht.
  - assert (⊢ (s2, t2) : T) as Ht' by eauto. apply progress in Ht'; destruct_all; eauto.
    left. exists x x0. pose proof (preservation_helper Hwt Hi Hwf H Ht) as [G' [_ [_ [Hwt' Ht']]]].
    exists (G & G'). repeat split*.
  - destruct b as [s12 t12]. specialize (IHHr _ _ _ _ eq_refl eq_refl).
    assert (⊢ (s1, t1) : T) as Ht1 by eauto.
    lets Hpr: (preservation Ht1 H). inversions Hpr.
    dependent induction H; eauto.
Qed.

Definition diverges := infseq red'.

Theorem safety t T :
  empty ⊢ t : T ->
  diverges (empty, t) \/ (exists s u G, star red' (empty, t) (s, u) /\ norm_form u /\ G ⊢ u : T /\ well_typed G s).
Proof.
  intros Ht.
  pose proof (infseq_or_finseq red' (empty, t)) as [? | [[s u] [Hr Hn]]]; eauto.
  right. epose proof (safety_helper Ht inert_empty wfe_empty well_typed_empty Hr)
    as [[s' [t' [G' [Hr' [Ht' Hwt]]]]] | [G [Hn' [Ht' Hwt]]]]; try solve [constructor]; eauto.
  - false* Hn.
  - repeat eexists; eauto.
Qed.

End Safety.

Section PathSafety.

Lemma lookup_step_pres G p T q s :
  inert G ->
  wf_env G ->
  well_typed G s ->
  G ⊢!!! p : T ->
  s ⟦ p ⟼ defp q ⟧ ->
  exists U, G ⊢!!! q : U.
Proof.
  intros Hi Hwf Hwt Hp Hl.
  apply pt2_exists in Hp as [U Hp].
  pose proof (named_lookup_step Hl) as [x [bs Heq]].
  pose proof (lookup_step_preservation_prec2 Hi Hwf Hwt Hl Hp Heq)
    as [[? [? [? [[=] ?]]]] |
        [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
         [r' [r [G1 [G2 [pT [S [[= ->] [-> [-> [[-> | Hr] [-> | Hr']]]]]]]]]]]]].
  - apply sngl_typed2 in Hp as [U Hr]; eauto.
  - eexists. do 2 apply* pt3_weaken. apply inert_ok in Hi.
    apply* ok_concat_inv_l.
  - apply sngl_typed3 in Hr as [U Hr]; eauto.
    eexists. do 2 apply* pt3_weaken. apply inert_ok in Hi.
    apply* ok_concat_inv_l. do 2 apply* inert_prefix.
  - eexists. do 2 apply* pt3_weaken. apply inert_ok in Hi.
    apply* ok_concat_inv_l.
Qed.

Lemma lookup_pres G p T q s :
  inert G ->
  wf_env G ->
  well_typed G s ->
  G ⊢!!! p : T ->
  s ⟦ defp p ⟼* defp q ⟧ ->
  exists U, G ⊢!!! q : U.
Proof.
  intros Hi Hwf Hwt Hp Hl. gen T. dependent induction Hl; introv Hp; eauto.
  destruct b.
  - pose proof (lookup_step_pres Hi Hwf Hwt Hp H) as [U Hq]. eauto.
  - apply lookup_val_inv in Hl as [=].
Qed.

Lemma path_safety G p T s :
  inert G ->
  wf_env G ->
  well_typed G s ->
  G ⊢ trm_path p : T ->
  (exists v, s ∋ (p, v)) \/ infseq (lookup_step s) (defp p).
Proof.
  intros Hi Hwf Hwt Hp.
  proof_recipe. apply repl_prec_exists in Hp as [U Hp].
  pose proof (infseq_or_finseq (lookup_step s) (defp p)) as [? | [t [Hl Hirr]]]; eauto.
  left. destruct t; eauto.
  pose proof (lookup_pres Hi Hwf Hwt Hp Hl) as [S Hq].
  pose proof (typ_to_lookup3 Hi Hwf Hwt Hq) as [t Hl'].
  false* Hirr.
Qed.

End PathSafety.
