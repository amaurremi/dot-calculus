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

Lemma def_typing_rhs z bs P G a t q :
      z; bs; P; G ⊢ {a := t} : {a ⦂ typ_sngl q} ->
      exists T, G ⊢ trm_path q : T.
Proof.
  intros Hd. dependent induction Hd; eauto.
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

Lemma pf_to_lft G x bs T S U :
  inert (G & x ~ T) ->
  G & x ~ T ⊢! p_sel (avar_f x) bs : S ⪼ U ->
  x ==> T =bs=> S.
Proof.
  intros Hi Hp. dependent induction Hp; eauto.
  - apply binds_push_eq_inv in H0 as ->. auto.
  - simpl_dot. specialize (IHHp _ _ _ _ Hi JMeq_refl eq_refl).
    pose proof (pf_bnd_T2 Hi Hp) as [V ->].
    econstructor; eauto. apply* pf_record_has_U.
Qed.

Lemma lft_inert x T bs U :
  inert_typ T ->
  x ==> T =bs=> typ_bnd U ->
  record_type U.
Proof. Admitted.

Lemma lft_unique x S bs T U :
  inert_typ S ->
  x ==> S =bs=> T ->
  x ==> S =bs=> U ->
  T = U.
Proof.
  intros Hi Hl1. gen U. induction Hl1; introv Hl2.
  - inversion Hl2; auto.
  - inversions Hl2. specialize (IHHl1 Hi _ H4) as [= ->].
    pose proof (lft_inert Hi Hl1).
    eapply unique_rcd_trm. apply* open_record_type_p. eauto. eauto.
Qed.

Lemma lft_typ_dec_inv x S bs A T U cs V :
  inert_typ S ->
  x ==> S =bs=> typ_bnd (typ_rcd {A >: T <: U}) ->
  x ==> S =cs++bs=> V ->
  cs = nil.
Proof.
  gen x S bs A T U V. induction cs; introv Hin Hl1 Hl2; auto.
  rewrite <- app_comm_cons in Hl2.
  inversions Hl2. specialize (IHcs _ _ _ _ _ _ _ Hin Hl1 H3) as ->.
  rewrite app_nil_l in H3.
  pose proof (lft_unique Hin Hl1 H3) as [= <-].
  inversions H5.
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

Lemma lft_trm_dec_inv x S bs T cs V :
  inert_typ S ->
  x ==> S =bs=> T ->
  x ==> S =cs++bs=> V ->
                 (cs = nil /\ T = V) \/
                 (exists a bs, cs = (a :: bs)%list /\ exists U, T = typ_bnd U).
Proof.
  gen x S bs T V. induction cs; introv Hi Hl1 Hl2; auto.
  - rewrite app_nil_l in *. left. split*. eapply lft_unique; eauto.
  - rewrite <- app_comm_cons in *. inversions Hl2.
    specialize (IHcs _ _ _ _ _ Hi Hl1 H3) as [[-> ->] | [b [ds [-> [W ->]]]]].
    + rewrite app_nil_l in *. clear H3. right. repeat eexists.
    + rewrite <- app_comm_cons in *. inversions H3. right. repeat eexists.
Qed.

Lemma lft_fld_unique S x a T cs bs U :
  inert_typ S ->
  x ==> S =bs=> typ_bnd (typ_rcd {a ⦂ T}) ->
  x ==> S =cs++bs=> U ->
  cs = nil \/ exists cs', cs = cs' ++ a :: nil.
Proof.
  intros Hin Hl1 Hl2. gen S x a T bs U. induction cs; introv Hin; introv Hl1; introv Hl2; eauto.
  rewrite <- app_comm_cons in *. inversions Hl2.
  specialize (IHcs _ Hin _ _ _ _ Hl1 _ H3) as [-> | [cs' ->]]; eauto.
  - right. repeat eexists. rewrite app_nil_l in *.
    pose proof (lft_unique Hin Hl1 H3) as [= <-]. inversion* H5.
  - right. exists (a :: cs'). rewrite* app_comm_cons.
Qed.

Lemma app_nil_cons {A} (cs bs : list A) c : (cs ++ c :: nil) ++ bs = cs ++ c :: bs.
Proof.
  gen c bs. induction cs; introv; auto.
  rewrite <- app_comm_cons. rewrite <- app_comm_cons. rewrite IHcs. auto.
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

(*Lemma defs_typing_rhs z bs P G d D a q U S cs T :
  z; bs; P; G ⊢ d : open_dec_p (p_sel (avar_f z) bs) D ->
  inert_typ S ->
  z ==> S =bs=> typ_bnd T ->
  record_has T D ->
  z ==> S =cs++bs=> typ_bnd U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++bs)) U) {a ⦂ typ_sngl q} ->
  exists W, G ⊢ trm_path q : W.
Proof.
  intros Hds Hin Hl1 Hl2 Hr. inversions Hds.
  - destruct D; inversions H.
    + Case "def_typ".
      destruct T; inversions x. destruct d; inversions H0.
      pose proof (lft_typ_dec_inv _ Hin Hl1 Hl2) as ->.
      rewrite app_nil_l in Hl2.
      pose proof (lft_unique Hin Hl1 Hl2) as [= <-].
      inversion Hr.
    + Case "def_all".
      destruct T; inversions x. destruct d; inversions H0.
      pose proof (lft_trm_dec_inv _ Hin Hl1 Hl2) as [[-> [= <-]] | [b [ds [-> [W [= <-]]]]]].
      * rewrite app_nil_l in *. destruct t2; inversions H2. inversion Hr.
      * destruct t2; inversions H2.
        pose proof (lft_fld_unique _ Hin Hl1 Hl2) as [[=] | [cs Heq]].
        rewrite Heq in Hl2.
        eapply lft_cons in Hl1; try solve [constructor].
        rewrite app_nil_cons in Hl2.
        pose proof (lft_typ_all_inv _ Hin Hl1 Hl2) as ->.
        rewrite app_nil_l in *.
        pose proof (lft_unique Hin Hl1 Hl2) as [=].
    + Case "def_new".
      destruct T; inversions x. destruct d; inversions H0.
      pose proof (ty_def_new _ eq_refl H8 H9).
      destruct cs as [|c cs].
      * rewrite app_nil_l in *.  pose proof (lft_unique Hin Hl1 Hl2) as [= <-].
        destruct t1; inversions H2.
        inversion Hr.
      * destruct t1; inversions H2.
        rename x0 into x. rename t0 into b. rename t1 into T.
        assert (x ==> S =b::bs=> open_typ_p (p_sel (avar_f x) bs) (typ_bnd T)) as Hl1'. {
          eapply lft_cons. eauto. constructor*.
        }
        unfold open_typ_p in Hl1'. simpl in Hl1'.
        pose proof (lft_fld_unique _ Hin Hl1 Hl2) as [[=] | [es Heq]].
        rewrite Heq in *. rewrite app_nil_cons in Hl2, Hr.
        pose proof (lfs_defs_typing _ H9 Hin Hl1' Hl2) as [ds' Hds'].
        pose proof (record_has_ty_defs Hds' Hr) as [d [Hdh Hd]].
        inversions Hd. eauto.
    + Case "def_path".
      pose proof (lft_trm_dec_inv _ Hin Hl1 Hl2) as [[-> [= <-]] | [b [ds [-> [W [= <-]]]]]].
      * rewrite app_nil_l in *.
        destruct T; inversions x. destruct d; inversions H0. destruct t1; inversions H4.
        unfold open_typ_p in Hr. simpl in Hr. inversions Hr. rewrite <- H0. eauto.
      * destruct T; inversions x. destruct d; inversions H0. destruct t1; inversions H4.
        pose proof (lft_fld_unique _ Hin Hl1 Hl2) as [[=] | [cs Heq]].
        rewrite Heq in Hl2.
        eapply lft_cons in Hl1; try solve [constructor].
        rewrite app_nil_cons in Hl2.
        pose proof (lft_typ_sngl_inv _ Hin Hl1 Hl2) as ->.
        rewrite app_nil_l in *.
        pose proof (lft_unique Hin Hl1 Hl2) as [=].
  - admit.
Qed.*)

Lemma defs_typing_rhs z bs P G ds T a q U S cs :
  z; bs; P; G ⊢ ds :: open_typ_p (p_sel (avar_f z) bs) T ->
  inert_typ S ->
  z ==> S =bs=> typ_bnd T ->
  z ==> S =cs++bs=> typ_bnd U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++bs)) U) {a ⦂ typ_sngl q} ->
  exists T, G ⊢ trm_path q : T.
Proof.
  intros Hds Hin Hl1 Hl2 Hr.
  gen S a q U cs. dependent induction Hds; introv Hin Hl1; introv Hl2 Hr.
  - destruct D; inversions H.
    + Case "def_typ".
      destruct T; inversions x. destruct d; inversions H0.
      pose proof (lft_typ_dec_inv _ Hin Hl1 Hl2) as ->.
      rewrite app_nil_l in Hl2.
      pose proof (lft_unique Hin Hl1 Hl2) as [= <-].
      inversion Hr.
    + Case "def_all".
      destruct T; inversions x. destruct d; inversions H0.
      pose proof (lft_trm_dec_inv _ Hin Hl1 Hl2) as [[-> [= <-]] | [b [ds [-> [W [= <-]]]]]].
      * rewrite app_nil_l in *. destruct t2; inversions H2. inversion Hr.
      * destruct t2; inversions H2.
        pose proof (lft_fld_unique _ Hin Hl1 Hl2) as [[=] | [cs Heq]].
        rewrite Heq in Hl2.
        eapply lft_cons in Hl1; try solve [constructor].
        rewrite app_nil_cons in Hl2.
        pose proof (lft_typ_all_inv _ Hin Hl1 Hl2) as ->.
        rewrite app_nil_l in *.
        pose proof (lft_unique Hin Hl1 Hl2) as [=].
    + Case "def_new".
      destruct T; inversions x. destruct d; inversions H0.
      pose proof (ty_def_new _ eq_refl H8 H9).
      destruct cs as [|c cs].
      * rewrite app_nil_l in *.  pose proof (lft_unique Hin Hl1 Hl2) as [= <-].
        destruct t1; inversions H2.
        inversion Hr.
      * destruct t1; inversions H2.
        rename x0 into x. rename t0 into b. rename t1 into T.
        assert (x ==> S =b::bs=> open_typ_p (p_sel (avar_f x) bs) (typ_bnd T)) as Hl1'. {
          eapply lft_cons. eauto. constructor*.
        }
        unfold open_typ_p in Hl1'. simpl in Hl1'.
        pose proof (lft_fld_unique _ Hin Hl1 Hl2) as [[=] | [es Heq]].
        rewrite Heq in *. rewrite app_nil_cons in Hl2, Hr.
        pose proof (lfs_defs_typing _ H9 Hin Hl1' Hl2) as [ds' Hds'].
        pose proof (record_has_ty_defs Hds' Hr) as [d [Hdh Hd]].
        inversions Hd. eauto.
    + Case "def_path".
      pose proof (lft_trm_dec_inv _ Hin Hl1 Hl2) as [[-> [= <-]] | [b [ds [-> [W [= <-]]]]]].
      * rewrite app_nil_l in *.
        destruct T; inversions x. destruct d; inversions H0. destruct t1; inversions H4.
        unfold open_typ_p in Hr. simpl in Hr. inversions Hr. rewrite <- H0. eauto.
      * destruct T; inversions x. destruct d; inversions H0. destruct t1; inversions H4.
        pose proof (lft_fld_unique _ Hin Hl1 Hl2) as [[=] | [cs Heq]].
        rewrite Heq in Hl2.
        eapply lft_cons in Hl1; try solve [constructor].
        rewrite app_nil_cons in Hl2.
        pose proof (lft_typ_sngl_inv _ Hin Hl1 Hl2) as ->.
        rewrite app_nil_l in *.
        pose proof (lft_unique Hin Hl1 Hl2) as [=].
  - admit.
Qed.

Lemma defs_typing_rhs z bs P G ds T a q :
  z; bs; P; G ⊢ ds :: T ->
  record_has T {a ⦂ typ_sngl q} ->
  exists T, G ⊢ trm_path q : T.
Proof.
  induction 1; intros Hr.
  - destruct D; inversions Hr. inversions H. inversion H8. apply* def_typing_rhs.
  - inversions Hr; eauto. inversions H5. inversions H0.
    + inversion H10.
    + eauto.
Qed.

Inductive wf_env_gen : ctx -> Prop :=
  | wfe_empty : wf_env_gen empty
  | wfe_push : forall (G : ctx) (x : var) (T : typ),
               wf_env_gen G ->
               x # G ->
               (forall (bs : fields) (q : path),
                G & x ~ T ⊢! p_sel (avar_f x) bs : typ_sngl q ⪼ typ_sngl q -> exists U, G & x ~ T ⊢ trm_path q : U) ->
               wf_env_gen (G & x ~ T).

Hint Constructors wf_env_gen.

Lemma wf_env_to_wf_gen G :
  wf_env G -> wf_env_gen G.
Proof.
  induction 1; auto.
  constructor*. introv Hp. specialize (H1 _ _ Hp) as [U Hq]. eexists. apply* precise_to_general2.
Qed.

Lemma val_typing G x v T :
  inert G ->
  wf_env G ->
  G ⊢ trm_val v : T ->
  x # G ->
  exists T', G ⊢!v v : T' /\
        G ⊢ T' <: T /\
        wf_env (G & x ~ T').
Proof.
  intros Hi Hwf Hv Hx. dependent induction Hv; eauto.
  - exists (typ_all T U). repeat split*. constructor; eauto. introv Hp.
    assert (binds x (typ_all T U) (G & x ~ typ_all T U)) as Hb by auto. apply pf_bind in Hb; auto.
    destruct bs as [|b bs].
    + apply pf_binds in Hp; auto. apply binds_push_eq_inv in Hp as [=].
    + apply pf_sngl in Hp as [? [? [=]%pf_binds%binds_push_eq_inv]]; auto.
  - exists (typ_bnd T). repeat split*. pick_fresh z. assert (z \notin L) as Hz by auto.
    specialize (H z Hz). assert (z # G) as Hz' by auto.
    assert (wf_env_gen (G & z ~ open_typ z T)) as Hwfgen. {
      constructor*. apply* wf_env_to_wf_gen.
      introv Hp.

    admit.
  - specialize (IHHv _ Hi Hwf eq_refl Hx). destruct_all. eauto.
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
      pose proof (val_typing Hi Hwf Ht Hng) as [V [Hv [Hs Hwf']]].
      exists (x ~ V). repeat split; auto.
      ** rewrite <- concat_empty_l. constructor~. eapply pfv_inert; eauto.
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
