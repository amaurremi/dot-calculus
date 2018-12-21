(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Sequences.
Require Import Coq.Program.Equality List.
Require Import Definitions Binding RecordAndInertTypes Replacement Subenvironments Narrowing.
Require Export PreciseFlow.

Inductive precise_typing2: ctx -> path -> typ -> Prop :=
| pt2: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢!! p: U
| pt2_sngl_trans : forall G p q a U,
    G ⊢!! p : typ_sngl q ->
    G ⊢!! q•a : U ->
    G ⊢!! p•a : typ_sngl q•a
where "G '⊢!!' p ':' T" := (precise_typing2 G p T).

Inductive precise_typing3: ctx -> path -> typ -> Prop :=
| pt3: forall G p T,
    G ⊢!! p : T ->
    G ⊢!!! p: T
| pt3_sngl_trans : forall G p q T,
    G ⊢!! p : typ_sngl q ->
    G ⊢!!! q : T ->
    G ⊢!!! p : T
where "G '⊢!!!' p ':' T" := (precise_typing3 G p T).

Hint Constructors precise_typing2 precise_typing3.

Lemma precise_to_general2: forall G p T,
    G ⊢!! p: T ->
    G ⊢ trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto using precise_to_general.
Qed.

Lemma precise_to_general3: forall G p T,
    G ⊢!!! p: T ->
    G ⊢ trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto using precise_to_general2.
Qed.

Lemma pf2_and_destruct1: forall G p T U,
    G ⊢!! p: typ_and T U ->
    G ⊢!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pf2_and_destruct2: forall G p T U,
    G ⊢!! p: typ_and T U ->
    G ⊢!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pf3_and_destruct1: forall G p T U,
    G ⊢!!! p: typ_and T U ->
    G ⊢!!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pf2_and_destruct1.
Qed.

Lemma pf3_and_destruct2: forall G p T U,
    G ⊢!!! p: typ_and T U ->
    G ⊢!!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pf2_and_destruct2.
Qed.

Lemma pf2_inertsngl : forall G p T,
    inert G ->
    G ⊢!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf.
  - apply* pf_inertsngl.
  - left. right. eexists. eauto.
Qed.

Lemma pf3_inertsngl : forall G p T,
    inert G ->
    G ⊢!!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf; eauto;
  apply* pf2_inertsngl.
Qed.

Lemma pt2_psel: forall G p q A,
    inert G ->
    G ⊢!! p : typ_path q A -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pf_psel.
Qed.

Lemma pt3_psel: forall G p q A,
    inert G ->
    G ⊢!!! p : typ_path q A -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pt2_psel.
Qed.

Lemma pt3_trans: forall G p q a U,
    G ⊢!! p : typ_sngl q ->
    G ⊢!!! q•a : U ->
    G ⊢!!! p•a : U.
Proof.
  introv Hp Hq. gen p. dependent induction Hq; introv Hp; eauto.
Qed.

Lemma pt3_trans2: forall G p q a U,
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q•a : U ->
    G ⊢!!! p•a : U.
Proof.
  introv Hp Hq. gen a U. dependent induction Hp; introv Hq.
  - apply* pt3_trans.
  - specialize (IHHp _ eq_refl _ _ Hq). apply* pt3_trans.
Qed.

Lemma pt3_field_elim: forall G p a T,
    G ⊢!!! p : typ_rcd { a ⦂ T } ->
    G ⊢!!! p•a : T.
Proof.
  introv Hp. dependent induction Hp.
  - dependent induction H; eauto.
  - specialize (IHHp _ _ eq_refl).
    gen p. dependent induction IHHp; introv Hpq; eauto.
Qed.

Lemma path_elim_prec: forall G p q a T,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! q•a : T ->
    G ⊢!!! p•a : typ_sngl q•a.
Proof.
  introv Hi Hp Hq.
  gen a T. dependent induction Hp; introv Hq.
  - inversion* Hq.
  - specialize (IHHp _ Hi eq_refl _ _ Hq). apply* pt3_trans.
Qed.

Lemma pf_pt2: forall G p T U V,
    inert G ->
    G ⊢! p: T ⪼ U ->
    G ⊢!! p: V ->
    inert_sngl V ->
    T = V.
Proof.
  introv Hi Hp1 Hp2 His. gen T U. induction Hp2; introv Hp1.
  - lets Heq: (pf_T_unique Hi Hp1 H). subst. destruct His.
    * destruct H0. apply* pf_forall_T. apply* pf_bnd_T.
    * inversions H0. destruct_all. apply* pf_sngl_T.
  - destruct (pf_path_sel _ _ Hi Hp1) as [V [W Hp]].
    lets Hpa: (pf_fld Hp). lets Heq: (pf_T_unique Hi Hp1 Hpa). subst.
    assert (inert_sngl (typ_sngl q)) as His'. { right. eexists. auto. }
    specialize (IHHp2_1 Hi His' _ _ Hp). inversion IHHp2_1.
Qed.

Lemma pf_pt2_sngl: forall G p T U q,
    inert G ->
    G ⊢! p: T ⪼ U ->
    G ⊢!! p: typ_sngl q ->
    T = typ_sngl q.
Proof.
  introv Hi Hp1 Hp2. apply* pf_pt2. right. eexists. auto.
Qed.

Lemma field_elim_q0: forall G p q a T,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢!! p•a : T ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen q.
  dependent induction Hpa; introv Hp; eauto.
  - dependent induction H; try simpl_dot; eauto.
    lets Heq: (pf_T_unique Hi Hp H). subst.
    apply pf_sngl_U in H. inversion H.
  - clear IHHpa1 IHHpa2. simpl_dot.
    lets Heq: (pf_pt2_sngl Hi Hp Hpa1). inversion* Heq.
Qed.

Lemma field_elim_q0': forall G p q a T T',
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢! p•a : T ⪼ T' ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen q.
  dependent induction Hpa; introv Hp; try simpl_dot; eauto.
  lets Hp2: (pf_pt2_sngl Hi Hpa Hp). subst.
  apply pf_sngl_U in Hpa. inversion Hpa.
Qed.

Lemma pf_pt2_sngl_invert G p q a T U :
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢! p•a : T ⪼ U ->
    False.
Proof.
  intros Hi Hp Hpf.
  assert (exists V S, G ⊢! p: V ⪼ S) as [V [S Hpvs]]. {
      dependent induction Hpf; try simpl_dot; eauto.
    }
  lets ->: (pf_pt2_sngl Hi Hpvs Hp). clear Hp.
  dependent induction Hpf; try simpl_dot; eauto.
  lets Heq: (pf_T_unique Hi Hpvs Hpf). subst. apply pf_sngl_U in Hpf as[=].
Qed.

Lemma pt2_sngl_exists: forall G p q T,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢!! p: T ->
    exists q', T = typ_sngl q'.
Proof.
  introv Hi Hp Ht. gen T. dependent induction Hp; introv Ht; eauto.
  - lets ->: (pf_sngl_T Hi H). dependent induction Ht; eauto.
    lets Heq: (pf_T_unique Hi H H0). subst. eauto using pf_sngl_U.
  - dependent induction Ht; eauto.
    lets Contra: (pf_pt2_sngl_invert _ Hi Hp1 H). inversion Contra.
Qed.

Lemma pt2_sngl_unique: forall G p q1 q2,
    inert G ->
    G ⊢!! p: typ_sngl q1 ->
    G ⊢!! p: typ_sngl q2 ->
    q1 = q2.
Proof.
  introv Hi Hp. gen q2. dependent induction Hp; introv Ht; eauto.
  - lets ->: (pf_sngl_T Hi H). dependent induction Ht; eauto.
    * lets Heq: (pf_T_unique Hi H H0). subst.
      apply pf_sngl_U in H0 as [=]. auto.
    * lets Contra: (pf_pt2_sngl_invert _ Hi Ht1 H). inversion Contra.
  - specialize (IHHp1 _ Hi eq_refl). gen q U.
    dependent induction Ht; introv Hpq IH1; introv Hqa IH2.
    * lets Contra: (pf_pt2_sngl_invert _ Hi Hpq H). inversion Contra.
    * simpl_dot. f_equal. eauto.
Qed.

Lemma pt2_sngl_unique' G p q T :
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢!! p: T ->
    T = typ_sngl q.
Proof.
  introv Hi Hp Hpt. destruct (pt2_sngl_exists Hi Hp Hpt) as [q' ->]. f_equal.
  eauto using pt2_sngl_unique.
Qed.

Lemma field_elim_q: forall G p q a T,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢!! p•a : T ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen a T. dependent induction Hp; introv Hpa.
  - lets Heq: (pf_sngl_T Hi H). subst. apply* field_elim_q0.
  - clear IHHp1 IHHp2.
    gen q0 U. dependent induction Hpa; introv Hp; introv Hq0.
    * apply* field_elim_q0'.
    * unfold sel_fields in x. destruct p0, p. inversions x.
      lets Hxbs: (pt2_sngl_trans _ Hp Hq0).
      assert (inert_sngl (typ_sngl q)) as His. {
        right. eexists. eauto.
      }
      simpl in *.
      lets Hu: (pt2_sngl_unique Hi Hpa1 Hxbs).
      inversions Hu. eauto.
Qed.

Lemma field_elim_q2: forall G p q a T,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!! p•a : T ->
    exists U, G ⊢!!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen a T. dependent induction Hp; introv Hpa.
  - destruct* (field_elim_q _ Hi H Hpa).
  - specialize (IHHp _ Hi eq_refl).
    destruct (field_elim_q _ Hi H Hpa) as [V Hqa]. apply* IHHp.
Qed.

Lemma field_elim_q3: forall G p q a T,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! p•a : T ->
    exists U, G ⊢!!! q•a: U.
Proof.
  introv Hi Hp Hpa.
  gen q. dependent induction Hpa; introv Hp.
  - gen a T. dependent induction Hp; introv Hpa;
               destruct* (field_elim_q _ Hi H Hpa).
  - clear IHHpa Hpa T. gen a q. dependent induction Hp; introv Hpa.
    * destruct* (field_elim_q _ Hi H Hpa).
    * lets Hp': (pt3_sngl_trans H Hp). apply* field_elim_q2.
Qed.

Lemma pt3_field_elim_p: forall G p q a U,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! p • a : U ->
    G ⊢!!! p • a : typ_sngl q • a.
Proof.
  introv Hi Hpq Hpa. destruct (field_elim_q3 _ Hi Hpq Hpa) as [T Hqa].
  apply* path_elim_prec.
Qed.

Lemma pt2_backtrack : forall G p a T,
    G ⊢!! p • a : T ->
    exists U, G ⊢!! p : U.
Proof.
  introv Hp. dependent induction Hp; eauto.
  - dependent induction H; try simpl_dot; eauto.
  - simpl_dot. eauto.
Qed.

Lemma pt3_backtrack : forall G p a T,
    G ⊢!!! p • a : T ->
    exists U, G ⊢!!! p : U.
Proof.
  introv Hp. dependent induction Hp;
               apply pt2_backtrack in H; destruct_all; eauto.
Qed.

Lemma pt3_sngl_trans3: forall G p q T,
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! q: T ->
    G ⊢!!! p : T.
Proof.
  introv Hp Hq. gen T. dependent induction Hp; introv Hq; eauto.
Qed.

Lemma pt3_field_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q••bs : T ->
    G ⊢!!! p••bs : typ_sngl q••bs.
Proof.
  introv Hi Hp Hq. gen T q. induction bs; introv Hp Hq;
                              unfolds sel_fields; destruct q, p; simpls; auto.
  rewrite proj_rewrite in *.
  destruct (pt3_backtrack _ _ Hq) as [U Hb].
  specialize (IHbs _ _ Hp Hb). rewrite proj_rewrite. apply* path_elim_prec.
Qed.

Lemma pt3_field_trans': forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q••bs : T ->
    G ⊢!!! p••bs : T.
Proof.
  introv Hi Hp1 Hp2. gen p q T.
  induction bs; introv Hp1; introv Hp2; unfolds sel_fields; destruct q, p; simpls.
  - apply* pt3_sngl_trans3.
  - rewrite proj_rewrite in *.
    destruct (pt3_backtrack _ _ Hp2) as [S Hb].
    lets Hh: (pt3_field_trans _ Hi Hp1 Hb).
    apply* pt3_sngl_trans3. apply* path_elim_prec.
Qed.

Lemma sngl_typed : forall G p q,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    exists T, G ⊢! q: T ⪼ T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto; try solve [apply pf_sngl_U in Hp; inversion Hp].
  - apply binds_inert in H0. inversion H0. auto.
  - destruct (pf_bnd_T2 Hi Hp) as [U Heq]. subst. destruct (pf_rec_rcd_U Hi Hp).
    * inversion H.
    * inversions H. inversions H0. clear IHHp.

      admit.
      (* here we change the def of inertness and get what we want? *)
Admitted.

Lemma sngl_typed2 : forall G p q,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    exists T, G ⊢!! q: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. lets Heq: (pf_sngl_T Hi H). subst.
  destruct* (sngl_typed Hi H).
Qed.

Lemma sngl_typed3 : forall G p q,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    exists T, G ⊢!!! q: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct* (sngl_typed2 Hi H).
Qed.

Lemma pt3_trans_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! p••bs : T ->
    G ⊢!!! p••bs : typ_sngl q••bs.
Proof.
  introv Hi Hp Hpbs. gen p q T.
  induction bs; introv Hp; introv Hpbs; unfolds sel_fields; destruct p, q; simpls; auto.
  repeat rewrite proj_rewrite in *. apply* pt3_field_elim_p.
  specialize (IHbs _ _ Hp). apply pt3_backtrack in Hpbs. destruct_all. eauto.
Qed.

Lemma pf_sngl_fld_elim: forall G p q a T U,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢! p•a : T ⪼ U ->
    False.
Proof.
  introv Hi Hp Hpa. dependent induction Hpa; try simpl_dot; eauto.
  lets Hu: (pf_T_unique Hi Hpa Hp). subst. apply pf_sngl_U in Hpa. false*.
Qed.

Lemma pf_sngl_flds_elim: forall G p q T U bs,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢! p••bs : T ⪼ U ->
    bs = nil.
Proof.
  introv Hi Hp Hpbs. gen T U. induction bs; introv Hpbs. auto.
  assert (exists T' U', G ⊢! p •• bs : T' ⪼ U') as [T' [U' Hpbs']]. {
    clear IHbs Hp. dependent induction Hpbs; try simpl_dot; eauto.
    unfolds sel_field, sel_fields. destruct p0, p. inversions x. repeat eexists. eauto.
  }
  specialize (IHbs _ _ Hpbs'). subst. unfold sel_fields in Hpbs. destruct p. simpls.
  rewrite proj_rewrite in *. false* pf_sngl_fld_elim.
Qed.

Lemma pt2_bnd : forall G p T,
    inert G ->
    G ⊢!! p: typ_bnd T ->
    G ⊢!! p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
Qed.

Lemma pt3_bnd : forall G p T,
    inert G ->
    G ⊢!!! p: typ_bnd T ->
    G ⊢!!! p: open_typ_p p T \/
              (exists q, G ⊢!!! p: typ_sngl q /\ G ⊢!!! p: open_typ_p q T).
Proof.
  introv Hi Hp. dependent induction Hp.
  - left. constructor. apply* pt2_bnd.
  - specialize (IHHp _ Hi eq_refl). destruct IHHp as [Hq | [r [Hr1 Hr2]]]; right*.
Qed.

Lemma pt2_exists: forall G p T,
    G ⊢!!! p: T ->
    exists U, G ⊢!! p: U.
Proof.
  induction 1; eauto.
Qed.

Lemma pf_pt2_trans_inv_mult : forall G p q bs T,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢!! p •• bs : T ->
    T = typ_sngl q •• bs.
Proof.
  introv Hi Hp Hpbs. gen T. induction bs; introv Hpbs.
  - repeat rewrite field_sel_nil in *. apply pt2 in Hp. apply eq_sym. apply eq_sym.
    eauto using pt2_sngl_unique'.
  - rewrite proj_rewrite' in *. destruct (pt2_backtrack _ _ Hpbs) as [U Hb].
    apply pt2 in Hp. specialize (IHbs _ Hb). subst.
    destruct (field_elim_q _ Hi Hb Hpbs) as [U Hf].
    lets Hp2: (pt2_sngl_trans _ Hb Hf).
    eauto using pt2_sngl_unique'.
Qed.

Lemma pf_pt3_trans_inv_mult : forall G p q T,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢!!! p : T ->
    inert_typ T \/ record_type T ->
    G ⊢!!! q : T.
Proof.
  introv Hi Hpq Hp Hr. gen q. induction Hp; introv Hpq.
  - constructor.
    assert (inert_sngl (typ_sngl q)) as His. {
      right. eexists. eauto.
    }
    lets ->: (pt2_sngl_unique' Hi Hpq H). destruct Hr.
    inversion His. inversion H1. inversion H0. inversion H0. inversion H1.
  - specialize (IHHp Hi Hr).
    assert (inert_sngl (typ_sngl q)) as His1. {
      right. eexists. eauto.
    }
    assert (inert_sngl (typ_sngl q0)) as His2. {
      right. eexists. eauto.
    }
    lets Heq: (pt2_sngl_unique' Hi Hpq H). inversions Heq. eauto.
Qed.

Lemma pf_pt3_trans_inv_mult' : forall G p q T bs,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢!!! p •• bs : T ->
    inert_typ T \/ record_type T ->
    G ⊢!!! q •• bs : T.
Proof.
  introv Hi Hp Hpbs Hr.
  assert (exists U, G ⊢!! p •• bs : U) as [U Hu] by apply* pt2_exists.
  apply* pf_pt3_trans_inv_mult. lets Hpf: (pf_pt2_trans_inv_mult _ Hi Hp Hu). subst*.
Qed.

Lemma pf_pt3_unique : forall G p S A T U,
    inert G ->
    G ⊢! p: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢!!! p: typ_rcd {A >: U <: U} ->
    T = U.
Proof.
  introv Hi Hp1 Hp3. dependent induction Hp3.
  - apply pt2 in Hp1. dependent induction H. dependent induction Hp1.
    lets Hu: (pf_T_unique Hi H0 H). subst.
    destruct (pf_bnd_T2 Hi H0) as [V Heq]. subst.
    apply* pf_dec_typ_unique.
  - clear IHHp3. apply pt2 in Hp1. assert (inert_sngl (typ_sngl q)) as His. {
      right. eexists. eauto.
    }
    lets Hu: (pt2_sngl_unique' Hi H Hp1). inversion Hu.
Qed.

(** Lemmas about replacement composition *)

Definition typed_repl_comp_qp G T1 T2 :=
  exists p q n,
    G ⊢! p: typ_sngl q ⪼ typ_sngl q /\ repl_typ n q p T1 T2.

Definition repl_composition_qp G := star (typed_repl_comp_qp G).

Notation "G '⊢' T '⟿' U" := (repl_composition_qp G U T) (at level 40, T at level 59).
(*Notation "G '⊢' T '⬳' U" := (repl_composition_qp G T U) (at level 40, T at level 59).*)
Notation "G '⊢' p '⟿'' q" := (G ⊢ typ_sngl p ⟿ typ_sngl q) (at level 40, p at level 59).
(*Notation "G '⊢p' p '⬳' q" := (G ⊢ typ_sngl p ⬳ typ_sngl q) (at level 40, p at level 59).*)

Lemma repl_comp_sngl_inv1 : forall G T p,
    G ⊢ typ_sngl p ⟿ T ->
    exists q, T = typ_sngl q.
Proof.
  introv Hr. dependent induction Hr; eauto.
  specialize (IHHr _ eq_refl). destruct_all. subst.
  inversions H. destruct_all. invert_repl. eexists; eauto.
Qed.

Lemma repl_comp_sngl_inv2 : forall G T p,
    G ⊢ T ⟿ typ_sngl p ->
    exists q, T = typ_sngl q.
Proof.
  introv Hr. dependent induction Hr; eauto.
  inversions H. destruct_all. invert_repl.
  specialize (IHHr _ eq_refl). destruct_all. eexists. eauto.
Qed.

Lemma repl_comp_bnd_inv1 G T U :
  G ⊢ typ_bnd U ⟿ T ->
  exists S, T = typ_bnd S.
Proof.
  introv Hr. dependent induction Hr; eauto.
  specialize (IHHr _ eq_refl). destruct_all. subst.
  inversions H. destruct_all. invert_repl. eexists; eauto.
Qed.

Lemma repl_comp_bnd_inv2 G T U :
  G ⊢ T ⟿ typ_bnd U ->
  exists S, T = typ_bnd S.
Proof.
  introv Hr. dependent induction Hr; eauto.
  inversions H. destruct_all. invert_repl.
  specialize (IHHr _ eq_refl). destruct_all. eexists. eauto.
Qed.

Lemma repl_comp_bnd': forall G T T',
    G ⊢ typ_bnd T ⟿ typ_bnd T' ->
    G ⊢ T ⟿ T'.
Proof.
  introv Hr. dependent induction Hr.
  - apply star_refl.
  - destruct H as [?[?[?[? ?]]]].
    assert (exists V, b = typ_bnd V) as [V ->]. {
      inversions H0. eauto.
    }
    apply star_trans with (b:=V). apply star_one. econstructor. repeat eexists. apply H. inversion* H0.
    apply* IHHr.
Qed.

Lemma repl_comp_typ_rcd G A T U S :
  G ⊢ typ_rcd { A >: T <: U } ⟿ S ->
  exists T' U', S = typ_rcd { A >: T' <: U' } /\ G ⊢ T ⟿ T' /\ G ⊢ U ⟿ U'.
Proof. Admitted.

Lemma repl_comp_typ_rcd' G A T U S :
  G ⊢ S ⟿ typ_rcd { A >: T <: U } ->
  exists T' U', S = typ_rcd { A >: T' <: U' } /\ G ⊢ T' ⟿ T /\ G ⊢ U' ⟿ U.
Proof. Admitted.

Lemma repl_comp_trm_rcd G a T S :
  G ⊢ typ_rcd { a ⦂ T } ⟿ S ->
  exists T', S = typ_rcd { a ⦂ T' } /\ G ⊢ T ⟿ T'.
Proof. Admitted.

Lemma repl_comp_trm_rcd' G a T S :
  G ⊢ S ⟿ typ_rcd { a ⦂ T } ->
  exists T', S = typ_rcd { a ⦂ T' } /\ G ⊢ T' ⟿ T .
Proof. Admitted.

Lemma repl_comp_typ_and1 G T U S :
  G ⊢ S ⟿ typ_and T U ->
  exists T' U', S = typ_and T' U' /\ G ⊢ T' ⟿ T /\ G ⊢ U' ⟿ U.
Proof. Admitted.

Lemma repl_comp_typ_and2 G T U S :
  G ⊢ typ_and T U ⟿ S ->
  exists T' U', S = typ_and T' U' /\ G ⊢ T ⟿ T' /\ G ⊢ U ⟿ U'.
Proof. Admitted.

Lemma repl_comp_record_has2 G T U U' a :
  G ⊢ T ⟿ U ->
  record_has U { a ⦂ U' } ->
  exists T', record_has T { a ⦂ T' } /\ G ⊢ T' ⟿ U'.
Proof.
  intros Hrc Hr. gen T. dependent induction Hr; introv Hrc.
  - apply repl_comp_trm_rcd' in Hrc as [T' [-> Hr]]. eauto.
  - apply repl_comp_typ_and1 in Hrc as [T' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc1) as [V [Hr' Hrc]].
    eexists. split. apply rh_andl. eauto. auto.
  - apply repl_comp_typ_and1 in Hrc as [T' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc2) as [V [Hr' Hrc]].
    eexists. split. apply rh_andr. eauto. auto.
Qed.

Lemma repl_comp_record_has1 G T U T' a :
  G ⊢ T ⟿ U ->
  record_has T { a ⦂ T' } ->
  exists U', record_has U { a ⦂ U' } /\ G ⊢ T' ⟿ U'.
Proof.
  intros Hrc Hr. gen U. dependent induction Hr; introv Hrc.
  - apply repl_comp_trm_rcd in Hrc as [T'' [-> Hr]]. eauto.
  - apply repl_comp_typ_and2 in Hrc as [T'' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc1) as [V [Hr' Hrc]].
    eexists. split. apply rh_andl. eauto. auto.
  - apply repl_comp_typ_and2 in Hrc as [T'' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc2) as [V [Hr' Hrc]].
    eexists. split. apply rh_andr. eauto. auto.
Qed.

Lemma repl_composition_open G T U p :
  G ⊢ T ⟿ U ->
  G ⊢ open_typ_p p T ⟿ open_typ_p p U.
Proof.
  intros Hrc. dependent induction Hrc.
  - apply star_refl.
  - eapply star_trans with (b:=open_typ_p p b); auto.
    destruct H as [q [r [n [Hp Hr]]]]. apply star_one. econstructor. repeat eexists. apply Hp. apply* repl_open.
    eapply sngl_path_named. apply* precise_to_general. eapply typed_paths_named. apply* precise_to_general.
Qed.

Lemma repl_composition_sngl: forall G p q T,
    inert G ->
    G ⊢ p ⟿' q ->
    G ⊢!!! p : T ->
    p = q \/ G ⊢!!! p : typ_sngl q.
Proof.
  introv Hi Hc Hq. dependent induction Hc; eauto.
  assert (exists r, b = typ_sngl r) as [p3 Heq].
  { inversion H as [x [y [n [_ H0]]]]. inversion* H0. }
  subst.
  specialize (IHHc _ _ Hi eq_refl eq_refl Hq).
  destruct H as [r1 [r2 [n [H Hr]]]]. inversions Hr.
  lets H': (pt3 (pt2 H)).
  destruct IHHc as [Heq | Hp]; subst.
  - lets Htt: (pt3_trans_trans _ Hi H' Hq).
    right*.
  - right.
    destruct (sngl_typed3 Hi Hp) as [S Hqbs].
    lets Htt: (pt3_trans_trans _ Hi H' Hqbs). apply* pt3_sngl_trans3.
Qed.

Lemma repl_composition_sngl2: forall G p q T,
    inert G ->
    G ⊢ p ⟿' q ->
    G ⊢!!! q : T ->
    p = q \/ G ⊢!!! p : typ_sngl q.
Proof.
  introv Hi Hc Hq. gen T. dependent induction Hc; introv Hq; eauto.
  assert (exists r, b = typ_sngl r) as [p3 Heq].
  { destruct H as [x [q0 [n [_ H]]]]. inversion* H. }
  subst.
  specialize (IHHc _ _ Hi eq_refl eq_refl).
  destruct H as [r1 [r2 [n [H Hr]]]]. inversions Hr.
  lets H': (pt3 (pt2 H)).
  lets Hqs: (pt3_field_trans _ Hi H' Hq).
  destruct (IHHc _ Hqs) as [Heq | Hp]; subst.
  - lets Htt: (pt3_trans_trans _ Hi H' Hqs). right*.
  - right. destruct (sngl_typed3 Hi Hp) as [S' Hqbs].
    lets Htt: (pt3_trans_trans _ Hi H' Hqbs). apply* pt3_sngl_trans3.
Qed.

Lemma repl_composition_weaken_one G x T U V :
  ok G ->
  x # G ->
  G ⊢ T ⟿ U ->
  G & x ~ V ⊢ T ⟿ U.
Proof.
  intros Hok Hn Hr. gen x V. dependent induction Hr; intros.
  - constructor.
  - destruct H as [r [? [n [Hrq Hr']]]].
    eapply star_trans. apply star_one. econstructor. repeat eexists. apply* pf_weaken.
    apply Hr'. apply* IHHr.
Qed.

Lemma repl_composition_weaken G G' T U :
  ok (G & G') ->
  G ⊢ T ⟿ U ->
  G & G' ⊢ T ⟿ U.
Proof.
  intros Hok Hr. induction G' using env_ind.
  - rewrite* concat_empty_r.
  - rewrite concat_assoc in *. apply ok_push_inv in Hok as [? ?].
    eapply repl_composition_weaken_one; eauto.
Qed.

Notation "G '⊩' T '⟿' U '⬳' V" := (G ⊢ T ⟿ U /\ G ⊢ V ⟿ U) (at level 40, T at level 59).
Notation "G '⊩' p '⟿'' q '⬳' r" := (G ⊢ p ⟿' q /\ G ⊢ r ⟿' q) (at level 40, p at level 59).

Lemma repl_comp_trans_open G S W T p :
  G ⊩ S ⟿ W ⬳ T ->
  G ⊩ open_typ_p p S ⟿ open_typ_p p W ⬳ open_typ_p p T.
Proof.
  split; apply* repl_composition_open.
Qed.

Lemma repl_comp_trans_record_has G T S U V a :
  G ⊩ T ⟿ S ⬳ U ->
  record_has U {a ⦂ V} ->
  exists V' S', record_has T {a ⦂ V'} /\ G ⊩ V' ⟿ S' ⬳ V.
Proof.
  intros [Hc1 Hc2] Hr. pose proof (repl_comp_record_has1 Hc2 Hr) as [V1 [Hr1 Hc1']].
  pose proof (repl_comp_record_has2 Hc1 Hr1) as [V2 [Hr2 Hc2']]. repeat eexists; eauto.
Qed.

Lemma field_typing_comp1: forall G r q a U,
  inert G ->
  G ⊢ q ⟿' r ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hq; eauto.
  destruct (repl_comp_sngl_inv1 Hr) as [p Heq]. subst.
  destruct H as [p' [q' [n [Hp' Hr']]]].
  specialize (IHHr _ _ Hi eq_refl eq_refl _ _ Hq). destruct IHHr as [T Hpa].
  assert (G ⊢!!! p : typ_sngl r) as Hpr. {
    clear Hq Hr. inversions Hr'. gen p' a T. induction bs; introv Hpa; introv Hq.
    repeat rewrite field_sel_nil in *. eauto.
    destruct (pt3_backtrack _ _ Hq) as [T1 Ht1]. rewrite proj_rewrite' in *.
    apply pt3_backtrack in Hq. destruct_all. rewrite proj_rewrite'.
    apply* pt3_field_elim_p.
  }
  apply* field_elim_q3.
Qed.

Lemma field_typing_comp2: forall G r q a U,
  inert G ->
  G ⊢ r ⟿' q ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hqa; eauto. inversions H.
  rename x into p.
  destruct H0 as [q' [n [Hp Hr']]].
  assert (exists q', b = typ_sngl q') as [q'' Heq] by inversion* Hr'.
  subst. specialize (IHHr _ _ Hi eq_refl eq_refl). invert_repl. apply* IHHr. clear IHHr Hr.
  gen q' a U. induction bs; intros; simpls.
  - repeat rewrite field_sel_nil in *. apply* pt3_trans2.
  - rewrite <- proj_rewrite' in *. apply* pt3_field_trans'.
Qed.

Lemma repl_composition_fld_elim: forall G p q a T,
    inert G ->
    G ⊢ p ⟿' q ->
    G ⊢!!! p • a : T ->
    G ⊢ p•a ⟿' q•a.
Proof.
  introv Hi Hr. gen T. dependent induction Hr; introv Hpa.
  - apply star_refl.
  - assert (exists p', b = typ_sngl p') as [p' Heq]. {
      dependent induction H; destruct_all; eauto. inversions H0. eauto.
    } subst.
    specialize (IHHr _ _ Hi eq_refl eq_refl).
    destruct H as [p'' [q' [n [Hpq Hr']]]]. apply star_trans with (b:=typ_sngl p' • a).
    * apply star_one. inversions Hr'. repeat eexists. apply Hpq.
      repeat rewrite <- proj_rewrite' in *.
      apply* rsngl.
    * invert_repl. apply* IHHr.
Qed.

Lemma pt2_strengthen_from_pt1 G G' p bs T T' U :
  G ⊢! p: T ⪼ T' ->
  G & G' ⊢!! p••bs : U ->
  G  ⊢!! p••bs : U.
Proof. Admitted.

Lemma pt1_strengthen_from_pt3 G G' p T U V :
  G ⊢!!! p: T ->
  G & G' ⊢! p : U ⪼ V ->
  G  ⊢! p : U ⪼ V.
Proof. Admitted.

Lemma pt2_strengthen_one G y bs T x U :
  inert (G & x ~ T) ->
  G & x ~ T ⊢!! p_sel (avar_f y) bs : U ->
  x <> y ->
  G ⊢!! p_sel (avar_f y) bs : U.
Proof.
  intros Hi Ht Hn. dependent induction Ht.
  - econstructor. apply* pf_strengthen.
  - simpl_dot.
    specialize (IHHt1 _ _ _ _ _ Hi JMeq_refl eq_refl Hn).
    (*pose proof (sngl_path_named (precise_to_general2 Ht1)) as [qx [qbs ->]].*)
    simpl in *.
    repeat rewrite proj_rewrite. eapply pt2_sngl_trans; auto. simpl.
    admit.
Admitted.

Lemma pt2_strengthen G G1 G2 bs T x U :
  G = G1 & x ~ T & G2 ->
  inert G ->
  G ⊢!! p_sel (avar_f x) bs : U ->
  G1 & x ~ T ⊢!! p_sel (avar_f x) bs : U.
Proof.
  induction G2 using env_ind. Admitted.

Lemma pt3_strengthen_one G bs T x y U :
  inert (G & x ~ T) ->
  G & x ~ T ⊢!!! p_sel (avar_f y) bs : U ->
  y <> x ->
  G ⊢!!! p_sel (avar_f y) bs : U.
Proof. Admitted.

Lemma pt3_strengthen G G1 G2 bs T x U :
  G = G1 & x ~ T & G2 ->
  inert G ->
  G ⊢!!! p_sel (avar_f x) bs : U ->
  G1 & x ~ T ⊢!! p_sel (avar_f x) bs : U.
Proof. Admitted.

Lemma pt3_exists G p T :
  G ⊢ trm_path p : T ->
  exists U, G ⊢!!! p : U.
Proof.
Admitted.

Lemma pt3_weaken G G' p T :
  G ⊢!!! p: T ->
  G & G' ⊢!!! p: T.
Proof.
  Admitted.

Lemma repl_comp_to_prec': forall G G' p q T,
    inert G ->
    G ⊢ p ⟿' q ->
    G & G' ⊢!!! p: T ->
    p = q \/ G ⊢!!! p: typ_sngl q.
Proof.
  introv Hi Hr Hp. gen T. dependent induction Hr; introv Hp; eauto.
  assert (exists r, b = typ_sngl r) as [r Heq].
  { inversion H as [x [y [n [_ H0]]]]. inversion* H0. }
  subst.
  specialize (IHHr _ _ Hi eq_refl eq_refl). destruct (IHHr _ Hp). subst.
  - destruct H as [p1 [p2 [n [H1 H2]]]]. right. inversions H2.
    destruct (pt2_exists Hp) as [U Hu].
    apply (pt2_strengthen_from_pt1 _ H1) in Hu.
    lets Hpf: (pf_pt2_trans_inv_mult _ Hi H1 Hu). subst*.
  - specialize (IHHr _ Hp). destruct H as [p1 [p2 [n [H1 H2]]]].
    destruct (repl_prefixes_sngl H2) as [bs [He1 He2]]. subst.
    destruct IHHr as [Heq | IH].
    * subst. right. lets Hs: (sngl_typed3 Hi (pt3 (pt2 H1))). destruct Hs.
      apply* pt3_trans_trans.
    * right*. apply* pt3_sngl_trans3.
      lets Hs: (sngl_typed3 Hi IH). destruct Hs.
      apply* pt3_trans_trans.
Qed. (* todo: rewrite above lemmas using this lemma *)

Lemma repl_comp_to_prec: forall G p q T,
    inert G ->
    G ⊢ p ⟿' q ->
    G ⊢!!! p: T ->
    p = q \/ G ⊢!!! p: typ_sngl q.
Proof.
  introv Hi Hp Hpt. assert (G = G & empty) as Heq by rewrite* concat_empty_r.
  rewrite Heq in Hpt. apply* repl_comp_to_prec'.
Qed.

Lemma repl_comp_typed : forall G p q T,
    inert G ->
    G ⊢ p ⟿' q ->
    G ⊢!!! q: T ->
    exists U, G ⊢!!! p: U.
Proof.
  introv Hi Hr Hq. gen T. dependent induction Hr; introv Hq; eauto.
  assert (exists q', b = typ_sngl q') as [q' Heq].
  { inversion H as [x [y [n [_ H0]]]]. inversion* H0. }
  subst.
  destruct H as [r [r' [n [H2 H3]]]].
  destruct (repl_prefixes_sngl H3) as [bs [He1 He2]]. subst.
  apply* IHHr. apply* pt3_field_trans'.
Qed.

Lemma pt23_invert : forall G p q T,
    inert G ->
    G ⊢!! p : T ->
    G ⊢!!! p : typ_sngl q ->
    exists q', typ_sngl q' = T /\ (q = q' \/ G ⊢!!! q' : typ_sngl q).
Proof.
  introv Hi Hp Hpq. gen T. dependent induction Hpq; introv Hp.
  - exists q. split*.
    apply eq_sym. apply* pt2_sngl_unique'.
  - lets Hu: (pt2_sngl_unique' Hi H Hp). subst*.
Qed.

Lemma pt3_invert : forall G p q T,
    inert G ->
    G ⊢!!! p : T ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q: T \/ exists q', typ_sngl q' = T /\ (q = q' \/ G ⊢!!! q' : typ_sngl q).
Proof.
  introv Hi Hp Hpq. gen q. dependent induction Hp; introv Hpq.
  - right. apply* pt23_invert.
  - destruct (pt23_invert Hi H Hpq) as [q' [Heq [Heq' | Hq']]]; inversions Heq; eauto.
Qed.

Lemma pt2_var_sngl G x p :
  inert G ->
  G ⊢!! pvar x : typ_sngl p ->
  False.
Proof.
  intros Hi Hp. dependent induction Hp; try simpl_dot.
  pose proof (pf_sngl_T Hi H) as ->. apply (pf_binds Hi) in H.
  apply (binds_inert H) in Hi. inversion Hi.
Qed.

Lemma pt3_var_sngl G x p :
  inert G ->
  G ⊢!!! pvar x : typ_sngl p ->
  False.
Proof.
  intros Hi Hp. dependent induction Hp; false* pt2_var_sngl.
Qed.

Lemma pt1_inert_pt2_sngl_false G p q T U :
  inert G ->
  G ⊢! p : T ⪼ U ->
  G ⊢!! p : typ_sngl q ->
  inert_typ T ->
  False.
Proof.
  intros Hi Hp Hq Hin. gen q. dependent induction Hp; eauto; introv Hpq.
  - false* pt3_var_sngl.
  - lets Hp': (pf_fld Hp). pose proof (pf_pt2_sngl Hi Hp' Hpq) as ->. inversion Hin.
Qed.

Lemma pt1_inert_pt3_sngl_false G p q T U :
  inert G ->
  G ⊢! p : T ⪼ U ->
  G ⊢!!! p : typ_sngl q ->
  inert_typ T ->
  False.
Proof.
  intros Hi Hp Hq Hin. gen T U. dependent induction Hq; introv Hin; introv Hp;
  apply* pt1_inert_pt2_sngl_false.
Qed.

Lemma pt3_inert_pt2_sngl_invert G p q T :
  inert G ->
  G ⊢!!! p : T ->
  G ⊢!! p : typ_sngl q ->
  inert_typ T ->
  G ⊢!!! q : T.
Proof.
  intros Hi Hp Hpq Hin. gen q. induction Hp; introv Hpq.
  - pose proof (pt2_sngl_unique' Hi Hpq H) as ->. inversion Hin.
  - pose proof (pt2_sngl_unique Hi H Hpq) as ->. eauto.
Qed.

Lemma pt3_inert_sngl_invert G p q T :
  inert G ->
  G ⊢!!! p : T ->
  G ⊢!!! p : typ_sngl q ->
  inert_typ T ->
  G ⊢!!! q : T.
Proof.
  introv Hi Hp Hpq. gen T. dependent induction Hpq; introv Hp Hin;
                             [.. | apply* IHHpq];
                             eapply (pt3_inert_pt2_sngl_invert Hi Hp); eauto.
Qed.
