Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Some_lemmas.

Lemma precise_inert_typ : forall G v T,
    G |-! trm_val v : T ->
    inert_typ T.
Proof.
  introv Ht. inversions Ht; constructor; rename T0 into T.
  pick_fresh z. assert (Hz: z \notin L) by auto. specialize (H1 z Hz). clear Hz.
  pose proof (ty_defs_record_type H1).
  assert (Hz: z \notin fv_typ T) by auto.
  apply* record_type_open.
Qed.

(*
Definition (Precise flow of a variable)

For a variable x, environment G, type T, the set Pf(x,G,T) is the set of all
precise types that x can have if G(x)=T. More "precisely":

If G(x)=T, then T is in Pf(x,G,T).
If {a: U} is in Pf(p,G,T) and inert U, then U is in Pf(p.a,G,U).
If rec(p:U) is in Pf(p,G,T), then U is in Pf(p,G,T).
If (U1 & U2) is in Pf(p,G,T), then U1 is in Pf(p,G,T).
If (U1 & U2) is in Pf(p,G,T), then U2 is in Pf(p,G,T).

 *)

Inductive precise_flow : path -> ctx -> typ -> typ -> Prop :=
  | pf_bind : forall x G T,
      binds x T G ->
      precise_flow (p_var (avar_f x)) G T T
  | pf_fld : forall G p a T U,
      precise_flow p G T (typ_rcd { a [strong] U }) ->
      inert_sngl U ->
      precise_flow (p_sel p a) G U U
  | pf_rec : forall p G T U,
      precise_flow p G T (typ_bnd U) ->
      precise_flow p G T (open_typ_p p U)
  | pf_and1 : forall p G T U1 U2,
      precise_flow p G T (typ_and U1 U2) ->
      precise_flow p G T U1
  | pf_and2 : forall p G T U1 U2,
      precise_flow p G T (typ_and U1 U2) ->
      precise_flow p G T U2.

Hint Constructors precise_flow.

Lemma precise_flow_lemma : forall U G p,
    G |-! trm_path p : U ->
    exists T, precise_flow p G T U.
Proof.
  introv H. dependent induction H; try (destruct* (IHty_trm_p _ eq_refl)); eauto.
Qed.

Lemma precise_flow_all_inv : forall p G S T U,
    precise_flow p G (typ_all S T) U ->
    U = typ_all S T.
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf S T eq_refl); inversion IHHpf.
Qed.

(* ###################################################################### *)
(** ** Inert types *)

(* Inert contexts bind inert:
If G |- x : T and G is a inert context then T is a inert type. *)

Lemma binds_inert : forall G x T,
    binds x T G ->
    inert G ->
    inert_typ T.
Proof.
  introv Bi Hinert. induction Hinert.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H1. subst. assumption.
    + destruct H1. apply (IHHinert H2).
Qed.

Lemma inert_typ_bnd_record : forall G x T,
    inert G ->
    binds x (typ_bnd T) G ->
    record_type T.
Proof.
  introv Bi Hgd.
  pose proof (binds_inert Hgd Bi).
  dependent induction H.
  assumption.
Qed.

Lemma pf_inert_sngl_T : forall G p T U,
    inert G ->
    precise_flow p G T U ->
    inert_sngl T.
Proof.
  introv Hi Pf. induction Pf; eauto.
  apply is_inert. apply (binds_inert H Hi).
Qed.

Lemma pf_rcd_T : forall G p T U,
    inert G ->
    precise_flow p G (typ_bnd T) U ->
    record_type T.
Proof.
  introv Hi Pf. apply pf_inert_sngl_T in Pf; inversions Pf; auto. inversion* H.
Qed.

Lemma pf_inert_or_rcd : forall G p T U,
    inert G ->
    precise_flow p G (typ_bnd T) U ->
    U = typ_bnd T \/ record_type U.
Proof.
  introv Hi Pf.
  dependent induction Pf; try solve [left*].
  - specialize (IHPf T Hi eq_refl). destruct IHPf as [eq | r].
    * inversions eq. right. lets Hr: (pf_rcd_T Hi Pf). apply* open_record_type_p.
    * inversion r. inversion H.
  - right. destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F. inversion Hr. inversions H.
    exists ls. assumption.
  - right. destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F. inversion Hr. inversions H.
    eexists. apply* rt_one.
Qed.

Lemma pf_inert_lambda_T : forall G p T U S,
    inert G ->
    precise_flow p G (typ_all T U) S ->
    S = typ_all T U.
Proof.
  introv Hi Pf. dependent induction Pf;
                  try (specialize (IHPf T U Hi eq_refl); inversion IHPf); auto.
Qed.

Lemma pf_sngl_T: forall G p q U,
    inert G ->
    precise_flow p G (typ_sngl q) U ->
    U = typ_sngl q.
Proof.
  introv Hi Pf. dependent induction Pf; auto; specialize (IHPf _ Hi eq_refl); inversion IHPf.
Qed.

Lemma pf_inert_bnd_U: forall G p T U,
    inert G ->
    precise_flow p G T (typ_bnd U) ->
    T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_sngl_T Hi Pf). destruct HT as [Hin |Hs].
  + inversions H; dependent induction Pf; auto.
    - destruct U0; inversions x.
      apply pf_inert_lambda_T in Pf. inversion* Pf. assumption.
    - apply pf_inert_lambda_T in Pf. inversion Pf. assumption.
    - apply pf_inert_lambda_T in Pf. inversion Pf. assumption.
    - specialize (IHPf _ Hi _ eq_refl eq_refl H0).
      destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
      * inversions Heq. destruct T; inversions x. inversion H0. inversion H.
      * inversions IHPf. inversion Hr. inversions H.
    - destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
      * inversions Heq.
      * inversions Hr. inversions H. inversions H3.
    - destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
      * inversions Heq.
      * inversions Hr. inversions H.
  + apply pf_sngl_T in Pf; auto.
Qed.

Lemma record_inert_false: forall U,
    inert_typ U ->
    record_type U ->
    False.
Proof.
  introv Hi. induction Hi; auto; intro Hr; inversion Hr; inversions H. inversion H0.
Qed.

Lemma pf_inert_rcd_typ_U: forall G p T Ds,
    inert G ->
    precise_flow p G T Ds ->
    record_type Ds ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf Hr.
  lets HT: (pf_inert_sngl_T Hi Pf). destruct HT as [T | Hs].
  - destruct H.
    + apply pf_inert_lambda_T in Pf; eauto. subst. inversion Hr. inversion H.
    + exists*.
  - apply pf_sngl_T in Pf. subst. inversion Hr. inversion H. assumption.
Qed.

Lemma pf_inert_rcd_U: forall G p T D,
    inert G ->
    precise_flow p G T (typ_rcd D) ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_sngl_T Hi Pf). destruct HT as [T | Hs].
  destruct H as [Hin | Hs].
  apply pf_inert_lambda_T in Pf; auto. inversion Pf.
  exists*. apply pf_sngl_T in Pf. inversion Pf. assumption.
Qed.

Lemma pf_inert_rcd_bnd_U : forall G p T U,
    inert G ->
    precise_flow p G T (typ_bnd U) ->
    record_type U.
Proof.
  introv Hi Pf. lets HT: (pf_inert_bnd_U Hi Pf). subst.
  lets HiT: (pf_rcd_T Hi Pf). assumption.
Qed.

Lemma pf_sngl_U: forall G p q T,
    inert G ->
    precise_flow p G T (typ_sngl q) ->
    T = typ_sngl q.
Proof.
  introv Hi Pf. lets His: (pf_inert_sngl_T Hi Pf). inversions His. inversions H.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - apply (pf_inert_or_rcd Hi) in Pf. destruct* Pf. inversion H. inversion H1.
  - apply pf_sngl_T in Pf; auto.
Qed.

Lemma pf_inert_lambda_U : forall p G S T U,
    inert G ->
    precise_flow p G U (typ_all S T) ->
    U = (typ_all S T).
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert_sngl_T Hi Pf).
  inversions Hiu. destruct H. apply precise_flow_all_inv in Pf. inversion* Pf.
  apply (pf_inert_or_rcd Hi) in Pf. destruct Pf as [Heq | Hr]. inversion Heq. inversion Hr. inversion H0.
  apply pf_sngl_T in Pf. inversion Pf. assumption.
Qed.

Lemma pf_binds: forall G x T U,
    precise_flow (p_var (avar_f x)) G T U ->
    binds x T G.
Proof.
  introv Pf. dependent induction Pf; auto.
Qed.

Lemma inert_precise_all_inv: forall G x T U,
    inert G ->
    G |-! trm_path (p_var (avar_f x)) : typ_all T U ->
    binds x (typ_all T U) G.
Proof.
  introv Hi Ht. destruct (precise_flow_lemma Ht) as [V Pf].
  lets HT: (pf_inert_lambda_U Hi Pf). subst. apply* pf_binds.
Qed.

Lemma pf_bot_false : forall G p T,
    inert G ->
    precise_flow p G T typ_bot ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_sngl_T Hi Pf). destruct HT as [Hin | Hs]. inversions H.
  apply precise_flow_all_inv in Pf. inversion Pf.
  apply (pf_inert_or_rcd Hi) in Pf. destruct Pf as [Heq | Hr]. inversion Heq. inversion Hr. inversion H.
  apply pf_sngl_T in Pf. inversion Pf. assumption.
Qed.

Lemma precise_bot_false : forall G p,
    inert G ->
    G |-! trm_path p : typ_bot ->
    False.
Proof.
  introv Hi Hp. destruct (precise_flow_lemma Hp) as [T Pf].
  apply* pf_bot_false.
Qed.

Lemma pf_psel_false : forall G T p q A,
    inert G ->
    precise_flow p G T (typ_path q A) ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_sngl_T Hi Pf). inversions HT. inversions H.
  - apply pf_inert_lambda_T in Pf. inversion Pf. apply pf_inert_lambda_T in Pf. inversion Pf. assumption.
  - destruct (pf_inert_or_rcd Hi Pf); inversion H0. inversion H. inversion H. inversion H2.
  - apply pf_sngl_T in Pf. inversion Pf. assumption.
Qed.

Lemma precise_psel_false : forall G p q A,
    inert G ->
    G |-! trm_path p : typ_path q A ->
    False.
Proof.
  introv Hi Hp. destruct (precise_flow_lemma Hp) as [T Pf].
  apply* pf_psel_false.
Qed.

Lemma pf_record_sub : forall p G T T' D,
    inert G ->
    precise_flow p G (typ_bnd T) T' ->
    record_has T' D ->
    record_has (open_typ_p p T) D.
Proof.
  introv Hi Pf Hr. dependent induction Pf.
  - inversions Hr.
  - inversions Hr.
  - apply (pf_inert_bnd_U Hi) in Pf. inversion* Pf.
  - apply* IHPf.
  - apply* IHPf.
Qed.

Lemma precise_flow_record_has: forall S G p D,
    inert G ->
    precise_flow p G (typ_bnd S) (typ_rcd D) ->
    record_has (open_typ_p p S) D.
Proof.
  introv Hi Pf.
  apply* pf_record_sub.
Qed.

Lemma pf_record_unique_tight_bounds_rec : forall G p T A T1 T2,
    inert G ->
    precise_flow p G (typ_bnd T) (typ_rcd { A >: T1 <: T1 }) ->
    precise_flow p G (typ_bnd T) (typ_rcd { A >: T2 <: T2 }) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (precise_flow_record_has Hi Pf1) as H1.
  pose proof (precise_flow_record_has Hi Pf2) as H2.
  eapply unique_rcd_typ; eauto. apply (pf_rcd_T Hi) in Pf1.
  apply* open_record_type_p.
Qed.

Lemma pf_inert_unique_tight_bounds : forall G p T T1 T2 A,
    inert G ->
    precise_flow p G T (typ_rcd { A >: T1 <: T1 }) ->
    precise_flow p G T (typ_rcd { A >: T2 <: T2 }) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  assert (record_type (typ_rcd { A >: T1 <: T1 })) as Hrt. {
    unfold record_type. eexists. apply* rt_one.
    constructor.
  }
  lets Hr: (pf_inert_rcd_typ_U Hi Pf1 Hrt). destruct Hr as [U Heq]. subst.
  apply* pf_record_unique_tight_bounds_rec.
Qed.

Lemma inert_pt_unique: forall G p T T1 T2,
    inert G ->
    precise_flow p G T T1 ->
    precise_flow p G T T2 ->
    inert_typ T1 ->
    inert_typ T2 ->
    T1 = T2.
Proof.
  introv Hi P1 P2 I1 I2. inversions I1; inversions I2.
  - apply (pf_inert_lambda_U Hi) in P1.
    apply (pf_inert_lambda_U Hi) in P2. inversions* P2.
  - apply (pf_inert_bnd_U Hi) in P2.
    apply (pf_inert_lambda_U Hi) in P1. inversions* P2.
  - apply (pf_inert_bnd_U Hi) in P1.
    apply (pf_inert_lambda_U Hi) in P2. inversions* P2.
  - apply (pf_inert_bnd_U Hi) in P2.
    apply (pf_inert_bnd_U Hi) in P1. inversions* P2.
Qed.

Lemma pf_rcd_unique: forall G p T a m1 m2 U1 U2,
    inert G ->
    precise_flow p G T (typ_rcd { a [m1] U1 }) ->
    precise_flow p G T (typ_rcd { a [m2] U2 }) ->
    m1 = m2 /\ U1 = U2.
Proof.
  introv Hi Pf1 Pf2. dependent induction Pf1.
  - apply (binds_inert H) in Hi. inversion Hi.
  - inversion H. inversion H0.
  - assert (record_type (typ_rcd { a [m2] U2 })) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    destruct U; inversions x. destruct d; inversions H0.
    apply (pf_inert_bnd_U Hi) in Pf1. inversions Pf1.
    lets Hr: (precise_flow_record_has Hi Pf2). inversion* Hr.
  - assert (record_type (typ_rcd { a [m2] U2 })) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    assert (record_has (typ_and (typ_rcd { a [m1] U1 }) U0) { a [m1] U1 }) as H
        by (apply* rh_andl).
    lets Hr1: (pf_record_sub Hi Pf1 H).
    lets Hr2: (precise_flow_record_has Hi Pf2).
    assert (record_type (open_typ_p p S)) as Hs. {
      apply open_record_type_p. apply pf_inert_sngl_T in Pf1; auto. inversions Pf1. inversion* H0.
    }
    apply* unique_rcd_trm.
  - assert (record_type (typ_rcd { a [m2] U2 })) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    assert (record_has (typ_and U3 (typ_rcd { a [m1] U1 })) { a [m1] U1 }) as H
        by (apply* rh_andr).
    lets Hr1: (pf_record_sub Hi Pf1 H).
    lets Hr2: (precise_flow_record_has Hi Pf2).
    assert (record_type (open_typ_p p S)) as Hs. {
      apply open_record_type_p. apply pf_inert_sngl_T in Pf1; auto. inversions Pf1. inversion* H0.
    }
    apply* unique_rcd_trm.
Qed.

Lemma p_bound_unique: forall G p T1 T2 U1 U2,
    inert G ->
    precise_flow p G T1 U1 ->
    precise_flow p G T2 U2 ->
    T1 = T2.
Proof.
  introv Hi Pf1. gen T2 U2. induction Pf1; intros; try solve [apply* IHPf1]; auto.
  - apply pf_binds in H0. apply (binds_func H H0).
  - dependent induction H0; eauto.
    specialize (IHPf1 Hi T0 (typ_rcd { a [strong] U0 }) H0). subst.
    lets Hu: (pf_rcd_unique Hi Pf1 H0). apply* Hu.
Qed.

Lemma p_rcd_unique: forall G p a m1 m2 U1 U2,
    inert G ->
    G |-! trm_path p : typ_rcd { a [m1] U1 } ->
    G |-! trm_path p : typ_rcd { a [m2] U2 } ->
    m1 = m2 /\ U1 = U2.
Proof.
  introv Hi H1 H2. destruct (precise_flow_lemma H1) as [T1 Pf1].
  destruct (precise_flow_lemma H2) as [T2 Pf2].
  lets Hu: (p_bound_unique Hi Pf1 Pf2). subst.
  apply* pf_rcd_unique.
Qed.

Lemma inert_unique_tight_bounds : forall G p T1 T2 A,
    inert G ->
    G |-! trm_path p : typ_rcd { A >: T1 <: T1 } ->
    G |-! trm_path p : typ_rcd { A >: T2 <: T2 } ->
    T1 = T2.
Proof.
  introv Hi H1 H2.
  destruct (precise_flow_lemma H1) as [T1' Pf1].
  destruct (precise_flow_lemma H2) as [T2' Pf2].
  lets Heq: (p_bound_unique Hi Pf1 Pf2). subst.
  apply* pf_inert_unique_tight_bounds.
Qed.

Lemma inert_ok : forall G,
    inert G ->
    ok G.
Proof.
  intros G HG. induction G using env_ind.
  auto.
  inversions HG. false* empty_push_inv.
  destruct (eq_push_inv H) as [Hx [HT HG]]. subst.
  apply* ok_push.
Qed.

Lemma pf_dec_typ_inv : forall G p T A S U,
    inert G ->
    precise_flow p G T (typ_rcd { A >: S <: U }) ->
    S = U.
Proof.
  introv Hi Pf.
  destruct (pf_inert_rcd_U Hi Pf) as [V H]. subst.
  destruct (pf_inert_or_rcd Hi Pf) as [H1 | H1]; inversions H1. inversions H.
  inversions* H1.
Qed.

Lemma precise_dec_typ_inv : forall G p A S U,
    inert G ->
    G |-! trm_path p : typ_rcd { A >: S <: U } ->
    S = U.
Proof.
  introv Hi Hpt. destruct (precise_flow_lemma Hpt) as [V Pf].
  apply* pf_dec_typ_inv.
Qed.

Lemma pf_sngl_unique: forall G p P T Q q,
    inert G ->
    precise_flow p G P T ->
    precise_flow p G Q (typ_sngl q) ->
    T = typ_sngl q.
Proof.
  introv Hi Pf1 Pf2. lets Hu: (p_bound_unique Hi Pf1 Pf2). subst.
  apply pf_sngl_U in Pf2. subst. apply* pf_sngl_T. assumption.
Qed.

Lemma p_sngl_unique: forall G p q T,
    inert G ->
    G |-! trm_path p: typ_sngl q ->
    G |-! trm_path p: T ->
    T = typ_sngl q.
Proof.
  introv Hi Hp1 Hp2.
  destruct (precise_flow_lemma Hp1) as [T1 H1]. destruct (precise_flow_lemma Hp2) as [T2 H2].
  apply* pf_sngl_unique.
Qed.
