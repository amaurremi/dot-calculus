Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Some_lemmas.

(* ###################################################################### *)
(** ** Substitution *)

Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

Fixpoint subst_path (z: var) (u: var) (p: path) : path :=
  match p with
  | p_var x   => p_var (subst_avar z u x)
  | p_sel p a => p_sel (subst_path z u p) a
  end.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_path p L   => typ_path (subst_path z u p) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  | typ_sngl p     => typ_sngl (subst_path z u p)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | { L >: T <: U } => { L >: subst_typ z u T <: subst_typ z u U }
  | { a [m] U } => { a [m] subst_typ z u U }
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_val v        => trm_val (subst_val z u v)
  | trm_path p       => trm_path (subst_path z u p)
  | trm_app x1 x2    => trm_app (subst_avar z u x1) (subst_avar z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: var) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | def_trm L t => def_trm L (subst_trm z u t)
  end
with subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx := map (subst_typ z u) G.

(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_typ_dec_path: forall x y,
  (forall T : typ  , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec  , x \notin fv_dec  D  -> subst_dec  x y D  = D ) /\
  (forall P : path , x \notin fv_path P  -> subst_path x y P  = P ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply subst_fresh_avar. assumption.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec_path x y).

Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec_path).
Qed.

Lemma invert_fv_ctx_types_push: forall x z T G,
  x \notin fv_ctx_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_ctx_types G).
Proof.
  introv N.
  unfold fv_ctx_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

Lemma subst_fresh_ctx: forall x y G,
  x \notin fv_ctx_types G -> subst_ctx x y G = G.
Proof.
  intros x y.
  apply (env_ind (fun G => x \notin fv_ctx_types G -> subst_ctx x y G = G)).
  + intro N. unfold subst_ctx. apply map_empty.
  + intros G z T IH N.
    apply invert_fv_ctx_types_push in N. destruct N as [N1 N2].
    unfold subst_ctx in *. rewrite map_push.
    rewrite (IH N2).
    rewrite ((proj1 (subst_fresh_typ_dec_path _ _)) _ N1).
    reflexivity.
Qed.

Definition subst_fvar(x y z: var): var := If z = x then y else z.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a)
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)) /\
  (forall p : path, forall n: nat,
     subst_path x y (open_rec_path n u p)
     = open_rec_path n (subst_fvar x y u) (subst_path x y p)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*.
  destruct a; simpl. case_if*. case_var*.
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (T ||^ u) = (subst_typ x y T) ||^ (subst_fvar x y u).
Proof.
  intros. apply* subst_open_commute_typ_dec.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec_path_p: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ_p n u t)
     = open_rec_typ_p n (subst_path x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec_p n u D)
     = open_rec_dec_p n (subst_path x y u) (subst_dec x y D)) /\
  (forall p: path, forall n: nat,
    subst_path x y (open_rec_path_p n u p)
    = open_rec_path_p n (subst_path x y u) (subst_path x y p)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*.
  destruct a; simpl. case_if*. case_var*.
Qed.

Lemma subst_open_commute_typ_p: forall x y u T,
  subst_typ x y (open_typ_p u T) = open_typ_p (subst_path x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec_path_p.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_trm_val_def_defs: forall x y u,
  (forall t : trm, forall n: Datatypes.nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: Datatypes.nat,
     subst_val x y (open_rec_val n u v)
     = open_rec_val n (subst_fvar x y u) (subst_val x y v)) /\
  (forall d : def , forall n: Datatypes.nat,
     subst_def x y (open_rec_def n u d)
     = open_rec_def n (subst_fvar x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: Datatypes.nat,
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ_dec).
Qed.

Lemma subst_open_commute_trm: forall x y u t,
  subst_trm x y (t |^ u) = (subst_trm x y t) |^ (subst_fvar x y u).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

Lemma subst_open_commute_defs: forall x y u ds,
  subst_defs x y (ds |||^ u) = (subst_defs x y ds) |||^ (subst_fvar x y u).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  t |^ u = subst_trm x u (t |^ x).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  ds |||^ u = subst_defs x u (ds |||^ x).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  T ||^ u = subst_typ x u (T ||^ x).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commute_typ.
  destruct (@subst_fresh_typ_dec_path x u) as [Q _]. rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct d; simpl; reflexivity.
Qed.

Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - simpl. reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if. apply (IHds Eq).
Qed.

Lemma subst_dec_preserves_label: forall D x y,
  label_of_dec D = label_of_dec (subst_dec x y D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma subst_record_dec: forall d x y,
  record_dec d -> record_dec (subst_dec x y d).
Proof.
  introv Hd. inversions Hd. apply rd_typ. apply rd_trm.
Qed.

Lemma subst_record_typ: forall T x y ls,
  record_typ T ls -> record_typ (subst_typ x y T) ls.
Proof.
  introv Hr. induction Hr; simpl.
  - apply* rt_one. apply* subst_record_dec. rewrite* <- subst_dec_preserves_label.
  - apply* rt_cons. apply* subst_record_dec. rewrite* <- subst_dec_preserves_label.
Qed.

Lemma subst_record_type: forall T x y,
  record_type T -> record_type (subst_typ x y T).
Proof.
  introv Hr. unfolds record_type. destruct Hr as [ls Hr].
  lets Hr': (subst_record_typ x y Hr). exists* ls.
Qed.

Lemma inert_subst: forall x y T,
    inert_typ T ->
    inert_typ (subst_typ x y T).
Proof.
  introv Ht. inversions Ht; simpl. constructor. constructor. apply* subst_record_type.
Qed.

Lemma inert_sngl_subst: forall x y T,
    inert_sngl T ->
    inert_sngl (subst_typ x y T).
Proof.
  introv Hi. inversions Hi. apply is_inert. apply* inert_subst.
  simpl. apply* is_sngl.
Qed.

(* ###################################################################### *)
(** ** The substitution principle *)

Lemma subst_rules: forall y S,
  (forall G t T, G |- t : T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_path (p_var (avar_f y)) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) |- subst_trm x y t : subst_typ x y T) /\
  (forall G p T, G |-\||/ p: T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_path (p_var (avar_f y)) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) |-\||/ subst_path x y p : subst_typ x y T) /\
  (forall G z T d D, G && z ~ T |- d : D -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2 & z ~ T) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_path (p_var (avar_f y)) :  subst_typ x y S ->
    G1 & (subst_ctx x y G2) && z ~ subst_typ x y T |- subst_def x y d : subst_dec x y D) /\
  (forall G z T ds U, G && z ~ T |- ds :: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2 & z ~ T) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_path (p_var (avar_f y)) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) && z ~ subst_typ x y T |- subst_defs x y ds :: subst_typ x y U) /\
  (forall G T U, G |- T <: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_path (p_var (avar_f y)) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) |- subst_typ x y T <: subst_typ x y U).
Proof.
  intros y S. apply rules_mutind; intros; simpl; subst; auto.
  - (* ty_var *)
    case_if.
    + subst. apply binds_middle_eq_inv in b. subst. assumption. assumption.
    + apply subst_fresh_ctx with (y:=y) in H1.
      apply binds_subst in b.
      apply ty_var. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map. assumption. assumption.
  - (* ty_all_intro *)
    apply_fresh ty_all_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    rewrite <- A at 3. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_all_elim *)
    rewrite subst_open_commute_typ.
    eapply ty_all_elim.
    simpl in H.
    apply H; eauto.
    apply H0; eauto.
  - (* ty_new_intro *)
    apply_fresh ty_new_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- A at 3. rewrite <- A at 4.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_defs.

    assert (subst_ctx x y G2 & z ~ subst_typ x y (T ||^ z) = subst_ctx x y (G2 & z ~ (T ||^ z))) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    apply H; eauto.
  - (* ty_fld_elim *) simpls. apply* ty_fld_elim.
  - (* ty_let *)
    apply_fresh ty_let as z; eauto.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    apply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_rec_intro *)
    apply ty_rec_intro.
    assert (trm_path (p_var (avar_f (If x = x0 then y else x)))
        = subst_trm x0 y (trm_path (p_var (avar_f x))) ) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    assert ((subst_typ x0 y T) ||^ (If x = x0 then y else x) = subst_typ x0 y (T ||^ x)) as B. {
      rewrite subst_open_commute_typ. unfold subst_fvar. reflexivity.
    }
    rewrite B. apply* H.
  - (* ty_rec_elim *)
    rewrite subst_open_commute_typ. apply* ty_rec_elim.
  - (* ty_and_intro *)
    apply ty_and_intro; eauto.
  - (* ty_sngl_intro *)
    apply* ty_sngl_intro.
  - (* ty_sub *)
    apply* ty_sub.
  - apply* ty_p_intro.
  - simpls. rewrite subst_open_commute_typ_p. apply* ty_p_rec_elim.
  - apply* ty_p_and_elim1.
  - apply* ty_p_and_elim_2.
  - simpls. apply* ty_p_fld_elim. apply* inert_sngl_subst.
  - apply* ty_p_sub.
  - (* ty_def_trm *)
    apply ty_def_trm.
    assert (G1 & subst_ctx x y G2 & z ~ subst_typ x y U = G1 & subst_ctx x y (G2 & z ~ U)) as Hs. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. rewrite concat_assoc.
      reflexivity.
    }
    rewrite Hs.
    assert (z <> x) as Hn. {
      rewrite <- concat_assoc in H1.
      apply ok_middle_inv_r in H1. unfold not. intro Hx. subst. unfold notin in H1.
      unfold not in H1. simpl_dom.
      assert (x \in \{ x} \u dom G2) as Hx. {
        rewrite in_union. left. rewrite in_singleton. reflexivity.
      }
      apply H1 in Hx. false.
    }
    apply H; auto. rewrite concat_assoc. reflexivity. rewrite concat_assoc.
    assumption.
    assert (subst_ctx x y (G2 & z ~ U) = (subst_ctx x y G2) & z ~ (subst_typ x y U)). {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite H0. rewrite concat_assoc. apply weaken_ty_trm.
    apply H3.
    assert (subst_ctx x y G2 & z ~ subst_typ x y U = subst_ctx x y (G2 & z ~ U)) as Hsu by auto.
    rewrite <- concat_assoc. rewrite Hsu. apply ok_concat_map. rewrite <- concat_assoc in H1.
    apply ok_remove in H1. assumption.
  - (* ty_def_val *)
    apply ty_def_val. specialize (H G1 (G2 & z ~ U) x).
    replace (G1 & subst_ctx x y G2 & z ~ subst_typ x y U) with (G1 & subst_ctx x y (G2 & z ~ U)).
    + apply H; auto; try rewrite* concat_assoc. unfold subst_ctx. rewrite map_concat.
      rewrite concat_assoc. unfold subst_ctx in H3. apply* weaken_ty_trm.
      apply ok_concat_map. rewrite <- concat_assoc in H1.
      apply ok_remove in H1. rewrite concat_assoc in H1. apply ok_push.
      * apply* ok_concat_map.
      * apply ok_push_inv in H1. destruct* H1.
    + unfold subst_ctx. rewrite map_concat. rewrite concat_assoc. rewrite* map_single.
  - (* ty_defs_cons *)
    apply* ty_defs_cons. rewrite <- subst_label_of_def. apply subst_defs_hasnt. assumption.
  - (* subtyp_trans *)
    eapply subtyp_trans; eauto.
  - (* subtyp_sel2 *)
    eapply subtyp_sel2; eauto.
    eapply H; eauto.
  - (* subtyp_sel1 *)
    eapply subtyp_sel1; eauto.
    eapply H; eauto.
  - (* subtyp_sngl_sel1 *)
    specialize (H0 _ _ _ eq_refl H2 H3 H4). simpl in H0.
    apply* subtyp_sngl_sel1.
  - (* subtyp_sngl_sel2 *)
    specialize (H0 _ _ _ eq_refl H2 H3 H4). simpl in H0.
    apply* subtyp_sngl_sel2.
  - (* subtyp_all *)
    apply_fresh subtyp_all as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- A at 3.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y S2 = subst_ctx x y (G2 & z ~ S2)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
Qed.

Lemma subst_ty_trm: forall y S G x t T,
    G & x ~ S |- t : T ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    G |- trm_path (p_var (avar_f y)) : subst_typ x y S ->
    G |- subst_trm x y t : subst_typ x y T.
Proof.
  intros.
  apply (proj51 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H.
  unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  assumption.
  unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption.
Qed.

Lemma subst_ty_defs: forall y S G x ds z U T,
    G & x ~ S && z ~ U |- ds :: T ->
    ok (G & x ~ S & z ~ U) ->
    x \notin fv_ctx_types G ->
    G |- trm_path (p_var (avar_f y)) : subst_typ x y S ->
    G && z ~ subst_typ x y U |- subst_defs x y ds :: subst_typ x y T.
Proof.
  intros.
  assert (G & subst_ctx x y empty && z ~ subst_typ x y U |- subst_defs x y ds :: subst_typ x y T) as Hs. {
    apply* subst_rules; try rewrite* concat_empty_r. unfold subst_ctx. rewrite map_empty.
    rewrite* concat_empty_r.
  }
  unfold subst_ctx in Hs. rewrite map_empty in Hs. rewrite* concat_empty_r in Hs.
Qed.
