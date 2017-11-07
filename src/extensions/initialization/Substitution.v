Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.

(* ###################################################################### *)
(** ** Substitution *)

Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_sel x L    => typ_sel (subst_avar z u x) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  | typ_ref T      => typ_ref (subst_typ z u T)
  | typ_nref T     => typ_nref (subst_typ z u T)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L U => dec_trm L (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_val v        => trm_val (subst_val z u v)
  | trm_sel x1 L     => trm_sel (subst_avar z u x1) L
  | trm_app x1 x2    => trm_app (subst_avar z u x1) (subst_avar z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  | trm_ref T        => trm_ref (subst_typ z u T)
  | trm_deref x      => trm_deref (subst_avar z u x)
  | trm_asg x y      => trm_asg (subst_avar z u x) (subst_avar z u y)
  | trm_ifnull x y   => trm_ifnull (subst_avar z u x) (subst_avar z u y)
  end
with subst_val (z: var) (u: var) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  | val_loc l        => val_loc l
  | val_null         => val_null
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

Definition subst_env (z: var) (u: var) (e: env typ) : env typ := map (subst_typ z u) e.

(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_avar.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec x y).

Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec).
Qed.

Lemma invert_fv_env_types_push: forall x z T G,
  x \notin fv_env_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_env_types G).
Proof.
  introv N.
  unfold fv_env_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

Lemma subst_fresh_env: forall x y e,
  x \notin fv_env_types e -> subst_env x y e = e.
Proof.
  intros x y.
  apply (env_ind (fun G => x \notin fv_env_types G -> subst_env x y G = G)).
  + intro N. unfold subst_env. apply map_empty.
  + intros G z T IH N.
    apply invert_fv_env_types_push in N. destruct N as [N1 N2].
    unfold subst_env in *. rewrite map_push.
    rewrite (IH N2).
    rewrite ((proj1 (subst_fresh_typ_dec _ _)) _ N1).
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
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_avar.
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec.
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
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

Lemma subst_open_commute_defs: forall x y u ds,
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commute_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
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

(* ###################################################################### *)
(** ** The substitution principle *)

Lemma subst_rules: forall y U,
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (trm_var (avar_f y)) (subst_typ x y U) ->
    m1 = ty_general ->
    m2 = sub_general ->
    ty_trm m1 m2 (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (subst_trm x y t) (subst_typ x y T)) /\
  (forall G S d D, ty_def G S d D -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (trm_var (avar_f y)) (subst_typ x y U) ->
    ty_def (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (subst_def x y d) (subst_dec x y D)) /\
  (forall G S ds T, ty_defs G S ds T -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (trm_var (avar_f y)) (subst_typ x y U) ->
    ty_defs (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (subst_defs x y ds) (subst_typ x y T)) /\
  (forall m1 m2 G S T V, subtyp m1 m2 G S T V -> forall G1 G2 S1 S2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_env_types G1 ->
    S = S1 & S2 ->
    x \notin fv_env_types S1 ->
    ty_trm ty_general sub_general (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (trm_var (avar_f y)) (subst_typ x y U) ->
    m1 = ty_general ->
    m2 = sub_general ->
    subtyp m1 m2 (G1 & (subst_env x y G2)) (S1 & subst_env x y S2) (subst_typ x y T) (subst_typ x y V)).
Proof.
  intros y S. apply rules_mutind; intros; subst.
  - (* ty_var *)
    simpl. cases_if.
    + apply binds_middle_eq_inv in b; subst; assumption.
    + apply subst_fresh_env with (y:=y) in H1.
      apply binds_subst in b; auto.
      apply ty_var. rewrite <- H1.
      unfold subst_env. rewrite <- map_concat.
      apply binds_map; auto.
  - (* ty_loc *)
    simpl. apply ty_loc. apply subst_fresh_env with (y:=y) in H3.
    rewrite <- H3. unfold subst_env. rewrite <- map_concat. apply binds_map. assumption.
  - (* ty_all_intro *)
    simpl.
    apply_fresh ty_all_intro as z; auto.
    assert (z \notin L) as FrL by auto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. auto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    rewrite <- A at 3. rewrite <- subst_open_commute_typ.
    assert (subst_env x y G2 & z ~ subst_typ x y T = subst_env x y (G2 & z ~ T)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    eapply H; auto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_env. auto.
  - (* ty_all_elim *)
    simpl. rewrite subst_open_commute_typ.
    eapply ty_all_elim.
    simpl in H.
    apply H; auto.
    apply H0; auto.
  - (* ty_new_intro *)
    simpl.
    apply_fresh ty_new_intro as z; auto.
    assert (z \notin L) as FrL by auto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. auto.
    }
    rewrite <- A at 2. rewrite <- A at 3. rewrite <- A at 4.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_defs.
    assert (subst_env x y G2 & z ~ subst_typ x y (open_typ z T) = subst_env x y (G2 & z ~ open_typ z T)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H; auto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_env. auto.
  - (* ty_new_elim *)
    simpl. apply ty_new_elim.
    apply H; auto.
  - (* ty_let *)
    simpl.
    apply_fresh ty_let as z; auto.
    assert (subst_env x y G2 & z ~ subst_typ x y T = subst_env x y (G2 & z ~ T)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r; auto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    apply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_env. auto.
  - (* ty_rec_intro *)
    simpl. apply ty_rec_intro.
    assert (trm_var (avar_f (If x = x0 then y else x)) = subst_trm x0 y (trm_var (avar_f x))) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    assert (open_typ (If x = x0 then y else x) (subst_typ x0 y T) = subst_typ x0 y (open_typ x T)) as B. {
      rewrite subst_open_commute_typ. unfold subst_fvar. reflexivity.
    }
    rewrite B.
    apply H; auto.
  - (* ty_rec_elim *)
    simpl. rewrite subst_open_commute_typ.
    apply ty_rec_elim.
    apply H; auto.
  - (* ty_and_intro *)
    simpl.
    assert (trm_var (avar_f (If x = x0 then y else x)) = subst_trm x0 y (trm_var (avar_f x))) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    apply ty_and_intro; eauto 3.
  - (* ty_sub *)
    eapply ty_sub; eauto.
  - (* ty_and1 *)
    simpl. eapply ty_and1; eauto.
  - (* ty_and2 *)
    simpl. eapply ty_and2; eauto.
  - (* ty_ref_intro *) 
    simpl. apply ty_ref_intro. 
  - (* ty_ref_elim *)
    apply ty_ref_elim; eauto.
  (* - (* ty_asgn_ref *) *)
  (*   apply ty_asgn_ref; eauto. *)
  - (* ty_asgn_nref *)
    apply ty_asgn_nref; eauto.
  - (* ty_ifnull *)
    simpl. apply ty_ifnull; eauto. 
  - (* ty_null *)
    constructor.
  - (* ty_def_typ *)
    simpl. apply ty_def_typ; auto.
  - (* ty_def_trm *)
    simpl. apply ty_def_trm; auto.
  - (* ty_defs_one *)
    simpl. apply ty_defs_one; auto.
  - (* ty_defs_cons *)
    simpl. apply ty_defs_cons; auto.
    rewrite <- subst_label_of_def.
    apply subst_defs_hasnt. assumption.
  - (* subtyp_top *)
    apply subtyp_top.
  - (* subtyp_bot *)
    apply subtyp_bot.
  - (* subtyp_refl *)
    apply subtyp_refl.
  - (* subtyp_trans *)
    eapply subtyp_trans; auto 5.
  - (* subtyp_and11 *)
    apply subtyp_and11; auto.
  - (* subtyp_and12 *)
    apply subtyp_and12; auto.
  - (* subtyp_and2 *)
    apply subtyp_and2; auto.
  - (* subtyp_fld *)
    apply subtyp_fld; auto.
  - (* subtyp_typ *)
    apply subtyp_typ; auto.
  - (* subtyp_sel2 *)
    eapply subtyp_sel2.
    apply H; auto.
  - (* subtyp_sel1 *)
    eapply subtyp_sel1.
    apply H; auto.
  - (* subtyp_sel2_tight *) inversion H7.
  - (* subtyp_sel1_tight *) inversion H7.
  - (* subtyp_all *)
    simpl. apply_fresh subtyp_all as z; auto.
    assert (z \notin L) as FrL by auto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. auto.
    }
    rewrite <- A at 2. rewrite <- A at 3.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_env x y G2 & z ~ subst_typ x y S2 = subst_env x y (G2 & z ~ S2)) as B. {
      unfold subst_env. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H0; auto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm_ctx. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_env. auto.
  - (* subtyp_ref *) 
    apply* subtyp_ref.
  - (* subtyp_nref *)
    apply* subtyp_nref. 
  - (* subtyp_ref_nref *)
    constructor.
Qed.

Lemma subst_ty_trm: forall y V G S x t T,
    ty_trm ty_general sub_general (G & x ~ V) S t T ->
    ok (G & x ~ V) ->
    x \notin fv_env_types G ->
    x \notin fv_env_types S ->
    ty_trm ty_general sub_general G S (trm_var (avar_f y)) (subst_typ x y V) ->
    ty_trm ty_general sub_general G S (subst_trm x y t) (subst_typ x y T).
Proof.
  intros.
  apply (proj51 (subst_rules y V)) with (G1:=G) (G2:=empty) (S1:=S) (S2:=empty) (x:=x) in H; try assumption.
  unfold subst_env in H. rewrite map_empty in H. rewrite concat_empty_r in H. 
  rewrite concat_empty_r in H. apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  rewrite concat_empty_r. reflexivity.
  unfold subst_env. rewrite map_empty. repeat rewrite concat_empty_r. assumption.
  reflexivity.
  reflexivity.
Qed.

Lemma subst_ty_defs: forall y V G S x ds T,
    ty_defs (G & x ~ V) S ds T ->
    ok (G & x ~ V) ->
    x \notin fv_env_types G ->
    x \notin fv_env_types S ->
    ty_trm ty_general sub_general G S (trm_var (avar_f y)) (subst_typ x y V) ->
    ty_defs G S (subst_defs x y ds) (subst_typ x y T).
Proof.
  intros.
  apply (proj53 (subst_rules y V)) with (G1:=G) (G2:=empty) (S1:=S) (S2:=empty) (x:=x) in H; try rewrite concat_empty_r; auto.
  - unfold subst_env in H. rewrite map_empty in H. repeat rewrite concat_empty_r in H.
    apply H.
  - unfold subst_env. rewrite map_empty. repeat rewrite concat_empty_r. assumption.
Qed.
