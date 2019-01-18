(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import List Coq.Program.Equality.
Require Import Definitions Binding Replacement Weakening.

Ltac subst_open_fresh :=
  match goal with
  | [ |- context [ open_typ ?z (subst_typ ?x ?p ?T) ] ] =>
    replace (open_typ z (subst_typ x p T)) with (open_typ_p (subst_path x p (pvar z)) (subst_typ x p T)) by
        (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_typ_eq; auto)
    | [ |- context [ open_defs ?z (subst_defs ?x ?p ?ds) ] ] =>
        replace (open_defs z (subst_defs x p ds)) with (open_defs_p (subst_path x p (pvar z)) (subst_defs x p ds))
          by (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_defs_eq; auto)
     | [ |- context [ open_trm ?z (subst_trm ?x ?p ?t) ] ] =>
        replace (open_trm z (subst_trm x p t)) with (open_trm_p (subst_path x p (pvar z)) (subst_trm x p t))
          by (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_trm_eq; auto)
    end.

Ltac subst_fresh_solver :=
  fresh_constructor;
  subst_open_fresh;
  match goal with
  | [ H: forall z, z \notin ?L -> forall G, _
      |- context [_ & subst_ctx ?x ?p ?G2 & ?z ~ subst_typ ?x ?p ?V] ] =>
    assert (subst_ctx x p G2 & z ~ subst_typ x p V = subst_ctx x p (G2 & z ~ V)) as B
        by (unfold subst_ctx; rewrite map_concat, map_single; reflexivity);
    rewrite <- concat_assoc; rewrite B;
    subst_open_fresh;
    rewrite* <- subst_open_commut_trm_p;
    rewrite* <- subst_open_commut_typ_p;
    rewrite <- open_var_typ_eq, <- open_var_trm_eq;
    apply* H; try rewrite* concat_assoc;
    rewrite <- B, concat_assoc; unfold subst_ctx;
    auto using weaken_ty_trm, ok_push, ok_concat_map
  end.
    (* try match goal with
            | [ |- _; _; _; _ ⊢ _ _ _ :: _ ] =>
              assert (z = subst_var_p x y z) as Hxyz by (unfold subst_var_p; rewrite~ If_r);
                rewrite Hxyz at 1
            end; *)

Ltac subst_tydef_solver :=
  match goal with
    | [ H: forall G3 G4 x, _,
          Hok: ok _,
          Hx: ?x \notin fv_ctx_types _,
          Hy: _ & _ ⊢ _ : _ |- _] =>
      specialize (H _ _ _ eq_refl Hok Hx);
      try solve [rewrite subst_open_commut_defs_p in H;
                 rewrite subst_open_commut_typ_p in H; eauto]
    end.


Lemma open_typ_subst: forall x y p T,
  named_path p ->
  x <> y ->
  open_typ x (subst_typ y p T) =
  subst_typ y p (open_typ x T).
Proof.
  intros.
  rewrite open_var_typ_eq.
  unfold open_typ.
  rewrite subst_open_commut_typ.
  - f_equal. unfold subst_var_p. case_if*.
  - apply H.
Qed.

(** * Substitution Lemma *)
(** [G1, x: S, G2 ⊢ t: T]            #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ t[y/x]: T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ d: D]            #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ d[y/x]: D[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ ds: T]           #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]       #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ ds[y/x]: T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ T <: U]           #<br>#
    [ok(G1, x: S, G2)]                #<br>#
    [x \notin fv(G1)]                  #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]        #<br>#
    [―――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ T[y/x] <: U[y/x]] #<br>#  #<br># *)

(** The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma subst_rules: forall p S,
  (forall G t T, G ⊢ t : T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    G1 & (subst_ctx x p G2) ⊢ subst_trm x p t : subst_typ x p T) /\
  (forall z bs P G d D, z; bs; P; G ⊢ d : D -> forall G1 G2 x p_x p_bs sbs,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    p = p_sel (avar_f p_x) p_bs ->
    z <> p_x ->
    z <> x ->
    sbs = (If z = x then p_bs ++ bs else bs) ->
    subst_var x p_x z; sbs; P; G1 & (subst_ctx x p G2) ⊢ subst_def x p d : subst_dec x p D) /\
  (forall z bs P G ds T, z; bs; P; G ⊢ ds :: T -> forall G1 G2 x p_x p_bs sbs,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    p = p_sel (avar_f p_x) p_bs ->
    z <> p_x ->
    z <> x ->
    sbs = (If z = x then p_bs ++ bs else bs) ->
    subst_var x p_x z; sbs; P; G1 & (subst_ctx x p G2) ⊢ subst_defs x p ds :: subst_typ x p T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    G1 & (subst_ctx x p G2) ⊢ subst_typ x p T <: subst_typ x p U).
Proof.
  intros p S.
  apply rules_mutind; intros; subst; simpl;
  try (subst_fresh_solver || rewrite subst_open_commut_typ_p);
  simpl in *; autounfold;
  try assert (named_path p) as Hn by apply* typed_paths_named;
  eauto 4.
  - Case "ty_var".
    cases_if.
    + apply binds_middle_eq_inv in b; subst*. destruct* p.
    + eapply subst_fresh_ctx in H1.
      apply binds_subst in b; auto.
      constructor. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map; auto.
  - Case "ty_all_intro".
    fresh_constructor.
    subst_open_fresh.
    destruct p as [p_x p_bs].
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _
        |- context [_ & subst_ctx ?x ?p ?G2 & ?z ~ subst_typ ?x ?p ?V] ] =>
      assert (subst_ctx x p G2 & z ~ subst_typ x p V = subst_ctx x p (G2 & z ~ V)) as B
          by (unfold subst_ctx; rewrite map_concat, map_single; reflexivity);
        rewrite <- concat_assoc; rewrite B;
          subst_open_fresh;
          rewrite* <- subst_open_commut_trm_p;
          rewrite* <- subst_open_commut_typ_p;
          rewrite <- open_var_trm_eq, <- open_var_typ_eq;
          apply* H; try rewrite* concat_assoc;
            rewrite <- B, concat_assoc; unfold subst_ctx;
              auto using weaken_ty_trm, ok_push, ok_concat_map
    end.
  - Case "ty_new_intro".
    fresh_constructor.
    subst_open_fresh.
    match goal with
    | [ |- _; _; _; _ ⊢ _ _ _ :: _ ] =>
      assert (pvar z = subst_var_p x p z) as Hxyz by (unfold subst_var_p; rewrite~ If_r);
      rewrite Hxyz at 1
    end.
    rewrite <- Hxyz.
    subst_open_fresh.
    rewrite* <- subst_open_commut_typ_p.
    rewrite* <- subst_open_commut_defs_p.
    assert (subst_ctx x p G2 & z ~ subst_typ x p (open_typ_p (pvar z) T) =
    subst_ctx x p (G2 & z ~ open_typ_p (pvar z) T)) as Heq
    by (unfold subst_ctx; rewrite map_concat, map_single; reflexivity).
    rewrite <- concat_assoc. rewrite Heq.
    destruct p as [p_x p_bs].
    assert (exists p_x0, p_x = avar_f p_x0) as Heq'. {
      inversions Hn. destruct_all. inversions H0. eauto.
    }
    destruct Heq' as [p_x0 Heq']; subst.
    assert (z = subst_var x p_x0 z) as Heq'. {
      unfolds subst_var; rewrite~ If_r.
    }
    rewrite Heq' at 1.
    rewrite <- open_var_typ_eq, <- open_var_defs_eq.
    apply* H; try rewrite* concat_assoc.
    unfolds subst_ctx. rewrite map_concat. rewrite concat_assoc.
    apply* weaken_ty_trm.
    simpl in Frz. eauto.
    assert (z <> x) as Hneq0 by eauto.
    case_if; eauto.
  - Case "ty_new_elim".
    asserts_rewrite (subst_path x p p0 • a = (subst_path x p p0) • a).
    destruct p0. apply sel_fields_subst. auto.
  - Case "ty_let".
    fresh_constructor.
    subst_open_fresh.
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _
      |- context [_ & subst_ctx ?x ?p ?G2 & ?z ~ subst_typ ?x ?p ?V] ] =>
      assert (subst_ctx x p G2 & z ~ subst_typ x p V = subst_ctx x p (G2 & z ~ V)) as B
      by (unfold subst_ctx; rewrite map_concat, map_single; reflexivity);
      rewrite <- concat_assoc; rewrite B;
        rewrite* <- subst_open_commut_trm_p;
      rewrite <- open_var_trm_eq;
        apply* H; try rewrite* concat_assoc;
          rewrite <- B, concat_assoc; unfold subst_ctx;
          auto using weaken_ty_trm, ok_push, ok_concat_map
    end.
  - Case "ty_path_elim".
    destruct p0, q.
    rewrite sel_fields_subst.
    rewrite sel_fields_subst.
    eapply ty_path_elim; try (rewrite <- sel_fields_subst); auto.
  - Case "ty_rec_intro".
    constructor. rewrite* <- subst_open_commut_typ_p.
  - Case "ty_def_new".
    specialize (H _ _ _ _ _ _ eq_refl H1 H2 H3 eq_refl H5 H6 eq_refl).
    assert (named_path (p_sel (avar_f p_x) p_bs)) as Hn by repeat eexists.
    rewrite* subst_open_commut_defs_p in H.
    rewrite* subst_open_commut_typ_p in H.
    unfolds subst_var.
    remember (p_sel (avar_f p_x) p_bs) as p.
    eapply ty_def_new; eauto.
    * replace (typ_bnd (subst_typ x0 p T)) with (subst_typ x0 p (typ_bnd T)) by reflexivity.
      apply inert_subst. apply i.
    * simpl. case_if*.
      replace (p_sel (avar_f x) (b :: bs)) with (subst_path x0 p (p_sel (avar_f x) (b :: bs))); eauto.
      simpl. unfold subst_var_p.
      case_if*. simpl. rewrite app_nil_r. reflexivity.
  - Case "ty_def_path".
    remember (p_sel (avar_f p_x) p_bs) as p in *.
    subst_tydef_solver.
    case_if; case_if.
    * eapply ty_def_path.
      3: { rewrite Heqp. simpl. eauto. }
      + replace (trm_path p •• cs)
        with (trm_path (subst_var_p x0 p y) •• cs).
        eapply H; eauto.
        f_equal. unfold subst_var_p. case_if. reflexivity.
      + apply inert_subst. apply i.
      + intro. destruct (H5 H0).
    * eapply ty_def_path.
      3: { simpl. eauto. }
      + replace (p_sel (avar_f y) nil) with (subst_var_p x0 p y).
        eapply H; eauto. unfold subst_var_p. case_if. reflexivity.
      + apply inert_subst. apply i.
      + rewrite app_nil_r. apply p0.
  - Case "ty_defs_one".
    apply ty_defs_one.
    eapply H; eauto.
  - Case "ty_defs_cons".
    apply ty_defs_cons.
    * eapply H; eauto.
    * eapply H0; eauto.
    * eapply subst_defs_hasnt_label. apply d0.
  - Case "subtyp_sngl_pq".
    subst_tydef_solver.
    eapply subtyp_sngl_pq; eauto.
    eapply repl_typ_subst. apply r.
  - Case "subtyp_sngl_qp".
    subst_tydef_solver.
    eapply subtyp_sngl_qp; eauto.
    eapply repl_typ_subst. apply r.
  - Case "subtyp_all".
    subst_tydef_solver.
    eapply (@subtyp_all (L \u \{ x } \u (dom (G1 & (subst_ctx x p G2)) \u (dom (G1 & x ~ S & G2))))). eauto.
    intros x0 Hx0.
    assert (Hx0inL: x0 \notin L) by auto.
    assert (Hxx0: x0 <> x) by auto.
    assert (Hx0inG: x0 # (G1 & (subst_ctx x p G2))) by auto.
    rewrite open_typ_subst; try assumption.
    rewrite open_typ_subst; try assumption.
    specialize (H0 x0 Hx0inL G1 (G2 & x0 ~ S2) x).
    replace (G1 & subst_ctx x p G2 & x0 ~ subst_typ x p S2)
    with (G1 & subst_ctx x p (G2 & x0 ~ S2)).
    * eapply H0.
      + rewrite concat_assoc. reflexivity.
      + rewrite concat_assoc. constructor.
        apply H2. auto.
      + apply H3.
      + unfold subst_ctx. rewrite map_push.
        rewrite concat_assoc. fold subst_ctx.
        apply weaken_ty_trm.
        apply H4. constructor; auto.
    * unfold subst_ctx. rewrite map_push.
      rewrite concat_assoc. reflexivity.
Qed.

(** The substitution lemma for term typing.
    This lemma corresponds to Lemma 3.14 in the paper. *)
Lemma subst_ty_trm: forall p S G x t T,
    G & x ~ S ⊢ t : T ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    G ⊢ trm_path p : subst_typ x p S ->
    G ⊢ subst_trm x p t : subst_typ x p T.
Proof.
  introv Ht Hok Hx Hp.
  apply (proj41 (subst_rules p S)) with (G1:=G) (G2:=empty) (x:=x) in Ht.
  unfold subst_ctx in Ht. rewrite map_empty, concat_empty_r in Ht.
  apply Ht. rewrite* concat_empty_r. rewrite* concat_empty_r. assumption.
  unfold subst_ctx. rewrite map_empty, concat_empty_r. assumption.
Qed.

Lemma subst_ty_defs: forall z bs P G x S ds T p p_x p_bs sbs,
    z; bs; P; G & x ~ S ⊢ ds :: T ->
    p = p_sel (avar_f p_x) p_bs ->
    z <> p_x ->
    z <> x ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    G ⊢ trm_path p : subst_typ x p S ->
    sbs = (If z = x then p_bs ++ bs else bs) ->
    subst_var x p_x z; sbs; P; G ⊢ subst_defs x p ds :: subst_typ x p T.
Proof.
  introv Hds Heq Hzpx Hzx Hok Hx Hp Hsbs.
  eapply (proj43 (subst_rules p S)) with
      (G1 := G) (G2 := empty) (x := x) (p_x := p_x) (p_bs := p_bs) (sbs := sbs) in Hds;
    unfold subst_ctx in *; try rewrite map_empty in *; try rewrite concat_empty_r in *; auto.
Qed.

(** * Renaming  *)

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z : T^z]    #<br>#
    [G ⊢ p: U]               #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^p : T^p]         *)
Lemma renaming_typ: forall G z T U t p,
    ok G ->
    z # G ->
    z \notin (fv_ctx_types G \u fv_typ U \u fv_typ T \u fv_trm t) ->
    G & z ~ U ⊢ open_trm z t : open_typ z T ->
    G ⊢ trm_path p : U ->
    G ⊢ open_trm_p p t : open_typ_p p T.
Proof.
  introv Hok Hnz Hnz' Hz Hx. rewrite subst_intro_typ with (x:=z). rewrite subst_intro_trm with (x:=z).
  eapply subst_ty_trm; auto. eapply Hz.
  rewrite subst_fresh_typ. all: eauto using typed_paths_named.
Qed.

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z : T^z]    #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x : T^x]         *)
Lemma renaming_fresh : forall L G T u U p,
    ok G ->
    (forall x : var, x \notin L -> G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢ trm_path p : T ->
    G ⊢ open_trm_p p u : U.
Proof.
  introv Hok Hu Hp. pick_fresh y.
  rewrite subst_intro_trm with (x:=y); auto.
  rewrite <- subst_fresh_typ with (x := y) (p := p); auto.
  eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
  apply* typed_paths_named.
Qed.

Lemma rename_defs G x P T ds z :
  x; nil; P; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T ->
  ok (G & x ~ open_typ x T & z ~ open_typ z T) ->
  z; nil; P; G & z ~ open_typ z T ⊢ open_defs z ds :: open_typ z T.
Proof.
  intros Hds Hok.
  apply weaken_ty_defs with (G2:=z ~ open_typ z T) in Hds; auto.
  assert (z = subst_var x z z) as Heq. {
    unfold subst_var. case_if; auto.
  }
  rewrite Heq at 1. rewrite open_var_defs_eq, open_var_typ_eq. rewrite subst_intro_defs with (x:=x).
  - rewrite subst_intro_typ with (x:=x).
    + (* todo: this doesn't work, we can't use substitution for this. we need to do a mutual induction
         and prove this from scratch. *)
  Admitted.
