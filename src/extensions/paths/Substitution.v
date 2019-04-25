(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Substitution and Renaming *)

Set Implicit Arguments.

Require Import List Coq.Program.Equality String.
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
        by (unfold subst_ctx; rewrite map_concat, map_single; auto);
    rewrite <- concat_assoc; rewrite B;
    subst_open_fresh;
    rewrite* <- subst_open_commut_trm_p;
    rewrite* <- subst_open_commut_typ_p;
    rewrite <- open_var_typ_eq, <- open_var_trm_eq;
    apply* H; try rewrite* concat_assoc;
    rewrite <- B, concat_assoc; unfold subst_ctx;
    auto using weaken_ty_trm, ok_push, ok_concat_map
  end.

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

(** Substitution preserves tight-boundness in types and declaration *)
Lemma tight_bounds_subst_mut :
  (forall T, tight_bounds T -> forall x p, tight_bounds (subst_typ x p T)) /\
  (forall D, tight_bounds_dec D -> forall x p, tight_bounds_dec (subst_dec x p D)).
Proof.
  apply typ_mutind; intros; subst; simpls; subst; eauto. split*.
Qed.

(** ...for types only *)
Lemma tight_bounds_subst x p T :
  tight_bounds T -> tight_bounds (subst_typ x p T).
Proof.
  intros. apply* tight_bounds_subst_mut.
Qed.

(** ** Substitution Lemma *)
(** [G1, x: S, G2 ⊢ t: T]            #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[p/x] ⊢ p: S[p/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[p/x] ⊢ t[p/x]: T[p/x]] #<br>#  #<br>#

    and

    [z.bs; G1, x: S, G2 ⊢ d: D]            #<br>#
    [x \notin fv(G1)]                 #<br>#
    [x ≠ z]                           #<br>#
    [G1, G2[p/x] ⊢ p: S[p/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [z.bs; G1, G2[p/x] ⊢ d[p/x]: D[p/x]] #<br>#  #<br>#

    and

    [z.bs; G1, x: S, G2 ⊢ ds: T]           #<br>#
    [x \notin fv(G1)]                 #<br>#
    [x ≠ z]                           #<br>#
    [G1, G2[p/x] ⊢ p: S[p/x]]       #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [z.bs; G1, G2[p/x] ⊢ ds[p/x]: T[p/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ T <: U]           #<br>#
    [x \notin fv(G1)]                  #<br>#
    [G1, G2[p/x] ⊢ p: S[p/x]]        #<br>#
    [―――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[p/x] ⊢ T[p/x] <: U[p/x]] #<br>#  #<br># *)

(** The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma subst_rules: forall p S,
  (forall G t T, G ⊢ t : T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    G1 & (subst_ctx x p G2) ⊢ subst_trm x p t : subst_typ x p T) /\
  (forall z bs G d D, z; bs; G ⊢ d : D -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    z <> x ->
    z; bs; G1 & (subst_ctx x p G2) ⊢ subst_def x p d : subst_dec x p D) /\
  (forall z bs G ds T, z; bs; G ⊢ ds :: T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    z <> x ->
    z; bs; G1 & (subst_ctx x p G2) ⊢ subst_defs x p ds :: subst_typ x p T) /\
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
  - Case "ty_var"%string.
    cases_if.
    + apply binds_middle_eq_inv in b; subst*. destruct* p.
    + eapply subst_fresh_ctx in H1.
      apply binds_subst in b; auto.
      constructor. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map; auto.
  - Case "ty_all_intro"%string.
    fresh_constructor.
    subst_open_fresh.
    destruct p as [p_x p_bs].
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _
        |- context [_ & subst_ctx ?x ?p ?G2 & ?z ~ subst_typ ?x ?p ?V] ] =>
      assert (subst_ctx x p G2 & z ~ subst_typ x p V = subst_ctx x p (G2 & z ~ V)) as B
          by (unfold subst_ctx; rewrite map_concat, map_single; auto);
        rewrite <- concat_assoc; rewrite B;
          subst_open_fresh;
          rewrite* <- subst_open_commut_trm_p;
          rewrite* <- subst_open_commut_typ_p;
          rewrite <- open_var_trm_eq, <- open_var_typ_eq;
          apply* H; try rewrite* concat_assoc;
            rewrite <- B, concat_assoc; unfold subst_ctx;
              auto using weaken_ty_trm, ok_push, ok_concat_map
    end.
  - Case "ty_new_intro"%string.
    fresh_constructor.
    subst_open_fresh.
    match goal with
    | [ |- _; _; _ ⊢ _ _ _ :: _ ] =>
      assert (pvar z = subst_var_p x p z) as Hxyz by (unfold subst_var_p; rewrite~ If_r);
      rewrite Hxyz at 1
    end.
    rewrite <- Hxyz.
    subst_open_fresh.
    rewrite* <- subst_open_commut_typ_p.
    rewrite* <- subst_open_commut_defs_p.
    assert (subst_ctx x p G2 & z ~ subst_typ x p (open_typ_p (pvar z) T) =
    subst_ctx x p (G2 & z ~ open_typ_p (pvar z) T)) as Heq
    by (unfold subst_ctx; rewrite map_concat, map_single; auto).
    rewrite <- concat_assoc. rewrite Heq.
    destruct p as [p_x p_bs].
    assert (exists p_x0, p_x = avar_f p_x0) as Heq'. {
      inversions Hn. destruct_all. inversions H0. eauto.
    }
    destruct Heq' as [p_x0 Heq']; subst.
    assert (z = subst_var x p_x0 z) as Heq'. {
      unfolds subst_var; rewrite~ If_r.
    }
    rewrite <- open_var_typ_eq, <- open_var_defs_eq.
    apply* H; try rewrite* concat_assoc.
    unfolds subst_ctx. rewrite map_concat. rewrite concat_assoc.
    apply* weaken_ty_trm.
  - Case "ty_new_elim"%string.
    asserts_rewrite (subst_path x p p0 • a = (subst_path x p p0) • a).
    destruct p0. apply sel_fields_subst. auto.
  - Case "ty_rcd_intro"%string.
    assert (subst_path x p p0 • a = (subst_path x p p0) • a) as Heq. {
      destruct p0. apply sel_fields_subst.
    }
    specialize (H _ _ _ eq_refl H1 H2 H3). rewrite Heq in H. eauto.
  - Case "ty_let"%string.
    fresh_constructor.
    subst_open_fresh.
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _
      |- context [_ & subst_ctx ?x ?p ?G2 & ?z ~ subst_typ ?x ?p ?V] ] =>
      assert (subst_ctx x p G2 & z ~ subst_typ x p V = subst_ctx x p (G2 & z ~ V)) as B
      by (unfold subst_ctx; rewrite map_concat, map_single; auto);
      rewrite <- concat_assoc; rewrite B;
        rewrite* <- subst_open_commut_trm_p;
      rewrite <- open_var_trm_eq;
        apply* H; try rewrite* concat_assoc;
          rewrite <- B, concat_assoc; unfold subst_ctx;
          auto using weaken_ty_trm, ok_push, ok_concat_map
    end.
  - Case "ty_path_elim"%string.
    destruct p0, q.
    rewrite sel_fields_subst.
    rewrite sel_fields_subst.
    eapply ty_path_elim; try (rewrite <- sel_fields_subst); auto.
  - Case "ty_rec_intro"%string.
    constructor. rewrite* <- subst_open_commut_typ_p.
  - Case "ty_def_new"%string.
    specialize (H _ _ _ eq_refl H1 H2 H3 H4).
    rewrite* subst_open_commut_defs_p in H.
    rewrite* subst_open_commut_typ_p in H.
    unfolds subst_var.
    eapply ty_def_new; eauto.
    * replace (μ (subst_typ x0 p T)) with (subst_typ x0 p (μ T)) by auto.
      apply tight_bounds_subst. eauto.
    * simpl.
      replace (p_sel (avar_f x) (b :: bs)) with (subst_path x0 p (p_sel (avar_f x) (b :: bs))); eauto.
      simpl. unfold subst_var_p.
      case_if*. simpl. rewrite app_nil_r. auto.
  - Case "ty_defs_cons"%string.
    apply ty_defs_cons.
    * eapply H; eauto.
    * eapply H0; eauto.
    * eapply subst_defs_hasnt_label. apply d0.
  - Case "subtyp_sngl_pq"%string.
    subst_tydef_solver.
    eapply subtyp_sngl_pq; eauto.
    eapply repl_typ_subst. apply r.
  - Case "subtyp_sngl_qp"%string.
    subst_tydef_solver.
    eapply subtyp_sngl_qp; eauto.
    eapply repl_typ_subst. apply r.
  - Case "subtyp_all"%string.
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
      + rewrite concat_assoc. auto.
      + rewrite concat_assoc. constructor.
        apply H2. auto.
      + apply H3.
      + unfold subst_ctx. rewrite map_push.
        rewrite concat_assoc. fold subst_ctx.
        apply weaken_ty_trm.
        apply H4. constructor; auto.
    * unfold subst_ctx. rewrite map_push.
      rewrite concat_assoc. auto.
Qed.

(** The substitution lemma for term typing. *)
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

(** Substitute a variable in the environment that is used for opening
    with a path of the same type #<br>#

    [z] fresh                #<br>#
    [G, z: U ⊢ t^z : T^z]    #<br>#
    [G ⊢ p: U]               #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^p : T^p]         *)
Lemma subst_var_path: forall G z T U t p,
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

(** Substitute a fresh opening variable with a path of the same type #<br>#

    [∀ fresh x, G, x: T ⊢ u^x: U] #<br>#
    [G ⊢ p: T]                    #<br>#
    [――――――――――――――――――――――]      #<br>#
    [G ⊢ u^p : U^p]         *)
Lemma subst_fresh_var_path : forall L G T u U p,
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

(** ** Renaming *)

(** Replace a variable bound in the environment with a fresh variable for typing *)
(** [G1, z: T, G2 ⊢ t: U]                      #<br>#
    [x] fresh                                  #<br>#
    [―――――――――――――――――――――――――――――――――――――――]  #<br>#
    [G1, x: T[x/z], G2[x/z] ⊢ t[x/z]: U[x/z]]
*)
Lemma rename_ty_trm x z G1 T G2 t U:
  z \notin fv_ctx_types G1 ->
  G1 & z ~ T & G2 ⊢ t : U ->
  ok (G1 & x ~ subst_typ z (pvar x) T & z ~ T & G2) ->
  G1 & x ~ subst_typ z (pvar x) T & subst_ctx z (pvar x) G2 ⊢ subst_trm z (pvar x) t : subst_typ z (pvar x) U.
Proof.
  intros Hz Ht Hok.
  assert (G1 & x ~ subst_typ z (pvar x) T & z ~ T & G2 ⊢ t : U). {
    rewrite <- concat_assoc in *. apply* weaken_rules.
  }
  eapply subst_rules.
  apply H. eauto. eauto.
  rewrite fv_ctx_types_push_eq. apply notin_union; split*.
  apply* fresh_subst_typ_dec. simpl. intros Hin. rewrite in_singleton in Hin. subst.
  rewrite <- concat_assoc in Hok.
  apply ok_middle_inv_r in Hok. simpl_dom. apply notin_union in Hok as [C%notin_singleton _]. false*.
  constructor. apply* binds_concat_left_ok. apply ok_remove in Hok.
  apply* ok_concat_map.
Qed.

(** Replace the this variable with a fresh variable for definition typing *)
(** [z.bs; G1, z: T, G2 ⊢ ds: U]                      #<br>#
    [x] fresh                                  #<br>#
    [―――――――――――――――――――――――――――――――――――――――]  #<br>#
    [x.bs; G1, x: T[x/z], G2[x/z] ⊢ ds[x/z]: U[x/z]]
*)
Lemma rename_def_defs :
  (forall z bs G d D, z; bs; G ⊢ d : D -> forall G1 T G2 x,
     G = G1 & z ~ T & G2 ->
     z \notin fv_ctx_types G1 ->
     ok (G1 & x ~ subst_typ z (pvar x) T & z ~ T & G2) ->
     x; bs; G1 & x ~ subst_typ z (pvar x) T & subst_ctx z (pvar x) G2 ⊢
                                                           subst_def z (pvar x) d : subst_dec z (pvar x) D) /\
  (forall z bs G ds U, z; bs; G ⊢ ds :: U -> forall G1 T G2 x,
     G = G1 & z ~ T & G2 ->
     z \notin fv_ctx_types G1 ->
     ok (G1 & x ~ subst_typ z (pvar x) T & z ~ T & G2) ->
     x; bs; G1 & x ~ subst_typ z (pvar x) T & subst_ctx z (pvar x) G2 ⊢
                                                           subst_defs z (pvar x) ds :: subst_typ z (pvar x) U).
Proof.
  apply ty_def_mutind; intros; subst.
  - constructor.
  - pose proof (rename_ty_trm H0 t0 H1).
    constructor*.
  - specialize (H _ _ _ _ eq_refl H1 H2). simpl in *. apply* ty_def_new.
    eapply tight_bounds_subst in t. eauto.
    rewrite subst_open_commut_defs_p in H; try repeat eexists.
    rewrite subst_open_commut_typ_p in H; try repeat eexists.
    unfold subst_path, subst_avar, subst_var_p in H. case_if.
    simpl in H. rewrite List.app_nil_r in H. simpl. auto.
  - pose proof (rename_ty_trm H0 t H1). econstructor; eauto.
  - constructor*.
  - specialize (H0 _ _ _ _ eq_refl H2 H3). specialize (H _ _ _ _ eq_refl H2 H3).
    econstructor; eauto. apply* subst_defs_hasnt. rewrite* <- subst_label_of_def.
Qed.

(** Replace the opening and this variable in definition typing *)
Lemma rename_defs G x T ds z :
  x \notin fv_typ T ->
  x \notin fv_defs ds ->
  x \notin fv_ctx_types G ->
  ok (G & z ~ subst_typ x (pvar z) (open_typ x T) & x ~ open_typ x T) ->
  x; nil; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T ->
  z; nil; G & z ~ open_typ z T ⊢ open_defs z ds :: open_typ z T.
Proof.
  intros Hn Hn' Hn'' Hok Hx.
  assert (G & z ~ open_typ z T = G & z ~ open_typ z T & empty) as Heq by rewrite* concat_empty_r.
  assert (G & x ~ open_typ x T = G & x ~ open_typ x T & empty) as Heq' by rewrite* concat_empty_r.
  rewrite Heq. rewrite Heq' in Hx. clear Heq Heq'.
  assert (open_typ z T = subst_typ x (pvar z) (open_typ x T)) as Heq. {
    rewrite open_var_typ_eq. rewrite* <- subst_intro_typ. repeat eexists.
  }
  repeat rewrite Heq.
  assert (open_defs z ds = subst_defs x (pvar z) (open_defs x ds)) as Heq'. {
    rewrite open_var_defs_eq. rewrite* <- subst_intro_defs. repeat eexists.
  }
  repeat rewrite Heq'.
  clear Heq Heq'.
  assert (empty = subst_ctx x (pvar z) empty) as Heq. {
    unfold subst_ctx. rewrite* map_empty.
  }
  rewrite Heq.
  apply* rename_def_defs.
  rewrite concat_empty_r. auto.
Qed.
