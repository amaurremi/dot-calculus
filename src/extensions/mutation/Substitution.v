(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions Binding Weakening.

Ltac subst_solver :=
    fresh_constructor;
    subst_open_fresh;
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _
        |- context [ _ & subst_ctx ?x ?y ?G2 & ?z ~ subst_typ ?x ?y ?V] ] =>
        assert (subst_ctx x y G2 & z ~ subst_typ x y V = subst_ctx x y (G2 & z ~ V)) as B
            by (unfold subst_ctx; rewrite map_concat, map_single; reflexivity);
        rewrite <- concat_assoc; rewrite B;
        apply~ H;
        try (rewrite concat_assoc; auto);
        rewrite <- B,concat_assoc; unfold subst_ctx;
        auto using weaken_ty_trm, ok_push, ok_concat_map
    end.

Ltac fold_subst :=
  repeat match goal with
    | [ |- context [ trm_var (avar_f (If ?x = ?y then ?z else ?x)) ] ] =>
        asserts_rewrite (trm_var (avar_f (If x = y then z else x))
                         = subst_trm y z (trm_var (avar_f x))); auto
    | [ |- context [ open_typ (If ?x = ?y then ?z else ?x) (subst_typ ?y ?z ?T) ] ] =>
        asserts_rewrite (open_typ (If x = y then z else x) (subst_typ y z T)
                     = subst_typ y z (open_typ x T)); auto  end.

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
Lemma subst_rules: forall y U,
  (forall G Sigma t T, G ⋆ Sigma ⊢ t : T -> forall G1 G2 Sigma1 Sigma2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_ctx_types G1 ->
    Sigma = Sigma1 & Sigma2 ->
    x \notin fv_stoty_types Sigma1 ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) ⊢ trm_var (avar_f y) : subst_typ x y U ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) ⊢ subst_trm x y t : subst_typ x y T) /\
  (forall G Sigma d D, G ⋆ Sigma /- d : D -> forall G1 G2 Sigma1 Sigma2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_ctx_types G1 ->
    Sigma = Sigma1 & Sigma2 ->
    x \notin fv_stoty_types Sigma1 ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) ⊢ trm_var (avar_f y) : subst_typ x y U ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) /- subst_def x y d : subst_dec x y D) /\
  (forall G Sigma ds T, G ⋆ Sigma /- ds :: T -> forall G1 G2 Sigma1 Sigma2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_ctx_types G1 ->
    Sigma = Sigma1 & Sigma2 ->
    x \notin fv_stoty_types Sigma1 ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) ⊢ trm_var (avar_f y) : subst_typ x y U ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) /- subst_defs x y ds :: subst_typ x y T) /\
  (forall G Sigma T V, G ⋆ Sigma ⊢ T <: V -> forall G1 G2 Sigma1 Sigma2 x,
    G = G1 & x ~ U & G2 ->
    ok (G1 & x ~ U & G2) ->
    x \notin fv_ctx_types G1 ->
    Sigma = Sigma1 & Sigma2 ->
    x \notin fv_stoty_types Sigma1 ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) ⊢ trm_var (avar_f y) : subst_typ x y U ->
    G1 & (subst_ctx x y G2) ⋆ (Sigma1 & subst_sigma x y Sigma2) ⊢ subst_typ x y T <: subst_typ x y V).
Proof.
  introv. apply rules_mutind; intros; subst; simpl;
            try (subst_solver || rewrite subst_open_commut_typ);
            simpl in *; eauto 4.
  - Case "ty_var".
    cases_if.
    + apply binds_middle_eq_inv in b; subst; assumption.
    + eapply subst_fresh_ctx in H1.
      apply binds_subst in b; auto.
      constructor. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map; auto.
  - Case "ty_loc".
    constructor.
    apply subst_fresh_sigma with (y:=y) in H3.
    rewrite <- H3. unfold subst_sigma. rewrite <- map_concat.
    apply binds_map; auto.
  - Case "ty_rec_intro".
    apply ty_rec_intro. fold_subst.
    rewrite subst_open_commut_typ. auto. eauto.
  - Case "ty_defs_cons".
    constructor*. rewrite <- subst_label_of_def. apply* subst_defs_hasnt.
Qed.

(** The substitution lemma for term typing.
    This lemma corresponds to Lemma 3.19 in the paper. *)
Lemma subst_ty_trm: forall y U G Sigma x t T,
    G & x ~ U ⋆ Sigma ⊢ t : T ->
    ok (G & x ~ U) ->
    x \notin fv_ctx_types G ->
    x \notin fv_stoty_types Sigma ->
    G ⋆ Sigma ⊢ trm_var (avar_f y) : subst_typ x y U ->
    G ⋆ Sigma ⊢ subst_trm x y t : subst_typ x y T.
Proof.
  intros.
  apply (proj51 (subst_rules y U)) with (G1:=G) (G2:=empty) (Sigma1:=Sigma) (Sigma2:=empty) (x:=x) in H;
  unfold subst_ctx, subst_sigma in *; try rewrite? map_empty in *; try rewrite? concat_empty_r in *; auto.
Qed.

(** The substitution lemma for definition typing. *)
Lemma subst_ty_defs: forall y U G Sigma x ds T,
    G & x ~ U ⋆ Sigma /- ds :: T ->
    ok (G & x ~ U) ->
    x \notin fv_ctx_types G ->
    x \notin fv_stoty_types Sigma ->
    G ⋆ Sigma ⊢ trm_var (avar_f y) : subst_typ x y U ->
    G ⋆ Sigma /- subst_defs x y ds :: subst_typ x y T.
Proof.
  intros.
  apply (proj53 (subst_rules y U)) with (G1:=G) (G2:=empty) (Sigma1:=Sigma) (Sigma2:=empty) (x:=x) in H;
    unfold subst_ctx, subst_sigma in *; try rewrite? map_empty in *; try rewrite? concat_empty_r in *; auto.
Qed.

(** * Renaming  *)

(** Renaming the name of the opening variable for definition typing.  #<br>#

    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: T^z ⊢ ds^z : T^z] #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ ds^x : T^x]         *)
Lemma renaming_def: forall G Sigma z T ds x,
    ok G ->
    z # G ->
    z \notin (fv_ctx_types G \u fv_stoty_types Sigma \u fv_defs ds \u fv_typ T) ->
    G & z ~ open_typ z T ⋆ Sigma /- open_defs z ds :: open_typ z T ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : open_typ x T ->
    G ⋆ Sigma /- open_defs x ds :: open_typ x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx. rewrite subst_intro_typ with (x:=z). rewrite subst_intro_defs with (x:=z).
  eapply subst_ty_defs; auto. eapply Hz. rewrite <- subst_intro_typ. all: auto.
Qed.

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z : T^z]    #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x : T^x]         *)
Lemma renaming_typ: forall G Sigma z T U t x,
    ok G ->
    z # G ->
    z \notin (fv_ctx_types G \u fv_stoty_types Sigma \u fv_typ U \u fv_typ T \u fv_trm t) ->
    G & z ~ U ⋆ Sigma ⊢ open_trm z t : open_typ z T ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : U ->
    G ⋆ Sigma ⊢ open_trm x t : open_typ x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx. rewrite subst_intro_typ with (x:=z). rewrite subst_intro_trm with (x:=z).
  eapply subst_ty_trm; auto. eapply Hz. rewrite subst_fresh_typ. all: auto.
Qed.

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z : T^z]    #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x : T^x]         *)
Lemma renaming_fresh : forall L G Sigma T u U x,
    ok G ->
    (forall x : var, x \notin L -> G & x ~ T ⋆ Sigma ⊢ open_trm x u : U) ->
    G ⋆ Sigma ⊢ trm_var (avar_f x) : T ->
    G ⋆ Sigma ⊢ open_trm x u : U.
Proof.
  introv Hok Hu Hx. pick_fresh y.
  rewrite subst_intro_trm with (x:=y); auto.
  rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
  eapply subst_ty_trm; auto. rewrite~ subst_fresh_typ.
Qed.
