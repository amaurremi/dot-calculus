(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import List Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding LocalClosure Weakening.

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
  lc_path p ->
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
    sbs = (If z = x then p_bs else bs) ->
    subst_var x p_x z; sbs; P; G1 & (subst_ctx x p G2) ⊢ subst_def x p d : subst_dec x p D) /\
  (forall z bs P G ds T, z; bs; P; G ⊢ ds :: T -> forall G1 G2 x p_x p_bs sbs,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    p = p_sel (avar_f p_x) p_bs ->
    sbs = (If z = x then p_bs else bs) ->
    subst_var x p_x z; sbs; P; G1 & (subst_ctx x p G2) ⊢ subst_defs x p ds :: subst_typ x p T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    G1 & (subst_ctx x p G2) ⊢ subst_typ x p T <: subst_typ x p U).
Proof.
  introv Hl. apply rules_mutind; intros; subst; simpl;
            try (subst_fresh_solver || rewrite subst_open_commut_typ_p);
            simpl in *; autounfold; eauto 4.
  - Case "ty_var".
    cases_if.
    + apply binds_middle_eq_inv in b; subst*. destruct* p.
    + eapply subst_fresh_ctx in H1.
      apply binds_subst in b; auto.
      constructor. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map; auto. apply ok_concat_map. apply* ok_remove.

  - Case "ty_new_intro".
    fresh_constructor.
    subst_open_fresh.
    destruct p as [p_x p_bs]. admit. (*
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
  end.*)

  - Case "ty_new_elim".
    asserts_rewrite (subst_path x p p0 • a = (subst_path x p p0) • a).
    destruct p0. apply sel_fields_subst. auto. Admitted. (*
  - Case "ty_rec_intro".
    constructor. rewrite <- subst_open_commut_typ_p. simpl in *. auto.
  - Case "ty_def_lambda".
    subst_tydef_solver. admit.
  - Case "ty_def_new".
    subst_tydef_solver. admit.
  - Case "ty_def_path".
    subst_tydef_solver. admit.
    (*apply* ty_def_path. intro. case_if; case_if*. *)
  - Case "ty_defs_cons".
    admit. (*constructor*.
    rewrite <- subst_label_of_def.
    apply subst_defs_hasnt. assumption.*)
Qed.*)

(** The substitution lemma for term typing.
    This lemma corresponds to Lemma 3.14 in the paper. *)
Lemma subst_ty_trm: forall p S G x t T,
    G & x ~ S ⊢ t : T ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    lc_path p ->
    G ⊢ trm_path p : subst_typ x p S ->
    G ⊢ subst_trm x p t : subst_typ x p T.
Proof.
  introv Ht Hok Hx Hl Hp.
  apply (proj41 (subst_rules S Hl)) with (G1:=G) (G2:=empty) (x:=x) in Ht.
  unfold subst_ctx in Ht. rewrite map_empty, concat_empty_r in Ht.
  apply Ht. rewrite* concat_empty_r. rewrite* concat_empty_r. assumption.
  unfold subst_ctx. rewrite map_empty, concat_empty_r. assumption.
Qed.

Lemma subst_ty_defs: forall z bs P G x S ds T p p_x p_bs sbs,
    z; bs; P; G & x ~ S ⊢ ds :: T ->
    p = p_sel (avar_f p_x) p_bs ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    G ⊢ trm_path p : subst_typ x p S ->
    sbs = (If z = x then p_bs else bs) ->
    subst_var x p_x z; sbs; P; G ⊢ subst_defs x p ds :: subst_typ x p T.
Proof.
  introv Hds Heq Hok Hx Hp Hsbs.
  assert (lc_path p) as Hl by (destruct p; inversion Heq; auto).
  Admitted. (*
  eapply (proj43 (subst_rules S Hl)) with
      (G1:=G) (G2:=empty) (x:=x) (p_x0:=p_x) (p_bs0:=p_bs) (sbs:=sbs) in Hds;
    unfold subst_ctx in *; try rewrite map_empty in *; try rewrite concat_empty_r in *; auto.
Qed.*)

(*
(** * Renaming  *)

(** Renaming the name of the opening variable for definition typing.  #<br>#

    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: T^z ⊢ ds^z : T^z] #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ ds^x : T^x]         *)
Lemma renaming_def: forall G z T ds x,
    ok G ->
    z # G ->
    z \notin (fv_ctx_types G \u fv_defs ds \u fv_typ T) ->
    G & z ~ open_typ z T /- open_defs z ds :: open_typ z T ->
    G ⊢ trm_var (avar_f x) : open_typ x T ->
    G /- open_defs x ds :: open_typ x T.
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
Lemma renaming_typ: forall G z T U t x,
    ok G ->
    z # G ->
    z \notin (fv_ctx_types G \u fv_typ U \u fv_typ T \u fv_trm t) ->
    G & z ~ U ⊢ open_trm z t : open_typ z T ->
    G ⊢ trm_var (avar_f x) : U ->
    G ⊢ open_trm x t : open_typ x T.
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
Lemma renaming_fresh : forall L G T u U x,
    ok G ->
    (forall x : var, x \notin L -> G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢ trm_var (avar_f x) : T ->
    G ⊢ open_trm x u : U.
Proof.
  introv Hok Hu Hx. pick_fresh y.
  rewrite subst_intro_trm with (x:=y); auto.
  rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
  eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
Qed.
*)
