(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions.
Require Import Operational_semantics.
Require Import Weakening Narrowing Helper_lemmas Precise_types Substitution Canonical_forms.

(** Reduction in an empty context *)
Notation "t '|->' u" := (empty [t |-> u]) (at level 50).

(** Typing in an empty context *)
Notation "'⊢' t ':' T" := (empty ⊢ t: T) (at level 40, t at level 59).

(** * Progress *)

Lemma open_rec_preserve_normal_form: forall k x t,
    x \notin fv_trm t ->
    normal_form (open_rec_trm k x t) ->
    normal_form t.
Proof.
  intros. generalize dependent x.
  generalize dependent k.
  induction t; auto; intros;
    try (solve [
    unfold open_trm in H0; unfold open_rec_trm in H0;
    inversion H0]).
  unfold open_trm in H0. unfold open_rec_trm in H0.  
  inversion H0. fold open_rec_trm in *.
  unfold fv_trm in H. fold fv_trm in H.
  assert (x \notin fv_trm t2); auto.
  specialize (IHt2 _ _ H4 H2).

  destruct t1; simpl; inversion H1.
  constructor. auto.
Qed.

Corollary open_preserve_normal_form : forall x t,
    x \notin fv_trm t ->
    normal_form (open_trm x t) ->
    normal_form t.
Proof. apply open_rec_preserve_normal_form. Qed.


(* terms in opened definitions must be opened terms *)
Lemma open_rec_defs_has_open_rec_trm: forall k x ds a t',
    defs_has (open_rec_defs k x ds) (def_trm a t') ->
    exists f, t' = open_rec_trm k x f.
Proof with auto.
  intros k x ds. generalize dependent k. generalize dependent x.
  induction ds; intros; simpl in *.
  - inversion H.
  - unfold defs_has in H. unfold get_def in *. fold get_def in H.
    case_if.
    + inversion H. destruct d; simpl in *; inversion H1.
      exists t0...
    + specialize (IHds x k a t'). unfold defs_has in IHds.
      apply IHds...
Qed.

Lemma open_lc_let_body : forall k t u x,
    k >= 1 ->
    lc_trm (trm_let t u) ->
    open_rec_trm k x u = u.
Proof.
  introv Hk H. inversion H.
  specialize (H3 x).
  pose proof H3 as H4.
  apply lc_opening with (n:=k) (x:=x) in H3.
  eapply (proj1 (lc_open_rec_open_trm_val_def_defs x _)).
  - intro Contra. instantiate (1 := 0) in Contra. Coq.omega.Omega.omega.
  - eassumption.
Qed.
Hint Resolve open_lc_let_body.      


Definition close_rec_avar k u a : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = u then avar_b k else avar_f x
  end.
Hint Unfold close_rec_avar.

Fixpoint close_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (close_rec_dec k u D)
  | typ_and T1 T2  => typ_and (close_rec_typ k u T1) (close_rec_typ k u T2)
  | typ_sel x L    => typ_sel (close_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (close_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (close_rec_typ k u T1) (close_rec_typ (S k) u T2)
  end
with close_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (close_rec_typ k u T) (close_rec_typ k u U)
  | dec_trm m T   => dec_trm m (close_rec_typ k u T)
  end.
Hint Unfold close_rec_typ close_rec_dec.


Fixpoint close_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (close_rec_avar k u a)
  | trm_val v      => trm_val (close_rec_val k u v)
  | trm_sel v m    => trm_sel (close_rec_avar k u v) m
  | trm_app f a    => trm_app (close_rec_avar k u f) (close_rec_avar k u a)
  | trm_let t1 t2  => trm_let (close_rec_trm k u t1) (close_rec_trm (S k) u t2)
  end
with close_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (close_rec_typ (S k) u T) (close_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (close_rec_typ k u T) (close_rec_trm (S k) u e)
  end
with close_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (close_rec_typ k u T)
  | def_trm m e => def_trm m (close_rec_trm k u e)
  end
with close_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (close_rec_defs k u tl) (close_rec_def k u d)
  end.
Hint Unfold close_rec_trm close_rec_val close_rec_def close_rec_defs.

Definition close_avar u a := close_rec_avar  0 u a.
Definition close_typ  u t := close_rec_typ   0 u t.
Definition close_dec  u D := close_rec_dec   0 u D.
Definition close_trm  u e := close_rec_trm   0 u e.
Definition close_val  u v := close_rec_val   0 u v.
Definition close_def  u d := close_rec_def   0 u d.
Definition close_defs u l := close_rec_defs  0 u l.
Hint Unfold close_avar close_typ close_dec close_trm close_val close_def close_defs.


Lemma close_rec_typ_dec_no_capture : forall x,
    (forall T k, x \notin fv_typ (close_rec_typ k x T)) /\
    (forall D k, x \notin fv_dec (close_rec_dec k x D)).
Proof.
  intros x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a
    end; simpl;
      try case_if; unfold fv_avar; auto.
Qed.


Lemma close_rec_trm_val_def_defs_no_capture: forall x,
    (forall t k, x \notin fv_trm (close_rec_trm k x t)) /\
    (forall v k, x \notin fv_val (close_rec_val k x v)) /\
    (forall d k, x \notin fv_def (close_rec_def k x d)) /\
    (forall ds k, x \notin fv_defs (close_rec_defs k x ds)).
Proof.
  intro x.
  apply trm_mutind; intros; simpl; auto;
    try apply notin_union; 
    repeat split;
    try applys close_rec_typ_dec_no_capture;
    repeat
      match goal with
      | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a; simpl
      end;
    repeat case_if; unfold fv_avar; auto.
Qed.


Lemma open_left_inverse_close_typ_dec:
  (forall T k x, lc_typ T -> x \notin fv_typ T -> open_rec_typ k x (close_rec_typ k x T) = T) /\
  (forall D k x, lc_dec D -> x \notin fv_dec D -> open_rec_dec k x (close_rec_dec k x D) = D).
Proof with auto.
  apply typ_mutind; intros; simpl in *; auto.
  - inversion H0. rewrite H...
  - inversion H1. rewrite H... rewrite H0...
  - inversion H. inversion H2.
    simpl. case_if; simpl; subst; try case_if...
  - inversion H0. admit.
  - inversion H1. rewrite H... admit.
  - inversion H1. rewrite H... rewrite H0...
  - inversion H0. rewrite H...
Qed.


Lemma open_left_inverse_close_trm_val_def_defs :
  (forall t k x, lc_trm t -> x \notin fv_trm t -> open_rec_trm k x (close_rec_trm k x t) = t) /\
  (forall v k x, lc_val v -> x \notin fv_val v -> open_rec_val k x (close_rec_val k x v) = v) /\
  (forall d k x, lc_def d -> x \notin fv_def d -> open_rec_def k x (close_rec_def k x d) = d) /\
  (forall ds k x, lc_defs ds -> x \notin fv_defs ds -> open_rec_defs k x (close_rec_defs k x ds) = ds).
Proof with auto.
  apply trm_mutind; intros; simpl in *; auto;
    repeat
      match goal with
      | [ H : _ \notin _ \u _ |- _ ] => apply notin_union in H; destruct H
      end;
    try solve [
          repeat
            match goal with
            | [ H: lc_trm (trm_var _) |- _ ] => inversion H; clear H
            | [ H: lc_trm (trm_sel _ _) |- _ ] => inversion H; clear H
            | [ H: lc_trm (trm_app _ _) |- _ ] => inversion H; clear H
            | [ H: lc_var _ |- _ ] => inversion H; clear H
            end; simpl; repeat case_if; simpl; subst; try case_if; auto].
  - inversion H0. rewrite H...
  - inversion H1. rewrite H... admit.
  - inversion H0. admit.
  - inversion H0. subst. rewrite (proj1 open_left_inverse_close_typ_dec)...
    admit.
  - inversion H. rewrite (proj1 open_left_inverse_close_typ_dec)...
  - inversion H0. rewrite H...
  - inversion H1. rewrite H... rewrite H0...
Qed.
    
(* Ltac optrm_struct H := *)
(*   (try match type of H with *)
(*        | open_trm _ _ => unfold open_trm in H *)
(*        end); *)
(*   (try match type of H with *)
(*        | _ = open_rec_trm _ _ _ => symmetry in H *)
(*        end); *)
(*   match type of H with *)
(*   | open_rec_trm _ _ ?t = _ => destruct t; simpl in H; inversion H *)
(*   end. *)

(* Lemma open_rec_eval_to_open_rec : forall k e x t t' v, *)
(*     x \notin dom e \u fv_trm t \u fv_val v -> *)
(*     lc_sto e -> lc_val v -> *)
(*     e & x ~ v[ open_rec_trm k x t |-> t'] -> *)
(*     exists f, (* (x \notin (fv_trm f)) /\ *) t' = open_rec_trm k x f. *)
(* Proof. *)
  (* intros. gen k e x t' v. *)
  (* induction t; intros; inversion H2; subst. *)
  (*   (* try solve [ *) *)
  (*   (*       match goal with *) *)
  (*   (*       | [ H : _ [ _ |-> _ ] |- _ ] => inversion H *) *)
  (*   (*       end]. *) *)
  (* - pose proof H9 as Hop. *)
  (*   apply open_rec_defs_has_open_rec_trm in H9. destruct_all. subst. *)
  (*   apply binds_push_inv in H7; destruct_all; subst; *)
  (*     repeat *)
  (*       match goal with *)
  (*       | [ H : binds _ _ e |- _ ] => apply lc_sto_binds_inv in H; auto *)
  (*       | [ H : lc_val (val_new _ _) |- _ ] => inversion H; clear H; subst *)
  (*       | [ H : forall _, lc_defs _, *)
  (*             Hdefs : defs_has (open_defs ?x _) _ |- _ ] => *)
  (*         specialize (H x); apply (lc_defs_has H) in Hdefs; inversion Hdefs; subst *)
  (*       end; *)
  (*     eexists; rewrite (proj1 (lc_opening_trm_val_def_defs _)) with (n:=k); auto. *)
  (* - apply binds_push_inv in H8; destruct_all; subst; *)
  (*     repeat *)
  (*       match goal with *)
  (*       | [ H : binds _ _ e |- _ ] => apply lc_sto_binds_inv in H; auto *)
  (*       | [ H : lc_val (val_lambda _ _) |- _ ] => inversion H; clear H *)
  (*       | [ H : forall _, lc_trm _ |- _ ] => specialize (H y) *)
  (*       end; *)
  (*     eexists; rewrite (proj1 (lc_opening_trm_val_def_defs x)); auto. *)
  (* - optrm_struct H3. unfold open_rec_avar in H5. *)

Lemma open_rec_eval_to_open_rec : forall e x t t' v,
    x \notin dom e \u fv_trm t \u fv_val v ->
    lc_sto e -> lc_val v ->
    e & x ~ v[ open_trm x t |-> t'] ->
    exists f, (x \notin (fv_trm f)) /\ t' = open_trm x f.
Proof.
(*   intros. gen e x t' v. *)
(*   induction t; intros; inversion H2; subst. *)
(*     (* try solve [ *) *)
(*     (*       match goal with *) *)
(*     (*       | [ H : _ [ _ |-> _ ] |- _ ] => inversion H *) *)
(*     (*       end]. *) *)
(*   - pose proof H9 as Hop. *)
(*     apply open_rec_defs_has_open_rec_trm in H9. destruct_all. subst. *)
(*     apply binds_push_inv in H7; destruct_all; subst; *)
(*       repeat *)
(*         match goal with *)
(*         | [ H : binds _ _ e |- _ ] => apply lc_sto_binds_inv in H; auto *)
(*         | [ H : lc_val (val_new _ _) |- _ ] => inversion H; clear H; subst *)
(*         | [ H : forall _, lc_defs _, *)
(*               Hdefs : defs_has (open_defs ?x _) _ |- _ ] => *)
(*           specialize (H x); apply (lc_defs_has H) in Hdefs; inversion Hdefs; subst *)
(*         end. *)
(*     + exists x1. *)
    
  (*     match goal with *)
  (*     | [ |- exists _, _ /\ ?l = (open_trm ?x _) ] => exists l; split; *)
  (*                                               [ |symmetry; *)
  (*                                               apply (proj1 (lc_opening_trm_val_def_defs x)); auto] *)
  (*     end. *)
  (* - apply binds_push_inv in H8; destruct_all; subst; *)
  (*     repeat *)
  (*       match goal with *)
  (*       | [ H : binds _ _ e |- _ ] => apply lc_sto_binds_inv in H; auto *)
  (*       | [ H : lc_val (val_lambda _ _) |- _ ] => inversion H; clear H *)
  (*       | [ H : forall _, lc_trm _ |- _ ] => specialize (H y) *)
  (*       end; *)
  (*     match goal with *)
  (*     | [ |- exists _, ?l = (open_trm ?x _) ] => exists l; symmetry; *)
  (*                                           apply (proj1 (lc_opening_trm_val_def_defs x)); auto *)
  (*     end. *)
  (* - inversion H7. specialize (H8 y). *)
  (*   match goal with *)
  (*   | [ |- exists _, ?l = (open_trm ?x _) ] => exists l; symmetry; *)
  (*                                         apply (proj1 (lc_opening_trm_val_def_defs x)); auto *)
  (*   end. *)
  (* - *)
    

    
  (* introv Hx Hlce Hlcv He. dependent induction He. *)
  (* - exists (open_trm y t0). *)
  (*   split. *)
  (*   + admit. *)
  (*   + *)
  (*   apply binds_push_inv in H0; destruct_all; subst; *)
  (*     repeat *)
  (*       match goal with *)
  (*       | [ H : binds _ _ e |- _ ] => apply lc_sto_binds_inv in H; auto *)
  (*       | [ H : lc_val (val_lambda _ _) |- _ ] => inversion H; clear H *)
  (*       | [ H : forall _, lc_trm _ |- _ ] => specialize (H y) *)
  (*       end; *)
  (*     rewrite (proj1 (lc_opening_trm_val_def_defs x1)); auto. *)
  (* - admit. *)
  (*   (* pose proof H1. apply open_rec_defs_has_open_rec_trm in H1. *) *)
  (*   (* apply binds_push_inv in H0; destruct_all; subst; *) *)
  (*   (*   repeat *) *)
  (*   (*     match goal with *) *)
  (*   (*     | [ H : binds _ _ e |- _ ] => apply lc_sto_binds_inv in H; auto *) *)
  (*   (*     | [ H : lc_val (val_new _ _) |- _ ] => inversion H; clear H; subst *) *)
  (*   (*     | [ H : forall _, lc_defs _, Hdefs : defs_has (open_defs ?x _) _ |- _ ] => *) *)
  (*   (*       specialize (H x); apply (lc_defs_has H) in Hdefs; inversion Hdefs; subst *) *)
  (*   (*     | [ |- exists _, open_rec_trm _ ?x ?t = open_rec_trm ?k ?y _ ] => *) *)
  (*   (*       exists (open_trm x t); rewrite (proj1 (lc_opening_trm_val_def_defs y)) with (n:= k); auto *) *)
  (*   (*     end. *) *)
  (* - rename x into Hop. destruct t; simpl in Hop; inversion Hop. *)

(*     admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(* Qed. *)
  
(*   intros. gen k e x t' v. induction t; intros. *)
(*   - inversion H2. *)
(*   - inversion H2. *)
(*   - unfold open_rec_trm in H2. unfold open_rec_avar in H2. *)
(*     destruct a; [case_if |]; inversion H2; subst. *)
(*     + apply binds_push_eq_inv in H7. subst. *)
(*       exists t'. destruct (open_rec_defs_has_open_rec_trm _ _ _ H9). *)
(*       subst. *)


(*       split. *)
(*       * unfold fv_val in H. fold fv_defs in H. *)
(*         assert (ds = open_defs x ds). { *)
          
(*         } *)
    

(*   (*   inversion H0. subst. *) *)
    
(*   (* intros. dependent induction H0; intros. *) *)
(*   (* - exists t. split; auto. *) *)
    
  
(* Lemma open_rec_eval_to_open_rec : forall e x t t' v, *)
(*   x \notin dom e \u fv_trm t \u fv_val v -> *)
(*   e & x ~ v[ open_trm x t |-> t'] -> *)
(*   exists f, (x \notin (fv_trm f)) /\ t' = open_trm x f. *)
(* Proof. *)
(*   introv Hx He. dependent induction He. *)
(*   -  *)
  
(*   (* induction t; intros; try (solve [inversion H0]). *) *)
Admitted.

Lemma subenv_empty_supremum : forall G, subenv G empty.
Proof.
  unfold subenv. intros.
  unfold binds in H. rewrite get_empty in H.
  inversion H.
Qed.

Inductive indc_subenv: ctx -> ctx -> Prop :=
| new_subenv_empty : indc_subenv empty empty
| new_subenv_push: forall G G' x T T',
    indc_subenv G G' ->
    ok G ->
    ok G' ->
    x # G ->
    x # G' ->
    G ⊢ T <: T' ->
    indc_subenv (G & x ~ T) (G' & x ~ T').
Hint Constructors indc_subenv.

Lemma indc_subenv_implies_subenv : forall G1 G2,
    indc_subenv G1 G2 -> subenv G1 G2.
Proof.
  introv H. induction H.
  - apply subenv_empty_supremum.
  - unfold subenv. intros y Tb Bi. apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
    + destruct Bi. subst. right. exists T. split.
      * apply binds_push_eq.
      * apply weaken_subtyp; auto.
    + destruct Bi. unfold subenv in IHindc_subenv.
      destruct (IHindc_subenv _ _ H6).
      * left. apply binds_push_neq; trivial.
      * destruct H7 as [T1 [Hb Hs]]. right.
        exists T1. split.
        -- apply binds_push_neq; trivial.
        -- apply weaken_subtyp; auto. 
Qed.
Hint Resolve indc_subenv_implies_subenv.

Lemma indc_subenv_empty_inv : forall G, indc_subenv empty G -> G = empty.
Proof.
  intros. dependent induction H.
  - trivial.
  - renames x to H5. symmetry in H5. apply empty_push_inv in H5. contradiction.
Qed.

Lemma indc_subenv_refl : forall G, ok G -> indc_subenv G G.
Proof.
  intros G H. induction H; auto.
Qed.
Hint Resolve indc_subenv_refl.

Lemma indc_subenv_trans : forall G1 G2 G3,
    indc_subenv G1 G2 ->
    indc_subenv G2 G3 ->
    indc_subenv G1 G3.
Proof.
  introv H. gen G3. induction H; intros; auto.
  dependent induction H5.
  - apply empty_push_inv in x. contradiction.
  - rename x into He. apply eq_push_inv in He. destruct_all.
    subst.
    apply IHindc_subenv in H5.
    constructor; auto.
    apply indc_subenv_implies_subenv in H.
    apply narrow_subtyping with (G':=G) in H10; auto.
    eapply subtyp_trans; eauto.
Qed.
Hint Resolve indc_subenv_trans.

Lemma indc_subenv_push : forall G1 G2 x T,
    indc_subenv G1 G2 ->
    ok (G1 & x ~ T) -> ok (G2 & x ~ T) ->
    indc_subenv (G1 & x ~ T) (G2 & x ~ T).
Proof.
  intros. induction H; intros; auto.
  constructor; auto;
    repeat
      match goal with
      | H : empty = _ & _ |- _ => destruct (empty_push_inv H)
      | H : _ & _ ~ _ = _ & _ ~ _ & _ ~ _ |- _ => apply eq_push_inv in H; destruct_all; subst; trivial
      | H : ok (?G & ?x ~ ?T & _ ~ _) |- x # ?G & ?x ~ ?T => inversion H
      end.
Qed.
Hint Resolve indc_subenv_push.


Lemma eval_renaming_subst : forall x y e1 e2 v t1 t2,
    x \notin dom e1 ->
    y \notin dom e1 \u fv_sto_vals e1 \u fv_val v \u fv_trm t1 ->
    (e1 & x ~ v & e2)[t1 |-> t2] ->
    (e1 & y ~ subst_val x y v & e2)[subst_trm x y t1 |-> subst_trm x y t2].
Proof.
  intros. dependent induction H1.
  (* - apply binds_concat_inv in H1. *)

  (*   apply binds_push_inv in H1. rewrite subst_open_commut_trm. *)
  (*   unfold subst_fvar. simpl in *. *)
  (*   (* destruct_all. *) *)
  (*   (* case_if. case_if. subst. *) *)
  (*   (* econstructor. auto. unfold subst_val. fold subst_trm. auto. *) *)
  (*   destruct_all; repeat case_if; subst; *)
  (*     econstructor; auto; *)
  (*       try solve [unfold subst_val; fold subst_trm; auto]. *)
  (*   all: instantiate (1 := T). Focus 2. *)
    (* not enough! values in e cannot capture x! *)
Admitted.

Lemma eval_renaming: forall x y e1 v t1 t2,
    x \notin (dom e1) \u (fv_val v) \u (fv_trm t1) \u (fv_trm t2) ->
    (e1 & x ~ v)[ open_trm x t1 |-> open_trm x t2 ] ->
    y \notin (dom e1) \u (fv_val v) \u (fv_trm t1) \u (fv_trm t2) ->
    (e1 & y ~ v)[ open_trm y t1 |-> open_trm y t2 ].
Proof.
  intros. dependent induction H0; intros.
  - destruct t1; inversion x2.


Admitted.
 

Lemma progress_ec: forall G' G e t T,
    lc_sto e ->
    lc_trm t ->
    indc_subenv G' G ->
    inert G' ->
    G' ~~ e ->
    G ⊢ t: T ->
    ok G ->
    (normal_form t \/ exists t', e[t |-> t']).
Proof with auto.
  introv Hlce Hlc Hsenv Hig Hwf Ht Hokg. gen G' e.
  induction Ht; eauto; intros.
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    destruct (canonical_forms_fun Hig Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. repeat eexists. apply* red_apply.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hig Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. repeat eexists. apply* red_project.
  - Case "ty_let".
    destruct t.
    + SCase "t = trm_var a".
      apply narrow_typing with (G':=G') in Ht; auto.
      destruct (var_typing_implies_avar_f Ht); subst.
      right. exists (open_trm x u). constructor...      
    + SCase "t = trm_val v".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pick_fresh x.
      destruct H0 with (x:=x) (G' := G' & x ~ T') (e := e & x ~ v); auto.
      * inversion Hlc. trivial.
      * intros. eapply indc_subenv_trans; econstructor; eauto.
      * constructor; auto. inversion Hlc. inversion H5. trivial.
      * intros. apply precise_to_general in H1.
        constructor; auto. eapply narrow_typing in H1; eauto.
      * left.
        destruct u; auto; apply open_preserve_normal_form in H3; auto.
      * right. destruct H3.

        (* exists. eapply red_let_val; auto. *)
        (* intros. *)
        
        
        pose proof H3.
        apply open_rec_eval_to_open_rec in H3; auto.
        destruct_all. subst.
        eexists. eapply red_let_val; auto.
        intros.
        eapply eval_renaming with (x:=x); eauto.
        inversion Hlc. inversion H7. trivial.
    + SCase "t = trm_sel a t".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_app a a0".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_let t1 t2".
      right. eexists. constructor. inversion Hlc. trivial.
Qed.  

(** ** Progress Theorem
    If [⊢ t : T], then either [t] is a normal form,
    or [t]] reduces to some [t']. *)
Theorem progress: forall t T,
    lc_trm t ->
    ⊢ t: T ->
    normal_form t \/ (exists t', t |-> t').
Proof.
  intros. apply* progress_ec; constructor; auto.  
Qed.

(** * Preservation *)

Lemma preservation_ec: forall G G' e t t' T,
    lc_trm t ->
    indc_subenv G' G ->
    G' ~~ e ->
    inert G' ->
    G ⊢ t: T ->
    e[t |-> t'] ->
    ok G ->
    G' ⊢ t': T.
Proof.
  introv Hlc Hsenv Hwf Hi Ht Hr Hok. gen e t'. gen G'.
  induction Ht; introv Hsenv Hi Hwf Hr; try solve [inversions Hr]; eauto.
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    apply narrow_typing with (G':=G') in Ht2; auto.
    destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hr.
    apply (binds_func H4) in Bis. inversions Bis.
    pick_fresh y. apply* renaming_typ.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hi Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    inversions Hr.
    apply (binds_func H3) in Bis. inversions Bis.
    rewrite <- (defs_has_inv Has H5). assumption.
  - Case "ty_let".
    inversions Hr.
    * SCase "red_let_var".
      pick_fresh x. assert (x \notin L); auto. specialize (H x H1).
      apply subst_ty_trm with (y:=y) in H; auto.
      -- assert (subst_typ x y U = U). {
           apply subst_fresh_typ_dec. auto.
         }
         rewrite H2 in H.
         assert (open_trm y u = subst_trm x y (open_trm x u)). {
           apply subst_intro_trm. auto.
         }
         rewrite <- H3 in H.
         apply narrow_typing with (G':=G') in H; auto.
      -- assert (subst_typ x y T = T). {
           apply subst_fresh_typ_dec. auto.
         }
         rewrite H2. trivial.
    * SCase "red_let_let".
      clear H0 IHHt.
      assert (forall x, x \notin (L \u dom G) -> G & x ~ T ⊢ open_trm x u : U). {
        intros. assert (x \notin L); auto.
      }
      clear H.
      dependent induction Ht.
      -- apply narrow_typing with (G' := G') in Ht; eauto.
         remember ((((((((((((L \u L0) \u dom G) \u fv_ctx_types G) \u dom G')
                            \u fv_ctx_types G') \u dom e) \u fv_trm u) \u fv_trm s)
                        \u fv_trm t0) \u fv_typ U) \u fv_typ T) \u fv_typ U0) as bigL.
         econstructor; eauto. intros.
         instantiate (1 := bigL) in H2.
         unfold open_trm, open_rec_trm. fold open_rec_trm.

         assert (open_rec_trm 1 x u = u); eauto.
         rewrite H3. clear H3.
         
         rewrite HeqbigL in H2.
         assert (x \notin L0); auto.
         specialize (H _ H3). 
         assert (subenv (G' & x ~ T) (G & x ~ T)). {
           apply subenv_push; auto.
         }
         apply narrow_typing with (G' := G' & x ~ T) in H; auto.
         rewrite <- HeqbigL in H2.         
         econstructor; eauto.
         intros. instantiate (1 := bigL \u \{ x }) in H6.
         subst bigL.
         assert (x0 \notin L \u dom G); auto.
         specialize (H1 _ H7).
         assert (G' & x0 ~ U0 ⊢ open_trm x0 u : U). {
           eapply narrow_typing; [eassumption | |]; auto.
         }
         eapply (proj1 weaken_rules); eauto.
      -- eapply IHHt; eauto; intros.
         specialize (H0 _ H1).
         eapply narrow_typing; eauto.
    * SCase "red_let_trm".
      inversion Hlc.
      specialize (IHHt H3 Hok _ Hsenv Hi _ Hwf t'0 H6).
      eapply ty_let; eauto. intros.
      instantiate (1 := (((((((((L \u dom G) \u fv_ctx_types G) \u dom G')
                                \u fv_ctx_types G') \u dom e) \u fv_trm t) \u fv_trm u)
                            \u fv_trm t'0) \u fv_typ T) \u fv_typ U) in H7.
      assert (x \notin L); auto.
      specialize (H _ H8).
      apply narrow_typing with (G':=G' & x ~ T) in H; auto.
    * SCase "red_let_val".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pose proof H1 as Htt.
      apply precise_to_general in Htt.
      apply narrow_typing with (G':=G') in Htt; auto.
      pick_fresh x. assert (x \notin L); auto.
      assert (ok (G & x ~ T)); auto.
      assert (indc_subenv (G' & x ~ T') (G & x ~ T)). {
        apply indc_subenv_trans with (G & x ~ T'); auto. }
      assert (inert (G' & x ~ T')); auto.
      assert (G' & x ~ T' ~~ e & x ~ v). {
        constructor; auto.
      }
      assert (x \notin L0); auto.
      inversion Hlc.
      specialize (H0 _ H3 (H14 _) H5 (G' & x ~ T') H7 H8 (e & x ~ v) H9 _ (H6 _ H10)).
      apply_fresh ty_let as y; eauto.

      apply weaken_ty_trm with (G2:=(y ~ T')) in H0; auto.
      
      pose proof (proj1 (subst_rules y T')) as Hsubst.
      specialize (Hsubst _ _ _ H0 G' (y ~ T') x).
      assert (HsubstU : subst_typ x y U = U). {
        apply subst_fresh_typ. auto.
      }
      rewrite HsubstU in Hsubst.

      assert (Hxyt : subst_typ x y T' = T'). {
        apply subst_fresh_typ. auto.
      }
      
      assert (Hopeny : subst_ctx x y (y ~ T') = y ~ T'). {
        unfold subst_ctx. rewrite map_single. rewrite Hxyt. trivial.
      }
      rewrite* Hopeny in Hsubst.

      assert (Hopent : subst_trm x y (open_trm x t'0) = open_trm y t'0). {
        rewrite subst_open_commut_trm.
        rewrite (proj1 (subst_fresh_trm_val_def_defs _ _)); auto.
        unfold subst_fvar. case_if; auto.
      }
      rewrite Hopent in Hsubst.

      apply Hsubst; auto.
      rewrite Hxyt. auto.
      
  - apply narrow_typing with (G' := G') in Ht; auto.
    apply narrow_subtyping with (G' := G') in H; auto.
    eapply ty_sub; eauto.
Qed.

  
(** ** Preservation Theorem
    If [⊢ t : T] and [t |-> t'], then [⊢ t': T]. *)
Theorem preservation: forall (t t' : trm) T,
    lc_trm t ->
    ⊢ t: T ->
    t |-> t' ->
    ⊢ t' : T.
Proof.
  intros. eapply preservation_ec; eauto. constructor.
Qed.
