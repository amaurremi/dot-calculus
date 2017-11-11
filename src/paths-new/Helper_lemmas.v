(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas used throughout the proof. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality List.
Require Import Definitions.

(** [G |- ds :: U]                          #<br>#
    [U] is a record type with labels [ls]  #<br>#
    [ds] are definitions with label [ls']  #<br>#
    [l \notin ls']                          #<br>#
    [―――――――――――――――――――――――――――――――――――]  #<br>#
    [l \notin ls] *)
Lemma hasnt_notin : forall x bs P G ds ls l U,
    x; bs; P; G ⊢ ds :: U ->
    record_typ U ls ->
    defs_hasnt ds l ->
    l \notin ls.
Proof.

  Ltac inversion_def_typ :=
    match goal with
    | H: _; _; _; _ ⊢ _ : _ |- _ => inversions H
    end.

  introv Hds Hrec Hhasnt.
  inversions Hhasnt. gen ds. induction Hrec; intros; inversions Hds.
  - inversion_def_typ; simpl in *; case_if; apply* notin_singleton.
  - apply notin_union; split; simpl in *.
    + apply* IHHrec. case_if*.
    + inversion_def_typ; case_if; apply* notin_singleton.
Qed.

(** * Lemmas About Opening *)

Lemma open_var_path_eq : forall x p n,
    open_rec_path n x p = open_rec_path_p n (pvar x) p.
Proof.
  intros. destruct p, a. simpl. repeat case_if*. rewrite* app_nil_r.
  simpl. reflexivity.
Qed.

Lemma open_var_typ_dec_eq: forall x,
    (forall T : typ, forall n : nat,
          open_rec_typ n x T = open_rec_typ_p n (pvar x) T) /\
    (forall D : dec, forall n : nat,
          open_rec_dec n x D = open_rec_dec_p n (pvar x) D).
Proof.
  intros. apply typ_mutind; unfold open_typ, open_typ_p; simpl; intros; auto;
            try solve [rewrite* H; rewrite* H0].
  unfold open_rec_avar, open_rec_avar_p. rewrite* open_var_path_eq.
Qed.

Lemma open_var_typ_eq: forall x T,
  open_typ x T = open_typ_p (pvar x) T.
Proof.
  intros. apply open_var_typ_dec_eq.
Qed.

Lemma open_var_dec_eq: forall x D,
  open_dec x D = open_dec_p (pvar x) D.
Proof.
  intros. apply open_var_typ_dec_eq.
Qed.

Hint Rewrite open_var_typ_eq open_var_dec_eq open_var_path_eq.

(** The following [open_fresh_XYZ_injective] lemmas state that given two
    symbols (variables, types, terms, etc.) [X] and [Y] and a variable [z],
    if [z \notin fv(X)] and [z \notin fv(Y)], then [X^z = Y^z] implies [X = Y]. *)

Lemma open_var_trm_val_def_eq : forall x,
  (forall t n,
      open_rec_trm n x t = open_rec_trm_p n (pvar x) t) /\
  (forall v n,
      open_rec_val n x v = open_rec_val_p n (pvar x) v) /\
  (forall d n,
      open_rec_def n x d = open_rec_def_p n (pvar x) d) /\
  (forall ds n,
      open_rec_defs n x ds = open_rec_defs_p n (pvar x) ds).
Proof.
  introv. apply trm_mutind; intros; simpl; f_equal*;
            try (rewrite* open_var_path_eq); rewrite* (proj1 (open_var_typ_dec_eq x)).
Qed.

Lemma open_var_defs_eq: forall x ds,
    open_defs x ds = open_defs_p (pvar x) ds.
Proof.
  intros. apply* open_var_trm_val_def_eq.
Qed.

Lemma open_var_trm_eq: forall x t,
    open_trm x t = open_trm_p (pvar x) t.
Proof.
  intros. apply* open_var_trm_val_def_eq.
Qed.

(** - variables *)
Lemma open_fresh_avar_injective : forall x y k z,
    z \notin fv_avar x ->
    z \notin fv_avar y ->
    open_rec_avar k z x = open_rec_avar k z y ->
    x = y.
Proof.
  intros. destruct x, y; inversion* H1; case_if; simpl in *;
            try solve [inversions H3; false* notin_same];
            case_if*. subst*.
Qed.

Lemma open_fresh_path_injective : forall p q k z,
    z \notin fv_path p ->
    z \notin fv_path q ->
    open_rec_path k z p = open_rec_path k z q ->
    p = q.
Proof.
  intros. destruct p, q. inversions* H1. simpl in *; f_equal.
  Admitted.

 Ltac invert_open :=
    match goal with
    | [ H: _ = open_rec_typ _ _ ?T' |- _ ] =>
       destruct T'; inversions* H
    | [ H: _ = open_rec_dec _ _ ?D' |- _ ] =>
       destruct D'; inversions* H
    end.

(** - types and declarations *)
Lemma open_fresh_typ_dec_injective:
  (forall T T' k x,
    x \notin fv_typ T ->
    x \notin fv_typ T' ->
    open_rec_typ k x T = open_rec_typ k x T' ->
    T = T') /\
  (forall D D' k x,
    x \notin fv_dec D ->
    x \notin fv_dec D' ->
    open_rec_dec k x D = open_rec_dec k x D' ->
    D = D').
Proof.
  apply typ_mutind; intros; invert_open; simpl in *;
    f_equal; eauto using open_fresh_avar_injective, open_fresh_path_injective.
Qed.

Lemma open_fresh_trm_val_def_defs_injective:
  (forall t t' k x,
      x \notin fv_trm t ->
      x \notin fv_trm t' ->
      open_rec_trm k x t = open_rec_trm k x t' ->
      t = t') /\
  (forall v v' k x,
      x \notin fv_val v ->
      x \notin fv_val v' ->
      open_rec_val k x v = open_rec_val k x v' ->
      v = v') /\
  (forall d d' k x,
      x \notin fv_def d ->
      x \notin fv_def d' ->
      open_rec_def k x d = open_rec_def k x d' ->
      d = d') /\
  (forall ds ds' k x,
      x \notin fv_defs ds ->
      x \notin fv_defs ds' ->
      open_rec_defs k x ds = open_rec_defs k x ds' ->
      ds = ds').
Proof.

  Ltac injective_solver :=
    match goal with
    | [ H: _ = open_rec_trm _ _ ?t |- _ ] =>
      destruct t; inversions H;
      try (f_equal; simpl in *);
           try (apply* open_fresh_avar_injective || apply* open_fresh_path_injective);
           match goal with
           | [ Ho: open_rec_avar _ _ _ = open_rec_avar _ _ _ |- _ ] =>
             apply open_fresh_avar_injective in Ho; subst*
           | [ Heq: forall _ _ _, _ -> _ -> _ -> ?u = _ |- ?u = _ ] =>
             apply* Heq
           end
    | [ H: _ = open_rec_val _ _ ?v |- _ ] =>
      destruct v; inversions H; f_equal; simpl in *;
      try apply* open_fresh_typ_dec_injective; eauto
    | [ H: _ = open_rec_def _ _ ?d |- _ ] =>
      destruct d; inversions H; f_equal;
      try apply* open_fresh_typ_dec_injective; eauto
    | [ H: _ = open_rec_defs _ _ ?ds |- _ ] =>
      destruct ds; inversions H; f_equal; simpl in *; eauto
    end.

  apply trm_mutind; intros; try solve [injective_solver].
Qed.

(** The following [open_comm_XYZ] lemmas state that opening two
    symbols (variables, types, terms, etc.) at different indices commute. *)

Lemma open_comm_path: forall p x y n m,
  n <> m ->
  open_rec_path n x (open_rec_path m y p) =
  open_rec_path m y (open_rec_path n x p).
Proof. Admitted.

(** - types and declarations *)
Lemma open_comm_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) =
        open_rec_typ m y (open_rec_typ n x T)) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) =
        open_rec_dec m y (open_rec_dec n x D)).
Proof.
  intros. apply typ_mutind; intros; subst*; simpl; try solve [rewrite* H; rewrite* H0].
  f_equal. apply* open_comm_path.
Qed.

(** - terms, values, definitions, and lists of definitions *)
Lemma open_comm_trm_val_def_defs : forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) =
        open_rec_trm m y (open_rec_trm n x t)) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) =
        open_rec_val m y (open_rec_val n x v)) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) =
        open_rec_def m y (open_rec_def n x d)) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) =
        open_rec_defs m y (open_rec_defs n x ds)).
Proof.
  intros. apply trm_mutind; intros; subst; simpl; auto;
            try solve [f_equal; try rewrite~ H; rewrite H0 || rewrite* open_comm_path];
            try solve [try rewrite* H; rewrite* H0 || rewrite* (proj21 (open_comm_typ_dec x y))].
Qed.

(** The following [lc_open_rec_open_XYZ] lemmas state that if opening
    a symbol (variables, types, terms, etc.) at index [n] that is
    already opened at index [m] results in the same opened symbol,
    opening the symbol itself at index [n] results in the same symbol. *)
(*
(** - types and declarations *)
Lemma lc_open_rec_open_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) = open_rec_typ m y T ->
        open_rec_typ n x T = T) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) = open_rec_dec m y D ->
        open_rec_dec n x D = D).
Proof.
  introv. apply typ_mutind; intros; simpls; auto.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=m); auto.
  - inversions H0. destruct a; simpl; auto.
    case_if; simpls; case_if; subst; simpl in *; repeat case_if~.
    reflexivity.
  - inversions H1. rewrite H with (m:=S m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=S m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=m); auto.
  - inversions H1. rewrite H with (m:=m); auto.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma lc_open_rec_open_trm_val_def_defs: forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) = open_rec_trm m y t ->
        open_rec_trm n x t = t) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) = open_rec_val m y v ->
        open_rec_val n x v = v) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) = open_rec_def m y d ->
        open_rec_def n x d = d) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) = open_rec_defs m y ds ->
        open_rec_defs n x ds = ds).
Proof.
  introv. apply trm_mutind; intros; simpls; auto.
  - destruct a; simpl; auto.
    case_if; simpl in *; case_if; simpl in *; auto; case_if.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H0.
    destruct a; simpl; auto.
    case_if; simpl in *; case_if; simpl in *; auto; case_if.
  - inversions H0. destruct a; destruct a0; simpl; auto; repeat case_if~; simpls; repeat case_if; simpl in *; repeat case_if~.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=S m); auto.
  - inversions H1. rewrite H with (m:=S m); auto.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=S m); auto.
  - inversions H1. rewrite H with (m:=S m); auto.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=m); auto.
  - inversions H0.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=m); auto.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=m); auto.
Qed.

(** The following [lc_opening_XYZ] lemmas state that opening a locally
    closed symbol (variables, types, terms, etc.) at any index
    results in the same symbol. *)

(** - variables *)
Lemma lc_opening_avar: forall n x y,
    lc_var y ->
    open_rec_avar n x y = y.
Proof.
  introv Hl. destruct y as [b | y]. inversion Hl. simpls*.
Qed.

(** - types and declarations *)
Lemma lc_opening_typ_dec: forall x,
    (forall T, lc_typ T -> forall n, open_rec_typ n x T = T) /\
    (forall D, lc_dec D -> forall n, open_rec_dec n x D = D).
Proof.
  intros. apply lc_typ_mutind; intros; simpls; f_equal*.
  - apply* lc_opening_avar.
  - specialize (H x (S n)). apply lc_open_rec_open_typ_dec in H; auto.
  - specialize (H x (S n)). apply lc_open_rec_open_typ_dec in H; auto.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma lc_opening_trm_val_def_defs: forall x,
  (forall t, lc_trm t -> forall n, open_rec_trm n x t = t) /\
  (forall v, lc_val v -> forall n, open_rec_val n x v = v) /\
  (forall d, lc_def d -> forall n, open_rec_def n x d = d) /\
  (forall ds, lc_defs ds -> forall n, open_rec_defs n x ds = ds).
Proof.
  introv. apply lc_mutind; intros; simpls; f_equal*; try (apply* lc_opening_avar).
  - specialize (H0 x (S n)).
    rewrite (proj41 (lc_open_rec_open_trm_val_def_defs) x x) with (m:=0); auto.
  - specialize (l x).
    apply (proj21 (lc_opening_typ_dec x)) with (n := S n) in l.
    rewrite (proj21 (lc_open_rec_open_typ_dec x x)) with (m:=0); auto.
  - specialize (H x (S n)).
    rewrite (proj44 (lc_open_rec_open_trm_val_def_defs) x x) with (m:=0); auto.
  - apply* lc_opening_typ_dec.
  - specialize (H x (S n)).
    rewrite (proj41 (lc_open_rec_open_trm_val_def_defs) x x) with (m:=0); auto.
  - apply* lc_opening_typ_dec.
Qed.

(** The [lc_opening_trm_val_def_defs] lemma, specialized to terms. *)
Lemma lc_opening : forall t n x,
    lc_trm t ->
    open_rec_trm n x t = t.
Proof.
  intros. apply* lc_opening_trm_val_def_defs.
Qed.

Lemma lc_opening_change_var_typ_dec: forall x x',
    (forall T, lc_typ T -> forall n T',
            T = open_rec_typ n x T' ->
            lc_typ (open_rec_typ n x' T')) /\
    (forall D, lc_dec D -> forall n D',
            D = open_rec_dec n x D' ->
            lc_dec (open_rec_dec n x' D')).
Proof.
  intros. apply lc_typ_mutind; intros; simpl in *.
  - destruct T'; inversions H. constructor.
  - destruct T'; inversions H. constructor.
  - destruct T'; inversions H0. simpl. constructor~.
  - destruct T'; inversions H1. simpl. constructor~.
  - destruct T'; inversions H. simpl. constructor.
    destruct~ a; inversions l; case_if; subst~; simpl; case_if~.
  - destruct T'; inversions H0. simpl. constructor.
    intros. pose proof (O_S n).
    rewrite ((proj21 (open_comm_typ_dec x0 x')) _ _ _ H0).
    eapply H.
    rewrite ((proj21 (open_comm_typ_dec x0 x)) _ _ _ H0). reflexivity.
  - destruct T'; inversions H1. simpl. constructor~.
    intros. pose proof (O_S n).
    rewrite ((proj21 (open_comm_typ_dec x0 x')) _ _ _ H1).
    eapply H.
    rewrite ((proj21 (open_comm_typ_dec x0 x)) _ _ _ H1). reflexivity.
  - destruct D'; inversions H1. simpl. constructor~.
  - destruct D'; inversions H0. simpl. constructor~.
Qed.

Lemma lc_opening_change_var_trm_val_def_defs: forall x x',
    (forall t, lc_trm t -> forall n t',
            t = open_rec_trm n x t' ->
            lc_trm (open_rec_trm n x' t')) /\
    (forall v, lc_val v -> forall n v',
            v = open_rec_val n x v' ->
            lc_val (open_rec_val n x' v')) /\
    (forall d, lc_def d -> forall n d',
            d = open_rec_def n x d' ->
            lc_def (open_rec_def n x' d')) /\
    (forall ds, lc_defs ds -> forall n ds',
             ds = open_rec_defs n x ds' ->
             lc_defs (open_rec_defs n x' ds')).
Proof.
  intros. apply lc_mutind; intros; simpl in *.
  - destruct t'; inversions H.
    destruct a0; simpl in *; auto; case_if~.
  - destruct t'; inversions H0. simpl. constructor~.
  - destruct t'; inversions H. simpl. constructor~.
    destruct a0; simpl in *; auto; case_if~.
  - destruct t'; inversions H. simpl. constructor~.
    + destruct a0; simpl in *; auto; case_if~.
    + destruct a1; simpl in *; auto; case_if~.
  - destruct t'; inversions H1. simpl. constructor~.
    intros. pose proof (O_S n).
    rewrite ((proj41 (open_comm_trm_val_def_defs x0 x')) _ _ _ H1).
    eapply H0.
    rewrite ((proj41 (open_comm_trm_val_def_defs x0 x)) _ _ _ H1). reflexivity.
  - destruct v'; inversions H0. simpl. constructor~.
    + intros. specialize (l x0). pose proof (O_S n).
      rewrite ((proj21 (open_comm_typ_dec x0 x)) _ _ _ H0) in l.
      rewrite ((proj21 (open_comm_typ_dec x0 x')) _ _ _ H0).
      eapply ((proj21 (lc_opening_change_var_typ_dec x x'))); eauto.
    + intros. specialize (l0 x0). pose proof (O_S n).
      rewrite ((proj44 (open_comm_trm_val_def_defs x0 x')) _ _ _ H0).
      eapply H.
      rewrite ((proj44 (open_comm_trm_val_def_defs x0 x)) _ _ _ H0). reflexivity.
  - destruct v'; inversions H0. simpl. constructor~.
    + eapply (proj21 (lc_opening_change_var_typ_dec _ _)); eauto.
    + intros. pose proof (O_S n).
      rewrite ((proj41 (open_comm_trm_val_def_defs x0 x')) _ _ _ H0).
      eapply H.
      rewrite ((proj41 (open_comm_trm_val_def_defs x0 x)) _ _ _ H0). reflexivity.
  - destruct d'; inversions H. simpl. constructor~.
    eapply (proj21 (lc_opening_change_var_typ_dec _ _)); eauto.
  - destruct d'; inversions H0. simpl. constructor~.
  - destruct ds'; inversions H. simpl. constructor~.
  - destruct ds'; inversions H1. simpl. constructor~.
Qed.

(** * Lemmas About Local Closure *)

(** When a binding is removed from a locally closed store, the
    resulting store and the value in the binding are both
    locally closed. *)
Lemma lc_sto_push_inv : forall s x v,
    lc_sto (s & x ~ v) ->
    lc_sto s /\ lc_val v.
Proof.
  intros s x v H.
  inversion H.
  - destruct (empty_push_inv H1).
  - destruct (eq_push_inv H0) as [? [? ?] ]; subst.
    auto.
Qed.

(** Values in a locally closed store are also locally closed. *)
Lemma lc_sto_binds_inv : forall s x v,
    lc_sto s ->
    binds x v s ->
    lc_val v.
Proof.
  intros.
  induction s using env_ind.
  - destruct (binds_empty_inv H0).
  - destruct (binds_push_inv H0) as [[? ?] | [? ?]]; subst.
    + apply (lc_sto_push_inv H).
    + apply IHs; auto.
      apply (lc_sto_push_inv H).
Qed.

(** A definition in a locally closed list of definitions is also
    locally closed. *)
Lemma lc_defs_has : forall ds d,
    lc_defs ds ->
    defs_has ds d ->
    lc_def d.
Proof.
  intros.
  induction ds.
  - inversion H0.
  - unfold defs_has in H0; simpl in H0.
    cases_if.
    + inversions H0. inversion H; auto.
    + apply IHds; auto. inversion H; auto.
Qed.*)

(** * Lemmas About Records and Record Types *)

(** [labels(D) = labels(D^x)] *)
Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_dec_preserves_label_p: forall D p i,
  label_of_dec D = label_of_dec (open_rec_dec_p i p D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record:
  (forall D, record_dec D ->
        forall x k, record_dec (open_rec_dec k x D)) /\
  (forall T ls , record_typ T ls ->
        forall x k, record_typ (open_rec_typ k x T) ls) /\
  (forall T, inert_typ T ->
        forall x k, inert_typ (open_rec_typ k x T)).
Proof.
  apply rcd_mutind; intros; try constructor; auto;
    try solve [erewrite open_dec_preserves_label in e; eauto].
  unfold open_typ. simpl. eauto.
Qed.

Lemma open_record_p:
  (forall D, record_dec D ->
        forall p k, record_dec (open_rec_dec_p k p D)) /\
  (forall T ls , record_typ T ls ->
        forall p k, record_typ (open_rec_typ_p k p T) ls) /\
  (forall T, inert_typ T ->
        forall p k, inert_typ (open_rec_typ_p k p T)).
Proof.
  apply rcd_mutind; intros; try constructor; auto;
    try solve [erewrite open_dec_preserves_label_p in e; eauto].
  unfold open_typ. simpl. eauto.
Qed.

(** [record_dec D]   #<br>#
    [――――――――――――――] #<br>#
    [record_dec D^x] *)
Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. apply* open_record.
Qed.

Lemma open_record_dec_p: forall D x,
  record_dec D -> record_dec (open_dec_p x D).
Proof.
  intros. apply* open_record_p.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. apply* open_record.
Qed.

Lemma open_record_typ_p: forall T p ls,
  record_typ T ls -> record_typ (open_typ_p p T) ls.
Proof.
  intros. apply* open_record_p.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

Lemma open_record_type_p: forall T p,
  record_type T -> record_type (open_typ_p p T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ_p.
  eassumption.
Qed.

(** The type of definitions is a record type. *)
Lemma ty_defs_record_type : forall z bs P G ds T,
    z; bs; P; G ⊢ ds :: T ->
    record_type T.
Proof.
  intros. induction H; destruct D;
    repeat match goal with
        | [ H: record_type _ |- _ ] =>
          destruct H
        | [ Hd: _; _; _; _ ⊢ _ : { _ >: _ <: _ } |- _ ] =>
          inversions Hd
        | [ Hd: _; _; _; _ ⊢ _ : dec_trm _ _  |- _ ] =>
          inversions Hd
    end;
    match goal with
    | [ ls: fset label,
        t: trm_label |- _ ] =>
      exists (ls \u \{ label_trm t })
    | [ ls: fset label,
        t: typ_label |- _ ] =>
      exists (ls \u \{ label_typ t })
    | [ t: trm_label |- _ ] =>
      exists \{ label_trm t }
    | [ t: typ_label |- _ ] =>
      exists \{ label_typ t }
    end;
    constructor*; try constructor; apply (hasnt_notin H); eauto.
Qed.

(** Opening does not affect the labels of a [record_typ]. *)
Lemma opening_preserves_labels : forall z T ls ls',
    record_typ T ls ->
    record_typ (open_typ z T) ls' ->
    ls = ls'.
Proof.
  introv Ht Hopen. gen ls'.
  dependent induction Ht; intros.
  - inversions Hopen. rewrite* <- open_dec_preserves_label.
  - inversions Hopen. rewrite* <- open_dec_preserves_label.
    specialize (IHHt ls0 H4). rewrite* IHHt.
Qed.

Lemma record_open:
  (forall D, record_dec D ->
        forall x k D',
          x \notin fv_dec D' ->
          D = open_rec_dec k x D' ->
          record_dec D') /\
  (forall T ls , record_typ T ls ->
            forall x k T',
              x \notin fv_typ T' ->
              T = open_rec_typ k x T' ->
              record_typ T' ls) /\
  (forall T, inert_typ T ->
        forall x k T',
          x \notin fv_typ T' ->
          T = open_rec_typ k x T' ->
          inert_typ T').
Proof.
  apply rcd_mutind; intros; invert_open; simpls.
  - apply open_fresh_typ_dec_injective in H4; auto. subst. constructor.
  - constructor*. rewrite* <- open_dec_preserves_label.
  - invert_open. simpls. constructor*. rewrite* <- open_dec_preserves_label.
Qed.

(** If [T] is a record type with labels [ls], and [T = ... /\ D /\ ...],
    then [label(D) isin ls]. *)
Lemma record_typ_has_label_in: forall T D ls,
  record_typ T ls ->
  record_has T D ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Has. generalize dependent D. induction Htyp; intros.
  - inversion Has. subst. apply in_singleton_self.
  - inversion Has; subst; rewrite in_union.
    + left. apply* IHHtyp.
    + right. inversions H5. apply in_singleton_self.
Qed.

(** [T = ... /\ {A: T1..T1} /\ ...] #<br>#
    [T = ... /\ {A: T2..T2} /\ ...] #<br>#
    [―――――――――――――――――――――――――――] #<br>#
    [T1 = T2] *)
Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_has T (dec_typ A T1 T1) ->
  record_has T (dec_typ A T2 T2) ->
  T1 = T2.
Proof.
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_typ A T1 T1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_typ A T2 T2) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

Lemma unique_rcd_trm: forall T a U1 U2,
    record_type T ->
    record_has T (dec_trm a U1) ->
    record_has T (dec_trm a U2) ->
    U1 = U2.
Proof.
  introv Htype Has1 Has2.
  gen U1 U2 a.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - eapply record_typ_has_label_in with (D:=dec_trm a U1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_trm a U2) in Htyp.
    + inversions H5. false* H1.
    + inversions H5. lets Hr: (record_typ_has_label_in Htyp H9).
      false* H1.
  - inversions H5. inversions* H9.
Qed.

(** [ds = ... /\ {a = t} /\ ...]  #<br>#
    [ds = ... /\ {a = t'} /\ ...] #<br>#
    [―――――――――――――――――――――――――] #<br>#
    [t = t'] *)
Lemma defs_has_inv: forall ds a t t',
    defs_has ds (def_trm a t) ->
    defs_has ds (def_trm a t') ->
    t = t'.
Proof.
  intros. unfold defs_has in *.
  inversions H. inversions H0.
  rewrite H1 in H2. inversions H2.
  reflexivity.
Qed.

Lemma record_has_sel_typ: forall G p T a U,
    G ⊢ trm_path p : T ->
    record_has T (dec_trm a U) ->
    G ⊢ trm_path (p • a) : U.
Proof.
  introv Hp Hr. dependent induction Hr; eauto.
Qed.

(** * Conversion into General Typing *)

(** Precise typing implies general typing. *)
Lemma precise_to_general: forall G t T,
    G ⊢! t : T ->
    G ⊢ t : T.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.

Lemma inv_to_tight: forall G p T,
    G ⊢## p: T ->
    G ⊢# trm_path p: T.
Proof.
  introv Ht. induction Ht; eauto. dependent induction H; eauto. constructor; auto.
Qed.

(** Tight typing implies general typing. *)
Lemma tight_to_general:
  (forall G t T,
     G ⊢# t : T ->
     G ⊢ t : T) /\
  (forall G S U,
     G ⊢# S <: U ->
     G ⊢ S <: U).
Proof.
  apply ts_mutind_ts; intros; subst; eauto using precise_to_general.
Qed.

(** * Well-formedness *)

(** If [G ~~ s] and [x \notin dom(s)], then [x \notin dom(G)]. *)
Lemma wf_sto_notin_dom: forall G s x,
    G ~~ s ->
    x # s -> x # G.
Proof.
  intros. induction H; auto.
Qed.

(** If [G ~~ s], the variables in the domain of [s] are distinct. *)
Lemma wf_sto_to_ok_G: forall s G,
    G ~~ s -> ok G.
Proof.
  induction 1; jauto.
Qed.
Hint Resolve wf_sto_to_ok_G.

(** * Other Lemmas *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.13 in the paper. *)
Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢! trm_val v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl) as [T' [Hty Hsub]]. eauto.
Qed.

Lemma last_field : forall p a x bs,
    p • a = p_sel x bs ->
    exists bs', bs = a :: bs'.
Proof.
  introv Heq. destruct* p. inversion* Heq.
Qed.

Lemma invert_path_sel : forall p q a b,
    p • a = q • b -> p = q /\ a = b.
Proof.
  introv Heq. destruct p as [x1 bs1]. destruct q as [x2 bs2].
  induction bs1; inversion* Heq.
Qed.

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x bs T,
  G ⊢ trm_path (p_sel (avar_f x) bs) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
  destruct (last_field _ _ x) as [bs' Hbs]. subst.
  eapply IHHt. destruct p. inversion* x.
Qed.

Lemma var_typing_implies_avar_f: forall G a bs T,
  G ⊢ trm_path (p_sel a bs) : T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; eauto.
  destruct (last_field _ _ x) as [bs' Hbs]. subst.
  eapply IHty_trm. destruct p. inversion* x.
Qed.
