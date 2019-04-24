(** * Tactics and Notatations used in Examples *)

Require Export Definitions Binding Weakening.
Require Export List.

Notation path_ref n := (p_sel (avar_b n) nil).

Notation this := (path_ref 0).
Notation super := (path_ref 1).
Notation ssuper := (path_ref 2).
Notation sssuper := (path_ref 3).
Notation ssssuper := (path_ref 4).
Notation sssssuper := (path_ref 5).

Notation lazy t := (defv (λ(⊤) t)).
Notation Lazy T := (∀(⊤) T).
Notation id := (λ(⊤) (trm_path this)).
Notation Id := (Lazy ⊤).
Notation let_trm t := (trm_let t (trm_path this)).

Notation "d1 'Λ' d2" := (defs_cons d1 d2) (at level 40).

Ltac crush :=
  repeat (progress (simpl; repeat case_if;
                    try (unfold open_trm, open_typ, open_typ_p, open_defs, open_defs_p))); auto;
  try match goal with
      | [ H: _ |- defs_hasnt _ _ ] =>
        simpl; repeat case_if; unfold defs_hasnt; simpl; repeat case_if; auto
      end.

Ltac remember_ctx G :=
   match goal with
      | H: _ |- ?G' ⊢ _ : _ =>
        remember G' as G
   end.
