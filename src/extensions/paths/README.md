pDOT Type Safety Proof
======================

This directory contains the Coq formalization type-safety proof of
the [pDOT calculus](https://arxiv.org/abs/1904.07298v1)
that generalizes [DOT](https://infoscience.epfl.ch/record/215280) by Amin et al. (2016).
with paths of arbitrary length. This allows
us to express path-dependent types of the form `x.a.b.A` as opposed to
just `x.A`.

## Compiling the Proof

**System requirements**:

  - make
  - an installation of [Coq 8.9.0](https://coq.inria.fr/opam-using.html), preferably through [opam](https://opam.ocaml.org/)
  - the [TLC](https://gitlab.inria.fr/charguer/tlc) library which can
  be installed through

```
 opam repo add coq-released http://coq.inria.fr/opam/released
 opam install -j4 coq-tlc
```

To **compile the proof**, navigate to the cloned directory and run

```
 cd src/extensions/paths
 make
```

## Proof Organization

### Safety Proof
The Coq proof is split up into the following modules:

  - **[Definitions.v](proof/Definitions.v)**: Definitions of pDOT's
    abstract syntax and type system.
  - **[OperationalSemantics.v](proof/OperationalSemantics.v)**:
    Normal forms and the operational semantics of pDOT.
  - **[Safety.v](proof/Safety.v)**: ***Final safety theorem***
    through Progress and Preservation.
  - [Lookup.v](proof/Lookup.v): Definition of path lookup and
    properties of lookup.
  - [Binding.v](proof/Binding.v): Lemmas related to opening and
    variable binding.
  - [SubEnvironments.v](proof/SubEnvironments.v): Lemmas related to
    subenvironments.
  - [Weakening.v](proof/Weakening.v): Weakening Lemma.
  - [RecordAndInertTypes.v](proof/RecordAndInertTypes.v): Lemmas
    related to record and inert types.
  - [Replacement.v](proof/Replacement.v): Properties of equivalent
    types.
  - [Narrowing.v](proof/Narrowing.v): Narrowing Lemma.
  - [PreciseFlow.v](proof/PreciseFlow.v) and
    [PreciseTyping.v](proof/PreciseTyping.v): Lemmas related to
    elimination typing. In particular, reasons about the possible
    precise types that a path can have in an inert environment.
  - [TightTyping.v](proof/TightTyping.v): Defines tight typing and
    subtyping.
  - [Substitution.v](proof/Substitution.v): Proves the Substitution
    Lemma.
  - [InvertibleTyping.v](proof/InvertibleTyping.v) and
    [ReplacementTyping.v](proof/ReplacementTyping.v): Lemmas related to
    introduction typing.
  - [GeneralToTight.v](proof/GeneralToTight.v): Proves that in an
    inert context, general typing implies tight typing.
  - [CanonicalForms.v](proof/CanonicalForms.v): Canonical Forms
    Lemma.
  - [Sequences.v](proof/Sequences.v): A library of relation
    operators by Xavier Leroy.

### Path Safety Proof

* [Safety.v](proof/Safety.v): Proves that well-typed paths
    are either cyclic or reduce to values.

### Examples

  - [CompilerExample.v](proof/CompilerExample.v): The dotty-compiler
    example that contains paths of length greater than one.
  - [ListExample.v](proof/ListExample.v): A covariant-list
    implementation.
  - [SingletonTypeExample.v](proof/SingletonTypeExample.v):
    Method chaining through singleton types.
  - [ExampleTactics.v](proof/ExampleTactics.v): Helper tactics to prove
    the above examples.

<!--The following figure shows a dependency graph between the Coq modules:-->

<!--![Dependency graph](paths/doc/graph.png)-->

## Paper Correspondence

The pDOT calculus is formalized using the [locally nameless
representation](http://www.chargueraud.org/softs/ln/)
with cofinite quantification
in which free variables are represented as named variables,
and bound variables are represented as de Bruijn indices.

- pDOT's **abstract syntax** (Figure 1)
    is defined in [Definitions.v](proof/Definitions.v):
    - variable: `avar`
    - term member: `trm_label`
    - type member: `typ_label`
    - path: `path`
    - term: `trm`
    - stable term: `def_rhs`
    - value: `val`
    - definition: `def`
    - type: `typ`
- pDOT **type system** (Figure 2)
    is defined in [Definitions.v](proof/Definitions.v):
    - term typing (Γ ⊢ t: T): `ty_trm`, notation: `Γ ⊢ t : T`
    - definition typing (p; Γ ⊢ d: T): `ty_def` and `ty_defs` for single
        and multiple definitions; notations: `x; bs; Γ ⊢ d : T` and
        `x; bs; G ⊢ d :: T`, where `x` is the receiver of the
        path and `bs` is the list of p's fields in *reverse* order.
        For example, a path x.a.b.c will be represented as
        x; \[c, b, a\]
    - tight bounds: `tight_bounds` function
    - subtyping (Γ ⊢ T <: U): `subtyp`, notation: `Γ ⊢ T <: U`
- pDOT's **operational semantics** (Figure 3)
    defined in [OperationalSemantics.v](proof/OperationalSemantics.v):
    - reduction relation (γ | t ↦ γ' | t'):
        `red'`, notation: `(γ, t) |=> (γ', t')`,
- **Path lookup** (Figure 4):
    - lookup relation (γ ⊢ p ⤳ s ):
        `lookup_step`, notation: `γ ⟦ p ⟼ s ⟧`,
        defined in
        [Lookup.v](proof/Lookup.v)
    - reflexive, transitive closure of lookup relation (γ ⊢ s ⤳* s' ):
        `lookup`, notation: `γ ⟦ s ⟼* s' ⟧`;
        we also define special notation for a lookup that results
        in a value: `γ ∋ (p, v)`;
        defined in
        [Lookup.v](proof/Lookup.v)
- **Inert** types (Figure 5)
    defined in [Definitions.v](proof/Definitions.v):
    - inert types: `inert_typ`
    - records `record_typ` and `record_dec`
    - inert contexts: `inert`
- **Well-formed** environments are defined in
    [PreciseTyping.v](proof/PreciseTyping.v) as `wf_env`
- **Correspondence** between a value and typing environment
    (γ: Γ) is represented as `well_typed Γ γ`,
    [Definitions.v](proof/Definitions.v)
- **Theorems**:
    In the progress and preservation lemmas,
    we use the `sta_trm_typ` judgment with a notation `⊢ (γ, t): T` to
    denote that for all inert, well-typed environment Γ such that
    γ: Γ, Γ ⊢ t: T.
  - Theorem 5.1 (**Soundness**): `safety` in [Safety.v](proof/Safety.v)
  - Lemma 5.2 (Progress): `progress` in [Safety.v](proof/Safety.v)
  - Lemma 5.3 (Preservation): `preservation` in [Safety.v](proof/Safety.v)
  - Lemma 5.4: `canonical_forms_fun` in
    [CanonicalForms.v](proof/CanonicalForms.v).
