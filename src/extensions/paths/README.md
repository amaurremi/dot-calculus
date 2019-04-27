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

  - **[Definitions.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Definitions.html)**: Definitions of pDOT's
    abstract syntax and type system.
  - **[OperationalSemantics.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/OperationalSemantics.html)**:
    Normal forms and the operational semantics of pDOT.
  - **[Safety.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Safety.html)**: ***Final safety theorem***
    through Progress and Preservation.
  - [Lookup.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Lookup.html): Definition of path lookup and
    properties of lookup.
  - [Binding.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Binding.html): Lemmas related to opening and
    variable binding.
  - [SubEnvironments.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/SubEnvironments.html): Lemmas related to
    subenvironments.
  - [Weakening.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Weakening.html): Weakening Lemma.
  - [RecordAndInertTypes.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/RecordAndInertTypes.html): Lemmas
    related to record and inert types.
  - [Replacement.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Replacement.html): Properties of equivalent
    types.
  - [Narrowing.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Narrowing.html): Narrowing Lemma.
  - [PreciseFlow.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/PreciseFlow.html) and
    [PreciseTyping.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/PreciseTyping.html): Lemmas related to
    elimination typing. In particular, reasons about the possible
    precise types that a path can have in an inert environment.
  - [TightTyping.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/TightTyping.html): Defines tight typing and
    subtyping.
  - [Substitution.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Substitution.html): Proves the Substitution
    Lemma.
  - [InvertibleTyping.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/InvertibleTyping.html) and
    [ReplacementTyping.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/ReplacementTyping.html): Lemmas related to
    introduction typing.
  - [GeneralToTight.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/GeneralToTight.html): Proves that in an
    inert context, general typing implies tight typing.
  - [CanonicalForms.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/CanonicalForms.html): Canonical Forms
    Lemma.
  - [Sequences.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Sequences.html): A library of relation
    operators by Xavier Leroy.

### Path Safety Proof

* [Safety.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Safety.html): Proves that well-typed paths
    are either cyclic or reduce to values.

### Examples

  - [CompilerExample.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/CompilerExample.html): The dotty-compiler
    example that contains paths of length greater than one.
  - [ListExample.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/ListExample.html): A covariant-list
    implementation.
  - [SingletonTypeExample.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/SingletonTypeExample.html):
    Method chaining through singleton types.
  - [ExampleTactics.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/ExampleTactics.html): Helper tactics to prove
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
    is defined in [Definitions.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Definitions.html):
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
    is defined in [Definitions.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Definitions.html):
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
    defined in [OperationalSemantics.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/OperationalSemantics.html):
    - reduction relation (γ | t ↦ γ' | t'):
        `red'`, notation: `(γ, t) |=> (γ', t')`,
- **Path lookup** (Figure 4):
    - lookup relation (γ ⊢ p ⤳ s ):
        `lookup_step`, notation: `γ ⟦ p ⟼ s ⟧`,
        defined in
        [Lookup.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Lookup.html)
    - reflexive, transitive closure of lookup relation (γ ⊢ s ⤳* s' ):
        `lookup`, notation: `γ ⟦ s ⟼* s' ⟧`;
        we also define special notation for a lookup that results
        in a value: `γ ∋ (p, v)`;
        defined in
        [Lookup.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Lookup.html)
- **Inert** types (Figure 5)
    defined in [Definitions.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Definitions.html):
    - inert types: `inert_typ`
    - records `record_typ` and `record_dec`
    - inert contexts: `inert`
- **Well-formed** environments are defined in
    [PreciseTyping.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/PreciseTyping.html) as `wf_env`
- **Correspondence** between a value and typing environment
    (γ: Γ) is represented as `well_typed Γ γ`,
    [Definitions.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Definitions.html)
- **Theorems**:
    In the progress and preservation lemmas,
    we use the `sta_trm_typ` judgment with a notation `⊢ (γ, t): T` to
    denote that for all inert, well-typed environment Γ such that
    γ: Γ, Γ ⊢ t: T.
  - Theorem 5.1 (**Soundness**): `safety` in [Safety.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Safety.html)
  - Lemma 5.2 (Progress): `progress` in [Safety.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Safety.html)
  - Lemma 5.3 (Preservation): `preservation` in [Safety.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/Safety.html)
  - Lemma 5.4: `canonical_forms_fun` in
    [CanonicalForms.v](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths/doc/CanonicalForms.html).
