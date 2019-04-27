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
  - **[Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)**: Definitions of pDOT's
    abstract syntax and type system.
  - **[OperationalSemantics.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/OperationalSemantics.html)**:
    Normal forms and the operational semantics of pDOT.
  - **[Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)**: ***Final safety theorem***
    through Progress and Preservation.
  - [Lookup.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Lookup.html): Definition of path lookup and
    properties of lookup.
  - [Binding.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Binding.html): Lemmas related to opening and
    variable binding.
  - [SubEnvironments.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/SubEnvironments.html): Lemmas related to
    subenvironments.
  - [Weakening.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Weakening.html): Weakening Lemma.
  - [RecordAndInertTypes.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/RecordAndInertTypes.html): Lemmas
    related to record and inert types.
  - [Replacement.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Replacement.html): Properties of equivalent
    types.
  - [Narrowing.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Narrowing.html): Narrowing Lemma.
  - [PreciseFlow.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/PreciseFlow.html) and
    [PreciseTyping.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/PreciseTyping.html): Lemmas related to
    elimination typing. In particular, reasons about the possible
    precise types that a path can have in an inert environment.
  - [TightTyping.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/TightTyping.html): Defines tight typing and
    subtyping.
  - [Substitution.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Substitution.html): Proves the Substitution
    Lemma.
  - [InvertibleTyping.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/InvertibleTyping.html) and
    [ReplacementTyping.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/ReplacementTyping.html): Lemmas related to
    introduction typing.
  - [GeneralToTight.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/GeneralToTight.html): Proves that in an
    inert context, general typing implies tight typing.
  - [CanonicalForms.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/CanonicalForms.html): Canonical Forms
    Lemma.
  - [Sequences.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Sequences.html): A library of relation
    operators by Xavier Leroy.

### Path Safety Proof

* [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html): Proves that well-typed paths
    are either cyclic or reduce to values.

### Examples

  - [CompilerExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/CompilerExample.html): The dotty-compiler
    example that contains paths of length greater than one.
  - [ListExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/ListExample.html): A covariant-list
    implementation.
  - [SingletonTypeExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/SingletonTypeExample.html):
    Method chaining through singleton types.
  - [ExampleTactics.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/ExampleTactics.html): Helper tactics to prove
    the above examples.

<!--The following figure shows a dependency graph between the Coq modules:-->

<!--![Dependency graph](paths/doc/graph.png)-->

## Paper Correspondence

The pDOT calculus is formalized using the [locally nameless
representation](http://www.chargueraud.org/softs/ln/)
with cofinite quantification
in which free variables are represented as named variables,
and bound variables are represented as de Bruijn indices.

| Definition                                          | In paper      | File                   | Paper notation                                                                         | Proof notations                                                                                                                                                                                  | Name in proof           |
|-----------------------------------------------------|---------------|------------------------|----------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------|
| Abstract Syntax                                     | Figure 1      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  |                         |
| - variable                                          | Figure 1      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  | avar                    |
| - term member                                       | Figure 1      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  | trm_label               |
| - type member                                       | Figure 1      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  | typ_label               |
| - path                                              | Figure 1      | Definitions.v          |  x.a.b.c<br>p.a (single field selection)<br> p.b̅ (selection of a list of fields)       |  [p_sel x [c, b, a]] (paths are represented as a pair of a receiver and a list of fields in reverse order) <br>[p•a]<br> <br>[p••b]                                                              | path                    |
| - term                                              | Figure 1      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  | trm                     |
| - stable term                                       | Figure 1      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  | def_rhs                 |
| - value                                             | Figure 1      | Definitions.v          | ν(x: T)ds <br>λ(x: T)t                                                                 | [ν(T)ds] <br>[λ(T)t]                                                                                                                                                                             | val                     |
| - definition                                        | Figure 1      | Definitions.v          | {a = t} <br>{A = T}                                                                    | [{a := t}] [{A ⦂= T}]                                                                                                                                                                            | def                     |
| - type                                              | Figure 1      | Definitions.v          | {a: T} <br>{A: T..U} <br>∀(x: T)U <br>p.A <br>p.type <br>μ(x: T) <br>T ∧ U <br>⊤ <br>⊥ | {a ⦂ T} <br>{A >: T <: U} <br>∀(T)U <br>p↓A <br>{{p}} <br>μ(T) <br>T ∧ U <br>⊤ <br>⊥                                                                                                             | typ                     |
| Type System                                         | Figure 2      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  |                         |
| - term typing                                       | Figure 2      | Definitions.v          | Γ ⊢ t: T                                                                               | [Γ ⊢ t : T]                                                                                                                                                                                      | [ty_trm]                |
| - definition typing                                 | Figure 2      | Definitions.v          | p; Γ ⊢ d: T                                                                            | [x; bs; Γ ⊢ d : T] (single definition typing)  <br> [x; bs; Γ ⊢ d :: T] (typing of multiple definitions) <br> Here, p=[x.bs], i.e. [x] is p's receiver, and [bs] are p's fields in reverse order | [ty_def] <br> [ty_defs] |
| - tight bounds                                      | Figure 2      | Definitions.v          |                                                                                        |                                                                                                                                                                                                  | [tight_bounds]          |
| - subtyping                                         | Figure 2      | Definitions.v          | Γ ⊢ T <: U                                                                             | [Γ ⊢ T <: U]                                                                                                                                                                                     | [subtyp]                |
| Operational semantics                               | Figure 3      | OperationalSemantics.v |                                                                                        |                                                                                                                                                                                                  | [red]                   |
| Path lookup                                         | Figure 4      | Lookup.v               | γ ⊢ p ⟼ s <br> γ ⊢ s ⟼* s' <br> γ ⊢ p ⟼ v                                              | [γ ⊢ ⟦ p ⟼ s ⟧ <br> γ ⊢ ⟦ s ⟼* s' ⟧ <br> γ ∋ (p, v)                                                                                                                                              | [lookup_step]           |
| Inert and record types                              | Figure 5      | Definitions.v          | inert T <br> inert Γ                                                                   | [inert_typ T] <br> [inert Γ]                                                                                                                                                                     |                         |
| Well-formed environments                            | Section 5.2.1 | PreciseTyping.v        |                                                                                        |                                                                                                                                                                                                  | [wf]                    |
| Correspondence between a value and type environment | Section 5     | Definitions.v          | γ: Γ                                                                                   | [γ ⫶ Γ]                                                                                                                                                                                          | [well_typed] |


- **Theorems**:
    In the progress and preservation lemmas,
    we use the `sta_trm_typ` judgment with a notation `⊢ (γ, t): T` to
    denote that for all inert, well-typed environment Γ such that
    γ: Γ, Γ ⊢ t: T.
  - Theorem 5.1 (**Soundness**): `safety` in [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)
  - Lemma 5.2 (Progress): `progress` in [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)
  - Lemma 5.3 (Preservation): `preservation` in [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)
  - Lemma 5.4: `canonical_forms_fun` in
    [CanonicalForms.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/CanonicalForms.html).
