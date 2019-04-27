pDOT Type Safety Proof
======================

This directory contains the Coq formalization type-safety proof of
the [pDOT calculus](https://arxiv.org/abs/1904.07298v1)
that generalizes [DOT](https://infoscience.epfl.ch/record/215280) by Amin et al. (2016).
with paths of arbitrary length. This allows
us to express path-dependent types of the form `x.a.b.A` as opposed to
just `x.A`.

[Link to the pDOT paper](https://arxiv.org/abs/1904.07298v1)

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

## Paper Correspondence

The pDOT calculus is formalized using the [locally nameless
representation](http://www.chargueraud.org/softs/ln/)
with cofinite quantification
in which free variables are represented as named variables,
and bound variables are represented as de Bruijn indices.

We include the [Sequences](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Sequences.html) library by [Xavier Leroy](https://xavierleroy.org/) into our development to reason about the reflexive, transitive closure of binary relations.

### Correspondence of Definitions

| Definition                                          | In [paper](https://arxiv.org/abs/1904.07298v1)      | File                   | Paper notations                                                                         | Proof notations                                                                                                                                                                                  | Name in proof           |
|-----------------------------------------------------|---------------|------------------------|----------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------|
| Abstract Syntax                                     | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |                                                                                        |                                                                                                                                                                                                  |                         |
| - variable                                          | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | | | [`avar`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#avar) |
| - term member                                       | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |                                                                                        |                                                                                                                                                                                                  | [`trm_label`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#trm_label)               |
| - type member                                       | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |                                                                                        |                                                                                                                                                                                                  | [`typ_label`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#typ_label)               |
| - path                                              | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |  x.a.b.c<br><br>p.a<br><br>p.b̅        |  `p_sel x (c::b::a::nil)` <br><br>`p•a`<br> <br>`p••b`                                                              | [`path`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#path)                   |
| - term                                              | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |                                                                                        |                                                                                                                                                                                                  | [`trm`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#trm)                     |
| - stable term                                       | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |                                                                                        |                                                                                                                                                                                                  | [`def_rhs`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#def_rhs)                 |
| - value                                             | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | ν(x: T)ds <br>λ(x: T)t                                                                 | `ν(T)ds` <br>`λ(T)t`                                                                                                                                                                             | [`val`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#val)                     |
| - definition                                        | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | {a = t} <br>{A = T}                                                                    | `{a := t}`<br> `{A ⦂= T}`                                                                                                                                                                            | [`def`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#def)                     |
| - type                                              | Fig. 1      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | {a: T} <br>{A: T..U} <br>∀(x: T)U <br>p.A <br>p.type <br>μ(x: T) <br>T ∧ U <br>⊤ <br>⊥ | `{a ⦂ T}` <br>`{A >: T <: U}` <br>`∀(T)U` <br>`p↓A` <br>`{{p}}` <br>`μ(T)` <br>`T ∧ U` <br>`⊤` <br>`⊥`                                                                                                            | [`typ`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#typ)                     |
| Type System                                         | Fig. 2      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |                                                                                        |                                                                                                                                                                                                  |                         |
| - term typing                                       | Fig. 2      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | Γ ⊢ t: T                                                                               | `Γ ⊢ t : T`                                                                                                                                                                                      | [`ty_trm`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#ty_trm)                |
| - definition typing                                 | Fig. 2      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | p; Γ ⊢ d: T                                                                            | `x; bs; Γ ⊢ d : T` <br>(single definition)  <br> `x; bs; Γ ⊢ d :: T` <br>(multiple definitions) <br> Here, p=`x.bs`, i.e. `x`<br> is p's receiver, and <br>`bs` are p's fields <br>in reverse order | [`ty_def`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#ty_def) <br> [`ty_defs`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#ty_defs) |
| - tight bounds                                      | Fig. 2      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          |                                                                                        |                                                                                                                                                                                                  | [`tight_bounds`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#tight_bounds)          |
| - subtyping                                         | Fig. 2      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | Γ ⊢ T <: U                                                                             | `Γ ⊢ T <: U`                                                                                                                                                                                     | [`subtyp`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#subtyp)                |
| Operational semantics | Fig. 3 | [Reduction.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Reduction.html) | γ&#124;t ⟼ γ'&#124;t' <br> γ&#124;t ⟼* γ'&#124;t' | `(γ, t) ⟼ (γ', t')` <br> `(γ, t) ⟼* (γ', t')` | [`red`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Reduction.html#red) |
| Path lookup                                         | Fig. 4      | [Lookup.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Lookup.html)               | γ ⊢ p ⤳ s <br> γ ⊢ s ⤳* s' <br> γ ⊢ p ⤳* v                                              | `γ ⟦ p ⤳ s ⟧` <br> `γ ⟦ s ⤳* s' ⟧` <br> `γ ∋ (p, v)`                                                                                                                                              | [`lookup_step`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Lookup.html#lookup_step)           |
| Extended reduction                                  | Sec. 5     | [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)               | γ&#124;t ↠ γ'&#124;t' <br> γ&#124;t ↠* γ'&#124;t'                                                                          | `(γ, t) ↠ (γ', t')` <br> `(γ, t) ↠* (γ', t')`                                                                                                                                                                              | [`extended_red`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html#extended_red)          |
| Inert and record types                              | Fig. 5      | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | inert T <br> inert Γ                                                                   | | [`inert_typ`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#inert_typ) <br> [`inert`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#inert)                                                                                                                                                                     |
| Well-formed <br> environments                            | Sec. 5.2.1 | [PreciseTyping.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/PreciseTyping.html)        |                                                                                        |                                                                                                                                                                                                  | [`wf`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/PreciseTyping.html#wf)                    |
| Correspondence <br>between a value<br> and type environment | Sec. 5     | [Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)          | γ: Γ                                                                                   | `γ ⫶ Γ`                                                                                                                                                                                          | [`well_typed`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html#well_typed) |


### Correspondence of Lemmas and Theorems

| Theorem                          | File             | Name in proof         |
|----------------------------------|------------------|-----------------------|
| Theorem 5.1 (Soundness)          | [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)         | [`safety`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html#safety)              |
| Theorem 5.2 (Extended Soundness) | [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)         | [`extended_safety`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html#extended_safety)     |
| Lemma 5.3 (Progress)             | [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)         | [`progress`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html#progress)            |
| Lemma 5.4 (Preservation)         | [Safety.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html)         | [`preservation`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Safety.html#preservation)        |
| Lemma 5.4                        | [CanonicalForms.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/CanonicalForms.html) | [`canonical_forms_fun`](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/CanonicalForms.html#canonical_forms_fun) |

### Correspondence of Examples

| Example                | In [paper](https://arxiv.org/abs/1904.07298v1)                 | File                   |
|------------------------|--------------------------|------------------------|
| List example           | Section 6.2, Figure 8 a) | [ListExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/ListExample.html)                   |
| Compiler example       | Section 6.3, Figure 8 b) | [CompilerExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/CompilerExample.html)           |
| Singleton type example | Section 6.4, Figure 8 c) | [SingletonTypeExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/SingletonTypeExample.html) |

## Proof Organization

### Safety Proof
The Coq proof is split up into the following modules:
  - **[Definitions.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Definitions.html)**: Definitions of pDOT's
    abstract syntax and type system.
  - **[Reduction.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/Reduction.html)**:
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

### Examples

  - [CompilerExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/CompilerExample.html): The dotty-compiler
    example that contains paths of length greater than one.
  - [ListExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/ListExample.html): A covariant-list
    implementation.
  - [SingletonTypeExample.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/SingletonTypeExample.html):
    Method chaining through singleton types.
  - [ExampleTactics.v](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/ExampleTactics.html): Helper tactics to prove
    the above examples.

The following figure shows a dependency graph between the Coq modules:

![Dependency graph](https://amaurremi.github.io/dot-calculus/src/extensions/paths/doc/graph.png)
