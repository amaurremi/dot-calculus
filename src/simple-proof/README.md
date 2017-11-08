# A Simple Soundness Proof for Dependent Object Types

Our [paper](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla17.pdf) presents a simplified type-safety proof for the [version of DOT](https://infoscience.epfl.ch/record/215280) presented at Wadlerfest 2016. This repository contains a formalization of the simple proof in Coq. The definitions of the abstract syntax and several lemmas are based on the [original](https://github.com/samuelgruetter/dot-calculus/blob/master/dev/lf/dot_top_bot.v) Coq proof that comes with Wadlerfest DOT paper.

This directory contains a Coq formalization of the DOT calculus and DOT's type safety proof. Our technique is based on eliminating bad bounds by using *inert types* and applying the *proof recipe*, as described in the OOPSLA'17 [paper](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla17.pdf).

## Documentation

The documentation can be accessed from the [table of contents](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/toc.html). This page lists links to pretty printed Coq source files, but the raw `.v` files can be found in the [proof](proof) directory. In the pretty-printed versions, the proof scripts are hidden by default, you may click on "Show Proofs" at the top of the page to display all the proofs, or click under the Lemma or Theorem statements to display their proofs.

### Proof Structure

The Coq proof is split up into the following modules:
  * [Definitions.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Definitions.html): The main inductive definitions and functions that are used in the proof. Defines the abstract syntax and type system.
  * [Binding.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Binding.html): Proves helper lemmas related to opening, closing, and local closure.
  * [SubEnvironments.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/SubEnvironments.html): Defines and proves lemmas related to subenvironments.
  * [Weakening.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Weakening.html): Proves the Weakening Lemma.
  * [RecordAndInertTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/RecordAndInertTypes.html): Defines and proves lemmas related to record and inert types.
  * [Narrowing.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Narrowing.html): Proves the Narrowing Lemma.
  * [OperationalSemantics.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/OperationalSemantics.html): Defines normal forms and the operational semantics of DOT, as well as related helper lemmas.
  * [PreciseTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/PreciseTypes.html): Defines and proves lemmas related to precise typing. In particular, reasons about the possible precise types that a variable can have in an inert environment.
  * [TightTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/TightTypes.html): Defines tight typing and subtyping.
  * [Substitution.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Substitution.html): Proves the Substitution Lemma.
  * [InvertibleTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/InvertibleTypes.html): Defines invertible typing and proves that in an inert context, tight typing implies invertible typing (both for variables and values).
  * [GeneralToTight.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/GeneralToTight.html): Proves that in an inert context, general typing implies tight typing.
  * [CanonicalForms.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/CanonicalForms.html): Proves the Canonical Forms Lemmas for functions and objects.
  * [Safety.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Safety.html): Proves the Progress and Preservation Theorems.

The following figure shows a dependency graph between the Coq modules.
![Dependency graph](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/graph.png)

### Evaluation Contexts vs. Runtime Environments

On paper, DOT's operational semantics is defined in terms of evaluation contexts. A type-soundness proof based on that semantics can be found in the [proof-ec](https://github.com/amaurremi/dot-calculus/tree/master/src/simple-proof/proof-ec) directory.

Evaluation contexts introduce complexity into the proof, which can be avoided by using an alternative semantics that is based on stacks.

A stack is a sequence of variable-to-value bindings, which serves as a runtime environment (in the literature, stacks are commonly referred to as stores). In the stack representation, the operational semantics is defined on pairs `(s, t)`, where `s` is a stack and `t` is a term. For example, the term `let x1 = v1 in let x1 = v2 in t` is represented as `({(x1, v1), (x2, v2)}, t)`.


## Compiling the Proof

To compile the proof, we require `coq 8.6` and related tooling to be run in a unix-like environment. In particular, we require the following tools (all version 8.6) in the `PATH` enviroment variable:
  * coqc
  * coqtop
  * coqdep
  * coqdoc
  * coqmakefile

Other requirements are:
  * make

To compile the proof, run

    git clone https://github.com/amaurremi/dot-calculus
    cd dot-calculus/src/simple-proof
    make

`make` will do the following:

- compile the `tlc` library
- compile the safety proof
- generate documentation.
