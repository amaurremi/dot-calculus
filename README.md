Extensions for Dependent Object Types
-------------------------------------

The DOT (Dependent Object Types) calculus by [Amin et al. (2016)](http://infoscience.epfl.ch/record/215280/files/paper_1.pdf) aims to formalizes Scala, specifically, abstract type members and path-dependent types.

This repository contains type-safe extensions to DOT that aim to bridge the gap between DOT and Scala, and to experiment with new Scala features. The extensions are based on our [simple](https://github.com/amaurremi/dot-calculus/tree/master/src/simple-proof) type-safety proof, which we started as a fork of the [original](https://github.com/samuelgruetter/dot-calculus) proof as presented by Amin et al. (2016).

If you want to understand the DOT safety proof, or are interested in creating your own extensions to DOT, you can read our [OOPSLA](http://mrapoport.com/publ/simple-dot-proof.pdf) paper, and check out the corresponding [Coq](https://github.com/amaurremi/dot-calculus/tree/master/src/simple-proof) proof.

This repo contains:
- the [simple DOT safety proof](https://github.com/amaurremi/dot-calculus/tree/master/src/simple-proof)
- extensions of DOT with:
  * *paths* of arbitrary length (adding type selections on _full paths_ of the form `p.A` instead of `x.A`, where `p` is a path and `x` is a variable)
  ([proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths)
  | [paper](https://mrapoport.com/publ/pdot.pdf))
  * *mutation* (adding _mutable references_ to DOT)
  ([proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/mutation) | [technical report](https://arxiv.org/abs/1611.07610))
  * *initialization* order (developing a sound _initialization order_)
  ([proof in progress](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/initialization))
