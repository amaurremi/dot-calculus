# DOT with Extended Paths

We are working on an extension for DOT that supports type selection on paths of arbitrary length, as opposed to type selection on variables. For example, we allow a type of the form `x.a.b.A` instead of only `x.A`.

This is work in progress. The definition of the type system can be found in `Definitions.v`.
