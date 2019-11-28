# MtacLite

This repository contains the work I've done for my TRE during my Master 1 at Paris 7.

It explores the compilation of typed tactic languages in Coq, with the intent of providing a compiler for the Mtac2 proof tactic language.

## Building

This project is built using the `dune` build tool. 

It depends on a modified version of coq which can be installed by running

```
opam pin coq https://github.com/xldenis/coq.git#extend-native-compil
```


# Compiling Tactics

Tactic languages like Mtac and Ltac2 model side-effects by having tactics operate in a tactic monad, with the monadic constructors corresponding to effects like non-termination, unification and exceptions. They require a hand-written and tuned interpreter for these languages, which either leads to higher complexity and less flexibility in language design or lower performance.

Because Mtac tactics are written as Gallina terms we can ask Coq to generate native code corresponding to each tactic. This will allow us to use OCaml to perform all the actual calculations in our tactic instead of Coq's evaluation or our own custom runtime. However, OCaml knows nothing about our monadic operations, it just sees them as constructors for an AST and happily normalizes our AST. We can teach OCaml how to handle our side-effects by writing an 'effect interpreter' which operates on the OCaml representation of our tactic code. With this, we can start evaluating tactical expressions! But it turns out we still have a rather large problem...

Tactic languages typically include a form of unification, which at least in coq is _not_ preserved by beta reduction. This means that `x -> x' -> unify x y -/-> unify x' y`. As an example we can look at `unify (?a ++ ?b) ([1] ++ [2])`, here `?a` and `?b` are metavariables so we the expression `?a ++ ?b` is already normal but `[1] ++ [2] --> [1; 2]` which won't unify anymore. This is a problem because OCaml uses call-by-value and will eagerly reduce any arguments to constructors or functions, which means that it won't attempt to preserve the `[1] ++ [2]`.

We still have a trick up our sleeve though, Coq's compilation needs to handle free variables, which it achieves by 'freezing' them in an accumulator, a structure which just stores every argument applied to it. It's almost like a thunk that we can't force (easily). If we can indentify the areas that need to avoid beta-reduction then we could turn those into accumulators during the compilation and bam! no more beta-reduction!

In this project we take as a hypothesis that _non-tactical_ arguments and terms are _symbolic_, they're terms that we want to avoid evaluating. On the other hand, all terms of a _tactical_ type are considered to be computational, after all we're evaluating tactics here! So we compile pure arguments/terms to accumulators and tactical ones to normal CBV functions.


# Project

This project defines a typed tactic language called Mtaclite, which contains the essential features of Mtac/Mtac2. Just like Mtac, this language is defined in Coq which means that tactics written in Mtaclite are themselves Gallina terms, albeit equipped with monadic effects. In Mtac, these terms are interpreted by an OCaml tree walking interpreter which provides interpretation for all effects during interpretation.

In Mtac2, this interpreter is written as a stack machine, providing faster execution. This stack machine adds a lot of complexity to the code, making it indirect and hard to follow. On top of that, a lot of work in tactics does not come (directly) from the effects, but occurs when we need to reduce the gallina terms inside the tactics to expose the next effects we need to perform. Mtac2 is still limited to using the Coq api to perform those reductions, but Coq provides another mechanism to perform reduction terms: compilation of OCaml.

For several years, Coq has provided a native compilation mechanism for gallina terms, compiling them down to a representation in OCaml which then allows us to use the much faster code produced by the OCaml compiler to execute our terms, after which we can 'readback' the resulting term to reconstruct the result as a Coq term. Mtaclite uses this mechanism to provided much faster execution for tactics without the complications of a stack machine or a custom compilation mechanism. Here's how it works:

Given a tactic term `T` with type `Mtac A`, we ask Coq to natively compile the term. Coq will very helpfully compile it for us to an equivalent OCaml term `U`, along with any functions or datatypes used within the term. We can now ask OCaml to evaluate the compilation of `U`, producing a normal form `U'`, which must have an `Mtac` constructor in head position. We can now use an interpreter to provide effects for the compiled, ocaml representation, and each time we need to evaluate a subterm, we're evaluating native ocaml functions and applications, a huge speed-boost over Coq's reductions.

