# MtacLite

This repository contains the work I've done for my TRE during my Master 1 at Paris 7.

It explores the compilation of typed tactic languages in Coq, with the intent of providing a compiler for the Mtac2 proof tactic language.

## Building

This the plugin contained within the `plugin/` subdirectory is built using `dune`. However, at the time of writing the latest release of `dune` does not yet support building Coq projects. To build a Coq project, you need a patched version of `dune`:

```
opam pin add dune https://github.com/ejgallego/dune.git#coq
```

Once this version of `dune` is installed a `dune build` or `dune watch` should suffice to build the project.

# Project

This project defines a typed tactic language called Mtaclite, which contains the essential features of Mtac/Mtac2. Just like Mtac, this language is defined in Coq which means that tactics written in Mtaclite are themselves Gallina terms, albeit equipped with monadic effects. In Mtac, these terms are interpreted by an OCaml tree walking interpreter which provides interpretation for all effects during interpretation.

In Mtac2, this interpreter is written as a stack machine, providing faster execution. This stack machine adds a lot of complexity to the code, making it indirect and hard to follow. On top of that, a lot of work in tactics does not come (directly) from the effects, but occurs when we need to reduce the gallina terms inside the tactics to expose the next effects we need to perform. Mtac2 is still limited to using the Coq api to perform those reductions, but Coq provides another mechanism to perform reduction terms: compilation of OCaml.

For several years, Coq has provided a native compilation mechanism for gallina terms, compiling them down to a representation in OCaml which then allows us to use the much faster code produced by the OCaml compiler to execute our terms, after which we can 'readback' the resulting term to reconstruct the result as a Coq term. Mtaclite uses this mechanism to provided much faster execution for tactics without the complications of a stack machine or a custom compilation mechanism. Here's how it works:

Given a tactic term `T` with type `Mtac A`, we ask Coq to natively compile the term. Coq will very helpfully compile it for us to an equivalent OCaml term `U`, along with any functions or datatypes used within the term. We can now ask OCaml to evaluate the compilation of `U`, producing a normal form `U'`, which must have an `Mtac` constructor in head position. We can now use an interpreter to provide effects for the compiled, ocaml representation, and each time we need to evaluate a subterm, we're evaluating native ocaml functions and applications, a huge speed-boost over Coq's reductions.

