# MtacLite

This repository contains the work I've done for my TRE during my Master 1 at Paris 7.

It explores the compilation of typed tactic languages in Coq, with the intent of providing a compiler for the Mtac2 proof tactic language.

## Building

This the plugin contained within the `plugin/` subdirectory is built using `dune`. However, at the time of writing the latest release of `dune` does not yet support building Coq projects. To build a Coq project, you need a patched version of `dune`:

```
opam pin add dune https://github.com/ejgallego/dune.git#coq
```

Once this version of `dune` is installed a `dune build` or `dune watch` should suffice to build the project.
