# Barocq

Barocq is a restricted functional programming language with built-in records and arrays.

# Overview

The purpose of Barocq is to integrate C-like features into a functionnal language to easily write system code (e.g. microkernel). Barocq is compiled to Clight, an intermediate language of the [CompCert](https://github.com/AbsInt/CompCert) C compiler. Clight programs can be pretty-printed as compilable C files.
A Barocq program can also be translated to a shallow and deep embedding in Coq/Rocq. Proofs of correspondence between the two embeddings are automatically generated.

# Dependencies

The Barocq compiler depends on OCaml, Coq/Rocq and the CompCert compiler.
First, install the OCaml Package Manager (OPAM).
Once `opam` is configured, add the Coq package repository:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
```

Finally, install the following dependencies with `opam install`:

```text
ocaml           (version 4.14.2)
menhir          (version 20240715)
coq             (version 8.20.0)
coq-compcert    (version 3.15, using the "-b" option)
```

# Building the project

The commands are the following:

```bash
make
make install
```
`make install` installs the binary executable `barocq` under the `bin/` folder of the current opam switch.

# Usage

Barocq file extension is `.br`. To compile a Barocq file to C, use:

```bash
barocq path/to/file.br
```

Without any additionnal option, a C file will be created at `path/to/a.c`.

To generate the shallow and deep embeddings, as well as the correspondence proofs, use:

```bash
barocq -gen-corres path/to/file.br
```

Other compiler flags and options are described with `barocq -help`.

# Editor support

There is a syntax-highlighting support for VSCode. Open the VSCode command palette, look for the command `Developer: Install Extension from Location...` and choose the directory `misc/vsbarocq`.