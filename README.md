# Barocq

Barocq is a minimal, first-order, purely functional programming language with built-in enums, records and arrays.

# Overview

The purpose of Barocq is to integrate C-like features into a functionnal language to easily write system code (e.g. microkernel). Barocq is compiled to Csyntax, the source language of the [CompCert](https://github.com/AbsInt/CompCert) C compiler. Csyntax programs can be pretty-printed as compilable C files.
A Barocq program can also be translated to a shallow and deep embedding in Coq/Rocq.

# Dependencies

The Barocq compiler depends on OCaml, Rocq and a customized version of the CompCert compiler.
First, install the OCaml Package Manager (OPAM).
It is recommended to create a new opam switch for building Barocq.
Once the switch is initialized, add the Rocq package repository:

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
```

Then, install the following dependencies with `opam install`:

```text
ocaml               (version 4.14.2)
menhir              (version 20250912)
coq                 (version 8.20.1)
coq-record-update   (version 0.3.6)
coq-vst-zlist       (version 2.13)
```

Finally, install the modified version of CompCert:

```bash
opam pin -y -b add https://gitlab.inria.fr/cchavano/compcert-ce.git
```

The `-b` option tells opam to keep the build directory of CompCert, which is necessary to build the Barocq compiler.

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