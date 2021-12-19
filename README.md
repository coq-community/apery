<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Apery

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/apery/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/apery/actions?query=workflow:"Docker%20CI"




This project contains a formal proof that the real number ζ(3),
also known as Apéry's constant, is irrational. It follows roughly
Apéry's original sketch of a proof. However, the recurrence
relations constituting the crux of the proof have been guessed by a
computer algebra program (in this case in Maple/Algolib). These
relations are formally checked a posteriori, so that Coq's kernel
remains the sole trusted code base.

## Meta

- Author(s):
  - Frédéric Chyzak (initial)
  - Assia Mahboubi (initial)
  - Thomas Sibut-Pinote (initial)
- License: [CeCILL-C](Licence_CeCILL-C_V1-en.txt)
- Compatible Coq versions: 8.11 or later
- Additional dependencies:
  - [MathComp ssreflect 1.12 or later](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp field](https://math-comp.github.io)
  - [CoqEAL 1.0.5 or later](https://github.com/coq-community/coqeal)
  - [MathComp real closed fields 1.1.2 or later](https://github.com/math-comp/real-closed)
  - [MathComp bigenough 1.0.0 or later](https://github.com/math-comp/bigenough)
- Coq namespace: `mathcomp.apery`
- Related publication(s):
  - [A Formal Proof of the Irrationality of ζ(3)](https://arxiv.org/abs/1912.06611) 
  - [A Computer-Algebra-Based Formal Proof of the Irrationality of ζ(3)](https://hal.inria.fr/hal-00984057) doi:[10.1007/978-3-319-08970-6_11](https://doi.org/10.1007/978-3-319-08970-6_11)

## Building and installation instructions

The easiest way to install the latest released version of Apery
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-apery
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/apery.git
cd apery
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



