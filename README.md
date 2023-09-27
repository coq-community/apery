<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Apery

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/apery/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/apery/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



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
- Coq-community maintainer(s):
  - Assia Mahboubi ([**@amahboubi**](https://github.com/amahboubi))
  - Kazuhiko Sakaguchi ([**@pi8027**](https://github.com/pi8027))
- License: [CeCILL-C](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [MathComp ssreflect 2.0 or later](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp field](https://math-comp.github.io)
  - [CoqEAL 2.0.0 or later](https://github.com/coq-community/coqeal)
  - [MathComp real closed fields 2.0.0 or later](https://github.com/math-comp/real-closed)
  - [MathComp bigenough 1.0.1 or later](https://github.com/math-comp/bigenough)
  - [Mczify](https://github.com/math-comp/mczify) 1.5.0 or later
  - [Algebra Tactics](https://github.com/math-comp/algebra-tactics) 1.2.0 or later
- Coq namespace: `mathcomp.apery`
- Related publication(s):
  - [A Formal Proof of the Irrationality of ζ(3)](https://arxiv.org/abs/1912.06611) 
  - [A Computer-Algebra-Based Formal Proof of the Irrationality of ζ(3)](https://hal.inria.fr/hal-00984057) doi:[10.1007/978-3-319-08970-6_11](https://doi.org/10.1007/978-3-319-08970-6_11)
  - [Reflexive Tactics for Algebra, Revisited](https://drops.dagstuhl.de/opus/volltexte/2022/16738/pdf/LIPIcs-ITP-2022-29.pdf) doi:[10.4230/LIPIcs.ITP.2022.29](https://doi.org/10.4230/LIPIcs.ITP.2022.29)

## Building and installation instructions

The easiest way to install the latest released version of Apery
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-apery
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/apery.git
cd apery
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



