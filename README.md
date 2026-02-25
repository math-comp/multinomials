<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# A Multivariate polynomial Library for the Mathematical Components Library

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/multinomials/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/multinomials/actions/workflows/docker-action.yml




This library provides a library for monomial algebra, for multivariate
polynomials over ring structures and an extended theory for polynomials whose
coefficients range over commutative rings and integral domains.

## Meta

- Author(s):
  - Pierre-Yves Strub (initial)
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Rocq/Coq versions: 8.20 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) ssreflect 2.4 or later
  - [MathComp](https://math-comp.github.io) algebra
  - [MathComp bigenough](https://github.com/math-comp/bigenough)
  - [MathComp finmap](https://github.com/math-comp/finmap)
- Rocq/Coq namespace: `mathcomp.multinomials`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of A Multivariate polynomial Library for the Mathematical Components Library
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-mathcomp-multinomials
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/math-comp/multinomials.git
cd multinomials
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



## Credits

Contributors:

- [Florent Hivert](https://www.lri.fr/~hivert/)
- [Laurent Thery](https://www-sop.inria.fr/marelle/personnel/Laurent.Thery/moi.html)

This library is also the result of discussions with:

- Sophie Bernard
- [Cyril Cohen](http://www.cyrilcohen.fr/)
- [Laurence Rideau](http://www-sop.inria.fr/members/Laurence.Rideau/)
