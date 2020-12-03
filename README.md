# Multivariate polynomials

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/math-comp/multinomials/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/math-comp/multinomials/actions?query=workflow%3ACI




This library provides a library for monomial algebra,for
multivariate polynomials over ring structures and an extended theory
for polynomials whose coefficients range over commutative rings and
integral domains.

## Meta

- Author(s):
  - Pierre-Yves Strub (initial)
- License: [CeCILL-B](LICENSE)
- Compatible Coq versions: Coq 8.10 to 8.12
- Additional dependencies:
  - [MathComp ssreflect 1.11](https://math-comp.github.io)
  - [MathComp algebra 1.11](https://math-comp.github.io)
  - [MathComp field 1.11](https://math-comp.github.io)
  - [MathComp field 1.11](https://math-comp.github.io)
  - [MathComp bigenough 1.0.0 or later](https://github.com/math-comp/bigenough)
- Coq namespace: `SsrMultinomials`
- Related publication(s):
  - [Formal proofs of transcendence for e and pi as an application of multivariate and symmetric polynomials.](http://www.strub.nu/biblio/pdf/conf-cpp-BernardBRS16.pdf) doi:[10.1145/2854065.2854072](https://doi.org/10.1145/2854065.2854072)

## Building and installation instructions

The easiest way to install the latest released version of Multivariate polynomials
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-multinomials
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/multinomials.git
cd multinomials
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Acknowledgments
### Contributors
- [Florent Hivert](https://www.lri.fr/~hivert/)
- [Laurent
Thery](https://www-sop.inria.fr/marelle/personnel/Laurent.Thery/moi.html)

### This library is also the result of discussions with
- Sophie Bernard
- [Cyril Cohen](http://www.cyrilcohen.fr/)
- [Laurence Rideau](http://www-sop.inria.fr/members/Laurence.Rideau/)
