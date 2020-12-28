A Multivariate polynomial Library for the Mathematical Components Library
========================================================================

This library provides a library for monomial algebra,for multivariate
polynomials over ring structures and an extended theory for
polynomials whose coefficients range over commutative rings and
integral domains.

Building and installation instructions
------------------------------------------------------------------------

The easiest way to install the latest released version this library is
via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-multinomials
```

If you want to install it manually, do:

``` shell
git clone https://github.com/math-comp/multinomials.git
cd multinomials
make   # or make -j <number-of-cores-on-your-machine> 
make install
```

Authors
========================================================================

  "Pierre-Yves Strub" \<pierre-yves@strub.nu\>

Contributors:

  - [Florent Hivert](https://www.lri.fr/~hivert/)
  - [Laurent Thery](https://www-sop.inria.fr/marelle/personnel/Laurent.Thery/moi.html)

This library is also the result of discussions with:

  - Sophie Bernard
  - [Cyril Cohen](http://www.cyrilcohen.fr/)
  - [Laurence Rideau](http://www-sop.inria.fr/members/Laurence.Rideau/)
