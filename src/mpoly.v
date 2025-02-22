(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* This file provides a library for multivariate polynomials over ring        *)
(* structures; it also provides an extended theory for polynomials            *)
(* whose coefficients range over commutative rings and integral domains.      *)
(*                                                                            *)
(*          'X_{1..n} == the type of monomials in n variables. m : 'X_{1..n}  *)
(*                       acts as a function from 'I_n to nat, returning the   *)
(*                       power of the i-th variable in m. Notations related   *)
(*                       to 'X_{1..n} lies in the multi_scope scope,          *)
(*                       delimited by %MM                                     *)
(* [multinom E i | i < n]                                                     *)
(*                    == the monomial in n variables whose i-th power is E(i) *)
(*             mdeg m == the degree of the monomial m; i.e.                   *)
(*                         mdeg m = \sum_(i < n) (m i)                        *)
(*      'X_{1..n < k} == the finite type of monomials in n variables with     *)
(*                       degree bounded by k.                                 *)
(*      (m1 <= m2)%MM == the point-wise partial order over monomials, i.e.    *)
(*                         (m1 <= m2)%MM <=> forall i, m1 i <= m2 i           *)
(*       (m1 <= m2)%O == the total cpo (equipped with a cpoType) over         *)
(*                       monomials. This is the degrevlex monomial ordering.  *)
(* 0, 'U_i, m1 + m2,  == 'X_{1..n} is equipped with a semi-group structure,   *)
(* m1 - m2, m *+ n, ...  all operations being point-wise. The substraction    *)
(*                       is truncated when (m1 <= m2)%MM does not hold.       *)
(*      mlcm m1 m2    == the monomial that is the least common multiple       *)
(*       {mpoly R[n]} == the type of multivariate polynomials in n variables  *)
(*                       and with coefficients of type R represented as       *)
(*                       {free 'X_{1..n} / R}, i.e. as a formal sum over      *)
(*                       'X_{1..n} and with coefficients in R.                *)
(*          [mpoly D] == the multivariate polynomial constructed from a free  *)
(*                       sum in {freeg 'X_{1..n} / R}                         *)
(*  0, 1, - p, p + q, == the usual ring operations: {mpoly R} has a canonical *)
(* p * q, p ^+ n, ...    ringType structure, which is commutative / integral  *)
(*                       when R is commutative / integral, respectively.      *)
(*       {ipoly R[n]} == the type obtained by iterating the univariate        *)
(*                       polynomial type, with R as base ring.                *)
(*     {ipoly R[n]}^p == copy of {ipoly R[n]} with a ring canonical structure *)
(*           mwiden p == the canonical injection (ring morphism) from         *)
(*                       {mpoly R[n]} to {mpoly R[n.+1]}                      *)
(*    mpolyC c, c%:MP == the constant multivariate polynomial c               *)
(*               'X_i == the variable i, for i : 'I_n                         *)
(*             'X_[m] == the monomial m as a multivariate polynomial          *)
(*            msupp p == the support of p, i.e. the m s.t. p@_m != 0          *)
(*               p@_m == the coefficient of 'X_[m] in p.                      *)
(*            msize p == 1 + the degree of p, or 0 if p = 0.                  *)
(*            mlead p == the leading monomial of p; this is the maximum       *)
(*                       monomial of p for the degrevlex monimial ordering.   *)
(*                       mlead p defaults to 0%MM when p is 0.                *)
(*            mlast p == the smallest non-zero monomial of p for the          *)
(*                         degrevlex monimial ordering.                       *)
(*                       mlast p defaults to 0%MM when p is 0.                *)
(*           mleadc p == the coefficient of the highest monomial in p;        *)
(*                       this is a notation for p@_(mlead p).                 *)
(* p \is a mpolyOver S <=> the coefficients of p satisfy S; S should have a   *)
(*                       key that should be (at least) an addrPred.           *)
(*             p.@[x] == the evaluation of a polynomial p at a point x, where *)
(*                       v is a n.-tuple R s.t. 'X_i evaluates to (tnth v i)  *)
(*             p^`M() == formal derivative of p w.r.t the i-th variable       *)
(*         p^`M(n, i) == formal n-derivative of p w.r.t the i-th variable     *)
(*            p^`M[m] == formal parallel (m i)-derivative of p w.r.t the      *)
(*                       i-th variable, i ranging in {0..n.-1}.               *)
(*          p \mPo lq == multivariate polynomial composition, where lq is a   *)
(*                       (n.-tuple {mpoly R[k]}) s.t. 'X_i is substituted by  *)
(*                       (tnth lq i).                                         *)
(*      map_mpoly f p == the image of the polynomial by the function f (which *)
(*                       is usually a ring morphism).                         *)
(*    p \is symmetric == p is a symmetric polynomial.                         *)
(*          's_(n, k) == the k-th elementary symmetric polynomial with        *)
(*                       n indeterminates. We prove the fundamental lemma of  *)
(*                       symmetric polynomials.                               *)
(*     p \is d.-homog == p is a homogeneous polynomial of degree d.           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From Corelib Require Import Setoid.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finfun bigop finset binomial.
From mathcomp Require Import order fingroup perm ssralg zmodp poly ssrint.
From mathcomp Require Import matrix vector.
From mathcomp Require Import bigenough.

Require Import ssrcomplements freeg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory BigEnough.

Local Open Scope ring_scope.

Declare Scope mpoly_scope.
Declare Scope multi_scope.

Delimit Scope mpoly_scope with MP.
Delimit Scope multi_scope with MM.

Local Notation simpm := Monoid.simpm.

Local Infix "@@" := (allpairs pair) (at level 60, right associativity).

Local Notation widen := (widen_ord (leqnSn _)).

Import Order.DefaultProdLexiOrder.
Import Order.DefaultSeqLexiOrder.
Import Order.DefaultTupleLexiOrder.

(* -------------------------------------------------------------------- *)
Reserved Notation "''X_{1..' n '}'"
  (at level 0, n at level 2).
Reserved Notation "''X_{1..' n  < b '}'"
  (at level 0, n, b at level 2).
Reserved Notation "''X_{1..' n  < b1 , b2 '}'"
  (at level 0, n, b1, b2 at level 2).
Reserved Notation "[ 'multinom' s ]"
  (at level 0, format "[ 'multinom'  s ]").
Reserved Notation "[ 'multinom' 'of' s ]"
  (at level 0, format "[ 'multinom'  'of'  s ]").
Reserved Notation "[ 'multinom' F | i < n ]"
  (at level 0, i at level 0,
     format "[ '[hv' 'multinom'  F '/'  |  i  <  n ] ']'").
Reserved Notation "'U_(' n )"
  (at level 0, n at level 2, no associativity, format "'U_(' n )").
Reserved Notation "{ 'mpoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'mpoly'  T [ n ] }").
Reserved Notation "[ 'mpoly' D ]"
  (at level 0, D at level 2, format "[ 'mpoly'  D ]").
Reserved Notation "{ 'ipoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'ipoly'  T [ n ] }").
Reserved Notation "{ 'ipoly' T [ n ] }^p"
  (at level 0, T, n at level 2, format "{ 'ipoly'  T [ n ] }^p").
Reserved Notation "''X_' i"
  (at level 8, i at level 2, format "''X_' i").
Reserved Notation "''X_[' i ]"
  (at level 8, i at level 2, format "''X_[' i ]").
Reserved Notation "''X_[' R , i ]"
  (at level 8, R, i at level 2, format "''X_[' R ,  i ]").
Reserved Notation "c %:MP"
  (at level 2, left associativity, format "c %:MP").
Reserved Notation "c %:MP_[ n ]"
  (at level 2, left associativity, n at level 50, format "c %:MP_[ n ]").
Reserved Notation "c %:IP"
  (at level 2, left associativity, format "c %:IP").
Reserved Notation "s @_ i"
   (at level 3, i at level 2, left associativity, format "s @_ i").
Reserved Notation "e .@[ x ]"
  (at level 2, left associativity, format "e .@[ x ]").
Reserved Notation "e .@[< x >]"
  (at level 2, left associativity, format "e .@[< x >]").
Reserved Notation "p \mPo q"
  (at level 50).
Reserved Notation "x ^[ f ]"
   (at level 2, left associativity, format "x ^[ f ]").
Reserved Notation "x ^[ f , g ]"
   (at level 2, left associativity, format "x ^[ f , g ]").
Reserved Notation "p ^`M ( m )"
   (at level 8, format "p ^`M ( m )").
Reserved Notation "p ^`M ( m , n )"
   (at level 8, format "p ^`M ( m ,  n )").
Reserved Notation "p ^`M [ m ]"
   (at level 8, format "p ^`M [ m ]").
Reserved Notation "''s_' k"
  (at level 8, k at level 2, format "''s_' k").
Reserved Notation "''s_' ( n , k )"
  (at level 8, n, k at level 2, format "''s_' ( n ,  k )").
Reserved Notation "''s_' ( K , n , k )"
  (at level 8, n, k, K at level 2, format "''s_' ( K ,  n ,  k )").
Reserved Notation "+%MM"
  (at level 0).
Reserved Notation "-%MM"
  (at level 0).

(* -------------------------------------------------------------------- *)
Section MultinomDef.
Context (n : nat).

Record multinom : predArgType := Multinom { multinom_val :> n.-tuple nat }.

HB.instance Definition _ := [isNew for multinom_val].

Definition fun_of_multinom M (i : 'I_n) := tnth (multinom_val M) i.

Coercion fun_of_multinom : multinom >-> Funclass.

Lemma multinomE M : Multinom M =1 tnth M.
Proof. by []. Qed.

End MultinomDef.

Notation "[ 'multinom' s ]" := (@Multinom _ s) : form_scope.
Notation "[ 'multinom' 'of'  s ]" := [multinom [tuple of s]] : form_scope.
Notation "[ 'multinom' E | i < n ]" :=
  [multinom [tuple E%N | i < n]] : form_scope.
Notation "[ 'multinom' E | i < n ]" :=
  [multinom [tuple E%N : nat | i < n]] (only parsing) : form_scope.

(* -------------------------------------------------------------------- *)
Notation "''X_{1..' n '}'" := (multinom n) : type_scope.

HB.instance Definition _ n := [Countable of 'X_{1..n} by <:].

Bind Scope multi_scope with multinom.

(* -------------------------------------------------------------------- *)
Definition lem n (m1 m2 : 'X_{1..n}) :=
  [forall i, m1%MM i <= m2%MM i].

Definition ltm n (m1 m2 : 'X_{1..n}) :=
  (m1 != m2) && (lem m1 m2).

(* -------------------------------------------------------------------- *)
Section MultinomTheory.
Context {n : nat}.
Implicit Types (m : 'X_{1..n}).

Lemma mnm_tnth m j : m j = tnth m j.
Proof. by []. Qed.

Lemma mnm_nth x0 m j : m j = nth x0 m j.
Proof. by rewrite mnm_tnth (tnth_nth x0). Qed.

Lemma mnmE E j : [multinom E i | i < n] j = E j.
Proof. by rewrite multinomE tnth_mktuple. Qed.

Lemma mnm_valK t : [multinom t] = t :> n.-tuple nat.
Proof. by []. Qed.

Lemma mnmP m1 m2 : (m1 = m2) <-> (m1 =1 m2).
Proof.
case: m1 m2 => [m1] [m2] /=; split => [->//|h].
by apply/val_inj/eq_from_tnth => i; rewrite -!multinomE.
Qed.

End MultinomTheory.

(* -------------------------------------------------------------------- *)
Section MultinomMonoid.
Context {n : nat}.
Implicit Types (m : 'X_{1..n}).

Definition mnm0 := [multinom 0 | _ < n].
Definition mnm1 (c : 'I_n) := [multinom c == i | i < n].
Definition mnm_add m1 m2 := [multinom m1 i + m2 i | i < n].
Definition mnm_sub m1 m2 := [multinom m1 i - m2 i | i < n].
Definition mnm_muln m i := nosimpl iterop _ i mnm_add m mnm0.

Local Notation "0"         := mnm0 : multi_scope.
Local Notation "'U_(' n )" := (mnm1 n) : multi_scope.
Local Notation "m1 + m2"   := (mnm_add m1 m2) : multi_scope.
Local Notation "m1 - m2"   := (mnm_sub m1 m2) : multi_scope.
Local Notation "x *+ n"    := (mnm_muln x n) : multi_scope.

Local Notation "+%MM" := (@mnm_add) : function_scope.
Local Notation "-%MM" := (@mnm_sub) : function_scope.

Local Notation "m1 <= m2" := (lem m1 m2) : multi_scope.
Local Notation "m1 < m2"  := (ltm m1 m2) : multi_scope.

Lemma mnm0E i : 0%MM i = 0%N. Proof. exact/mnmE. Qed.

Lemma mnmDE i m1 m2 : (m1 + m2)%MM i = (m1 i + m2 i)%N. Proof. exact/mnmE. Qed.

Lemma mnmBE i m1 m2 : (m1 - m2)%MM i = (m1 i - m2 i)%N. Proof. exact/mnmE. Qed.

Lemma mnm_sumE (I : Type) i (r : seq I) P F :
  (\big[+%MM/0%MM]_(x <- r | P x) (F x)) i = (\sum_(x <- r | P x) (F x i))%N.
Proof. by apply/(big_morph (fun m => m i)) => [x y|]; rewrite mnmE. Qed.

(*-------------------------------------------------------------------- *)
Lemma mnm_lepP {m1 m2} : reflect (forall i, m1 i <= m2 i) (m1 <= m2)%MM.
Proof. exact: (iffP forallP). Qed.

Lemma lepm_refl m : (m <= m)%MM. Proof. exact/mnm_lepP. Qed.

Lemma lepm_trans m3 m1 m2 : (m1 <= m2 -> m2 <= m3 -> m1 <= m3)%MM.
Proof.
move=> h1 h2; apply/mnm_lepP => i.
exact: leq_trans (mnm_lepP h1 i) (mnm_lepP h2 i).
Qed.

Lemma addmC : commutative +%MM.
Proof. by move=> m1 m2; apply/mnmP=> i; rewrite !mnmE addnC. Qed.

Lemma addmA : associative +%MM.
Proof. by move=> m1 m2 m3; apply/mnmP=> i; rewrite !mnmE addnA. Qed.

Lemma add0m : left_id 0%MM +%MM.
Proof. by move=> m; apply/mnmP=> i; rewrite !mnmE add0n. Qed.

Lemma addm0 : right_id 0%MM +%MM.
Proof. by move=> m; rewrite addmC add0m. Qed.

HB.instance Definition _ := Monoid.isComLaw.Build 'X_{1..n} 0%MM +%MM
  addmA addmC add0m.

Lemma subm0 m : (m - 0)%MM = m.
Proof. by apply/mnmP=> i; rewrite !mnmE subn0. Qed.

Lemma sub0m m : (0 - m = 0)%MM.
Proof. by apply/mnmP=> i; rewrite !mnmE sub0n. Qed.

Lemma addmK m : cancel (+%MM^~ m) (-%MM^~ m).
Proof. by move=> m' /=; apply/mnmP=> i; rewrite !mnmE addnK. Qed.

Lemma addIm : left_injective +%MM.
Proof. by move=> ? ? ? /(can_inj (@addmK _)). Qed.

Lemma addmI : right_injective +%MM.
Proof. by move=> m ? ?; rewrite ![(m + _)%MM]addmC => /addIm. Qed.

Lemma eqm_add2l m n1 n2 : (m + n1 == m + n2)%MM = (n1 == n2).
Proof. exact/inj_eq/addmI. Qed.

Lemma eqm_add2r m n1 n2 : (n1 + m == n2 + m)%MM = (n1 == n2).
Proof. exact: (inj_eq (@addIm _)). Qed.

Lemma submK m m' : (m <= m')%MM -> (m' - m + m = m')%MM.
Proof. by move/mnm_lepP=> h; apply/mnmP=> i; rewrite !mnmE subnK. Qed.

Lemma addmBA m1 m2 m3 :
  (m3 <= m2)%MM -> (m1 + (m2 - m3))%MM = (m1 + m2 - m3)%MM.
Proof. by move/mnm_lepP=> h; apply/mnmP=> i; rewrite !mnmE addnBA. Qed.

Lemma submDA m1 m2 m3 : (m1 - m2 - m3)%MM = (m1 - (m2 + m3))%MM.
Proof. by apply/mnmP=> i; rewrite !mnmE subnDA. Qed.

Lemma submBA m1 m2 m3 : (m3 <= m2)%MM -> (m1 - (m2 - m3) = m1 + m3 - m2)%MM.
Proof. by move/mnm_lepP=> h; apply/mnmP=> i; rewrite !mnmE subnBA. Qed.

Lemma lem_subr m1 m2 : (m1 - m2 <= m1)%MM.
Proof. by apply/mnm_lepP=> i; rewrite !mnmE leq_subr. Qed.

Lemma lem_addr m1 m2 : (m1 <= m1 + m2)%MM.
Proof. by apply/mnm_lepP=> i; rewrite mnmDE leq_addr. Qed.

Lemma lem_addl m1 m2 : (m2 <= m1 + m2)%MM.
Proof. by apply/mnm_lepP=> i; rewrite mnmDE leq_addl. Qed.

(* -------------------------------------------------------------------- *)
Lemma mulm0n m : (m *+ 0 = 0)%MM.
Proof. by []. Qed.

Lemma mulm1n m : (m *+ 1 = m)%MM.
Proof. by []. Qed.

Lemma mulmS m i : (m *+ i.+1 = m + m *+ i)%MM.
Proof. by rewrite /mnm_muln !Monoid.iteropE iterS. Qed.

Lemma mulmSr m i : (m *+ i.+1 = m *+ i + m)%MM.
Proof. by rewrite mulmS addmC. Qed.

Lemma mulmnE m k i : ((m *+ k) i)%MM = (m i * k)%N.
Proof.
elim: k => [|k ih]; first by rewrite muln0 mulm0n !mnmE.
by rewrite mulmS mulnS mnmDE ih.
Qed.

Lemma mnm1E i j : U_(i)%MM j = (i == j). Proof. exact/mnmE. Qed.

Lemma lep1mP i m : (U_(i) <= m)%MM = (m i != 0%N).
Proof.
apply/mnm_lepP/idP=> [/(_ i)|]; rewrite -lt0n; first by rewrite mnm1E eqxx.
by move=> lt0_mi j; rewrite mnm1E; case: eqP=> // <-.
Qed.

End MultinomMonoid.

(* -------------------------------------------------------------------- *)
Notation "+%MM" := (@mnm_add _).
Notation "-%MM" := (@mnm_sub _).

Notation "0"         := (@mnm0 _) : multi_scope.
Notation "'U_(' n )" := (mnm1 n) : multi_scope.
Notation "m1 + m2"   := (mnm_add m1 m2) : multi_scope.
Notation "m1 - m2"   := (mnm_sub m1 m2) : multi_scope.
Notation "x *+ n"    := (mnm_muln x n) : multi_scope.

Notation "m1 <= m2" := (lem m1 m2) : multi_scope.
Notation "m1 < m2"  := (ltm m1 m2) : multi_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%MM/0%MM]_(i <- r | P%B) F%MM) : multi_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%MM/0%MM]_(i <- r) F%MM) : multi_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%MM/0%MM]_(m <= i < n | P%B) F%MM) : multi_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%MM/0%MM]_(m <= i < n) F%MM) : multi_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%MM/0%MM]_(i | P%B) F%MM) : multi_scope.
Notation "\sum_ i F" :=
  (\big[+%MM/0%MM]_i F%MM) : multi_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%MM/0%MM]_(i : t | P%B) F%MM) (only parsing) : multi_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%MM/0%MM]_(i : t) F%MM) (only parsing) : multi_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%MM/0%MM]_(i < n | P%B) F%MM) : multi_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%MM/0%MM]_(i < n) F%MM) : multi_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%MM/0%MM]_(i in A | P%B) F%MM) : multi_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%MM/0%MM]_(i in A) F%MM) : multi_scope.

(* -------------------------------------------------------------------- *)
Lemma multinomUE_id n (m : 'X_{1..n}) : m = (\sum_i U_(i) *+ m i)%MM.
Proof.
apply/mnmP=> i; rewrite mnm_sumE (bigD1 i) //=.
rewrite big1; first by rewrite addn0 mulmnE mnm1E eqxx mul1n.
by move=> j ne_ji; rewrite mulmnE mnm1E (negbTE ne_ji).
Qed.

Lemma multinomUE n (s : 'S_n) (m : 'X_{1..n}) :
  m = (\sum_i U_(s i) *+ m (s i))%MM.
Proof.
rewrite (reindex s^-1)%g //=; last first.
  by exists s=> i _; rewrite (permK, permKV).
by rewrite [LHS]multinomUE_id; apply/eq_bigr => i _; rewrite permKV.
Qed.

(* -------------------------------------------------------------------- *)
Section MultinomDeg.
Context {n : nat}.
Implicit Types (m : 'X_{1..n}).

Definition mdeg m := (\sum_(i <- m) i)%N.

Lemma mdegE m : mdeg m = (\sum_i (m i))%N.
Proof. exact: big_tuple. Qed.

Lemma mdeg0 : mdeg 0%MM = 0%N.
Proof. by rewrite mdegE big1 // => i; rewrite mnmE. Qed.

Lemma mdeg1 i : mdeg U_(i) = 1%N.
Proof.
rewrite mdegE (bigD1 i) //= big1 => [|j]; first by rewrite mnmE eqxx addn0.
by rewrite mnmE eq_sym => /negbTE ->.
Qed.

Lemma mdegD m1 m2 : mdeg (m1 + m2) = (mdeg m1 + mdeg m2)%N.
Proof. by rewrite !mdegE -big_split; apply/eq_bigr => i _; rewrite mnmE. Qed.

Lemma mdegB m1 m2 : mdeg (m1 - m2) <= mdeg m1.
Proof. by rewrite !mdegE; apply/leq_sum => i _; rewrite mnmE leq_subr.  Qed.

Lemma mdegMn m k : mdeg (m *+ k) = (mdeg m * k)%N.
Proof. by rewrite !mdegE big_distrl; apply/eq_bigr => i _; rewrite mulmnE. Qed.

Lemma mdeg_sum (I : Type) (r : seq I) P F :
  mdeg (\sum_(x <- r | P x) F x) = (\sum_(x <- r | P x) mdeg (F x))%N.
Proof. exact/big_morph/mdeg0/mdegD. Qed.

Lemma mdeg_eq0 m : (mdeg m == 0%N) = (m == 0%MM).
Proof.
apply/idP/eqP=> [h|->]; last by rewrite mdeg0.
apply/mnmP=> i; move: h; rewrite mdegE mnm0E.
by rewrite (bigD1 i) //= addn_eq0 => /andP[/eqP-> _].
Qed.

Lemma mnmD_eq0 m1 m2 : (m1 + m2 == 0)%MM = (m1 == 0%MM) && (m2 == 0%MM).
Proof. by rewrite -!mdeg_eq0 mdegD addn_eq0. Qed.

Lemma mnm1_eq0 i : (U_(i) == 0 :> 'X_{1..n})%MM = false.
Proof. by rewrite -mdeg_eq0 mdeg1. Qed.

Lemma eq_mnm1 (i j : 'I_n) : (U_(i)%MM == U_(j)%MM) = (i == j).
Proof.
by apply/eqP/eqP => [/mnmP /(_ j)|->//]; rewrite !mnm1E eqxx; case: eqP.
Qed.

Lemma mdeg_eq1 m : (mdeg m == 1%N) = [exists i : 'I_n, m == U_(i)%MM].
Proof.
apply/eqP/idP=> [|/existsP[i /eqP ->]]; last by rewrite mdeg1.
rewrite [m]multinomUE_id => Hmdeg.
have: [exists i, m i != 0%N].
  rewrite -negb_forall; apply/contra_eqN: Hmdeg => /forallP Hm0.
  by rewrite big1 ?mdeg0 //= => i _; rewrite (eqP (Hm0 i)).
case/existsP => i Hi; apply/existsP; exists i; move: Hmdeg.
rewrite (bigD1 i) //= mdegD mdegMn mdeg1 mul1n.
case: (m i) Hi => [|[|]] //= _ [] /eqP; rewrite mdeg_eq0 => /eqP ->.
by rewrite mulm1n addm0.
Qed.

Lemma mdeg1P m : reflect (exists i, m == U_(i)%MM) (mdeg m == 1%N).
Proof. by rewrite mdeg_eq1; apply/existsP. Qed.

End MultinomDeg.

(* -------------------------------------------------------------------- *)
Section MultinomOrder.
Context {n : nat}.
Implicit Types (m : 'X_{1..n}).

Definition mnmc_le m1 m2 := (mdeg m1 :: m1 <= mdeg m2 :: m2)%O.

Definition mnmc_lt m1 m2 := (mdeg m1 :: m1 < mdeg m2 :: m2)%O.

Local Lemma lemc_refl : reflexive mnmc_le.
Proof. by move=> m; apply/le_refl. Qed.

Local Lemma lemc_anti : antisymmetric mnmc_le.
Proof. by move=> m1 m2 /le_anti [_] /val_inj/val_inj. Qed.

Local Lemma lemc_trans : transitive mnmc_le.
Proof. by move=> m2 m1 m3; apply/le_trans. Qed.

Lemma lemc_total : total mnmc_le.
Proof. by move=> m1 m2; apply/le_total. Qed.

Local Lemma ltmc_def m1 m2 : mnmc_lt m1 m2 = (m2 != m1) && mnmc_le m1 m2.
Proof.
apply/esym; rewrite andbC /mnmc_lt /mnmc_le lt_def lexi_cons eqseq_cons.
by case: ltgtP; rewrite //= 1?andbC //; apply/contra_ltN => /eqP ->.
Qed.

HB.instance Definition _ := Order.isPOrder.Build Order.default_display 'X_{1..n}
  ltmc_def lemc_refl lemc_anti lemc_trans.

Lemma leEmnm m1 m2 : (m1 <= m2)%O = (mdeg m1 :: val m1 <= mdeg m2 :: val m2)%O.
Proof. by []. Qed.

Lemma ltEmnm m m' : (m < m')%O = (mdeg m :: m < mdeg m' :: m')%O.
Proof. by []. Qed.

HB.instance Definition _ :=
  Order.POrder_isTotal.Build Order.default_display 'X_{1..n} lemc_total.

Lemma le0m m : (0%MM <= m)%O.
Proof.
rewrite leEmnm; have [/eqP|] := eqVneq (mdeg m) 0%N.
  by rewrite mdeg_eq0 => /eqP->; rewrite lexx.
by rewrite -lt0n mdeg0 lexi_cons leEnat; case: ltngtP.
Qed.

HB.instance Definition _ :=
  Order.hasBottom.Build Order.default_display 'X_{1..n} le0m.

Lemma ltmcP m1 m2 : mdeg m1 = mdeg m2 -> reflect
  (exists2 i : 'I_n, forall (j : 'I_n), j < i -> m1 j = m2 j & m1 i < m2 i)
  (m1 < m2)%O.
Proof.
by move=> eq_mdeg; rewrite ltEmnm eq_mdeg eqhead_ltxiE; apply: ltxi_tuplePlt.
Qed.

Lemma lemc_mdeg m1 m2 : (m1 <= m2)%O -> mdeg m1 <= mdeg m2.
Proof. by rewrite leEmnm lexi_cons leEnat; case: ltngtP. Qed.

Lemma lt_mdeg_ltmc m1 m2 : mdeg m1 < mdeg m2 -> (m1 < m2)%O.
Proof. by rewrite ltEmnm ltxi_cons leEnat; case: ltngtP. Qed.

Lemma mdeg_max m1 m2 : mdeg (m1 `|` m2)%O = maxn (mdeg m1) (mdeg m2).
Proof.
have [/lemc_mdeg|Hgt] := leP; first by case: ltngtP.
by apply/esym/maxn_idPl; apply/contra_lt_leq: Hgt => /lt_mdeg_ltmc /ltW.
Qed.

(* FIXME: introduce \max_ to replace \join_ ? This would require bOrderType. *)
Lemma mdeg_bigmax (r : seq 'X_{1..n}) :
  mdeg (\join_(m <- r) m)%O = \max_(m <- r) mdeg m.
Proof.
elim: r => [|m r ih]; first by rewrite !big_nil mdeg0.
by rewrite !big_cons mdeg_max ih.
Qed.

Lemma ltmc_add2r m m1 m2 : ((m + m1)%MM < (m + m2)%MM)%O = (m1 < m2)%O.
Proof.
case: (ltngtP (mdeg m1) (mdeg m2)) => [lt|lt|].
+ by rewrite !lt_mdeg_ltmc // !mdegD ltn_add2l.
+ rewrite !ltNge !le_eqVlt !lt_mdeg_ltmc ?orbT //.
  by rewrite !mdegD ltn_add2l.
move=> eq; have eqD: mdeg (m + m1) = mdeg (m + m2).
  by rewrite !mdegD (rwP eqP) eqn_add2l eq.
apply/ltmcP/ltmcP => // {eq eqD} -[i eq lt]; exists i.
+ by move=> j /eq /eqP; rewrite !mnmDE (rwP eqP) eqn_add2l.
+ by move: lt; rewrite !mnmDE ltn_add2l.
+ by move=> j /eq /eqP; rewrite !mnmDE (rwP eqP) eqn_add2l.
+ by rewrite !mnmDE ltn_add2l.
Qed.

Lemma ltmc_add2l m1 m2 m : ((m1 + m)%MM < (m2 + m)%MM)%O = (m1 < m2)%O.
Proof. by rewrite ![(_+m)%MM]addmC ltmc_add2r. Qed.

Lemma lemc_add2r m m1 m2 : ((m + m1)%MM <= (m + m2)%MM)%O = (m1 <= m2)%O.
Proof. by rewrite !le_eqVlt eqm_add2l ltmc_add2r. Qed.

Lemma lemc_add2l m1 m2 m : ((m1 + m)%MM <= (m2 + m)%MM)%O = (m1 <= m2)%O.
Proof. by rewrite ![(_+m)%MM]addmC lemc_add2r. Qed.

Lemma lemc_addr m1 m2 : (m1 <= (m1 + m2)%MM)%O.
Proof. by rewrite -{1}[m1]addm0 lemc_add2r le0x. Qed.

Lemma lemc_addl m1 m2 : (m2 <= (m1 + m2)%MM)%O.
Proof. by rewrite addmC lemc_addr. Qed.

Lemma lemc_lt_add m1 m2 n1 n2 :
  (m1 <= n1 -> m2 < n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
Proof.
move=> le lt; apply/(le_lt_trans (y := n1 + m2)%MM).
  by rewrite lemc_add2l. by rewrite ltmc_add2r.
Qed.

Lemma ltmc_le_add m1 m2 n1 n2 :
  (m1 < n1 -> m2 <= n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
Proof.
move=> lt le; apply/(lt_le_trans (y := n1 + m2)%MM).
  by rewrite ltmc_add2l. by rewrite lemc_add2r.
Qed.

Lemma ltm_add m1 m2 n1 n2 :
  (m1 < n1 -> m2 < n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
Proof. by move=> lt1 /ltW /(ltmc_le_add lt1). Qed.

Lemma lem_add m1 m2 n1 n2 :
  (m1 <= n1 -> m2 <= n2 -> (m1 + m2)%MM <= (n1 + n2)%MM)%O.
Proof.
move=> le1 le2; apply/(le_trans (y := m1 + n2)%MM).
  by rewrite lemc_add2r. by rewrite lemc_add2l.
Qed.

Lemma lem_leo m1 m2 : (m1 <= m2)%MM -> (m1 <= m2)%O.
Proof. by move=> ml; rewrite -(submK ml) -{1}[m1]add0m lem_add // le0x. Qed.

(* -------------------------------------------------------------------- *)
Section WF.
Context (P : 'X_{1..n} -> Type).

Lemma ltmwf :
  (forall m1, (forall m2, (m2 < m1)%O -> P m2) -> P m1) -> forall m, P m.
Proof.
pose tof m := [tuple of mdeg m :: m].
move=> ih m; move: {2}(tof _) (erefl (tof m))=> t.
elim/(@ltxwf _ nat): t m=> //=; last first.
  move=> t wih m Em; apply/ih=> m' lt_m'm.
  by apply/(wih (tof m')); rewrite // -Em.
move=> Q {}ih x; elim: x {-2}x (leqnn x).
  move=> x; rewrite leqn0=> /eqP->; apply/ih.
  by move=> y; rewrite ltEnat/= ltn0.
move=> k wih l le_l_Sk; apply/ih=> y; rewrite ltEnat => lt_yl.
by apply/wih; have := leq_trans lt_yl le_l_Sk; rewrite ltnS.
Qed.

End WF.

Lemma ltom_wf : @well_founded 'X_{1..n} <%O.
Proof. by apply: ltmwf=> m1 IH; apply: Acc_intro => m2 /IH. Qed.

End MultinomOrder.

(* -------------------------------------------------------------------- *)
Section DegBoundMultinom.
Context (n bound : nat).

Record bmultinom := BMultinom { bmnm :> 'X_{1..n}; _ : mdeg bmnm < bound }.

HB.instance Definition _ := [isSub for bmnm].
HB.instance Definition _ := [Countable of bmultinom by <:].

Lemma bmeqP (m1 m2 : bmultinom) : (m1 == m2) = (m1 == m2 :> 'X_{1..n}).
Proof. by []. Qed.

Lemma bmdeg (m : bmultinom) : mdeg m < bound.
Proof. by case: m. Qed.

Lemma bm0_proof : mdeg (0%MM : 'X_{1..n}) < bound.+1.
Proof. by rewrite mdeg0. Qed.

End DegBoundMultinom.

Definition bm0 n b := BMultinom (bm0_proof n b).
Arguments bm0 {n b}.

Notation "''X_{1..' n  <  b '}'"       := (bmultinom n b) : type_scope.
Notation "''X_{1..' n  <  b1 , b2 '}'" :=
  ('X_{1..n < b1} * 'X_{1..n < b2})%type : type_scope.

(* -------------------------------------------------------------------- *)
Section FinDegBound.
Context (n b : nat).

Definition bmnm_enum : seq 'X_{1..n < b} :=
  let project (x : n.-tuple 'I_b) := [multinom of map val x] in
  pmap insub [seq (project x) | x <- enum {: n.-tuple 'I_b }].

Lemma bmnm_enumP : Finite.axiom bmnm_enum.
Proof.
case=> m lt_dm_b /=; rewrite count_uniq_mem; last first.
  rewrite (pmap_uniq (@insubK _ _ _)) 1?map_inj_uniq ?enum_uniq //.
  by move=> t1 t2 [] /(inj_map val_inj) /val_inj ->.
apply/eqP; rewrite eqb1 mem_pmap_sub /=; apply/mapP.
case: b m lt_dm_b=> // b' [m] /= lt_dm_Sb; exists [tuple of map inord m].
  by rewrite mem_enum.
apply/mnmP=> i; rewrite !multinomE !tnth_map inordK //.
move: lt_dm_Sb; rewrite mdegE (bigD1 i) //= multinomE.
by move=> /(leq_trans _) ->//; rewrite ltnS leq_addr.
Qed.

HB.instance Definition _ := isFinite.Build 'X_{1..n < b} bmnm_enumP.

End FinDegBound.

Section Mlcm.
Context (n : nat).
Implicit Types (m : 'X_{1..n}).

Definition mlcm m1 m2 := [multinom maxn (m1 i) (m2 i) | i < n].

Lemma mlcmC : commutative mlcm.
Proof.
by move=> m1 m2; apply/mnmP=> i; rewrite /mlcm /= !mnmE maxnC.
Qed.

Lemma mlc0m : left_id 0%MM mlcm.
Proof. by move=> m; apply/mnmP=> i; rewrite /mlcm /= !mnmE max0n. Qed.

Lemma mlcm0 : right_id 0%MM mlcm.
Proof. by move=> m; rewrite mlcmC mlc0m. Qed.

Lemma mlcmE m1 m2 : mlcm m1 m2 = (m1 + (m2 - m1))%MM.
Proof. by apply/mnmP=> i; rewrite /mlcm /= !mnmE maxnE. Qed.

Lemma lem_mlcm m m1 m2 : (mlcm m1 m2 <= m)%MM = (m1 <= m)%MM && (m2 <= m)%MM.
Proof.
apply/forallP/andP => [H|[/forallP H1 /forallP H2] i]; first split.
- by apply/forallP=> i; apply: leq_trans (H i); rewrite mnmE leq_maxl.
- by apply/forallP=> i; apply: leq_trans (H i); rewrite mnmE leq_maxr.
by rewrite mnmE geq_max H1 H2.
Qed.

Lemma lem_mlcml m1 m2 : (m1 <= mlcm m1 m2)%MM.
Proof. by apply/forallP=> i; rewrite /mlcm /= !mnmE leq_maxl. Qed.

Lemma lem_mlcmr m1 m2 : (m2 <= mlcm m1 m2)%MM.
Proof. by apply/forallP=> i; rewrite /mlcm /= !mnmE leq_maxr. Qed.

End Mlcm.

(* -------------------------------------------------------------------- *)
Section MPolyDef.
Context (n : nat) (R : ringType).

Inductive mpoly := MPoly of {freeg 'X_{1..n} / R}.

Coercion mpoly_val p := let: MPoly D := p in D.

HB.instance Definition _ := [isNew for mpoly_val].
HB.instance Definition _ := [Choice of mpoly by <:].

End MPolyDef.

Bind Scope ring_scope with mpoly.

Notation "{ 'mpoly' T [ n ] }" := (mpoly n T).
Notation "[ 'mpoly' D ]" := (@MPoly _ _ D).

(* -------------------------------------------------------------------- *)
Section MPolyTheory.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}) (D : {freeg 'X_{1..n} / R}).

Lemma mpoly_valK D : [mpoly D] = D :> {freeg _ / _}.
Proof. by []. Qed.

Lemma mpoly_eqP p q : (p = q) <-> (p = q :> {freeg _ / _}).
Proof.
split=> [->//|]; case: p q => [p] [q].
by rewrite !mpoly_valK=> ->.
Qed.

Definition mpolyC (c : R) : {mpoly R[n]} := [mpoly << c *g 0%MM >>].

Local Notation "c %:MP" := (mpolyC c) : ring_scope.

Lemma mpolyC_eq (c1 c2 : R) : (c1%:MP == c2%:MP) = (c1 == c2).
Proof.
apply/eqP/eqP=> [|->//] /eqP /freeg_eqP /(_ 0%MM).
by rewrite !coeffU eqxx !mulr1.
Qed.

Definition mcoeff (m : 'X_{1..n}) p : R := coeff m p.

Lemma mcoeff_MPoly D m : mcoeff m (MPoly D) = coeff m D.
Proof. by []. Qed.

Local Notation "p @_ i" := (mcoeff i p) : ring_scope.

Lemma mcoeffC c m : c%:MP@_m = c * (m == 0%MM)%:R.
Proof. by rewrite mcoeff_MPoly coeffU eq_sym. Qed.

Lemma mpolyCK : cancel mpolyC (mcoeff 0%MM).
Proof. by move=> c; rewrite mcoeffC eqxx mulr1. Qed.

Definition msupp p : seq 'X_{1..n} := nosimpl (dom p).

Lemma msuppE p : msupp p = dom p :> seq _.
Proof. by []. Qed.

Lemma msupp_uniq p : uniq (msupp p).
Proof. by rewrite msuppE uniq_dom. Qed.

Lemma mcoeff_msupp p m : (m \in msupp p) = (p@_m != 0).
Proof. by rewrite msuppE /mcoeff mem_dom. Qed.

Lemma memN_msupp_eq0 p m : m \notin msupp p -> p@_m = 0.
Proof. by rewrite !msuppE /mcoeff => /coeff_outdom. Qed.

Lemma mcoeff_eq0 p m : (p@_m == 0) = (m \notin msupp p).
Proof. by rewrite msuppE mem_dom /mcoeff negbK. Qed.

Lemma msupp0 : msupp 0%:MP = [::].
Proof. by rewrite msuppE /= freegU0 dom0. Qed.

Lemma msupp1 : msupp 1%:MP = [:: 0%MM].
Proof. by rewrite msuppE /= domU1. Qed.

Lemma msuppC (c : R) :
  msupp c%:MP = if c == 0 then [::] else [:: 0%MM].
Proof. by have [->|nz_c] := eqVneq; [rewrite msupp0 | rewrite msuppE domU]. Qed.

Lemma mpolyP p q : (forall m, mcoeff m p = mcoeff m q) <-> (p = q).
Proof. by split=> [|->] // h; apply/mpoly_eqP/eqP/freeg_eqP/h. Qed.

Lemma freeg_mpoly p: p = [mpoly \sum_(m <- msupp p) << p@_m *g m >>].
Proof. by case: p=> p; apply/mpoly_eqP; rewrite /= -{1}[p]freeg_sumE. Qed.

End MPolyTheory.

Notation "c %:MP" := (mpolyC _ c) : ring_scope.
Notation "c %:MP_[ n ]" := (mpolyC n c) : ring_scope.

Notation "p @_ i" := (mcoeff i p) : ring_scope.

#[global] Hint Resolve msupp_uniq : core.

(* -------------------------------------------------------------------- *)
Section NVar0.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}).

Lemma nvar0_mnmE : @all_equal_to 'X_{1..0} 0%MM.
Proof. by move=> mon; apply/mnmP; case. Qed.

Lemma nvar0_mpolyC (p : {mpoly R[0]}): p = (p@_0%MM)%:MP.
Proof. by apply/mpolyP=> m; rewrite mcoeffC nvar0_mnmE eqxx mulr1. Qed.

Lemma nvar0_mpolyC_eq p : n = 0%N -> p = (p@_0%MM)%:MP.
Proof. by move=> z_p; move:p; rewrite z_p; apply/nvar0_mpolyC. Qed.

End NVar0.

(* -------------------------------------------------------------------- *)
Section MPolyZMod.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}).

Definition mpoly_opp p := [mpoly - mpoly_val p].

Definition mpoly_add p q := [mpoly mpoly_val p + mpoly_val q].

Lemma add_mpoly0 : left_id 0%:MP mpoly_add.
Proof. by move=> p; apply/mpoly_eqP; rewrite !mpoly_valK freegU0 add0r. Qed.

Lemma add_mpolyN : left_inverse 0%:MP mpoly_opp mpoly_add.
Proof. by move=> p; apply/mpoly_eqP; rewrite !mpoly_valK freegU0 addrC subrr. Qed.

Lemma add_mpolyC : commutative mpoly_add.
Proof. by move=> p q; apply/mpoly_eqP; rewrite !mpoly_valK addrC. Qed.

Lemma add_mpolyA : associative mpoly_add.
Proof. by move=> p q r; apply/mpoly_eqP; rewrite !mpoly_valK addrA. Qed.

HB.instance Definition _ := GRing.isZmodule.Build (mpoly n R)
  add_mpolyA add_mpolyC add_mpoly0 add_mpolyN.
HB.instance Definition _ := GRing.Zmodule.on {mpoly R[n]}.

Definition mpoly_scale c p := [mpoly c *: mpoly_val p].

Local Notation "c *:M p" := (mpoly_scale c p) (at level 40, left associativity).

Lemma scale_mpolyA c1 c2 p : c1 *:M (c2 *:M p) = (c1 * c2) *:M p.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerA. Qed.

Lemma scale_mpoly1m p : 1 *:M p = p.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scale1r. Qed.

Lemma scale_mpolyDr c p1 p2 : c *:M (p1 + p2) = c *:M p1 + c *:M p2.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerDr. Qed.

Lemma scale_mpolyDl p c1 c2 : (c1 + c2) *:M p = c1 *:M p + c2 *:M p.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerDl. Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R (mpoly n R)
 scale_mpolyA scale_mpoly1m scale_mpolyDr scale_mpolyDl.
HB.instance Definition _ := GRing.Lmodule.on {mpoly R[n]}.

Local Notation mcoeff := (@mcoeff n R).

Lemma mcoeff_is_additive m : additive (mcoeff m).
Proof. by move=> p q /=; rewrite /mcoeff raddfB. Qed.

HB.instance Definition _ m := GRing.isAdditive.Build {mpoly R[n]} R (mcoeff m)
  (mcoeff_is_additive m).

Lemma mcoeff0   m   : mcoeff m 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mcoeffN   m   : {morph mcoeff m: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mcoeffD   m   : {morph mcoeff m: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mcoeffB   m   : {morph mcoeff m: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mcoeffMn  m k : {morph mcoeff m: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mcoeffMNn m k : {morph mcoeff m: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma mcoeffZ c p m : mcoeff m (c *: p) = c * (mcoeff m p).
Proof. by rewrite /mcoeff coeffZ. Qed.

HB.instance Definition _ m :=
  GRing.isScalable.Build R {mpoly R[n]} R *%R (mcoeff m)
    (fun c => (mcoeffZ c)^~ m).

Local Notation mpolyC := (@mpolyC n R).

Lemma mpolyC_is_additive : additive mpolyC.
Proof. by move=> p q; apply/mpoly_eqP; rewrite /= freegUB. Qed.

HB.instance Definition _ := GRing.isAdditive.Build R {mpoly R[n]} mpolyC
  mpolyC_is_additive.

Lemma mpolyC0     : mpolyC 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mpolyCN     : {morph mpolyC: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mpolyCD     : {morph mpolyC: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mpolyCB     : {morph mpolyC: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mpolyCMn  k : {morph mpolyC: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mpolyCMNn k : {morph mpolyC: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma msupp_eq0 p : (msupp p == [::]) = (p == 0).
Proof.
case: p=> p /=; rewrite msuppE /GRing.zero /= /mpolyC.
by rewrite dom_eq0 freegU0 /=.
Qed.

Lemma msuppnil0 p : msupp p = [::] -> p = 0.
Proof. by move/eqP; rewrite msupp_eq0 => /eqP. Qed.

Lemma mpolyC_eq0 c : (c%:MP == 0 :> {mpoly R[n]}) = (c == 0).
Proof.
rewrite eqE /=; apply/idP/eqP=> [/freeg_eqP/(_ 0%MM)|->//].
by rewrite !coeffU eqxx !mulr1.
Qed.

End MPolyZMod.

(* -------------------------------------------------------------------- *)
HB.mixin Record isMeasure (n : nat) (mf : 'X_{1..n} -> nat) := {
  mf0 : mf 0%MM = 0%N;
  mfD : {morph mf : m1 m2 / (m1 + m2)%MM >-> (m1 + m2)%N};
}.

#[short(type="measure")]
HB.structure Definition Measure (n : nat) := {mf of isMeasure n mf}.

#[deprecated(since="multinomials 2.2.0", note="Use Measure.clone instead.")]
Notation "[ 'measure' 'of' f ]" := (Measure.clone _ f _)
  (at level 0, only parsing) : form_scope.

(* -------------------------------------------------------------------- *)
#[hnf] HB.instance Definition _ n := isMeasure.Build n mdeg mdeg0 mdegD.

(* -------------------------------------------------------------------- *)
Section MMeasure.
Context (n : nat) (R : ringType) (mf : measure n).
Implicit Types (m : 'X_{1..n}) (p q : {mpoly R[n]}).

Lemma mfE m : mf m = (\sum_(i < n) (m i) * mf U_(i)%MM)%N.
Proof.
rewrite {1}(multinomUE_id m) (big_morph mf mfD mf0); apply/eq_bigr => i _.
elim: (m i) => [// | d ih] /=; first by rewrite mul0n mulm0n mf0.
by rewrite mulmS mulSn mfD ih.
Qed.

Definition mmeasure p := (\max_(m <- msupp p) (mf m).+1)%N.

Lemma mmeasureE p : mmeasure p = (\max_(m <- msupp p) (mf m).+1)%N.
Proof. by []. Qed.

Lemma mmeasure0 : mmeasure 0 = 0%N.
Proof. by rewrite /mmeasure msupp0 big_nil. Qed.

Lemma mmeasure_mnm_lt p m : m \in msupp p -> mf m < mmeasure p.
Proof. by move=> m_in_p; rewrite /mmeasure (bigD1_seq m) //= leq_max leqnn. Qed.

Lemma mmeasure_mnm_ge p m : mmeasure p <= mf m -> m \notin msupp p.
Proof. by apply/contra_leqN => /mmeasure_mnm_lt. Qed.

End MMeasure.

(* -------------------------------------------------------------------- *)
Section MSuppZMod.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}) (D : {freeg 'X_{1..n} / R}).

Lemma msuppN p : perm_eq (msupp (-p)) (msupp p).
Proof. by apply/domN_perm_eq. Qed.

Lemma msuppD_le p q : {subset msupp (p + q) <= msupp p ++ msupp q}.
Proof. by move=> x /domD_subset. Qed.

Lemma msuppB_le p q : {subset msupp (p - q) <= msupp p ++ msupp q}.
Proof. by move=> x /msuppD_le; rewrite !mem_cat (perm_mem (msuppN _)). Qed.

Lemma msuppD (p1 p2 : {mpoly R[n]}) :
     [predI (msupp p1) & (msupp p2)] =1 xpred0
  -> perm_eq (msupp (p1 + p2)) (msupp p1 ++ msupp p2).
Proof. by apply/domD_perm_eq. Qed.

Lemma msupp_sum_le (T : Type) (F : T -> {mpoly R[n]}) P (r : seq T) :
  {subset    msupp (\sum_(i <- r | P i) (F i))
          <= flatten [seq msupp (F i) | i <- r & P i]}.
Proof.
  elim: r => /= [|x r ih]; first by rewrite !big_nil msupp0.
  rewrite !big_cons; case: (P x)=> // m /msuppD_le.
  by rewrite !mem_cat => /orP [->//|] /ih ->; rewrite orbT.
Qed.

Lemma msupp_sum (T : eqType) (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}) :
     uniq r
  -> {in r &, forall x y, x != y ->
        [predI (msupp (F x)) & (msupp (F y))] =1 xpred0}
  -> perm_eq
       (msupp (\sum_(i <- r | P i) F i))
       (flatten [seq msupp (F i) | i <- r & P i]).
Proof.
elim: r => /= [|x r ih]; first by rewrite !big_nil msupp0.
case/andP=> x_notin_r uq_r h; rewrite !big_cons /=.
case: (P x); last apply/ih=> //; last first.
  by move=> y1 y2 y1_in_r y2_in_r; apply/h; rewrite 1?mem_behead.
move/(_ uq_r): ih; rewrite -(perm_cat2l (msupp (F x))) => h'.
rewrite -(permPr (h' _)); first apply/msuppD.
  move=> m /=; case: (boolP (m \in _))=> //= m_in_Fx.
  apply/negP=> /msupp_sum_le /flattenP[/= ms] /mapP[y].
  rewrite mem_filter => /andP[_ y_in_r] ->.
  have /= := h x y _ _ _ m; rewrite m_in_Fx=> /= -> //.
    by rewrite mem_head. by rewrite mem_behead.
  by move/memPnC: x_notin_r => /(_ _ y_in_r).
by move=> y1 y2 y1_in_r y2_in_r; apply/h; rewrite 1?mem_behead.
Qed.

End MSuppZMod.

(* -------------------------------------------------------------------- *)
Notation msize p := (@mmeasure _ _ mdeg p).

(* -------------------------------------------------------------------- *)
Section MWeight.
Context {n : nat}.
Implicit Types (m : 'X_{1..n}).

Definition mnmwgt m := (\sum_i m i * i.+1)%N.

Lemma mnmwgt0 : mnmwgt 0 = 0%N.
Proof. by rewrite /mnmwgt big1 // => /= i _; rewrite mnm0E mul0n. Qed.

Lemma mnmwgt1 i : mnmwgt U_(i) = i.+1.
Proof.
rewrite /mnmwgt (bigD1 i) //= mnm1E eqxx mul1n.
rewrite big1 ?addn0 //= => j ne_ij; rewrite mnm1E.
by rewrite eq_sym (negbTE ne_ij) mul0n.
Qed.

Lemma mnmwgtD m1 m2 : mnmwgt (m1 + m2) = (mnmwgt m1 + mnmwgt m2)%N.
Proof.
rewrite /mnmwgt -big_split /=; apply/eq_bigr=> i _.
by rewrite mnmDE mulnDl.
Qed.

End MWeight.

#[hnf] HB.instance Definition _ n := isMeasure.Build n mnmwgt mnmwgt0 mnmwgtD.

(* -------------------------------------------------------------------- *)
(* FIXME: removing Measure.clone below breaks the proof of mweight_XLS *)
Notation mweight p := (@mmeasure _ _ (Measure.clone _ mnmwgt _) p).

Section MSize.
Context (n : nat) (R : ringType).
Implicit Types (m : 'X_{1..n}) (p : {mpoly R[n]}).

Lemma msizeE p : msize p = (\max_(m <- msupp p) (mdeg m).+1)%N.
Proof. exact/mmeasureE. Qed.

Definition msize0 := mmeasure0 R (@mdeg n).

Lemma msize_mdeg_lt p m : m \in msupp p -> mdeg m < msize p.
Proof. exact/mmeasure_mnm_lt. Qed.

Lemma msize_mdeg_ge p m : msize p <= mdeg m -> m \notin msupp p.
Proof. exact/mmeasure_mnm_ge. Qed.

End MSize.

(* -------------------------------------------------------------------- *)
Section MMeasureZMod.
Context (n : nat) (R : ringType) (mf : measure n).
Implicit Types (c : R) (m : 'X_{1..n}) (p q : {mpoly R[n]}).

Local Notation mmeasure := (@mmeasure n R mf).

Lemma mmeasureC c : mmeasure c%:MP = (c != 0%R) :> nat.
Proof.
rewrite mmeasureE msuppC; case: (_ == 0)=> /=.
by rewrite big_nil. by rewrite big_seq1 mf0.
Qed.

Lemma mmeasureD_le p q : mmeasure (p + q) <= maxn (mmeasure p) (mmeasure q).
Proof.
rewrite {1}mmeasureE big_tnth; apply/bigmax_leqP=> /= i _.
set m := tnth _ _; have: m \in msupp (p + q) by apply/mem_tnth.
move/msuppD_le; rewrite leq_max mem_cat.
by case/orP=> /mmeasure_mnm_lt->; rewrite !simpm.
Qed.

Lemma mmeasure_sum (T : Type) (r : seq _) (F : T -> {mpoly R[n]}) (P : pred T) :
  mmeasure (\sum_(i <- r | P i) F i) <= \max_(i <- r | P i) mmeasure (F i).
Proof.
elim/big_rec2: _ => /= [|i k p _ le]; first by rewrite mmeasure0.
apply/(leq_trans (mmeasureD_le _ _)); rewrite geq_max.
by rewrite leq_maxl /= leq_max le orbC.
Qed.

Lemma mmeasureN p : mmeasure (-p) = mmeasure p.
Proof. by rewrite mmeasureE (perm_big _ (msuppN _)). Qed.

Lemma mmeasure_poly_eq0 p : (mmeasure p == 0%N) = (p == 0).
Proof.
apply/idP/eqP=> [z_p|->]; last by rewrite mmeasure0.
apply/mpoly_eqP; move: z_p; rewrite mmeasureE.
rewrite {2}[p]freeg_mpoly; case: (msupp p).
  by rewrite !big_nil /= freegU0.
by move=> m q; rewrite !big_cons -leqn0 geq_max.
Qed.

Lemma mpolySpred p : p != 0 -> mmeasure p = (mmeasure p).-1.+1.
Proof. by rewrite -mmeasure_poly_eq0 -lt0n => /prednK. Qed.

Lemma mmeasure_msupp0 p : (mmeasure p == 0%N) = (msupp p == [::]).
Proof.
rewrite mmeasureE; case: (msupp _) => [|m s].
  by rewrite big_nil !eqxx.
rewrite big_cons /= -[_::_==_]/false; apply/negbTE.
by rewrite -lt0n leq_max.
Qed.

End MMeasureZMod.

(* -------------------------------------------------------------------- *)
Definition msizeC    n R := @mmeasureC n R mdeg.
Definition msizeD_le n R := @mmeasureD_le n R mdeg.
Definition msize_sum n R := @mmeasure_sum n R mdeg.
Definition msizeN    n R := @mmeasureN n R mdeg.

Definition msize_poly_eq0 n R := @mmeasure_poly_eq0 n R mdeg.
Definition msize_msupp0   n R := @mmeasure_msupp0 n R mdeg.

(* -------------------------------------------------------------------- *)
Definition polyn (R : ringType) :=
  fix polyn n := if n is p.+1 then {poly (polyn p)} else R.

Definition ipoly (T : Type) : Type := T.

Notation "{ 'ipoly' T [ n ] }"   := (polyn T n).
Notation "{ 'ipoly' T [ n ] }^p" := (ipoly {ipoly T[n]}).

Section IPoly.
Context (R : ringType) (n : nat).

HB.instance Definition _ := GRing.Ring.on {ipoly R[n]}^p.

End IPoly.

(* -------------------------------------------------------------------- *)
Section Inject.
Context (R : ringType).

Fixpoint inject n m (p : {ipoly R[n]}) : {ipoly R[m + n]} :=
  if m is m'.+1 return {ipoly R[m + n]} then (inject m' p)%:P else p.

Lemma inject_inj n m : injective (@inject n m).
Proof. by elim: m=> [|m ih] p q //= /polyC_inj /ih. Qed.

Lemma inject_is_additive n m : additive (@inject n m).
Proof.
elim: m => [|m ih] //=; rewrite -/(_ \o _).
pose iaM := GRing.isAdditive.Build _ _ _ ih.
pose iA : GRing.Additive.type _ _ := HB.pack (@inject n m) iaM.
have ->: inject m = iA by [].
exact: raddfB.
Qed.

HB.instance Definition _ n m :=
  GRing.isAdditive.Build {ipoly R[n]} {ipoly R[m+n]} (@inject n m)
    (@inject_is_additive n m).

Lemma inject_is_multiplicative n m : multiplicative (@inject n m).
Proof.
elim: m => [|m ih] //=; rewrite -/(_ \o _).
pose imM := GRing.isMultiplicative.Build _ _ _ ih.
pose iM : GRing.RMorphism.type _ _ := HB.pack (@inject n m) imM.
have ->: inject m = iM by [].
exact: (rmorphM _, rmorph1 _).
Qed.

HB.instance Definition _ n m :=
  GRing.isMultiplicative.Build {ipoly R[n]} {ipoly R[m+n]} (@inject n m)
    (@inject_is_multiplicative n m).

Definition inject_cast n m k E : {ipoly R[n]} -> {ipoly R[k]} :=
  ecast k (_ -> {ipoly R[k]}) E (@inject n m).

Lemma inject_cast_inj n m k E :
  injective (@inject_cast n m k E).
Proof. by case: k / E; apply/inject_inj. Qed.

Lemma inject_cast_is_additive n m k E : additive (@inject_cast n m k E).
Proof. case: k /E; exact: raddfB. Qed.

Lemma inject_cast_is_multiplicative n m k E :
  multiplicative (@inject_cast n m k E).
Proof. case: k / E; exact: (rmorphM _, rmorph1 _). Qed.

HB.instance Definition _ n m k e :=
  GRing.isAdditive.Build
    {ipoly R[n]} {ipoly R[k]} (@inject_cast n m k e)
    (inject_cast_is_additive e).

HB.instance Definition _ n m k e :=
  GRing.isMultiplicative.Build
    {ipoly R[n]} {ipoly R[k]} (@inject_cast n m k e)
    (inject_cast_is_multiplicative e).

Lemma inject1_proof n (i : 'I_n.+1) : (n - i + i = n)%N.
Proof. by rewrite subnK // -ltnS. Qed.

Definition inject1 n (i : 'I_n.+1) (p : {ipoly R[i]}) : {ipoly R[n]} :=
  inject_cast (inject1_proof i) p.

Local Notation "c %:IP" := (inject_cast (inject1_proof ord0) c).

Section IScale.
Context (n : nat).

Lemma iscaleA (c1 c2 : R) (p : {ipoly R[n]}) :
  c1%:IP * (c2%:IP * p) = (c1 * c2)%:IP * p.
Proof. by rewrite mulrA rmorphM /=. Qed.

Lemma iscale1r (p : {ipoly R[n]}) : 1%:IP * p = p.
Proof. by rewrite rmorph1 mul1r. Qed.

Lemma iscaleDr (c : R) (p q : {ipoly R[n]}) :
  c%:IP * (p + q) = c%:IP * p + c%:IP * q.
Proof. by rewrite mulrDr. Qed.

Lemma iscaleDl (p : {ipoly R[n]}) (c1 c2 : R) :
  (c1 + c2)%:IP * p = c1%:IP * p + c2%:IP * p.
Proof. by rewrite raddfD /= mulrDl. Qed.

Definition iscale (c : R) (p : {ipoly R[n]}) := c%:IP * p.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R {ipoly R[n]}^p
  iscaleA iscale1r iscaleDr iscaleDl.

End IScale.

Definition injectX n (m : 'X_{1..n}) : {ipoly R[n]} :=
  \prod_(i < n) (@inject1 _ (rshift 1 i) 'X)^+(m i).

Definition minject n (p : {mpoly R[n]}) : {ipoly R[n]} :=
  fglift (@injectX n : _ -> {ipoly R[n]}^p) p.

End Inject.

(* -------------------------------------------------------------------- *)
Section MPolyRing.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}) (m : 'X_{1..n}).

Local Notation "`| p |" := (msize p) : ring_scope.
Local Notation "!| m |" := (mdeg  m) (format "!| m |"): ring_scope.

Local Notation "p *M_[ m ] q" :=
  << (p@_m.1)%MM * (q@_m.2)%MM *g (m.1 + m.2)%MM >>
  (at level 40, no associativity, format "p  *M_[ m ]  q").

Definition mpoly_mul p q : {mpoly R[n]} :=
  [mpoly \sum_(m <- msupp p @@ msupp q) p *M_[m] q].

Local Notation "p *M q" := (mpoly_mul p q)
  (at level 40, left associativity, format "p  *M  q").

Lemma mul_poly1_eq0L p q (m : 'X_{1..n} * 'X_{1..n}) :
  m.1 \notin msupp p -> p *M_[m] q = 0.
Proof. by move/memN_msupp_eq0=> ->; rewrite mul0r freegU0. Qed.

Lemma mul_poly1_eq0R p q (m : 'X_{1..n} * 'X_{1..n}) :
  m.2 \notin msupp q -> p *M_[m] q = 0.
Proof. by move/memN_msupp_eq0=> ->; rewrite mulr0 freegU0. Qed.

Lemma mpoly_mulwE p q kp kq : msize p <= kp -> msize q <= kq ->
  p *M q = [mpoly \sum_(m : 'X_{1..n < kp, kq}) p *M_[m] q].
Proof.
pose Ip : subFinType _ := 'X_{1..n < kp}.
pose Iq : subFinType _ := 'X_{1..n < kq}.
move=> lep leq; apply/mpoly_eqP/esym=> /=.
rewrite big_allpairs/= big_pairA.
rewrite (big_mksub Ip) ?msupp_uniq //=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
rewrite [X in _ = X]big_rmcond /=; last first.
  move=> i /memN_msupp_eq0 ->; rewrite big1=> //.
  by move=> j _; rewrite mul0r freegU0.
apply/eq_bigr=> i _; rewrite (big_mksub Iq) /=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
  by rewrite msupp_uniq.
rewrite [X in _ = X]big_rmcond //= => j /memN_msupp_eq0 ->.
by rewrite mulr0 freegU0.
Qed.

Arguments mpoly_mulwE [p q].

Lemma mpoly_mul_revwE p q kp kq : msize p <= kp -> msize q <= kq ->
  p *M q = [mpoly \sum_(m : 'X_{1..n < kq, kp}) p *M_[(m.2, m.1)] q].
Proof.
by move=> lep leq; rewrite big_pairA exchange_big pair_bigA -mpoly_mulwE.
Qed.

Arguments mpoly_mul_revwE [p q].

Lemma mcoeff_poly_mul p q m k : !|m| < k ->
  (p *M q)@_m =
    \sum_(k : 'X_{1..n < k, k} | m == (k.1 + k.2)%MM) p@_k.1 * q@_k.2.
Proof.
pose_big_enough i; first rewrite (mpoly_mulwE i i) // => lt_mk.
  rewrite mcoeff_MPoly raddf_sum /=; have lt_mi: k < i by [].
  apply/esym; rewrite big_cond_mulrn !big_pairA /=.
  pose Ik : subFinType _ := 'X_{1..n < k}.
  pose Ii : subFinType _ := 'X_{1..n < i}.
  pose F i j := (p@_i * q@_j) *+ (m == (i + j))%MM.
  pose G i   := \sum_(j : 'X_{1..n < k}) (F i j).
  rewrite (big_sub_widen Ik Ii xpredT G) /=; last first.
    by move=> x /leq_trans; apply.
  rewrite big_rmcond /=; last first.
    case=> /= j _; rewrite -leqNgt => /(leq_trans lt_mk) h.
    rewrite {}/G {}/F big1 // => /= l _.
    case: eqP h => [{1}->|]; last by rewrite mulr0n.
    by rewrite mdegD ltnNge leq_addr.
  apply/eq_bigr=> j _; rewrite {}/G.
  rewrite (big_sub_widen Ik Ii xpredT (F _)) /=; last first.
    by move=> x /leq_trans; apply.
  rewrite big_rmcond => //=; last first.
    move=> l; rewrite -leqNgt => /(leq_trans lt_mk) h.
    rewrite {}/F; case: eqP h; rewrite ?mulr0n //.
    by move=> ->; rewrite mdegD ltnNge leq_addl.
  by apply/eq_bigr=> l _; rewrite {}/F coeffU eq_sym mulr_natr.
by close.
Qed.

Lemma mcoeff_poly_mul_rev p q m k : !|m| < k ->
  (p *M q)@_m =
    \sum_(k : 'X_{1..n < k, k} | m == (k.1 + k.2)%MM) p@_k.2 * q@_k.1.
Proof.
move=> /mcoeff_poly_mul ->; rewrite big_cond_mulrn.
rewrite big_pairA /= exchange_big pair_bigA /=.
by rewrite /= -big_cond_mulrn; apply/eq_big=> // i /=; rewrite addmC.
Qed.

Lemma mcoeff_poly_mul_lin p q m k : !|m| < k ->
  (p *M q)@_m = \sum_(k : 'X_{1..n < k} | (k <= m)%MM) p@_k * q@_(m-k).
Proof.
move=> lt_m_k; rewrite (mcoeff_poly_mul _ _ (k := k)) //.
pose P (k1 k2 : 'X_{1..n < k}) := m == (k1 + k2)%MM.
pose Q (k : 'X_{1..n < k}) := (k <= m)%MM.
pose F (k1 k2 : 'X_{1..n}) := p@_k1 * q@_k2.
rewrite -(pair_big_dep xpredT P F) (bigID Q) /= addrC.
(rewrite big1 ?add0r {}/P {}/Q; first apply/eq_bigr)=> /= h1.
+ move=> le_h1_m; have pr: !|m - h1| < k.
    by rewrite (leq_ltn_trans _ lt_m_k) // mdegB.
  rewrite (big_pred1 (BMultinom pr)) //= => h2 /=.
  rewrite bmeqP /=; apply/eqP/eqP=> ->.
  * by rewrite addmC addmK.
  * by rewrite addmC submK //; apply/mnm_lepP.
+ rewrite negb_forall => /existsP /= [i Nle].
  rewrite big_pred0 //= => h2; apply/negbTE/eqP.
  move/mnmP/(_ i); rewrite mnmDE=> eq; move: Nle.
  by rewrite eq leq_addr.
Qed.
Arguments mcoeff_poly_mul_lin [p q m].

Local Notation mcoeff_pml := mcoeff_poly_mul_lin.

Lemma mcoeff_poly_mul_lin_rev p q m k : !|m| < k ->
  (p *M q)@_m = \sum_(k : 'X_{1..n < k} | (k <= m)%MM) p@_(m-k) * q@_k.
Proof.
move=> /[dup] /mcoeff_pml -> lt.
have pr (h : 'X_{1..n}) : !|m - h| < k by exact: leq_ltn_trans (mdegB _ _) _.
pose F (k : 'X_{1..n < k}) := BMultinom (pr k).
have inv_F (h : 'X_{1..n}): (h <= m)%MM -> (m - (m - h))%MM = h.
  by move=> le_hm; rewrite submBA // addmC addmK.
rewrite (reindex_onto F F) //=; last first.
  by move=> h /inv_F eqh; apply/eqP; rewrite eqE /= eqh.
apply/esym/eq_big => [h /=|h /inv_F -> //]; apply/esym; rewrite lem_subr eqE /=.
by apply/eqP/idP => [<-|/inv_F //]; apply/mnm_lepP=> i; rewrite !mnmBE leq_subr.
Qed.
Arguments mcoeff_poly_mul_lin_rev [p q m].

Local Notation mcoeff_pmlr := mcoeff_poly_mul_lin_rev.

Lemma poly_mulA : associative mpoly_mul.
Proof.
move=> p q r; apply/mpolyP=> mi; pose_big_enough b.
rewrite (mcoeff_pml b) // (mcoeff_pmlr b) //. 2: by close.
have h m: !|mi - m| < b by exact/(leq_ltn_trans (mdegB mi m)).
pose coef3 mj mk := p@_mj * (q@_(mi - mj - mk)%MM * r@_mk).
transitivity (\sum_(mj : 'X_{1..n < b} | (mj <= mi)%MM)
                \sum_(mk : 'X_{1..n < b} | (mk <= mi - mj)%MM)
                   coef3 mj mk).
  by apply/eq_bigr=> /= mj _; rewrite (mcoeff_pmlr b) 1?big_distrr.
pose P (mj : 'X_{1..n < b}) := (mj <= mi)%MM.
rewrite (exchange_big_dep P) //= {}/P; last first.
  by move=> mj mk _ /lepm_trans; apply; apply/lem_subr.
apply/eq_bigr=> /= mk /mnm_lepP le_mk_mi.
transitivity (\sum_(mj : 'X_{1..n < b} | (mj <= mi - mk)%MM) coef3 mj mk).
+ apply/eq_bigl=> m /=.
  apply/idP/idP => [/andP[/mnm_lepP le1 /mnm_lepP le2]|le1].
  * apply/mnm_lepP => i; rewrite mnmBE /leq subnBA // addnC -subnBA //.
    by rewrite -mnmBE; apply/le2.
  * have le2: (m <= mi)%MM by rewrite (lepm_trans le1) ?lem_subr.
    rewrite le2; apply/mnm_lepP=> i; rewrite mnmBE /leq.
    move/mnm_lepP: le2 => le2; rewrite subnBA // addnC.
    by rewrite -subnBA //; move/mnm_lepP/(_ i): le1; rewrite mnmBE.
rewrite (mcoeff_pml b) /coef3 1?big_distrl //=.
by apply/eq_bigr=> mj le_mj_miBk; rewrite !mulrA !submDA addmC.
Qed.

Lemma poly_mul1m : left_id 1%:MP mpoly_mul.
Proof.
move=> p; apply/mpoly_eqP/esym; rewrite /mpoly_mul /=.
rewrite msupp1 big_allpairs big_seq1 {1}[p]freeg_mpoly /=.
by apply: eq_bigr => i _; rewrite mpolyCK !simpm.
Qed.

Lemma poly_mulm1 : right_id 1%:MP mpoly_mul.
Proof.
move=> p; apply/mpoly_eqP/esym; rewrite /mpoly_mul /=.
rewrite msupp1 big_allpairs exchange_big big_seq1 {1}[p]freeg_mpoly /=.
by apply: eq_bigr=> i _; rewrite mpolyCK !simpm.
Qed.

Lemma poly_mulDl : left_distributive mpoly_mul +%R.
Proof.
move=> p q r; pose_big_enough i.
  rewrite !(mpoly_mulwE i (msize r)) //=.
  apply/mpoly_eqP=> /=; rewrite -big_split /=; apply: eq_bigr.
  by case=> [[i1 /= _] [i2 /= _]] _; rewrite freegUD -mulrDl -mcoeffD.
by close.
Qed.

Lemma poly_mulDr : right_distributive mpoly_mul +%R.
Proof.
move=> p q r; pose_big_enough i.
  rewrite !(mpoly_mulwE (msize p) i) //=.
  apply/mpoly_eqP=> /=; rewrite -big_split /=; apply: eq_bigr.
  by case=> [[i1 /= _] [i2 /= _]] _; rewrite freegUD -mulrDr -mcoeffD.
by close.
Qed.

Lemma poly_oner_neq0 : 1%:MP != 0 :> {mpoly R[n]}.
Proof. by rewrite mpolyC_eq oner_eq0. Qed.

HB.instance Definition _ := GRing.Zmodule_isRing.Build (mpoly n R)
  poly_mulA poly_mul1m poly_mulm1 poly_mulDl poly_mulDr poly_oner_neq0.
HB.instance Definition _ := GRing.Ring.on {mpoly R[n]}.

Lemma mcoeff1 m : 1@_m = (m == 0%MM)%:R.
Proof. by rewrite mcoeffC mul1r. Qed.

Lemma mcoeffM p q m :
  (p * q)@_m =
    \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 + k.2)%MM)
      (p@_k.1 * q@_k.2).
Proof. exact: mcoeff_poly_mul. Qed.

Lemma mcoeffMr p q m :
  (p * q)@_m =
    \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 + k.2)%MM)
      (p@_k.2 * q@_k.1).
Proof.
rewrite mcoeffM big_cond_mulrn big_pairA/=.
rewrite exchange_big pair_bigA /= -big_cond_mulrn.
by apply: eq_bigl=> k /=; rewrite addmC.
Qed.

Lemma msuppM_le p q :
  {subset msupp (p * q) <= [seq (m1 + m2)%MM | m1 <- msupp p, m2 <- msupp q]}.
Proof.
move=> m; rewrite -[_ \in _]negbK -mcoeff_eq0 mcoeffM=> nz_s.
apply/memPn=> /= h; move: nz_s; rewrite big1 ?eqxx //=.
case=> m1 m2 /=; pose m'1 : 'X_{1..n} := m1; pose m'2 : 'X_{1..n} := m2.
move/eqP=> mE; case: (boolP (m'1 \in msupp p)); last first.
  by move/memN_msupp_eq0=> ->; rewrite mul0r.
case: (boolP (m'2 \in msupp q)); last first.
  by move/memN_msupp_eq0=> ->; rewrite mulr0.
rewrite {}/m'1 {}/m'2=> m2_in_q m1_in_p; absurd false=> //.
move: (h m); rewrite eqxx; apply; apply/allpairsP=> /=.
exists (m1 : 'X_{1..n}, m2 : 'X_{1..n}) => /=.
by rewrite m1_in_p m2_in_q /=.
Qed.

Lemma mul_mpolyC c p : c%:MP * p = c *: p.
Proof.
have [->|nz_c] := eqVneq c 0; first by rewrite scale0r mul0r.
apply/mpoly_eqP=> /=; rewrite big_allpairs msuppC (negbTE nz_c) big_seq1.
by apply: eq_bigr => i _; rewrite mpolyCK !simpm.
Qed.

Lemma mcoeffCM c p m : (c%:MP * p)@_m = c * p@_m.
Proof. by rewrite mul_mpolyC mcoeffZ. Qed.

Lemma msuppZ_le (c : R) p : {subset msupp (c *: p) <= msupp p}.
Proof.
move=> /= m; rewrite !mcoeff_msupp -mul_mpolyC.
rewrite mcoeffCM; have [->|//] := eqVneq p@_m 0.
by rewrite mulr0 eqxx.
Qed.

Lemma mpolyC_is_multiplicative : multiplicative (mpolyC n (R := R)).
Proof.
split=> // p q; apply/mpolyP=> m.
by rewrite mcoeffCM !mcoeffC mulrA.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build R {mpoly R[n]} (@mpolyC n R)
    mpolyC_is_multiplicative.

Lemma mpolyC1 : mpolyC n 1 = 1.
Proof. exact: rmorph1. Qed.

Lemma msize1_polyC p : msize p <= 1 -> p = (p@_0)%:MP.
Proof.
move=> le_p_1; apply/mpolyP=> m; rewrite mcoeffC.
case: (m =P 0%MM)=> [->|/eqP]; first by rewrite mulr1.
rewrite mulr0 -mdeg_eq0 => nz_m; rewrite memN_msupp_eq0 //.
by apply/msize_mdeg_ge; rewrite 1?(@leq_trans 1) // lt0n.
Qed.

Lemma msize_poly1P p : reflect (exists2 c, c != 0 & p = c%:MP) (msize p == 1%N).
Proof.
apply: (iffP eqP)=> [pC|[c nz_c ->]]; last by rewrite msizeC nz_c.
have def_p: p = (p@_0)%:MP by rewrite -msize1_polyC ?pC.
by exists p@_0; rewrite // -(mpolyC_eq0 n) -def_p -msize_poly_eq0 pC.
Qed.

Lemma mpolyC_nat (k : nat) : (k%:R)%:MP = k%:R :> {mpoly R[n]}.
Proof.
apply/mpolyP=> i; rewrite mcoeffC mcoeffMn mcoeffC.
by rewrite mul1r commr_nat mulr_natr.
Qed.

Lemma mpolyCM : {morph mpolyC n (R := _): p q / p * q}.
Proof. exact: rmorphM. Qed.

Lemma mmeasure1 mf : mmeasure mf 1 = 1%N.
Proof. by rewrite mmeasureC oner_eq0. Qed.

Lemma msize1 : msize 1 = 1%N.
Proof. exact/mmeasure1. Qed.

Lemma mmeasureZ_le mf (p : {mpoly R[n]}) c :
  mmeasure mf (c *: p) <= mmeasure mf p.
Proof.
rewrite {1}mmeasureE big_tnth; apply/bigmax_leqP=> /= i _.
set m := tnth _ _; have: m \in msupp (c *: p) by apply/mem_tnth.
by move/msuppZ_le=> /mmeasure_mnm_lt->.
Qed.

Lemma mpoly_scaleAl c p q : c *: (p * q) = (c *: p) * q.
Proof. by rewrite -!mul_mpolyC mulrA. Qed.

HB.instance Definition _ := GRing.Lmodule_isLalgebra.Build R (mpoly n R)
  mpoly_scaleAl.
HB.instance Definition _ := GRing.Lalgebra.on {mpoly R[n]}.

Lemma alg_mpolyC c : c%:A = c%:MP :> {mpoly R[n]}.
Proof. by rewrite -mul_mpolyC mulr1. Qed.

Lemma mcoeff0_is_multiplicative :
  multiplicative (mcoeff 0%MM : {mpoly R[n]} -> R).
Proof.
split=> [p q|]; rewrite ?mpolyCK //.
rewrite (mcoeff_poly_mul _ _ (k := 1)) ?mdeg0 //.
rewrite (bigD1 (bm0, bm0)) ?simpm //=; last first.
rewrite [X in _+X]big1 ?addr0 // => i /andP [] h.
rewrite eqE /= !bmeqP /=; move/eqP/esym/(congr1 mdeg): h.
rewrite mdegD [X in _=X]mdeg0 => /eqP; rewrite addn_eq0.
by rewrite !mdeg_eq0=> /andP [/eqP->/eqP->]; rewrite !eqxx.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {mpoly R[n]} R (mcoeff 0)
    mcoeff0_is_multiplicative.

End MPolyRing.

(* -------------------------------------------------------------------- *)
Section MPolyVar.
Context (n : nat) (R : ringType).

Definition mpolyX_def (m : 'X_{1..n}) : {mpoly R[n]} := [mpoly << m >>].

Fact mpolyX_key : unit. Proof. by []. Qed.

Definition mpolyX m : {mpoly R[n]} :=
  locked_with mpolyX_key (mpolyX_def m).

Canonical mpolyX_unlockable m := [unlockable of (mpolyX m)].

Definition mX (k : 'I_n) : 'X_{1..n} :=
  nosimpl [multinom (i == k : nat) | i < n].

End MPolyVar.

Notation "'X_[ R , m ]" := (@mpolyX _ R m).
Notation "'X_[ m ]"     := (@mpolyX _ _ m).
Notation "'X_ i"        := (@mpolyX _ _ U_(i)).

(* -------------------------------------------------------------------- *)
Section MPolyVarTheory.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}) (m : 'X_{1..n}).

Local Notation "'X_[ m ]" := (@mpolyX n R m).

Lemma msuppX m : msupp 'X_[m] = [:: m].
Proof. by rewrite unlock /msupp domU1. Qed.

Lemma mem_msuppXP m m' : reflect (m = m') (m' \in msupp 'X_[m]).
Proof. by rewrite msuppX mem_seq1; apply: (iffP eqP). Qed.

Lemma mcoeffX m k : 'X_[m]@_k = (m == k)%:R.
Proof. by rewrite unlock /mpolyX_def mcoeff_MPoly coeffU mul1r. Qed.

Lemma mcoeffXU (i j : 'I_n) : ('X_i : {mpoly R[n]})@_U_(j) = (i == j)%:R.
Proof. by rewrite mcoeffX eq_mnm1. Qed.

Lemma mmeasureX mf m : mmeasure mf 'X_[R, m] = (mf m).+1.
Proof. by rewrite mmeasureE msuppX big_seq1. Qed.

Lemma msizeX m : msize 'X_[R, m] = (mdeg m).+1.
Proof. exact/mmeasureX. Qed.

Lemma msupp_rem (p : {mpoly R[n]}) m :
  perm_eq (msupp (p - p@_m *: 'X_[m])) (rem m (msupp p)).
Proof.
case: (boolP (m \in msupp p)) => h.
  apply/uniq_perm; rewrite ?rem_uniq //.
  move=> m'; rewrite mem_rem_uniq // inE /=.
  rewrite !mcoeff_msupp mcoeffB mcoeffZ mcoeffX.
  case: (eqVneq m' m) => [->|] /=.
  by rewrite mulr1 subrr eqxx. by rewrite mulr0 subr0.
have/rem_id -> := h; move: h.
rewrite mcoeff_msupp negbK=> /eqP ->.
by rewrite scale0r subr0.
Qed.

Lemma mpolyX0 : 'X_[0] = 1.
Proof. by apply/mpolyP=> m; rewrite mcoeffX mcoeffC mul1r eq_sym. Qed.

Lemma mpolyXD m1 m2 : 'X_[m1 + m2] = 'X_[m1] * 'X_[m2] :> {mpoly R[n]}.
Proof.
apply/mpoly_eqP; rewrite /GRing.mul /= !msuppX big_seq1 /=.
by rewrite !mcoeffX !eqxx !simpm unlock /=.
Qed.

Lemma mpolyX_prod s P :
  \prod_(i <- s | P i) 'X_[i] = 'X_[\sum_(i <- s | P i) i].
Proof.
elim: s => [|i s ih]; first by rewrite !big_nil mpolyX0.
by rewrite !big_cons; case: (P i); rewrite ?mpolyXD ih.
Qed.

Lemma mpolyXn m i : 'X_[m] ^+ i = 'X_[m *+ i].
Proof.
elim: i=> [|i ih]; first by rewrite expr0 mulm0n mpolyX0.
by rewrite mulmS mpolyXD -ih exprS.
Qed.

Lemma mprodXnE {I} F P (m : I -> nat) (r : seq _) :
    \prod_(i <- r | P i) 'X_[R, F i] ^+ m i
  = 'X_[\sum_(i <- r | P i) (F i *+ m i)].
Proof.
elim/big_rec2: _ => /= [|i m' p Pi ->].
  by rewrite mpolyX0. by rewrite ?(mpolyXD, mpolyXn).
Qed.

Lemma mprodXE {I} (F : I -> 'X_{1..n}) P (r : seq _) :
  \prod_(i <- r | P i) 'X_[R, F i] = 'X_[\sum_(i <- r | P i) F i].
Proof.
rewrite (eq_bigr (fun i => 'X_[R, F i] ^+ 1)) => [|i _].
  by rewrite mprodXnE. by rewrite expr1.
Qed.

Lemma mpolyXE (s : 'S_n) m : 'X_[m] = \prod_(i < n) 'X_(s i) ^+ m (s i).
Proof.
rewrite {1}[m](multinomUE s) -mprodXE.
by apply/eq_bigr=> i _; rewrite mpolyXn.
Qed.

Lemma mpolyXE_id m : 'X_[m] = \prod_(i < n) 'X_i ^+ m i.
Proof. by rewrite (mpolyXE 1); apply/eq_bigr=> /= i _; rewrite perm1. Qed.

Lemma mcoeffXn m i k : ('X_[m] ^+ i)@_k = ((m *+ i)%MM == k)%:R.
Proof. by rewrite mpolyXn mcoeffX. Qed.

Lemma mpolyE p : p = \sum_(m <- msupp p) (p@_m *: 'X_[m]).
Proof.
apply/mpolyP=> m; rewrite {1}[p]freeg_mpoly /= mcoeff_MPoly.
rewrite !raddf_sum /=; apply/eq_bigr=> i _.
by rewrite -mul_mpolyC mcoeffCM mcoeffX coeffU.
Qed.

Lemma mpolywE k p : msize p <= k ->
  p = \sum_(m : 'X_{1..n < k}) (p@_m *: 'X_[m]).
Proof.
move=> lt_pk; pose I : subFinType _ := 'X_{1..n < k}.
rewrite {1}[p]mpolyE (big_mksub I) //=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
  by rewrite msupp_uniq.
by rewrite big_rmcond //= => i; move/memN_msupp_eq0 ->; rewrite scale0r.
Qed.

Lemma mpolyME p q :
  p * q = \sum_(m <- msupp p @@ msupp q) (p@_m.1 * q@_m.2) *: 'X_[m.1 + m.2].
Proof.
apply/mpolyP=> m; rewrite {1}/GRing.mul /= mcoeff_MPoly.
rewrite !raddf_sum; apply/eq_bigr=> i _ /=.
by rewrite coeffU -mul_mpolyC mcoeffCM mcoeffX.
Qed.

Lemma mpolywME p q k : msize p <= k -> msize q <= k ->
  p * q = \sum_(m : 'X_{1..n < k, k}) (p@_m.1 * q@_m.2) *: 'X_[m.1 + m.2].
Proof.
move=> ltpk ltqk; rewrite mpolyME; pose I : subFinType _ := 'X_{1..n < k}.
rewrite big_allpairs (big_mksub I) /=; last first.
  by move=> m /msize_mdeg_lt /leq_trans; apply. by rewrite msupp_uniq.
rewrite big_rmcond /= => [|i]; last first.
  by move/memN_msupp_eq0=> ->; rewrite big1 // => j _; rewrite mul0r scale0r.
rewrite big_pairA /=; apply/eq_bigr=> i _; rewrite (big_mksub I)/=; last first.
- by move=> m /msize_mdeg_lt /leq_trans; apply.
- by rewrite msupp_uniq.
rewrite big_rmcond /= => [//|j].
by move/memN_msupp_eq0=> ->; rewrite mulr0 scale0r.
Qed.

Lemma commr_mpolyX m p : GRing.comm p 'X_[m].
Proof.
apply/mpolyP=> k; rewrite mcoeffM mcoeffMr.
by apply/eq_bigr=> /= i _; rewrite !mcoeffX GRing.commr_nat.
Qed.

Lemma mcoeffMX p m k : (p * 'X_[m])@_(m + k) = p@_k.
Proof.
rewrite commr_mpolyX mpolyME msuppX big_allpairs.
rewrite big_seq1 [X in _=X@__]mpolyE !raddf_sum /=.
by apply/eq_bigr=> i _; rewrite !mcoeffZ !mcoeffX eqxx mul1r eqm_add2l.
Qed.

Lemma msuppMX p m :
  perm_eq (msupp (p * 'X_[m])) [seq (m + m')%MM | m' <- msupp p].
Proof.
apply/uniq_perm=> //; first rewrite map_inj_uniq //.
  by move=> m1 m2 /=; rewrite ![(m + _)%MM]addmC; apply: addIm.
move=> m'; apply/idP/idP; last first.
  case/mapP=> mp mp_in_p ->; rewrite mcoeff_msupp.
  by rewrite mcoeffMX -mcoeff_msupp.
move/msuppM_le; rewrite msuppX => /allpairsP [[p1 p2]] /=.
rewrite mem_seq1; case=> p1_in_p /eqP <- ->.
by apply/mapP; exists p1; last rewrite addmC.
Qed.

Lemma msuppMCX c m : c != 0 -> msupp (c *: 'X_[m]) = [:: m].
Proof.
move=> nz_c; rewrite -mul_mpolyC; apply/perm_small_eq=> //.
by rewrite (permPl (msuppMX _ _)) msuppC (negbTE nz_c) /= addm0.
Qed.

Lemma msupp_sumX (r : seq 'X_{1..n}) (f : 'X_{1..n} -> R) :
  uniq r -> {in r, forall m, f m != 0} ->
  perm_eq (msupp (\sum_(m <- r) (f m) *: 'X_[m])) r.
Proof.
move=> uq_r h; set F := fun m => (f m *: 'X_[m] : {mpoly R[n]}).
have msFm m: m \in r -> msupp (f m *: 'X_[m]) = [:: m].
  by move=> m_in_r; rewrite msuppMCX // h.
rewrite (permPl (msupp_sum xpredT _ _)) //.
  move/eq_in_map: msFm; rewrite filter_predT=> ->.
  set s := flatten _; have ->: s = r => //.
  by rewrite {}/s; elim: {uq_r h} r=> //= m r ->.
move=> m1 m2 /h nz_fm1 /h nz_fm2 nz_m1m2 m /=.
rewrite !msuppMCX // !mem_seq1; case: eqP=> //= ->.
by rewrite (negbTE nz_m1m2).
Qed.

Lemma mcoeff_mpoly (E : 'X_{1..n} -> R) m k : mdeg m < k ->
  (\sum_(m : 'X_{1..n < k}) (E m *: 'X_[m]))@_m = E m.
Proof.
move=> lt_mk; rewrite raddf_sum (bigD1 (Sub m lt_mk)) //=.
rewrite big1 ?addr0; last first.
  case=> i /= lt_ik; rewrite eqE /= => ne_im.
  by rewrite mcoeffZ mcoeffX (negbTE ne_im) mulr0.
by rewrite mcoeffZ mcoeffX eqxx mulr1.
Qed.

Lemma MPoly_is_linear: linear (@MPoly n R).
Proof. by move=> c p q; apply/mpoly_eqP. Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R {freeg 'X_{1.. n} / R} {mpoly R[n]}
    _ (@MPoly n R) MPoly_is_linear.

Lemma MPolyU c m : MPoly << c *g m >> = c *: 'X_[m].
Proof.
apply/mpolyP=> k; rewrite mcoeff_MPoly.
by rewrite mcoeffZ mcoeffX coeffU.
Qed.

Lemma mpolyrect (P : {mpoly R[n]} -> Type) :
     P 0
  -> (forall c m p, m \notin msupp p -> c != 0 -> P p -> P (c *: 'X_[m] + p))
  -> forall p, P p.
Proof.
move=> h0 hS [p] /=; elim/freeg_rect_dom0: p => [|c q m mdom nz_c /hS h].
  by rewrite raddf0.
by rewrite raddfD /= MPolyU; apply: h.
Qed.

Lemma mpolyind (P : {mpoly R[n]} -> Prop) :
     P 0
  -> (forall c m p, m \notin msupp p -> c != 0 -> P p -> P (c *: 'X_[m] + p))
  -> forall p, P p.
Proof. exact: mpolyrect. Qed.

End MPolyVarTheory.

(* -------------------------------------------------------------------- *)
Section MPolyLead.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}).

Definition mlead p : 'X_{1..n} := (\join_(m <- msupp p) m)%O.

Lemma mleadC (c : R) : mlead c%:MP = 0%MM.
Proof.
rewrite /mlead msuppC; case: eqP=> _.
  by rewrite big_nil. by rewrite big_seq1.
Qed.

Lemma mlead0 : mlead 0 = 0%MM.
Proof. by rewrite mleadC. Qed.

Lemma mlead1 : mlead 1 = 0%MM.
Proof. by rewrite mleadC. Qed.

Lemma mleadXm m : mlead 'X_[m] = m.
Proof. by rewrite /mlead msuppX big_seq1. Qed.

Lemma mlead_supp p : p != 0 -> mlead p \in msupp p.
Proof.
rewrite -msupp_eq0 /mlead => nz_p; case: bigjoinP => //; first exact: le_total.
by case: (msupp p) nz_p.
Qed.

Lemma mlead_deg p : p != 0 -> (mdeg (mlead p)).+1 = msize p.
Proof.
move=> /mlead_supp lc_in_p; rewrite /mlead msizeE mdeg_bigmax.
have: msupp p != [::] by case: (msupp p) lc_in_p.
elim: (msupp p)=> [|m [|m' r] ih] // _; first by rewrite !big_seq1.
by rewrite big_cons -maxnSS {}ih // !big_cons.
Qed.

Lemma msupp_le_mlead p m : m \in msupp p -> (m <= mlead p)%O.
Proof. by move=> mp; apply/joins_sup_seq. Qed.

Lemma mleadN p : mlead (-p) = mlead p.
Proof.
have [->|nz_p] := eqVneq p 0; first by rewrite oppr0.
by rewrite /mlead (perm_big _ (msuppN p)).
Qed.

Lemma mleadD_le p q : (mlead (p + q) <= mlead p `|` mlead q)%O.
Proof.
have [->|] := eqVneq (p+q) 0; first by rewrite mlead0 le0x.
move/mlead_supp/msuppD_le; rewrite mem_cat => /orP[].
+ by move/msupp_le_mlead=> h; apply/(le_trans h)/leUl.
+ by move/msupp_le_mlead=> h; apply/(le_trans h)/leUr.
Qed.

Lemma mleadB_le p q : (mlead (p - q) <= mlead p `|` mlead q)%O.
Proof. by rewrite -(mleadN q); apply/mleadD_le. Qed.

Lemma mleadc_eq0 p : (p@_(mlead p) == 0) = (p == 0).
Proof.
apply/idP/idP => [|/eqP->]; last by rewrite mcoeff0.
by case: (p =P 0) => // /eqP /mlead_supp; rewrite mcoeff_eq0 => ->.
Qed.

Lemma mcoeff_gt_mlead p m : (mlead p < m)%O -> p@_m = 0.
Proof.
move=> lt_lcp_m; apply/eqP; rewrite mcoeff_eq0; apply/negP.
by move/msupp_le_mlead; rewrite leNgt lt_lcp_m.
Qed.

Lemma mleadDr (p1 p2 : {mpoly R[n]}) :
  (mlead p1 < mlead p2)%O -> mlead (p1 + p2) = mlead p2.
Proof.
move=> lt_p1p2. apply/le_anti.
move/ltW/join_r: (lt_p1p2) (mleadD_le p1 p2) => -> -> /=.
rewrite leNgt; apply/negP=> /mcoeff_gt_mlead.
rewrite mcoeffD mcoeff_gt_mlead // add0r => /eqP.
rewrite mleadc_eq0=> /eqP z_p2; move: lt_p1p2.
by rewrite z_p2 mlead0 ltx0.
Qed.

Lemma mleadDl (p1 p2 : {mpoly R[n]}) :
  (mlead p2 < mlead p1)%O -> mlead (p1 + p2) = mlead p1.
Proof. by move/mleadDr; rewrite addrC => ->. Qed.

Lemma mleadD (p1 p2 : {mpoly R[n]}) :
  mlead p1 != mlead p2 -> mlead (p1 + p2) = (mlead p1 `|` mlead p2)%O.
Proof. by case: ltgtP => [/mleadDr ->|/mleadDl ->|->] //; rewrite eqxx. Qed.

Lemma mlead_sum_le {T} (r : seq T) P F :
  (mlead (\sum_(p <- r | P p) F p) <= \join_(p <- r | P p) mlead (F p))%O.
Proof.
elim/big_rec2: _ => /= [|x m p Px le]; first by rewrite mlead0.
by apply/(le_trans (mleadD_le _ _))/leU2.
Qed.

Lemma mlead_sum {T} (r : seq T) P F :
  uniq [seq mlead (F x) | x <- r & P x] ->
  mlead (\sum_(p <- r | P p) F p) = (\join_(p <- r | P p) mlead (F p))%O.
Proof.
elim: r=> [|p r ih]; first by rewrite !big_nil mlead0.
rewrite !big_cons /=; case: (P p)=> //= /andP[Fp_ml uq_ml].
pose Q i := P (nth p r i); rewrite !(big_nth p) -!(big_filter _ Q).
set itg := [seq _ <- _ | _]; have [/size0nil->|nz_szr] := eqVneq (size itg) 0%N.
  by rewrite !big_nil joinx0 addr0.
move: {ih}(ih uq_ml); rewrite !(big_nth p) -!(big_filter _ Q) -/itg.
move=> ih; rewrite mleadD ih //.
case: bigjoinP; [exact: le_total | by rewrite /nilp; case: eqP nz_szr |].
move=> /= x; rewrite mem_filter => /andP[Px].
rewrite mem_iota add0n subn0 => /andP[_ lt_x_szr].
apply/contra: Fp_ml=> /eqP-> {Q itg uq_ml nz_szr ih}.
elim: r x Px lt_x_szr=> [|y r ih] [|x] //=.
  by move=> -> /=; rewrite mem_head.
rewrite ltnS=> Px lt_x_szr; case: (P y)=> /=.
  by rewrite 1?mem_behead //=; apply/ih. by apply/ih.
Qed.

Lemma mleadM_le p q : (mlead (p * q) <= (mlead p + mlead q)%MM)%O.
Proof.
have [->|] := eqVneq (p * q) 0; first by rewrite mlead0 le0x.
move/mlead_supp/msuppM_le/allpairsP => [[m1 m2] /=] [m1_in_p m2_in_q ->].
by apply/lem_add; apply/msupp_le_mlead.
Qed.

Lemma mlead_prod_le T (r : seq T) (P : pred T) F :
  (mlead (\prod_(p <- r | P p) F p) <= (\sum_(p <- r | P p) mlead (F p))%MM)%O.
Proof.
elim/big_rec2: _ => /= [|x m p Px ih]; first by rewrite mlead1.
by apply/(le_trans (mleadM_le (F x) p)); apply/lem_add.
Qed.

Notation mleadc p := (p@_(mlead p)).

Lemma mleadcC (c : R) : mleadc c%:MP_[n] = c.
Proof. by rewrite mleadC mcoeffC eqxx mulr1. Qed.

Lemma mleadc0 : mleadc (0 : {mpoly R[n]}) = 0.
Proof. by rewrite mleadcC. Qed.

Lemma mleadc1 : mleadc (1 : {mpoly R[n]}) = 1.
Proof. by rewrite mleadcC. Qed.

Lemma mleadcM p q :
  (p * q)@_(mlead p + mlead q) = mleadc p * mleadc q.
Proof.
have [->|nz_p] := eqVneq p 0; first by rewrite mleadc0 !mul0r mcoeff0.
have [->|nz_q] := eqVneq q 0; first by rewrite mleadc0 !mulr0 mcoeff0.
rewrite mpolyME (bigD1_seq (mlead p, mlead q)) /=; first last.
+ by rewrite allpairs_uniq => // -[? ?] [].
+ by rewrite allpairs_f// !mlead_supp.
rewrite mcoeffD mcoeffZ mcoeffX eqxx mulr1.
rewrite big_seq_cond raddf_sum /= big1 ?addr0 //.
case=> m1 m2; rewrite in_allpairs//= -andbA; case/and3P.
move=> m1_in_p m2_in_q ne_m_lc; rewrite mcoeffZ mcoeffX.
move/msupp_le_mlead: m1_in_p; move/msupp_le_mlead: m2_in_q.
rewrite le_eqVlt => /predU1P[m2E|]; last first.
  by move=> lt /lemc_lt_add /(_ lt) /lt_eqF ->; rewrite mulr0.
move: ne_m_lc; rewrite m2E xpair_eqE eqxx andbT.
rewrite le_eqVlt=> /negbTE -> /=; rewrite eqm_add2r.
by move/lt_eqF=> ->; rewrite mulr0.
Qed.

Lemma mleadcMW p q (mp mq : 'X_{1..n}) :
     (mlead p <= mp)%O -> (mlead q <= mq)%O
  -> (p * q)@_(mp + mq)%MM = p@_mp * q@_mq.
Proof.
case: (boolP ((mlead p < mp) || (mlead q < mq)))%O; last first.
  by case: ltgtP => // <-; case: ltgtP => // <- _ _ _; apply: mleadcM.
move=> lt_lm lep leq; have lt_lmD: ((mlead p + mlead q)%MM < (mp + mq)%MM)%O.
  by case/orP: lt_lm=> lt; [apply/ltmc_le_add | apply/lemc_lt_add].
move/(le_lt_trans (mleadM_le p q))/mcoeff_gt_mlead: lt_lmD.
by case/orP: lt_lm=> /mcoeff_gt_mlead ->; rewrite ?(mul0r, mulr0).
Qed.

Lemma mleadc_prod T (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}) :
     (\prod_(p <- r | P p) F p)@_(\sum_(p <- r | P p) mlead (F p))%MM
  =  \prod_(p <- r | P p) mleadc (F p).
Proof.
elim: r => [|p r ih]; first by rewrite !big_nil mcoeff1 eqxx.
rewrite !big_cons; case: (P p); rewrite // mleadcMW //.
  by rewrite ih. by apply/mlead_prod_le.
Qed.

Lemma mleadcZ c p : (c *: p)@_(mlead p) = c * mleadc p.
Proof. by rewrite mcoeffZ. Qed.

Lemma mleadM_proper p q : mleadc p * mleadc q != 0 ->
  mlead (p * q) = (mlead p + mlead q)%MM.
Proof.
move: (mleadM_le p q); rewrite le_eqVlt => /predU1P[->//|].
rewrite -mleadcM mcoeff_eq0 negbK => ltm /msupp_le_mlead lem.
by move: (lt_le_trans ltm lem); rewrite ltxx.
Qed.

Lemma mleadcM_proper p q : mleadc p * mleadc q != 0 ->
  mleadc (p * q) = mleadc p * mleadc q.
Proof. by move/mleadM_proper=> ->; rewrite mleadcM. Qed.

Lemma lreg_mleadc p : GRing.lreg (mleadc p) -> GRing.lreg p.
Proof.
move/mulrI_eq0=> reg_p; apply/mulrI0_lreg=> q /eqP.
apply/contraTeq => nz_q; rewrite -mleadc_eq0.
by rewrite mleadcM_proper reg_p mleadc_eq0.
Qed.

Section MLeadProd.
Context (T : eqType) (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}).

Lemma mlead_prod_proper :
  (forall x, x \in r -> P x -> GRing.lreg (mleadc (F x))) ->
  mlead (\prod_(p <- r | P p) F p) = (\sum_(p <- r | P p) mlead (F p))%MM.
Proof.
pose Q (s : seq T) := forall x, x \in s -> P x -> GRing.lreg (mleadc (F x)).
rewrite -/(Q r); elim: r => [|x s ih] h; first by rewrite !big_nil mleadC.
have lreg_s: Q s.
  by move=> y y_in_s; apply: (h y); rewrite mem_behead.
rewrite !big_cons; case: (boolP (P x))=> Px; last exact/ih.
have lreg_x := (h x (mem_head _ _) Px).
rewrite mleadM_proper; first by rewrite ih.
by rewrite mulrI_eq0 ?ih // mleadc_prod; apply/lreg_neq0/lreg_prod.
Qed.

Lemma mleadc_prod_proper :
  (forall x, x \in r -> P x -> GRing.lreg (mleadc (F x))) ->
  mleadc (\prod_(p <- r | P p) F p) = \prod_(p <- r | P p) mleadc (F p).
Proof. by move/mlead_prod_proper=> ->; rewrite mleadc_prod. Qed.

End MLeadProd.

Lemma mleadX_le p k : (mlead (p ^+ k) <= (mlead p *+ k)%MM)%O.
Proof.
rewrite -[k](card_ord k) -prodr_const /mnm_muln.
by rewrite Monoid.iteropE -big_const; apply/mlead_prod_le.
Qed.

Lemma mleadcX p k : (p ^+ k)@_(mlead p *+ k) = (mleadc p) ^+ k.
Proof.
rewrite -[k](card_ord k) -prodr_const /mnm_muln.
by rewrite Monoid.iteropE -big_const mleadc_prod prodr_const.
Qed.

Lemma mleadX_proper p k : GRing.lreg (mleadc p) ->
  mlead (p ^+ k) = (mlead p *+ k)%MM.
Proof.
move=> h; rewrite -[k](card_ord k) -prodr_const.
rewrite /mnm_muln Monoid.iteropE -big_const.
by apply/mlead_prod_proper=> /= i _ _.
Qed.

Lemma mleadcX_proper p k : GRing.lreg (mleadc p) ->
  mleadc (p ^+ k) = mleadc p ^+ k.
Proof.
move=> h; rewrite -[k](card_ord k) -!prodr_const.
by apply/mleadc_prod_proper=> /= i _ _.
Qed.

Lemma msizeM_le (p q : {mpoly R[n]}) :
  msize (p * q) <= (msize p + msize q).+1.
Proof.
have [->|nz_p ] := eqVneq p 0; first by rewrite mul0r msize0.
have [->|nz_q ] := eqVneq q 0; first by rewrite mulr0 msize0.
have [->|nz_pq] := eqVneq (p * q) 0; first by rewrite msize0.
rewrite -!mlead_deg // !(addSn, addnS) 2?ltnW // !ltnS.
by have /lemc_mdeg := mleadM_le p q; rewrite mdegD.
Qed.

Lemma msizeM_proper p q : mleadc p * mleadc q != 0 ->
   msize (p * q) = (msize p + msize q).-1.
Proof.
have [->|nz_p ] := eqVneq p 0; first by rewrite mleadc0 mul0r eqxx.
have [->|nz_q ] := eqVneq q 0; first by rewrite mleadc0 mulr0 eqxx.
move=> h; rewrite -?[msize p]mlead_deg -?[msize q]mlead_deg //.
rewrite !(addSn, addnS) -mdegD /= -mleadM_proper //.
rewrite mlead_deg //; apply/negP; pose m := (mlead p + mlead q)%MM.
move/eqP/(congr1 (mcoeff m)); rewrite mleadcM mcoeff0.
by move/eqP; rewrite (negbTE h).
Qed.

Lemma mleadZ_le c p : (mlead (c *: p) <= mlead p)%O.
Proof.
have [->|] := eqVneq (c *: p) 0; first by rewrite mlead0 le0x.
by move/mlead_supp/msuppZ_le/msupp_le_mlead.
Qed.

Lemma mleadZ_proper c p : c * mleadc p != 0 -> mlead (c *: p) = mlead p.
Proof.
move: (mleadZ_le c p); rewrite le_eqVlt => /predU1P[->//|].
rewrite -mleadcZ mcoeff_eq0 negbK => ltm /msupp_le_mlead lem.
by move: (lt_le_trans ltm lem); rewrite ltxx.
Qed.

Lemma ltm_mleadD p (q := p - p@_(mlead p) *: 'X_[mlead p]) :
    p != 0 -> q != 0 ->  (mlead q < mlead p)%O.
Proof.
move=> Zp Zq; have: mlead q \in (rem (mlead p) (msupp p)).
  by rewrite -(perm_mem (msupp_rem p _)) // mlead_supp.
rewrite (rem_filter _ (msupp_uniq p)) mem_filter /= => /andP[h].
suff: (mlead q <= mlead p)%O by rewrite le_eqVlt (negPf h).
apply: le_trans (mleadB_le _ _) _; rewrite leUx lexx /=.
by rewrite (le_trans (mleadZ_le _ _)) // mleadXm.
Qed.

Lemma msizeZ_le p c : msize (c *: p) <= msize p.
Proof. exact: mmeasureZ_le. Qed.

Lemma msizeZ_proper (p : {mpoly R[n]}) c :
  c * mleadc p != 0 -> msize (c *: p) = msize p.
Proof.
have [->|nz_p] := eqVneq p 0; first by rewrite mleadc0 mulr0 eqxx.
have [->|nz_c] := eqVneq c 0; first by rewrite mul0r eqxx.
move=> h; rewrite -[msize p]mlead_deg // -(mleadZ_proper h).
rewrite mlead_deg //; pose m := (mlead p); apply/negP.
move/eqP/(congr1 (mcoeff m)); rewrite mcoeffZ mcoeff0.
by move/eqP; rewrite (negbTE h).
Qed.

Lemma mleadrect (P : {mpoly R[n]} -> Type) :
  (forall p, (forall q, (mlead q < mlead p)%O -> P q) -> P p) -> forall p, P p.
Proof.
move=> ih p; move: {2}(mlead p) (lexx (mlead p))=> m.
elim/(ltmwf (n := n)): m p=> m1 wih p lt_pm1; apply/ih=> q lt_pq.
by apply/(wih (mlead q)); first exact: lt_le_trans lt_pq _.
Qed.

End MPolyLead.

Notation mleadc p := (p@_(mlead p)).

(* -------------------------------------------------------------------- *)
Section MPolyLast.
Context {R : ringType} {n : nat}.

Definition mlast (p : {mpoly R[n]}) : 'X_{1..n} :=
  head 0%MM (sort <=%O (msupp p)).

Lemma mlast0 : mlast 0 = 0%MM.
Proof. by rewrite /mlast msupp0. Qed.

Lemma mlast_supp p : p != 0 -> mlast p \in msupp p.
Proof.
rewrite -msupp_eq0 /mlast; move: (msupp p) => s nz_s.
rewrite -(perm_mem (permEl (perm_sort <=%O%O _))).
by rewrite -nth0 mem_nth // size_sort lt0n size_eq0.
Qed.

Lemma mlast_lemc m p : m \in msupp p -> (mlast p <= m)%O.
Proof.
rewrite /mlast -nth0; set s := sort _ _.
have: perm_eq s (msupp p) by apply/permEl/perm_sort.
have: sorted <=%O%O s by apply/sort_sorted/le_total.
case: s => /= [_|m' s srt_s]; first rewrite perm_sym.
  by move/perm_small_eq=> -> //.
move/perm_mem => <-; rewrite in_cons => /predU1P[->//|].
elim: s m' srt_s => //= m'' s ih m' /andP[le_mm' /ih {}ih].
by rewrite in_cons => /predU1P[->//|/ih /(le_trans le_mm')].
Qed.

Lemma mlastE (p : {mpoly R[n]}) (m  : 'X_{1..n}) :
     m \in msupp p
  -> (forall m' : 'X_{1..n}, m' \in msupp p -> (m <= m')%O)
  -> mlast p = m.
Proof.
move=> mp le; apply/le_anti; rewrite mlast_lemc //=.
by apply/le; rewrite mlast_supp // -msupp_eq0; case: msupp mp.
Qed.

Lemma mcoeff_lt_mlast p m : (m < mlast p)%O -> p@_m = 0.
Proof.
move=> le; case/boolP: (m \in msupp p).
  by move/mlast_lemc/(lt_le_trans le); rewrite ltxx.
by rewrite mcoeff_msupp negbK => /eqP.
Qed.

End MPolyLast.

(* -------------------------------------------------------------------- *)
Section MPoly0.
Context (R : ringType).

Lemma mpolyKC : cancel (@mcoeff 0 R 0%MM) (@mpolyC 0 R).
Proof.
  move=> p; apply/mpolyP=> m; rewrite mcoeffC.
  case: (m =P 0%MM)=> [->|/eqP]; first by rewrite mulr1.
  by apply/contraNeq=> _; apply/eqP/mnmP; case.
Qed.

End MPoly0.

(* -------------------------------------------------------------------- *)
Section MPolyDeriv.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}) (m : 'X_{1..n}).

Definition mderiv (i : 'I_n) p :=
  \sum_(m <- msupp p) ((m i)%:R * p@_m) *: 'X_[m - U_(i)].

Local Notation "p ^`M ( i )" := (mderiv i p).

Lemma mderivwE i p k : msize p <= k ->
  p^`M(i) = \sum_(m : 'X_{1..n < k}) ((m i)%:R * p@_m) *: 'X_[m - U_(i)].
Proof.
pose I : subFinType _ := 'X_{1..n < k}.
move=> le_pk; rewrite /mderiv (big_mksub I) /=; first last.
  by move=> x /msize_mdeg_lt/leq_trans/(_ le_pk).
  by rewrite msupp_uniq.
rewrite big_rmcond //= => j /memN_msupp_eq0 ->.
by rewrite mulr0 scale0r.
Qed.
Arguments mderivwE [i p].

Lemma mcoeff_deriv i m p : p^`M(i)@_m = p@_(m + U_(i)) *+ (m i).+1.
Proof.
pose_big_enough j; first rewrite {2}[p](mpolywE (k := j)) //.
  rewrite !(mderivwE j) // !raddf_sum -sumrMnl; apply/eq_bigr.
  move=> /= [k /= _] _; rewrite !mcoeffZ !mcoeffX.
  case: (k =P m + U_(i))%MM=> [{1 3}->|].
    by rewrite mnmDE mnm1E eqxx addn1 addmK eqxx !simpm mulr_natl.
  rewrite !simpm mul0rn; have [->|nz_mi] := (eqVneq (k i) 0%N).
    by rewrite !simpm.
  case: eqP=> [{1}<-|]; rewrite ?simpm //.
  rewrite submK //; apply/mnm_lepP => l; rewrite mnm1E.
  by case: (i =P l) nz_mi=> // ->; rewrite -lt0n.
by close.
Qed.

Lemma mderiv_is_linear i : linear (mderiv i).
Proof.
move=> c p q; pose_big_enough j; first rewrite !(mderivwE j) //.
  rewrite scaler_sumr -big_split /=; apply/eq_bigr=> k _.
  rewrite !scalerA -scalerDl; congr (_ *: _).
  by rewrite mcoeffD mcoeffZ mulrDr !mulrA commr_nat.
by close.
Qed.

HB.instance Definition _ i := GRing.isLinear.Build R {mpoly R[n]} {mpoly R[n]}
  _ (mderiv i) (mderiv_is_linear i).

Lemma mderiv0 i : mderiv i 0 = 0.
Proof. exact: raddf0. Qed.

Lemma mderivC i c : mderiv i c%:MP = 0.
Proof.
apply/mpolyP=> m; rewrite mcoeff0 mcoeff_deriv mcoeffC.
by rewrite mnmD_eq0 mnm1_eq0 andbF mulr0 mul0rn.
Qed.

Lemma mderivX i m : mderiv i 'X_[m] = (m i)%:R *: 'X_[m - U_(i)].
Proof. by rewrite /mderiv msuppX big_seq1 mcoeffX eqxx mulr1. Qed.

Lemma commr_mderivX i m p : GRing.comm p ('X_[m])^`M(i).
Proof.
rewrite /GRing.comm mderivX -mul_mpolyC mpolyC_nat.
by rewrite -{1}commr_nat mulrA commr_nat commr_mpolyX mulrA.
Qed.

Lemma mderivN i : {morph mderiv i: x / - x}.
Proof. exact: raddfN. Qed.

Lemma mderivD i : {morph mderiv i: x y / x + y}.
Proof. exact: raddfD. Qed.

Lemma mderivB i : {morph mderiv i: x y / x - y}.
Proof. exact: raddfB. Qed.

Lemma mderivMn i k : {morph mderiv i: x / x *+ k}.
Proof. exact: raddfMn. Qed.

Lemma mderivMNn i k : {morph mderiv i: x / x *- k}.
Proof. exact: raddfMNn. Qed.

Lemma mderivZ i c p : (c *: p)^`M(i) = c *: p^`M(i).
Proof. by rewrite linearZ. Qed.

Lemma mderiv_mulC i c p : (c%:MP * p)^`M(i) = c%:MP * p^`M(i).
Proof. by rewrite !mul_mpolyC mderivZ. Qed.

Lemma mderivM i p q : (p * q)^`M(i) = (p^`M(i) * q) + (p * q^`M(i)).
Proof.
elim/mpolyind: p; first by rewrite !(mul0r, add0r, mderiv0).
move=> c m p _ _ ih; rewrite !(mulrDl, mderivD) -addrA.
rewrite [X in _=_+X]addrCA -ih addrA => {ih}; congr (_ + _).
rewrite -!scalerAl !mderivZ -scalerAl -scalerDr; congr (_ *: _).
pose_big_enough k; rewrite 1?[q](mpolywE (k := k)) //; try by close.
do! rewrite mulr_sumr ?raddf_sum /=; rewrite -big_split /=.
apply/eq_bigr=> h _; rewrite -!commr_mpolyX -scalerAl -mpolyXD.
rewrite !mderivZ -commr_mderivX -!scalerAl -scalerDr; congr (_ *: _).
rewrite !mderivX -!commr_mpolyX -!scalerAl -!mpolyXD mnmDE.
have [z_mi|ne_mi] := eqVneq (m i) 0%N.
  rewrite z_mi addn0 scale0r add0r; congr (_ *: 'X_[_]).
  apply/mnmP=> j; rewrite !(mnmBE, mnmDE, mnm1E).
  by case: eqP => /= [<-|]; rewrite ?subn0 // z_mi !addn0.
apply/esym; rewrite addmC addmBA; last by rewrite lep1mP.
have [z_hi|ne_hi] := eqVneq (h i) 0%N.
  by rewrite z_hi add0n scale0r addr0.
rewrite addrC addmC addmBA; last by rewrite lep1mP.
by rewrite addmC -scalerDl natrD.
Qed.

Lemma mderiv_comm i j p : p^`M(i)^`M(j) = p^`M(j)^`M(i).
Proof.                          (* FIXME: f_equal *)
pose_big_enough k; first pose mderivE := (mderivwE k).
  rewrite ![p^`M(_)]mderivE // !raddf_sum /=; apply/eq_bigr.
  move=> l _; rewrite !mderivZ !mderivX !scalerA.
  rewrite !submDA addmC -!commr_nat -!mulrA -!natrM.
  f_equal; congr (_ * _%:R); rewrite !mnmBE !mnm1E.
  by case: eqVneq => [->|_] //=; rewrite !subn0 mulnC.
by close.
Qed.

Lemma mderiv_perm (s1 s2 : seq 'I_n) p :
  perm_eq s1 s2 -> foldr mderiv p s1 = foldr mderiv p s2.
Proof.
pose M q s := foldr mderiv q s; rewrite -!/(M _ _).
have h (s : seq 'I_n) (x : 'I_n) q: x \in s ->
  M q s = M q (x :: rem x s).
+ elim: s=> [|y s ih] //; rewrite in_cons /=.
  by case: eqVneq => [->|ne_xy {}/ih ->] //=; rewrite mderiv_comm.
elim: s1 s2 => [|x s1 ih] s2.
  by rewrite perm_sym=> /perm_small_eq=> ->.
move=> peq_xDs1_s2; have x_in_s2: x \in s2.
  by rewrite -(perm_mem peq_xDs1_s2) mem_head.
have /h ->/= := x_in_s2; rewrite -ih // -(perm_cons x).
by rewrite (permPl peq_xDs1_s2) perm_to_rem.
Qed.

Definition mderivm m p : {mpoly R[n]} :=
  foldr (fun i => iter (m i) (mderiv i)) p (enum 'I_n).

Local Notation "p ^`M [ m ]" := (mderivm m p).

Lemma mderivm_foldr m p :
  let s := flatten [seq nseq (m i) i | i <- enum 'I_n] in
  p^`M[m] = foldr mderiv p s.
Proof.
rewrite /mderivm; elim: (enum _)=> //= i s ih.
by rewrite foldr_cat; elim: (m i)=> //= k ->.
Qed.

Lemma mderivm0m p : p^`M[0] = p.
Proof.
rewrite mderivm_foldr (eq_map (_ : _ =1 fun=> [::])); first by elim: (enum _).
by move=> i /=; rewrite mnm0E.
Qed.

Lemma mderivmDm m1 m2 p : p^`M[m1 + m2] = p^`M[m1]^`M[m2].
Proof.
rewrite !mderivm_foldr -foldr_cat; apply/mderiv_perm.
apply/seq.permP => /= a; rewrite count_cat !count_flatten.
rewrite !sumnE !big_map -big_split /=; apply/eq_bigr=> i _.
by rewrite mnmDE nseqD count_cat addnC.
Qed.

Lemma mderiv_summ (T : Type) (r : seq T) (P : pred T) F p :
    p^`M[\sum_(x <- r | P x) (F x)]
  = foldr mderivm p [seq F x | x <- r & P x].
Proof.
elim: r => //= [|x s ih]; first by rewrite big_nil mderivm0m.
by rewrite big_cons; case: (P x); rewrite //= addmC mderivmDm ih.
Qed.

Lemma mderivmU1m i p : p^`M[U_(i)] = p^`M(i).
Proof.
rewrite mderivm_foldr (@mderiv_perm _ [:: i]) //.
apply/seq.permP=> /= a; rewrite addn0 count_flatten sumnE !big_map.
rewrite -/(index_enum _) (bigD1 i) //=.
rewrite mnm1E eqxx /= big1 ?addn0 // => j ne_ji.
by rewrite mnm1E eq_sym (negbTE ne_ji).
Qed.

Lemma mderivm_is_linear m : linear (mderivm m).
Proof.
move=> c p q; rewrite /mderivm; elim: (enum _)=> //= i s ih.
by elim: (m i) => //= {ih}k ->; rewrite mderivD mderivZ.
Qed.

HB.instance Definition _ m :=
  GRing.isLinear.Build R {mpoly R[n]} {mpoly R[n]} _ (mderivm m)
    (mderivm_is_linear m).

Lemma mderivmN m : {morph mderivm m: x / - x}.
Proof. exact: raddfN. Qed.

Lemma mderivmD m : {morph mderivm m: x y / x + y}.
Proof. exact: raddfD. Qed.

Lemma mderivmB m : {morph mderivm m: x y / x - y}.
Proof. exact: raddfB. Qed.

Lemma mderivmMn m k : {morph mderivm m: x / x *+ k}.
Proof. exact: raddfMn. Qed.

Lemma mderivmMNn m k : {morph mderivm m: x / x *- k}.
Proof. exact: raddfMNn. Qed.

Lemma mderivmZ m c p : (c *: p)^`M[m] = c *: p^`M[m].
Proof. by rewrite linearZ. Qed.

Lemma mderivm_mulC m c p : (c%:MP * p)^`M[m] = c%:MP * p^`M[m].
Proof. by rewrite !mul_mpolyC mderivmZ. Qed.

Local Notation "p ^`M ( i , n )" := (mderivm (U_(i) *+ n) p).

Lemma mderivn0 i p : p^`M(i, 0) = p.
Proof. by rewrite mulm0n mderivm0m. Qed.

Lemma nderivn1 i p : p^`M(i, 1) = p^`M(i).
Proof. by rewrite mulm1n mderivmU1m. Qed.

Lemma mderivSn i k p : p^`M(i, k.+1) = p^`M(i)^`M(i, k).
Proof. by rewrite mulmS mderivmDm mderivmU1m. Qed.

Lemma mderivnS i k p : p^`M(i, k.+1) = p^`M(i, k)^`M(i).
Proof. by rewrite mulmS addmC mderivmDm mderivmU1m. Qed.

Lemma mderivn_iter i k p :
  p^`M(i, k) = iter k (mderiv i) p.
Proof. by elim: k => /= [|k ih]; rewrite ?mderivn0 // mderivnS ih. Qed.

Lemma mderivmX m1 m2 :
  ('X_[m1])^`M[m2] = (\prod_(i < n) (m1 i)^_(m2 i))%:R *: 'X_[m1-m2].
Proof.
rewrite [m2]multinomUE_id mderiv_summ filter_predT /index_enum -enumT /=.
elim: (enum _) (enum_uniq 'I_n) => /= [|i s ih /andP [i_notin_s uq_s]].
  by move=> _; rewrite !big_nil scale1r subm0.
pose F j := (m1 j) ^_ (m2 j); rewrite ih // mderivmZ.
rewrite big_seq [X in X%:R](eq_bigr F) -?big_seq; last first.
  move=> j j_in_s; rewrite (bigD1_seq j) //=.
  rewrite mnmDE mnm_sumE mulmnE mnm1E eqxx mul1n.
  rewrite big1 ?addn0 // => j' ne_j'j; rewrite mulmnE.
  by rewrite mnm1E (negbTE ne_j'j).
rewrite big_cons mulnC natrM -scalerA; apply/esym.
rewrite 2![X in X%:R*:(_*:_)](big_seq, eq_bigr F); last first.
  move=> j j_in_s; rewrite big_cons mnmDE mnm_sumE.
  rewrite (bigD1_seq j) //= big1 ?addn0 => [|j' ne_j'j].
    rewrite !mulmnE !mnm1E eqxx mul1n; move/memPn: i_notin_s.
    by rewrite eq_sym => /(_ j j_in_s) /negbTE ->.
  by rewrite mulmnE mnm1E (negbTE ne_j'j).
rewrite -big_seq; congr (_ *: _); rewrite !big_cons.
rewrite mnmDE mnm_sumE big_seq big1 ?addn0; last first.
  move=> /= j j_in_s; rewrite mulmnE mnm1E; move/memPn: i_notin_s.
  by move/(_ j j_in_s)=> /negbTE->.
rewrite mulmnE mnm1E eqxx mul1n; elim: (m2 i)=> /= [|k ihk].
  by rewrite ffactn0 scale1r mulm0n add0m mderivm0m.
rewrite mderivnS -ihk mderivZ mderivX scalerA -natrM.
rewrite submDA Monoid.mulmAC /= mulmSr; congr (_%:R *: 'X_[_]).
rewrite mnmBE mnmDE mnm_sumE big_seq big1; last first.
  move=> /= j j_in_s; rewrite mulmnE mnm1E; move: i_notin_s.
  by move/memPn/(_ j j_in_s)=> /negbTE->.
by rewrite addn0 mulmnE mnm1E eqxx mul1n ffactnSr.
Qed.

Lemma mderivmE m p : p^`M[m] =
  \sum_(m' <- msupp p)
     (p@_m' * (\prod_(i < n) (m' i)^_(m i))%:R *: 'X_[m'-m]).
Proof.
rewrite {1}[p]mpolyE raddf_sum /=; apply/eq_bigr=> m' _.
by rewrite mderivmZ -scalerA -mderivmX.
Qed.

Lemma mderivmwE k m p : msize p <= k -> p^`M[m] =
  \sum_(m' : 'X_{1..n < k})
     (p@_m' * (\prod_(i < n) (m' i)^_(m i))%:R *: 'X_[m'-m]).
Proof.
move=> lt_pk; pose P (m : 'X_{1..n < k}) := (val m) \in msupp p.
rewrite (bigID P) {}/P /= addrC big1 ?add0r; last first.
  by move=> m' /memN_msupp_eq0=> ->; rewrite mul0r scale0r.
rewrite mderivmE (big_mksub 'X_{1..n < k}) //=; first exact/msupp_uniq.
by move=> m' /msize_mdeg_lt /leq_trans; apply.
Qed.

Lemma mderivnE i k p : p^`M(i, k) =
  \sum_(m <- msupp p) (((m i)^_k)%:R * p@_m) *: 'X_[m - U_(i) *+ k].
Proof.
rewrite mderivmE; apply/eq_bigr=> /= m _.
rewrite -commr_nat (bigD1 i) //= big1 ?muln1.
  by rewrite mulmnE mnm1E eqxx mul1n.
by move=> j ne_ji; rewrite mulmnE mnm1E eq_sym (negbTE ne_ji).
Qed.

Lemma mderivnX i k m : 'X_[m]^`M(i, k) = ((m i)^_k)%:R *: 'X_[m - U_(i) *+ k].
Proof. by rewrite mderivnE msuppX big_seq1 mcoeffX eqxx mulr1. Qed.

Lemma mcoeff_mderivm m p m' :
  (p^`M[m])@_m' = p@_(m + m') *+ (\prod_(i < n) ((m + m')%MM i)^_(m i)).
Proof.
pose_big_enough i; first rewrite (@mderivmwE i) //.
  have lt_mDm'_i: mdeg (m + m') < i by [].
  rewrite (bigD1 (Sub (m + m')%MM lt_mDm'_i)) //=.
  rewrite mcoeffD raddf_sum /= [X in _+X]big1; last first.
    case=> j lt_ji; rewrite eqE /= => ne_j_mDm'.
    rewrite mcoeffZ mcoeffX; case: eqP; rewrite ?mulr0 //=.
    move=> eq_m'_jBm; move: ne_j_mDm'; rewrite -eq_m'_jBm.
    case: (boolP (m <= j))%MM => [/addmBA->|].
      by rewrite [(m + j)%MM]addmC /= addmK eqxx.
    rewrite negb_forall; case/existsP=> /= k Nle_mj.
    by rewrite (bigD1 k) //= ffact_small ?simpm // ltnNge.
  rewrite addr0 mcoeffZ mcoeffX {3}[(m + m')%MM]addmC addmK.
  by rewrite eqxx mulr1 mulr_natr.
by close.
Qed.

Lemma mcoeff_mderiv i p m : (p^`M(i))@_m = p@_(m + U_(i)) *+ (m i).+1.
Proof.
rewrite -mderivmU1m mcoeff_mderivm addmC /=.
rewrite (bigD1 i) //= mnmDE !mnm1E eqxx addn1 ffactn1.
rewrite (eq_bigr (fun _ => 1%N)) ?prod_nat_const /=.
  by rewrite exp1n muln1.
move=> j ne_ji; rewrite mnmDE mnm1E eq_sym.
by rewrite (negbTE ne_ji) ffactn0.
Qed.

End MPolyDeriv.

Notation "p ^`M ( i )"     := (mderiv i p).
Notation "p ^`M [ m ]"     := (mderivm m p).
Notation "p ^`M ( i , n )" := (mderivm (U_(i) *+ n) p).

(* -------------------------------------------------------------------- *)
Section MPolyMorphism.
Context (n : nat) (R S : ringType).
Implicit Types (p q r : {mpoly R[n]}) (m : 'X_{1..n}).

Section Defs.
Context (f : R -> S) (h : 'I_n -> S).
Definition mmap1 m := \prod_(i < n) (h i)^+(m i).
Definition mmap  p := \sum_(m <- msupp p) (f p@_m) * (mmap1 m).
End Defs.

Lemma mmap11 h : mmap1 h 0%MM = 1.
Proof. by rewrite /mmap1 big1 // => /= i _; rewrite mnm0E expr0. Qed.

Lemma mmap1U h i : mmap1 h U_(i) = h i.
Proof.
pose inj j := insubd i j; rewrite /mmap1.
pose F j := h (inj j) ^+ U_(i)%MM (inj j).
have FE j: j < n -> F j = (h (inj j)) ^+ (i == j :> nat).
  move=> lt_jn; rewrite /F /inj /insubd insubT /=.
  by rewrite mnm1E -val_eqE.
rewrite (eq_bigr (F \o val)) //; last first.
  by move=> j _ /=; rewrite FE // mnm1E /inj /insubd valK.
have ->: n = (i.+1 + (n - i.+1))%N by rewrite subnKC.
rewrite big_split_ord /= [X in _*X]big1 ?mulr1; last first.
  case=> j /= lt_nBSi _; rewrite FE -?ltn_subRL //.
  case: (_ =P _); last by rewrite expr0.
  by rewrite addSnnS -{1}[val i]addn0 /= => /addnI.
rewrite big_ord_recr /= big1 ?mul1r; last first.
  case=> j /= lt_ji _; rewrite FE; last first.
    by rewrite (@leq_trans i) // ltnW.
  by rewrite eq_sym (ltn_eqF lt_ji) expr0.
by rewrite FE // eqxx expr1 /inj /insubd valK.
Qed.

Lemma commr_mmap1_M h m1 m2 :
     (forall i x, GRing.comm x (h i))
  -> mmap1 h (m1 + m2) = (mmap1 h m1) * (mmap1 h m2).
Proof.
move=> comm; pose F (i : 'I_n) := (h i ^+ m1 i) * (h i ^+ m2 i).
rewrite /mmap1 (eq_bigr F) => [|i _]; last first.
  by rewrite mnmDE exprD.
rewrite {}/F; elim/big_rec3: _; first by rewrite mulr1.
move=> i y1 y2 y3 _ ->; rewrite -!mulrA; congr (_ * _).
have commn k j x: GRing.comm x ((h j)^+k) by apply/commrX.
by rewrite -commn -mulrA commn.
Qed.

Local Notation "m ^[ h ]"     := (mmap1 h m).
Local Notation "p ^[ f , h ]" := (mmap f h p).

Section Additive.
Context (h : 'I_n -> S) (f : {additive R -> S}).

Lemma mmapE p i : msize p <= i ->
  p^[f,h] = \sum_(m : 'X_{1..n < i}) (f p@_m) * m^[h].
Proof.
move=> le_pi; set I : subFinType _ := 'X_{1..n < i}.
rewrite /mmap (big_mksub I) ?msupp_uniq //=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
rewrite big_rmcond //= => j /memN_msupp_eq0 ->.
by rewrite raddf0 mul0r.
Qed.
Arguments mmapE [p].

Lemma mmap_is_additive : additive (mmap f h).
Proof.
move=> p q /=; pose_big_enough i.
  rewrite !(mmapE i) // -sumrB; apply/eq_bigr.
  by case=> /= [m _] _; rewrite !raddfB /= mulrDl mulNr.
by close.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build {mpoly R[n]} S (mmap f h)
  mmap_is_additive.

Local Notation mmap := (mmap f h).

Lemma mmap0     : mmap 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mmapN     : {morph mmap: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mmapD     : {morph mmap: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mmapB     : {morph mmap: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mmapMn  k : {morph mmap: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mmapMNn k : {morph mmap: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma mmapC c : mmap c%:MP = f c.
Proof.
have [->|nz_c] := eqVneq c 0; first by rewrite mmap0 raddf0.
rewrite /mmap msuppC (negbTE nz_c) big_seq1 mmap11 mulr1.
by rewrite mcoeffC eqxx mulr1.
Qed.

End Additive.

Arguments mmapE [h f p].

Section Multiplicative.
Context (h : 'I_n -> S) (f : {rmorphism R -> S}).

Lemma mmapX m : ('X_[m])^[f,h] = m^[h].
Proof. by rewrite /mmap msuppX big_seq1 mcoeffX eqxx rmorph1 mul1r. Qed.

Lemma mmapZ c p : (c *: p)^[f,h] = (f c) * p^[f,h].
Proof.
pose_big_enough i.
  rewrite !(mmapE i) // mulr_sumr; apply/eq_bigr.
  by move=> j _; rewrite mcoeffZ mulrA -rmorphM.
by close.
Qed.

Hypothesis commr_h: forall i x, GRing.comm x (h i).
Hypothesis commr_f: forall p m m', GRing.comm (f p@_m) (m'^[h]).

Lemma commr_mmap_is_multiplicative: multiplicative (mmap f h).
Proof.
split=> //= [p q|]; last first.
  by rewrite /mmap msupp1 big_seq1 mpolyCK rmorph1 mul1r mmap11.
pose_big_enough i.
  rewrite (mpolywME (k := i)) // raddf_sum /= !(mmapE i) //.
  rewrite big_distrlr /= pair_bigA; apply/eq_bigr=> /=.
  case=> j1 j2 _ /=; rewrite mmapZ mmapX; apply/esym.
  rewrite [f q@__ * _]commr_f mulrA -[X in X*_]mulrA.
  by rewrite -commr_mmap1_M // -mulrA -commr_f !mulrA rmorphM.
by close.
Qed.

End Multiplicative.
End MPolyMorphism.

Arguments mmapE [n R S h f p].

(* -------------------------------------------------------------------- *)
Lemma mmap1_eq n (R : ringType) (f1 f2 : 'I_n -> R) m :
  f1 =1 f2 -> mmap1 f1 m = mmap1 f2 m.
Proof.
move=> eq_f; rewrite /mmap1; apply/eq_bigr.
by move=> /= i _; rewrite eq_f.
Qed.

Lemma mmap1_id n (R : ringType) m :
  mmap1 (fun i => 'X_i) m = 'X_[m] :> {mpoly R[n]}.
Proof. by rewrite mpolyXE_id. Qed.

(* -------------------------------------------------------------------- *)
Section MPolyMorphismComm.
Context (n : nat) (R : ringType) (S : comRingType).
Context (h : 'I_n -> S) (f : {rmorphism R -> S}).
Implicit Types (p q r : {mpoly R[n]}).

Lemma mmap_is_multiplicative : multiplicative (mmap f h).
Proof.
  apply/commr_mmap_is_multiplicative.
  + by move=> i x; apply/mulrC.
  + by move=> p m m'; apply/mulrC.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {mpoly R[n]} S (mmap f h)
    mmap_is_multiplicative.

End MPolyMorphismComm.

(* -------------------------------------------------------------------- *)
Section MPolyComRing.
Context (n : nat) (R : comRingType).
Implicit Types (p q r : {mpoly R[n]}).

Lemma mpoly_mulC p q : p * q = q * p.
Proof.
apply/mpolyP=> /= m; rewrite mcoeffM mcoeffMr.
by apply: eq_bigr=> /= i _; rewrite mulrC.
Qed.

HB.instance Definition _ := GRing.Ring_hasCommutativeMul.Build (mpoly n R)
  mpoly_mulC.
HB.instance Definition _ := GRing.ComRing.on {mpoly R[n]}.

#[hnf]
HB.instance Definition _ := GRing.Lalgebra_isComAlgebra.Build R {mpoly R[n]}.
#[hnf]
HB.instance Definition _ := GRing.Lalgebra_isComAlgebra.Build R (mpoly n R).

End MPolyComRing.

(* -------------------------------------------------------------------- *)
Section MPolyComp.
Context (n : nat) (R : ringType) (k : nat).
Implicit Types (p q : {mpoly R[n]}) (lp lq : n.-tuple {mpoly R[k]}).

Definition comp_mpoly lq p : {mpoly R[k]} := mmap (@mpolyC _ R) (tnth lq) p.

Local Notation "p \mPo lq" := (comp_mpoly lq p).

Lemma comp_mpolyE p lq :
  p \mPo lq = \sum_(m <- msupp p) p@_m *: \prod_(i < n) (tnth lq i)^+(m i).
Proof. by apply/eq_bigr=> m _; rewrite -mul_mpolyC. Qed.

Lemma comp_mpolywE p lq w : msize p <= w -> p \mPo lq =
  \sum_(m : 'X_{1..n < w}) (p@_m *: \prod_(i < n) (tnth lq i)^+(m i)).
Proof.
move=> le_szp_w; rewrite /comp_mpoly (mmapE w) //=.
by apply/eq_bigr=> m _; rewrite mul_mpolyC.
Qed.

Lemma comp_mpoly_is_additive lq : additive (comp_mpoly lq).
Proof. by move=> p q; rewrite /comp_mpoly -mmapB. Qed.

HB.instance Definition _ lq := GRing.isAdditive.Build {mpoly R[n]} {mpoly R[k]}
  (comp_mpoly lq) (comp_mpoly_is_additive lq).

Lemma comp_mpoly0   lq   : 0 \mPo lq = 0                     . Proof. exact: raddf0. Qed.
Lemma comp_mpolyN   lq   : {morph comp_mpoly lq: x / - x}    . Proof. exact: raddfN. Qed.
Lemma comp_mpolyD   lq   : {morph comp_mpoly lq: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma comp_mpolyB   lq   : {morph comp_mpoly lq: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma comp_mpolyMn  lq l : {morph comp_mpoly lq: x / x *+ l} . Proof. exact: raddfMn. Qed.
Lemma comp_mpolyMNn lq l : {morph comp_mpoly lq: x / x *- l} . Proof. exact: raddfMNn. Qed.

Lemma comp_mpoly_is_linear lq : scalable (comp_mpoly lq).
Proof. by move=> c p; rewrite /comp_mpoly mmapZ mul_mpolyC. Qed.

HB.instance Definition _ lq :=
  GRing.isScalable.Build R {mpoly R[n]} {mpoly R[k]} _ (comp_mpoly lq)
    (comp_mpoly_is_linear lq).

Lemma comp_mpoly1 lq : 1 \mPo lq = 1.
Proof. by rewrite /comp_mpoly -mpolyC1 mmapC. Qed.

Lemma comp_mpolyC c lq : c%:MP \mPo lq = c%:MP.
Proof. by rewrite [LHS]mmapC. Qed.

Lemma comp_mpolyZ c p lq : (c *: p) \mPo lq = c *: (p \mPo lq).
Proof. exact/linearZ. Qed.

Lemma comp_mpolyXU i lq : 'X_i \mPo lq = lq`_i.
Proof. by rewrite /comp_mpoly mmapX mmap1U -tnth_nth. Qed.

Lemma comp_mpolyX m lq : 'X_[m] \mPo lq = \prod_(i < n) (tnth lq i)^+(m i).
Proof. by rewrite [LHS]mmapX. Qed.

Lemma comp_mpolyEX p lq :
  p \mPo lq = \sum_(m <- msupp p) (p@_m *: ('X_[m] \mPo lq)).
Proof. by apply/eq_bigr=> m _; rewrite mul_mpolyC comp_mpolyX. Qed.

End MPolyComp.

Notation "p \mPo lq" := (@comp_mpoly _ _ _ lq p).

Section MPolyCompComm.
Context (n : nat) (R : comRingType) (k : nat) (lp : n.-tuple {mpoly R[k]}).

Lemma comp_mpoly_is_multiplicative : multiplicative (comp_mpoly lp).
Proof. exact: mmap_is_multiplicative. Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {mpoly R[n]} {mpoly R[k]} (comp_mpoly lp)
    comp_mpoly_is_multiplicative.

End MPolyCompComm.

(* -------------------------------------------------------------------- *)
Section MPolyCompHomo.
Context (n : nat) (R : ringType).
Implicit Types (p q : {mpoly R[n]}).

Lemma comp_mpoly_id p : p \mPo [tuple 'X_i | i < n] = p.
Proof.
rewrite [p]mpolyE raddf_sum /=; apply/eq_bigr.
move=> m _; rewrite comp_mpolyZ; congr (_ *: _).
rewrite /comp_mpoly mmapX -mmap1_id; apply/mmap1_eq.
by move=> /= i; rewrite tnth_map tnth_ord_tuple.
Qed.

End MPolyCompHomo.

(* -------------------------------------------------------------------- *)
Section MEval.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}) (v : 'I_n -> R).

Definition meval v p := mmap idfun v p.

Lemma mevalE v p : meval v p = \sum_(m <- msupp p) p@_m * \prod_i v i ^+ m i.
Proof. by []. Qed.

Lemma meval_is_additive v : additive (meval v).
Proof. exact/mmap_is_additive. Qed.

HB.instance Definition _ v := GRing.isAdditive.Build {mpoly R[n]} R (meval v)
  (meval_is_additive v).

Lemma meval0   v   : meval v 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mevalN   v   : {morph meval v: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mevalD   v   : {morph meval v: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mevalB   v   : {morph meval v: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mevalMn  v k : {morph meval v: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mevalMNn v k : {morph meval v: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma mevalC v c : meval v c%:MP = c.
Proof. by rewrite [LHS]mmapC. Qed.

Lemma meval1 v : meval v 1 = 1.
Proof. exact/mevalC. Qed.

Lemma mevalXU v i : meval v 'X_i = v i.
Proof. by rewrite [LHS]mmapX mmap1U. Qed.

Lemma mevalX v m : meval v 'X_[m] = \prod_(i < n) (v i) ^+ (m i).
Proof. by rewrite [LHS]mmapX. Qed.

Lemma meval_is_scalable v : scalable_for *%R (meval v).
Proof. by move=> /= c p; rewrite [LHS]mmapZ. Qed.

Lemma mevalZ v c p : meval v (c *: p) = c * (meval v p).
Proof. exact: meval_is_scalable. Qed.

Lemma meval_eq v1 v2 p : v1 =1 v2 -> meval v1 p = meval v2 p.
Proof.
move=> eq_v; rewrite !mevalE; apply/eq_bigr=> i _.
by congr *%R; apply/eq_bigr=> j _; rewrite eq_v.
Qed.

End MEval.

Notation "p .@[ v ]" := (@meval _ _ v p).
Notation "p .@[< v >]" := (@meval _ _ (nth v) p).

(* -------------------------------------------------------------------- *)
Section MEvalCom.
Context (n k : nat) (R : comRingType).
Implicit Types (p q r : {mpoly R[n]}) (v : 'I_n -> R).

Lemma meval_is_lrmorphism v : scalable_for *%R (meval v).
Proof. by move=> /= c p; rewrite /meval mmapZ /=. Qed.

HB.instance Definition _ v := GRing.RMorphism.copy (meval v) (meval v).

HB.instance Definition _ v :=
  GRing.isScalable.Build R {mpoly R[n]} R *%R (meval v)
    (meval_is_lrmorphism v).

Lemma mevalM v : {morph meval v: x y / x * y}.
Proof. exact: rmorphM. Qed.

End MEvalCom.

(* -------------------------------------------------------------------- *)
Section MEvalComp.
Context (n k : nat) (R : comRingType) (v : 'I_n -> R) (p : {mpoly R[k]}).
Context (lq : k.-tuple {mpoly R[n]}).

Lemma comp_mpoly_meval : (p \mPo lq).@[v] = p.@[fun i => (tnth lq i).@[v]].
Proof.
rewrite comp_mpolyEX [X in _ = X.@[_]](mpolyE p) !raddf_sum /=.
apply/eq_bigr => m _; rewrite !mevalZ; congr *%R.
rewrite comp_mpolyX rmorph_prod /= mevalX.
by apply/eq_bigr=> i _; rewrite rmorphXn.
Qed.

End MEvalComp.

(* -------------------------------------------------------------------- *)
Section MPolyMap.
Context (n : nat) (R S : ringType).
Implicit Types (p q r : {mpoly R[n]}).

Definition map_mpoly (f : R -> S) p : {mpoly S[n]} :=
  mmap ((@mpolyC n _) \o f) (fun i => 'X_i) p.

Section Additive.
Context (f : {additive R -> S}).

Local Notation "p ^f" := (map_mpoly f p).

Lemma map_mpoly_is_additive : additive (map_mpoly f).
Proof. exact/mmap_is_additive. Qed.

HB.instance Definition _ := GRing.isAdditive.Build {mpoly R[n]} {mpoly S[n]}
  (map_mpoly f) map_mpoly_is_additive.

Lemma map_mpolyC c : map_mpoly f c%:MP_[n] = (f c)%:MP_[n].
Proof. by rewrite [LHS]mmapC. Qed.

Lemma map_mpolyE p k : msize p <= k ->
  p^f = \sum_(m : 'X_{1..n < k}) (f p@_m) *: 'X_[m].
Proof.
rewrite /map_mpoly; move/mmapE=> -> /=; apply/eq_bigr.
by move=> i _; rewrite mmap1_id mul_mpolyC.
Qed.
Arguments map_mpolyE [p].

Lemma mcoeff_map_mpoly m p : p^f@_m = f p@_m.
Proof.
pose_big_enough i; first rewrite (map_mpolyE i) //.
  by rewrite (mcoeff_mpoly (fun m => (f p@_m))).
by close.
Qed.

End Additive.

Section Multiplicative.
Context (f : {rmorphism R -> S}).

Local Notation "p ^f" := (map_mpoly f p).

Lemma map_mpoly_is_multiplicative : multiplicative (map_mpoly f).
Proof.
apply/commr_mmap_is_multiplicative => /=.
+ by move=> i x; apply/commr_mpolyX.
+ by move=> p m m'; rewrite mmap1_id; apply/commr_mpolyX.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {mpoly R[n]} {mpoly S[n]} (map_mpoly f)
    map_mpoly_is_multiplicative.

Lemma map_mpolyX (m : 'X_{1..n}) :
  map_mpoly f 'X_[m] = 'X_[m].
Proof. by rewrite /map_mpoly mmapX mmap1_id. Qed.

Lemma map_mpolyZ (c : R) (p : {mpoly R[n]}) :
  map_mpoly f (c *: p) = (f c) *: (map_mpoly f p).
Proof. by rewrite /map_mpoly mmapZ /= mul_mpolyC. Qed.

Lemma msupp_map_mpoly p :
  injective f -> perm_eq (msupp (map_mpoly f p)) (msupp p).
Proof.
move=> inj_f; apply/uniq_perm; rewrite ?msupp_uniq //=.
by move=> m; rewrite !mcoeff_msupp mcoeff_map_mpoly raddf_eq0.
Qed.

End Multiplicative.
End MPolyMap.

(* -------------------------------------------------------------------- *)
Section MPolyMapComp.
Context (n k : nat) (R S : ringType) (f : {rmorphism R -> S}).
Context (lq : n.-tuple {mpoly R[k]}) (p : {mpoly R[n]}).

Local Notation "p ^f" := (map_mpoly f p).

Lemma map_mpoly_comp : injective f ->
  (p \mPo lq)^f = (p^f) \mPo [tuple of [seq map_mpoly f q | q <- lq]].
Proof.
move=> inj_f; apply/mpolyP=> m; rewrite mcoeff_map_mpoly.
rewrite !raddf_sum (perm_big _ (msupp_map_mpoly _ inj_f)) /=.
apply/eq_bigr=> m' _; rewrite mcoeff_map_mpoly !mcoeffCM rmorphM /=.
congr *%R; rewrite /mmap1 -mcoeff_map_mpoly rmorph_prod /=.
by congr _@__; apply/eq_bigr=> i /=; rewrite tnth_map rmorphXn.
Qed.

End MPolyMapComp.

(* -------------------------------------------------------------------- *)
Section MPolyOver.
Context (n : nat) (R : ringType).

Definition mpolyOver_pred (S : {pred R}) :=
  fun p : {mpoly R[n]} => all (mem S) [seq p@_m | m <- msupp p].
Arguments mpolyOver_pred _ _ /.
Definition mpolyOver (S : {pred R}) := [qualify a p | mpolyOver_pred S p].

Lemma mpolyOverS (S1 S2 : {pred R}) :
  {subset S1 <= S2} -> {subset mpolyOver S1 <= mpolyOver S2}.
Proof.
move=> sS12 p /(all_nthP 0)S1p.
by apply/(all_nthP 0)=> i /S1p; apply: sS12.
Qed.

Lemma mpolyOver0 S: 0 \is a mpolyOver S.
Proof. by rewrite qualifE /= msupp0. Qed.

Lemma mpolyOver_mpoly (S : {pred R}) E :
     (forall m : 'X_{1..n}, m \in dom E -> coeff m E \in S)
  -> [mpoly E] \is a mpolyOver S.
Proof.
move=> S_E; apply/(all_nthP 0)=> i; rewrite size_map /= => lt.
by rewrite (nth_map 0%MM) // mcoeff_MPoly S_E ?mem_nth.
Qed.

Section MPolyOverAdd.
Variable S : addrClosed R.

Lemma mpolyOverP {p} : reflect (forall m, p@_m \in S) (p \in mpolyOver S).
Proof.
case: p=> E; rewrite qualifE /=; apply: (iffP allP); last first.
  by move=> h x /mapP /= [m m_in_E] ->; apply/h.
move=> h m; case: (boolP (m \in msupp (MPoly E))).
  by move=> m_in_E; apply/h/map_f.
  by rewrite -mcoeff_eq0 => /eqP->; rewrite rpred0.
Qed.

Lemma mpolyOverC c : (c%:MP \in mpolyOver S) = (c \in S).
Proof.
rewrite qualifE /= msuppC; case: eqP=> [->|] //=;
by rewrite ?rpred0 // andbT mcoeffC eqxx mulr1.
Qed.

Lemma mpolyOver_addr_closed : addr_closed (mpolyOver S).
Proof.
split=> [|p q Sp Sq]; first exact: mpolyOver0.
by apply/mpolyOverP=> i; rewrite mcoeffD rpredD ?(mpolyOverP _).
Qed.

HB.instance Definition _ :=
  GRing.isAddClosed.Build {mpoly R[n]} (mpolyOver_pred S)
    mpolyOver_addr_closed.

End MPolyOverAdd.

Lemma mpolyOverNr (addS : zmodClosed R) : oppr_closed (mpolyOver addS).
Proof.
by move=> p /mpolyOverP Sp; apply/mpolyOverP=> i; rewrite mcoeffN rpredN.
Qed.

HB.instance Definition _ (addS : zmodClosed R) :=
  GRing.isOppClosed.Build {mpoly R[n]} (mpolyOver_pred addS)
    (@mpolyOverNr addS).

Section MPolyOverSemiring.
Variable S : semiringClosed R.

Lemma mpolyOver_mulr_closed : mulr_closed (mpolyOver S).
Proof.
split=> [|p q /mpolyOverP Sp /mpolyOverP Sq].
  by rewrite mpolyOverC rpred1.
apply/mpolyOverP=> i; rewrite mcoeffM rpred_sum //.
by move=> j _; apply: rpredM.
Qed.

HB.instance Definition _ :=
  GRing.isMulClosed.Build {mpoly R[n]} (mpolyOver_pred S)
    mpolyOver_mulr_closed.

Lemma mpolyOverZ : {in S & mpolyOver S, forall c p, c *: p \is a mpolyOver S}.
Proof.
move=> c p Sc /mpolyOverP Sp; apply/mpolyOverP=> i.
by rewrite mcoeffZ rpredM ?Sp.
Qed.

Lemma mpolyOverX m : 'X_[m] \in mpolyOver S.
Proof. by rewrite qualifE /= msuppX /= mcoeffX eqxx rpred1. Qed.

Lemma rpred_mhorner :
  {in mpolyOver S, forall p (v : 'I_n -> R),
     [forall i : 'I_n, v i \in S] -> p.@[v] \in S}.
Proof.
move=> p /mpolyOverP Sp v Sv; rewrite mevalE rpred_sum // => m _.
rewrite rpredM // rpred_prod //= => /= i _.
by rewrite rpredX //; move/forallP: Sv; apply; apply/mem_tnth.
Qed.

End MPolyOverSemiring.

Section MPolyOverRing.
Variable S : subringClosed R.

HB.instance Definition _ :=
  GRing.isMulClosed.Build {mpoly R[n]} (mpolyOver_pred S)
    (mpolyOver_mulr_closed S).

Lemma mpolyOverXaddC m c : ('X_[m] + c%:MP \in mpolyOver S) = (c \in S).
Proof. by rewrite rpredDl ?mpolyOverX ?mpolyOverC. Qed.

End MPolyOverRing.
End MPolyOver.
Arguments mpolyOver_pred _ _ _ _ /.

(* -------------------------------------------------------------------- *)
Section MPolyIdomain.
Context (n : nat) (R : idomainType).
Implicit Types (p q r : {mpoly R[n]}).

Lemma mleadM p q : p != 0 -> q != 0 -> mlead (p * q) = (mlead p + mlead q)%MM.
Proof.
move=> nz_p nz_q; rewrite mleadM_proper //.
by rewrite mulf_neq0 // mleadc_eq0.
Qed.

Lemma mlead_prod (T : eqType) (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}) :
     (forall x, x \in r -> P x -> F x != 0)
  -> mlead (\prod_(p <- r | P p) F p) = (\sum_(p <- r | P p) mlead (F p))%MM.
Proof.
move=> nz_Fr; rewrite mlead_prod_proper // => x x_in_r Px.
apply/lregP; rewrite mleadc_eq0; exact/nz_Fr.
Qed.

Lemma mleadX p k : p != 0 -> mlead (p ^+ k) = (mlead p *+ k)%MM.
Proof.
by move=> nz_p; rewrite mleadX_proper //; apply/lregP; rewrite mleadc_eq0.
Qed.

Lemma mleadZ c p : c != 0 -> mlead (c *: p) = mlead p.
Proof.
move=> nz_c; have [->|nz_p] := eqVneq p 0; first by rewrite scaler0.
by rewrite mleadZ_proper // mulf_neq0 // mleadc_eq0.
Qed.

Lemma mleadcZE a p : mleadc (a *: p) = a * mleadc p.
Proof.
have [->|Za] := eqVneq a 0; last by rewrite mleadZ // mcoeffZ.
by rewrite scale0r mleadc0 mul0r.
Qed.

Lemma msizeM p q : p != 0 -> q != 0 -> msize (p * q) = (msize p + msize q).-1.
Proof. by move=> nz_p nz_q; rewrite msizeM_proper ?mulf_neq0 // mleadc_eq0. Qed.

Lemma msuppZ c p : c != 0 -> perm_eq (msupp (c *: p)) (msupp p).
Proof.
move=> nz_c; apply/uniq_perm=> // m.
by rewrite !mcoeff_msupp mcoeffZ mulf_eq0 (negbTE nz_c).
Qed.

Lemma mscalerI a p : (a *: p == 0) = (a == 0) || (p == 0).
Proof.
have [/eqP->| /(msuppZ p)/perm_size] := boolP (a == 0).
  by rewrite scale0r eqxx.
by rewrite -!msupp_eq0; case: msupp => [|a1 l1]; case: msupp.
Qed.

Lemma mmeasureZ c p mf : c != 0 -> mmeasure mf (c *: p) = mmeasure mf p.
Proof. by move=> nz_c; rewrite !mmeasureE; apply/perm_big/msuppZ. Qed.

Lemma msizeZ c p : c != 0 -> msize (c *: p) = msize p.
Proof. exact/mmeasureZ. Qed.

Lemma mpoly_idomainAxiom p q : p * q = 0 -> (p == 0) || (q == 0).
Proof.
apply: contra_eqT => /norP[nz_p nz_q]; rewrite -msize_poly_eq0 msizeM //.
by rewrite (mpolySpred _ nz_p) (mpolySpred _ nz_q) addnS.
Qed.

Definition mpoly_unit : pred {mpoly R[n]} :=
  fun p => (p == (p@_0)%:MP) && (p@_0 \in GRing.unit).

Definition mpoly_inv p :=
  if p \in mpoly_unit then (p@_0)^-1%:MP else p.

Lemma mpoly_mulVp : {in mpoly_unit, left_inverse 1 mpoly_inv *%R}.
Proof.
move=> p Up; rewrite /mpoly_inv Up; case/andP: Up.
by move/eqP=> {3}->; rewrite -mpolyCM => /mulVr ->.
Qed.

Lemma mpoly_intro_unit p q : q * p = 1 -> p \in mpoly_unit.
Proof.
move=> qp1; apply/andP; split; last first.
  apply/unitrP; exists q@_0.
  by rewrite 2!mulrC -rmorphM qp1 rmorph1.
apply/eqP/msize1_polyC; have: msize (q * p) == 1%N.
  by rewrite qp1 msize1.
have [-> | nz_p] := eqVneq p 0; first by rewrite mulr0 msize0.
have [-> | nz_q] := eqVneq q 0; first by rewrite mul0r msize0.
rewrite msizeM // (mpolySpred _ nz_p) (mpolySpred _ nz_q).
by rewrite addnS addSn !eqSS addn_eq0 => /andP[] _ /eqP->.
Qed.

Lemma mpoly_inv_out : {in [predC mpoly_unit], mpoly_inv =1 id}.
Proof.  by rewrite /mpoly_inv => p /negbTE /= ->. Qed.

HB.instance Definition _ := GRing.ComRing_hasMulInverse.Build (mpoly n R)
  mpoly_mulVp mpoly_intro_unit mpoly_inv_out.
HB.instance Definition _ := GRing.ComUnitRing.on {mpoly R[n]}.

#[hnf]
HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build (mpoly n R)
  mpoly_idomainAxiom.
#[hnf]
HB.instance Definition _ := GRing.IntegralDomain.on {mpoly R[n]}.

End MPolyIdomain.

(* -------------------------------------------------------------------- *)
Section MWeightTheory.
Context (n : nat) (R : ringType).
Implicit Types (m : 'X_{1..n}) (p : {mpoly R[n]}).

Lemma leq_mdeg_mnmwgt m : mdeg m <= mnmwgt m.
Proof.
rewrite /mnmwgt mdegE leq_sum //= => i _; exact: leq_pmulr.
Qed.

Lemma leq_msize_meight p : msize p <= mweight p.
Proof.
rewrite !mmeasureE; elim: (msupp p)=> [|m r ih].
  by rewrite !big_nil.
rewrite !big_cons geq_max !leq_max !ltnS.
by rewrite leq_mdeg_mnmwgt /= ih orbT.
Qed.

End MWeightTheory.

(* -------------------------------------------------------------------- *)
Section MPerm.
Context (n : nat) (R : ringType).
Implicit Types (m : 'X_{1..n}).

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma mperm_inj (s : 'S_n) : injective (fun m => m#s).
Proof.
move=> m1 m2 /= /mnmP h; apply/mnmP=> i.
by move: (h (s^-1 i)%g); rewrite !mnmE permKV.
Qed.

Lemma mperm1 m : m#(1 : 'S_n)%g = m.
Proof. by apply/mnmP=> i; rewrite mnmE perm1. Qed.

Lemma mpermM m (s1 s2 : 'S_n) : m#(s1 * s2)%g = m#s2#s1.
Proof. by apply/mnmP=> i; rewrite !mnmE permM. Qed.

Lemma mpermKV (s : 'S_n) : cancel (fun m => m#s) (fun m => m#(s^-1))%g.
Proof. by move=> m /=; apply/mnmP=> i; rewrite !mnmE permKV. Qed.

Lemma mpermK (s : 'S_n) : cancel (fun m => m#(s^-1))%g (fun m => m#s).
Proof. by move=> m /=; apply/mnmP=> i; rewrite !mnmE permK. Qed.

Lemma mdeg_mperm m (s : 'S_n) : mdeg (m#s) = mdeg m.
Proof.
rewrite !mdegE (reindex_inj (h := s^-1))%g /=; last exact/perm_inj.
by apply/eq_bigr=> j _; rewrite !mnmE permKV.
Qed.

End MPerm.

(* -------------------------------------------------------------------- *)
Section MPolySym.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}).

Definition msym (s : 'S_n) p : {mpoly R[n]} :=
  mmap (@mpolyC n R) (fun i => 'X_(s i)) p.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma msymE p (s : 'S_n) k : msize p <= k ->
  msym s p = \sum_(m : 'X_{1..n < k}) (p@_m *: 'X_[m#(s^-1)%g]).
Proof.
move=> lt_pk; rewrite /msym (mmapE k) //=; apply/eq_bigr.
move=> m' _; rewrite mul_mpolyC; congr (_ *: _).
rewrite /mmap1 mprodXnE [X in _=X]mpolyXE_id mprodXnE.
rewrite [X in _='X_[X]](reindex (fun i : 'I_n => s i)) /=.
  congr 'X_[_]; apply/eq_bigr=> i _; congr (_ *+ _)%MM.
  by rewrite mnmE /= permK.
by exists (s^-1)%g=> i _; rewrite (permK, permKV).
Qed.

Arguments msymE [p].

Lemma mcoeff_sym p (s : 'S_n) m : (msym s p)@_m = p@_(m#s).
Proof.
pose_big_enough i; first rewrite (msymE s i) //.
  apply/esym; rewrite {1}[p](mpolywE (k := i)) //.
  rewrite !raddf_sum /=; apply/eq_bigr=> j _.
  rewrite !mcoeffZ !mcoeffX; congr (_ * _).
  have bijF: bijective (fun (m : 'X_{1..n}) => m#(s^-1)%g).
    exists (fun (m : 'X_{1..n}) => m#s) => m'.
    + by apply/mnmP=> k; rewrite !mnmE permK.
    + by apply/mnmP=> k; rewrite !mnmE permKV.
  rewrite -(bij_eq bijF); have ->//: m#s#(s^-1)%g = m.
  by apply/mnmP=> k; rewrite !mnmE /= permKV.
by close.
Qed.

Lemma msymX m s : msym s 'X_[m] = 'X_[m#(s^-1)%g].
Proof.
apply/mpolyP=> m'; rewrite mcoeff_sym !mcoeffX.
congr (_ : bool)%:R; apply/eqP/eqP=> [->|<-].
+ by apply/mnmP=> i; rewrite !mnmE permKV.
+ by apply/mnmP=> i; rewrite !mnmE permK.
Qed.

Lemma msym_is_additive s: additive (msym s).
Proof. exact/mmap_is_additive. Qed.

HB.instance Definition _ s :=
  GRing.isAdditive.Build {mpoly R[n]} {mpoly R[n]} (msym s)
    (msym_is_additive s).

Lemma msym0   s   : msym s 0 = 0               . Proof. exact: raddf0. Qed.
Lemma msymN   s   : {morph msym s: x / - x}    . Proof. exact: raddfN. Qed.
Lemma msymD   s   : {morph msym s: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma msymB   s   : {morph msym s: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma msymMn  s k : {morph msym s: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma msymMNn s k : {morph msym s: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma msym_is_multiplicative s : multiplicative (msym s).
Proof.
apply/commr_mmap_is_multiplicative => [i x|p m1 m2]; first exact/commr_mpolyX.
rewrite /= /mmap1; elim/big_rec: _ => [|i q _]; first exact/commr1.
exact/commrM/commrX/commr_mpolyX.
Qed.

HB.instance Definition _ s :=
  GRing.isMultiplicative.Build {mpoly R[n]} {mpoly R[n]} (msym s)
    (msym_is_multiplicative s).

Lemma msym1 s : msym s 1 = 1.
Proof. exact: rmorph1. Qed.

Lemma msymM s : {morph msym s: x y / x * y}.
Proof. exact: rmorphM. Qed.

Lemma msymZ c p s : msym s (c *: p) = c *: (msym s p).
Proof.
pose_big_enough i; first rewrite !(msymE s i) //.
  rewrite scaler_sumr; apply/eq_bigr => j _.
  by rewrite mcoeffZ scalerA.
by close.
Qed.

HB.instance Definition _ s :=
  GRing.isScalable.Build R {mpoly R[n]} {mpoly R[n]} *:%R (msym s)
    (fun c => (msymZ c)^~ s).

Definition symmetric_pred : pred {mpoly R[n]} :=
  fun p => [forall s, msym s p == p].
Arguments symmetric_pred _ /.
Definition symmetric : qualifier 0 {mpoly R[n]} :=
  [qualify p | symmetric_pred p].

Lemma issymP p : reflect (forall s, msym s p = p) (p \is symmetric).
Proof.
apply: (iffP forallP)=> /= h s; last by rewrite h.
by rewrite (eqP (h s)).
Qed.

Lemma sym_zmod : zmod_closed symmetric.
Proof.
split=> [|p q /issymP sp /issymP sq]; apply/issymP=> s.
  by rewrite msym0.
by rewrite msymB sp sq.
Qed.

HB.instance Definition _ :=
  GRing.isZmodClosed.Build {mpoly R[n]} symmetric_pred sym_zmod.

Lemma sym_mulr_closed : mulr_closed symmetric.
Proof.
split=> [|p q /issymP sp /issymP sq]; apply/issymP=> s.
  by rewrite msym1.
by rewrite msymM sp sq.
Qed.

HB.instance Definition _ := GRing.isMulClosed.Build {mpoly R[n]} symmetric_pred
  sym_mulr_closed.

Lemma sym_submod_closed : submod_closed symmetric.
Proof.
split=> [|c p q /issymP sp /issymP sq]; apply/issymP=> s.
  by rewrite msym0.
by rewrite msymD msymZ sp sq.
Qed.

HB.instance Definition _ :=
  GRing.isSubmodClosed.Build R {mpoly R[n]} symmetric_pred
    sym_submod_closed.

Lemma issym_msupp p (s : 'S_n) (m : 'X_{1..n}) : p \is symmetric ->
  (m#s \in msupp p) = (m \in msupp p).
Proof. by rewrite !mcoeff_msupp -mcoeff_sym => /issymP ->. Qed.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma msym_coeff (p : {mpoly R[n]}) (m : 'X_{1..n}) (s : 'S_n) :
  p \is symmetric -> p@_(m#s) = p@_m.
Proof.
move/issymP=> /(_ s^-1)%g {1}<-; rewrite mcoeff_sym.
by congr (_@__); apply/mnmP=> i /=; rewrite !mnmE permKV.
Qed.

Lemma msym1m p : msym 1 p = p.
Proof. by apply/mpolyP=> m; rewrite mcoeff_sym mperm1. Qed.

Lemma msymMm p (s1 s2 : 'S_n) : msym (s1 * s2)%g p = msym s2 (msym s1 p).
Proof. by apply/mpolyP=> m; rewrite !mcoeff_sym mpermM. Qed.

Lemma inj_msym (s : 'S_n) : injective (msym s).
Proof.
move=> p q; move/(congr1 (msym s^-1)%g).
by rewrite -!msymMm mulgV !msym1m.
Qed.

Lemma mlead_msym_sorted (p : {mpoly R[n]}) : p \is symmetric ->
  forall (i j : 'I_n), i <= j -> (mlead p) j <= (mlead p) i.
Proof.
move=> sym_p i j le_ij; have [->|nz_p] := eqVneq p 0.
  by rewrite mlead0 !mnm0E.
set m := mlead p; case: leqP=> // h.
pose s := tperm i j; pose ms := m#s; have: (m < ms)%O.
  apply/ltmcP; first by rewrite mdeg_mperm.
  exists i=> [k lt_ki|]; last by rewrite mnmE tpermL.
  rewrite mnmE tpermD // neq_ltn orbC ?lt_ki //.
  by move/leq_trans: lt_ki => /(_ _ le_ij) ->.
have: ms \in msupp p by rewrite issym_msupp // mlead_supp.
by move/msupp_le_mlead; rewrite leNgt => /negbTE=> ->.
Qed.

End MPolySym.

Arguments inj_msym  {n R}.
Arguments symmetric_pred _ _ _ /.
Arguments symmetric {n R}.

(* -------------------------------------------------------------------- *)
Section MPolySymComp.
Context (n : nat) (R : ringType).

Lemma mcomp_sym k (p : {mpoly R[n]}) (t : n.-tuple {mpoly R[k]}) :
  (forall i : 'I_n, t`_i \is symmetric) -> p \mPo t \is symmetric.
Proof.
move=> sym_t; pose_big_enough l.
  rewrite (comp_mpolywE _ (w := l)) //. 2: by close.
apply/rpred_sum=> m _; apply/rpredZ/rpred_prod=> i _.
by rewrite (tnth_nth 0); apply/rpredX/sym_t.
Qed.

End MPolySymComp.

(* -------------------------------------------------------------------- *)
Section MPolySymCompCom.
Context (n : nat) (R : comRingType).

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma msym_mPo (s : 'S_n) (p : {mpoly R[n]}) k (T : n.-tuple {mpoly R[k]}) :
  (msym s p) \mPo T = p \mPo [tuple tnth T (s i) | i < n].
Proof.
pose_big_enough l; [rewrite !(comp_mpolywE _ (w := l)) // | by close].
have FP (m : 'X_{1..n < l}) : mdeg (m#s) < l by rewrite mdeg_mperm bmdeg.
pose F (m : 'X_{1..n < l}) := BMultinom (FP m).
have inj_F: injective F.
  by move=> m1 m2 /(congr1 val) /mperm_inj /val_inj.
rewrite [RHS](reindex_inj inj_F); apply/eq_bigr=> m _ /=.
rewrite mcoeff_sym (reindex_inj (@perm_inj _ s)) /=; congr (_ *: _).
by apply/eq_bigr=> i _; rewrite mnmE tnth_mktuple.
Qed.

Lemma msym_comp_poly k (p : {mpoly R[n]}) (t : n.-tuple {mpoly R[k]}) :
     p \is symmetric
  -> (forall s : 'S_k, perm_eq t [tuple (msym s t`_i) | i < n])
  -> p \mPo t \is symmetric.
Proof.
move=> sym_p sym_t; apply/issymP=> s; pose_big_enough l.
  rewrite (comp_mpolywE _ (w := l)) //. 2: by close.
case/tuple_permP: (sym_t s^-1)%g => s' tE.
pose F (m : 'X_{1..n < l}) := insubd m [multinom m (s' i) | i < n].
have FE m: F m = [multinom m (s' i) | i < n] :> 'X_{1..n}.
  by rewrite insubdK // -topredE /= mdeg_mperm ?bmdeg.
rewrite raddf_sum {1}(reindex_inj (h := F)) /=; last first.
  move=> m1 m2 /(congr1 (@bmnm _ _)); rewrite !FE.
  by move/mperm_inj=> /val_inj.
apply/eq_bigr=> m _; rewrite linearZ /= FE msym_coeff //.
rewrite rmorph_prod /= (reindex_inj (perm_inj (s := s'^-1))) /=.
congr (_ *: _); apply/eq_bigr=> i _; rewrite rmorphXn /=.
rewrite mnmE permKV (tnth_nth 0) {1}tE -!tnth_nth.
rewrite !tnth_map !tnth_ord_tuple permKV -msymMm.
by rewrite mulVg msym1m -tnth_nth.
Qed.

End MPolySymCompCom.

(* -------------------------------------------------------------------- *)
Section MPolySymUnit.
Context (n : nat) (R : idomainType).
Implicit Types (p q r : {mpoly R[n]}).

Lemma msymMK (p q : {mpoly R[n]}) :
  p != 0 -> p \is symmetric -> p * q \is symmetric -> q \is symmetric.
Proof.
move=> nz_p /issymP sym_p /issymP sym_pq; apply/issymP => s.
by move/(_ s): sym_pq; rewrite msymM sym_p => /(mulfI nz_p).
Qed.

Lemma sym_divring : divring_closed (symmetric (n := n) (R := R)).
Proof.
split; try solve [apply/rpred1 | apply/rpredB].
move=> p q sym_p sym_q /=; case: (boolP (q \isn't a GRing.unit)).
  by move/invr_out=> ->; apply/rpredM.
rewrite negbK=> inv_q; apply/(msymMK _ sym_q).
  by apply/contraTneq: inv_q=> ->; rewrite unitr0.
by rewrite mulrCA divrr // mulr1.
Qed.

HB.instance Definition _ :=
  GRing.isDivringClosed.Build {mpoly R[n]}
    (@symmetric_pred n R)
    sym_divring.

End MPolySymUnit.

(* -------------------------------------------------------------------- *)
Section MElemPolySym.
Context (n : nat) (R : ringType).
Implicit Types (p q r : {mpoly R[n]}) (h : {set 'I_n}).

Definition mesym (k : nat) : {mpoly R[n]} :=
  \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i.

Local Notation "''s_' k" := (@mesym k).

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Definition mesym1 (h : {set 'I_n}) := [multinom i \in h | i < n].

Lemma mesym1_set0 : mesym1 set0 = 0%MM.
Proof. by apply/mnmP=> i; rewrite mnmE mnm0E in_set0. Qed.

Lemma mesym1_set1 i : mesym1 [set i] = U_(i)%MM.
Proof. by apply/mnmP=> j; rewrite mnmE in_set1 mnmE eq_sym. Qed.

Lemma mesym1_setT : mesym1 setT = (\sum_(i < n) U_(i))%MM.
Proof.
apply/mnmP=> i; rewrite mnmE mnm_sumE in_setT /=.
rewrite (bigD1 i) //= mnmE eqxx big1 ?addn0 //.
by move=> j; rewrite mnmE => /negbTE->.
Qed.

Lemma mesymE k : 's_k = \sum_(h : {set 'I_n} | #|h| == k) 'X_[mesym1 h].
Proof.
apply/eq_bigr=> /= h _; rewrite mprodXE; congr 'X_[_].
apply/mnmP=> i; rewrite mnmE mnm_sumE big_mkcond /=.
rewrite (bigD1 i) //= mnmE eqxx /= big1 ?addn0 // => j ne_ji.
by case: (_ \in _); rewrite // mnmE (negbTE ne_ji).
Qed.

Lemma mdeg_mesym1 h : mdeg (mesym1 h) = #|h|.
Proof.
rewrite mdegE (bigID (mem h)) /= addnC big1 ?add0n; last first.
  by move=> i i_notin_h; rewrite mnmE (negbTE i_notin_h).
rewrite (eq_bigr (fun _ => 1%N)) ?sum1_card //.
by move=> i i_in_h; rewrite mnmE i_in_h.
Qed.

Lemma inj_mesym1 : injective mesym1.
Proof.
move=> h1 h2 /mnmP eqh; apply/setP=> /= i.
by have := eqh i; rewrite !mnmE; do! case: (_ \in _).
Qed.

Local Hint Resolve inj_mesym1 : core.

Lemma msupp_mesym k :
  perm_eq
    (msupp 's_k)
    [seq mesym1 h | h : {set 'I_n} <- enum {set 'I_n} & #|h| == k].
Proof.
rewrite mesymE; apply/(perm_trans (msupp_sum _ _ _))=> /=.
+ by rewrite /index_enum -enumT enum_uniq.
+ move=> h1 h2 _ _ ne_h1h2 m /=; rewrite !msuppX !mem_seq1.
  apply/negbTE/negP=> /andP[/eqP->] /eqP /inj_mesym1.
  by move/eqP; rewrite (negbTE ne_h1h2).
rewrite /index_enum -enumT /= (eq_map (fun h => msuppX _ (mesym1 h))).
by rewrite (map_comp (cons^~ [::])) flatten_seq1.
Qed.

Lemma msupp_mesymP (k : nat) m :
  (m \in msupp 's_k) = [exists h : {set 'I_n}, (#|h| == k) && (m == mesym1 h)].
Proof.
rewrite (perm_mem (msupp_mesym _)); apply/idP/existsP=> /=.
+ case/mapP=> /= h; rewrite mem_filter=> /andP[/eqP<- _ ->].
  by exists h; rewrite !eqxx.
+ case=> h /andP[/eqP<- /eqP->]; apply/mapP; exists h=> //.
  by rewrite mem_filter eqxx /= mem_enum.
Qed.

Definition mechar k (m : 'X_{1..n}) := (mdeg m == k) && [forall i, m i <= 1%N].

Lemma mecharP k m :
  mechar k m = [exists h : {set 'I_n}, (m == mesym1 h) && (#|h| == k)].
Proof.
apply/idP/existsP=> /=; last first.
  case=> h /andP[/eqP-> /eqP<-]; rewrite /mechar.
  rewrite mdeg_mesym1 eqxx /=; apply/forallP=> /= i.
  by rewrite mnmE leq_b1.
case/andP=> /eqP<- /forallP /= mE; exists [set i | m i != 0%N].
apply/andP; split; [apply/eqP/mnmP=> i|apply/eqP].
  by rewrite mnmE inE; have := mE i; case: (m i)=> [|[|]].
rewrite mdegE (bigID (fun i => m i == 0%N)) /=.
rewrite big1 ?add0n; last by move=> i /eqP->.
rewrite (eq_bigr (fun _ => 1%N)) ?sum1_card ?cardsE //.
by move=> i; have := mE i; case: (m i) => [|[|]].
Qed.

Lemma mcoeff_mesym (k : nat) m : ('s_k)@_m = (mechar k m)%:R.
Proof.
rewrite mecharP; case: (altP existsP) => /= [[h /andP[/eqP-> /eqP<-]]|].
  rewrite mesymE raddf_sum (bigD1 h) //= mcoeffX eqxx big1 ?addr0 //.
  move=> h' /andP[_ ne_h]; rewrite mcoeffX -[0]/0%:R.
  by congr _%:R; apply/eqP; rewrite eqb0 inj_eq.
rewrite negb_exists=> /forallP /= ne.
rewrite mesymE raddf_sum big1 //= => h cardh; have := ne h.
by rewrite cardh andbT mcoeffX; case: eqVneq.
Qed.

Lemma mem_msupp_mesym k m : m \in msupp 's_k = mechar k m.
Proof.
rewrite mcoeff_msupp mcoeff_mesym.
by case: (mechar _ _); rewrite ?eqxx // oner_eq0.
Qed.

Lemma mperm_mechar k (m : 'X_{1..n}) (s : 'S_n) :
  mechar k (m#s) = mechar k m.
Proof.
rewrite /mechar mdeg_mperm; congr (_ && _).
apply/forallP/forallP=> //=.
+ by move=> h i; move/(_ (s^-1 i))%g: h; rewrite mnmE permKV.
+ by move=> h i; rewrite mnmE; apply/h.
Qed.

Lemma mesym_sym k : 's_k \is symmetric.
Proof.
apply/issymP=> s; apply/mpolyP=> m.
by rewrite mcoeff_sym !mcoeff_mesym mperm_mechar.
Qed.

Lemma mem_mesym1_mesym h : mesym1 h \in msupp 's_#|h|.
Proof.
rewrite mem_msupp_mesym mecharP; apply/existsP.
by exists h; rewrite !eqxx.
Qed.

Lemma mesym0E : 's_0 = 1.
Proof.
rewrite mesymE (bigD1 set0) ?cards0 //= mesym1_set0 mpolyX0.
by rewrite big1 ?addr0 // => i /andP[/eqP/cards0_eq->]; rewrite eqxx.
Qed.

Lemma mesym1E : 's_1 = \sum_(i < n) 'X_i.
Proof.
rewrite mesymE -big_set /=; set S := [set _ | _].
have ->: S = [set [set i] | i : 'I_n].
  apply/eqP; rewrite eqEcard (card_imset _ set1_inj).
  rewrite card_draws /= !card_ord bin1 leqnn andbT.
  apply/subsetP=> /= s; rewrite inE => /cards1P /= [i {s}->].
  by apply/imsetP; exists i.
rewrite big_imset /=; last by move=> i1 i2 _ _; apply/set1_inj.
by apply/eq_bigr=> i _; rewrite mesym1_set1.
Qed.

Lemma mesymnnE : 's_n = \prod_(i < n) 'X_i.
Proof.
rewrite mesymE (bigD1 setT) ?cardsT ?card_ord //=.
rewrite [X in _+X]big1 ?addr0; last first.
  move=> i /andP []; rewrite eqEcard => /eqP ->.
  by rewrite subsetT cardsT card_ord leqnn.
by rewrite mprodXE mesym1_setT.
Qed.

Lemma mesym_geqnE i : i > n -> mesym i = 0.
Proof.
rewrite /mesym => Hn; apply: big1 => s /eqP Hs; exfalso.
by have:= subset_leq_card (subsetT s); rewrite Hs cardsT card_ord leqNgt Hn.
Qed.

Definition mesymlmnm k : {set 'I_n} := [set i : 'I_n | i < k].
Definition mesymlm   k : 'X_{1..n}  := mesym1 (mesymlmnm k).

Let card_mesymlmnm k (le_kn : k <= n) : #|mesymlmnm k| = k.
Proof.
rewrite -sum1dep_card -(big_ord_widen _ (fun _ => 1%N)) //=.
by rewrite sum1_card card_ord.
Qed.

Let mesymlmE k : mesymlm k = [multinom (i < k : nat) | i < n].
Proof. by apply/mnmP=> i; rewrite !mnmE in_set. Qed.

Let mesymlm_max (h : {set 'I_n}) : #|h| <= n -> (mesym1 h <= mesymlm #|h|)%O.
Proof.                        (* FIXME: far too convoluted *)
move=> le_Ch_n; pose P := [exists i : 'I_n, (i < #|h|) && (i \notin h)].
case: (boolP P)=> [/existsP[/= i /andP[lt_ih i_notin_h]]|hNP]; last first.
  suff ->: h = mesymlmnm #|h|; first by rewrite card_mesymlmnm.
  move: hNP; rewrite negb_exists => /forallP /= {P} hNP.
  have eq1: forall i : 'I_n, i < #|h| -> i \in h.
    move=> i lt_i_Ch; move: (hNP i); rewrite negb_and.
    by rewrite lt_i_Ch /= negbK.
  have eq2: forall i : 'I_n, i >= #|h| -> i \notin h.
    move=> i le_Ch_i; apply/negP=> i_in_h; move: (leqnn #|h|).
    rewrite -{1}sum1_card; pose P (j : 'I_n) := j < #|h|.
    rewrite (bigID P) big_andbC (eq_bigl P) {}/P /=; last first.
      move=> j /=; apply/andb_idr=> lt_j_Ch; have := hNP j.
      by rewrite lt_j_Ch /= negbK.
    rewrite -(big_ord_widen _ (fun _ => 1%N)) // sum1_card card_ord.
    rewrite -[X in _<=X]addn0 leq_add2l leqn0; apply/eqP.
    by rewrite (bigD1 i) // -leqNgt le_Ch_i andbT.
  apply/setP=> i; rewrite in_set; case: (leqP #|h| i).
    by move/eq2/negbTE. by move/eq1.
pose i0 : 'I_n := [arg min_(j < i | j \notin h) j].
apply/ltW/ltmcP; first by rewrite !mdeg_mesym1 card_mesymlmnm.
exists i0; rewrite {}/i0; case: arg_minnP => //=.
+ move=> i0 i0_notin_h i0_min j lt_j_i0; rewrite !mnmE in_set.
  rewrite (@ltn_trans i) // 1?(@leq_trans i0) // ?i0_min //.
  by case: (boolP (j \in h))=> // /i0_min; rewrite leqNgt lt_j_i0.
+ move=> i0 i0_notin_h i0_min; rewrite !mnmE in_set.
  by rewrite (negbTE i0_notin_h) lt0n // (@leq_ltn_trans i) // i0_min.
Qed.

Lemma mesym_neq0 k (le_kn : k <= n) : 's_k != 0 :> {mpoly R[n]}.
Proof.
apply/eqP=> z_sk; pose h : {set 'I_n} := mesymlmnm k.
have := mem_mesym1_mesym h; rewrite card_mesymlmnm //.
by rewrite mcoeff_msupp z_sk mcoeff0 eqxx.
Qed.

Lemma mlead_mesym k (le_kn : k <= n) :
  mlead 's_k = [multinom (i < k : nat) | i < n].
Proof.
rewrite -mesymlmE /mlead (bigD1_seq (mesymlm k)) //=; last first.
  rewrite mem_msupp_mesym mecharP; apply/existsP.
  by exists (mesymlmnm k); rewrite card_mesymlmnm ?eqxx.
apply/join_l/joinsP_seq=> /= {}m.
rewrite msupp_mesymP => /existsP[/=].
move=> h /andP[/eqP Chk /eqP->] _; rewrite -Chk.
by apply/mesymlm_max; rewrite Chk.
Qed.

Lemma mleadc_mesym k (le_kn : k <= n) : mleadc 's_k = 1.
Proof.
rewrite mcoeff_mesym; case: (boolP (mechar _ _))=> //=.
by rewrite -mem_msupp_mesym mlead_supp // mesym_neq0.
Qed.

Definition tmono (n : nat) (h : seq 'I_n) :=
  sorted ltn (map val h).

Lemma uniq_tmono (h : seq 'I_n) : tmono h -> uniq h.
Proof.
rewrite /tmono => /sorted_uniq; rewrite (map_inj_uniq val_inj).
by apply; [apply/ltn_trans | move=> ?; rewrite /ltn /= ltnn].
Qed.

Lemma eq_tmono (h1 h2 : seq 'I_n) : tmono h1 -> tmono h2 -> h1 =i h2 -> h1 = h2.
Proof.
move=> tm1 tm2 h; apply/(inj_map val_inj).
apply/(irr_sorted_eq (leT := ltn)) => //.
  exact/ltn_trans.
  by move=> ?; rewrite /ltn /= ltnn.
move=> m; apply/mapP/mapP; case=> /= x;
  by rewrite (h, =^~ h)=> {}h ->; exists x.
Qed.

Lemma mesym_tupleE (k : nat) : 's_k =
  \sum_(h : k.-tuple 'I_n | tmono h) \prod_(i <- h) 'X_i.
Proof.
have tval_tcast T k1 k2 (eq : k1 = k2) (x : k1.-tuple T) :
  tval (tcast eq x) = tval x.
+ by rewrite /tcast; case: k2 / eq.
pose t2s (t : k.-tuple 'I_n) := [set x | x \in t].
rewrite /mesym -[X in X=_]big_set -[X in _=X]big_set /=.
set E := [set t2s x | x in [pred t | tmono (tval t)]].
have h: E = [set i : {set 'I_n} | #|i| == k].
  apply/setP=> /= h; rewrite inE; apply/imsetP/idP=> /=.
  + case=> t; rewrite inE => tmono_t -> /=; rewrite /t2s.
    rewrite cardsE /= -[X in _==X](size_tuple t).
    by apply/eqP/card_uniqP/uniq_tmono.
  + move/eqP=> eq_sz; exists (tcast eq_sz [tuple of (enum h)]).
    * rewrite inE /tmono tval_tcast /=; pose I := enum 'I_n.
      apply/(subseq_sorted _ (s2 := [seq val i | i <- I])).
        exact/ltn_trans.
        by apply/map_subseq; rewrite /enum_mem -enumT; apply/filter_subseq.
        by rewrite val_enum_ord iota_ltn_sorted.
    * by apply/setP=> i; rewrite !(inE, memtE) tval_tcast mem_enum.
rewrite -h {h}/E big_imset 1?big_set /=; last first.
  move=> t1 t2; rewrite !inE => tmono_t1 tmono_t2 /setP eq.
  by apply/val_inj/eq_tmono => // i; move: (eq i); rewrite !inE.
apply/eq_big=> // i; rewrite inE 1?big_set /=.
case: i => i sz_i /= tmono_i; rewrite (eq_bigl (mem i)) //=.
by rewrite !mprodXE big_uniq //; apply/uniq_tmono.
Qed.

End MElemPolySym.

Local Notation "''s_' ( K , n , k )" := (@mesym n K k).
Local Notation "''s_' ( n , k )" := (@mesym n _ k).

(* -------------------------------------------------------------------- *)
Section MWiden.
Context (n : nat) (R : ringType).

Definition mwiden (p : {mpoly R[n]}) : {mpoly R[n.+1]} :=
  mmap (@mpolyC _ _) (fun i => 'X_(widen i)) p.

Definition mnmwiden (m : 'X_{1..n}) : 'X_{1..n.+1} := [multinom of rcons m 0%N].

Lemma mnmwiden_ordmax m : (mnmwiden m) ord_max = 0%N.
Proof.
rewrite multinomE (tnth_nth 0%N) nth_rcons /=.
by rewrite size_tuple ltnn eqxx.
Qed.

Lemma mnmwiden_widen m (i : 'I_n) : (mnmwiden m) (widen i) = m i.
Proof.
case: m=> m; rewrite !(mnm_nth 0%N) nth_rcons.
by rewrite size_tuple /=; case: i => i /= ->.
Qed.

Lemma mnmwiden0 : mnmwiden 0 = 0%MM.
Proof.
apply/mnmP=> i; rewrite mnmE (mnm_nth 0%N) nth_rcons.
case: ssrnat.ltnP; last by rewrite ?if_same.
rewrite size_tuple=> lt_in; pose oi := Ordinal lt_in.
by rewrite (nth_map oi) //; rewrite size_tuple.
Qed.

Lemma mnmwidenD m1 m2 : mnmwiden (m1 + m2) = (mnmwiden m1 + mnmwiden m2)%MM.
Proof.
apply/mnmP=> i; rewrite mnmDE !multinomE !(tnth_nth 0%N) /=.
rewrite !nth_rcons size_map size_enum_ord !size_tuple !if_same.
case h: (i < n); last by rewrite addn0.
rewrite (nth_map (Ordinal h)) ?size_enum_ord //.
by rewrite !(mnm_nth 0%N) /= !nth_enum_ord.
Qed.

Lemma mnmwiden_sum (I : Type) (r : seq I) P F :
    mnmwiden (\sum_(x <- r | P x) (F x))
  = (\sum_(x <- r | P x) (mnmwiden (F x)))%MM.
Proof. exact/big_morph/mnmwiden0/mnmwidenD. Qed.

Lemma mnmwiden1 i : (mnmwiden U_(i) = U_(widen i))%MM.
Proof.
apply/mnmP; case=> j /= lt; rewrite /mnmwiden !mnmE; apply/esym.
rewrite eqE multinomE /tnth /=; move: (tnth_default _ _) => x.
rewrite nth_rcons size_map size_enum_ord; move: lt.
rewrite ltnS leq_eqVlt => /predU1P[->|lt].
  by apply/eqP; rewrite ltnn eqxx eqb0 ltn_eqF.
rewrite lt (nth_map i) ?size_enum_ord //.
by apply/esym; rewrite eqE /= nth_enum_ord.
Qed.

Lemma inj_mnmwiden : injective mnmwiden.
Proof.
move=> m1 m2 /mnmP h; apply/mnmP=> i; move: (h (widen i)).
by rewrite !mnmwiden_widen.
Qed.

Lemma mwiden_is_additive : additive mwiden.
Proof. exact/mmap_is_additive. Qed.

Lemma mwiden0     : mwiden 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mwidenN     : {morph mwiden: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mwidenD     : {morph mwiden: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mwidenB     : {morph mwiden: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mwidenMn  k : {morph mwiden: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mwidenMNn k : {morph mwiden: x / x *- k} . Proof. exact: raddfMNn. Qed.

HB.instance Definition _ :=
  GRing.isAdditive.Build {mpoly R[n]} {mpoly R[n.+1]} mwiden
    mwiden_is_additive.

Lemma mwiden_is_multiplicative : multiplicative mwiden.
Proof.
apply/commr_mmap_is_multiplicative=> [i p|p m m']; first exact/commr_mpolyX.
rewrite /= /mmap1; elim/big_rec: _ => /= [|i q _]; first exact/commr1.
exact/commrM/commrX/commr_mpolyX.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {mpoly R[n]} {mpoly R[n.+1]} mwiden
    mwiden_is_multiplicative.

Lemma mwiden1 : mwiden 1 = 1.
Proof. exact: rmorph1. Qed.

Lemma mwidenM : {morph mwiden: x y / x * y}.
Proof. exact: rmorphM. Qed.

Lemma mwidenC c : mwiden c%:MP = c%:MP.
Proof. by rewrite /mwiden mmapC. Qed.

Lemma mwidenN1 : mwiden (-1) = -1.
Proof. by rewrite raddfN /= mwidenC. Qed.

Lemma mwidenX m : mwiden 'X_[m] = 'X_[mnmwiden m].
Proof.
rewrite /mwiden mmapX /mmap1 /= (mpolyXE _ 1); apply/esym.
rewrite (eq_bigr (fun i => 'X_i ^+ (mnmwiden m i))); last first.
  by move=> i _; rewrite perm1.
rewrite big_ord_recr /= mnmwiden_ordmax expr0 mulr1.
by apply/eq_bigr=> i _; rewrite mnmwiden_widen.
Qed.

Lemma mwidenZ c p : mwiden (c *: p) = c *: mwiden p.
Proof. by rewrite /mwiden mmapZ /= mul_mpolyC. Qed.

Lemma mwidenE (p : {mpoly R[n]}) (k : nat) : msize p <= k ->
  mwiden p = \sum_(m : 'X_{1..n < k}) (p@_m *: 'X_[mnmwiden m]).
Proof.
move=> h; rewrite {1}[p](mpolywE (k := k)) //.
rewrite raddf_sum /=; apply/eq_bigr=> m _.
by rewrite mwidenZ mwidenX.
Qed.

Lemma mwiden_mnmwiden p m : (mwiden p)@_(mnmwiden m) = p@_m.
Proof.
rewrite (mwidenE (k := msize p)) // raddf_sum /=.
rewrite [X in _=X@__](mpolywE (k := msize p)) //.
rewrite raddf_sum /=; apply/eq_bigr=> i _.
by rewrite !mcoeffZ !mcoeffX inj_eq //; apply/inj_mnmwiden.
Qed.

Lemma inj_mwiden : injective mwiden.
Proof.
move=> m1 m2 /mpolyP h; apply/mpolyP=> m.
by move: (h (mnmwiden m)); rewrite !mwiden_mnmwiden.
Qed.

Definition mpwiden (p : {poly {mpoly R[n]}}) : {poly {mpoly R[n.+1]}} :=
  map_poly mwiden p.

Lemma mpwiden_is_additive : additive mpwiden.
Proof. exact: map_poly_is_additive. Qed.

HB.instance Definition _ :=
  GRing.isAdditive.Build {poly {mpoly R[n]}} {poly {mpoly R[n.+1]}}
    mpwiden mpwiden_is_additive.

Lemma mpwiden_is_multiplicative : multiplicative mpwiden.
Proof. exact: map_poly_is_multiplicative. Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {poly {mpoly R[n]}} {poly {mpoly R[n.+1]}}
    mpwiden mpwiden_is_multiplicative.

Lemma mpwidenX : mpwiden 'X = 'X.
Proof. by rewrite /mpwiden map_polyX. Qed.

Lemma mpwidenC c : mpwiden c%:P = (mwiden c)%:P.
Proof. by rewrite /mpwiden map_polyC. Qed.

Lemma mpwidenZ c p : mpwiden (c *: p) = mwiden c *: (mpwiden p).
Proof. by rewrite /mpwiden map_polyZ. Qed.

End MWiden.

(* -------------------------------------------------------------------- *)
Section MPolyUni.
Context (n : nat) (R : ringType).
Implicit Types (p q : {mpoly R[n.+1]}).

Let X (i : 'I_n.+1) : {poly {mpoly R[n]}} :=
  match split (cast_ord (esym (addn1 n)) i) with
  | inl j => ('X_j)%:P
  | inr _ => 'X
  end.

Definition muni (p : {mpoly R[n.+1]}) : {poly {mpoly R[n]}} :=
  nosimpl (mmap (polyC \o @mpolyC _ _) X p).

Let XE m : mmap1 X m = 'X_[[multinom (m (widen i)) | i < n]] *: 'X^(m ord_max).
Proof.
have X1: X ord_max = 'X.
  rewrite /X; case: splitP=> //; case=> j lt_jn /eqP /=.
  by have := lt_jn; rewrite ltn_neqAle eq_sym=> /andP[/negbTE->].
have X2 i: X (widen i) = ('X_i)%:P.
  rewrite /X; case: splitP=> [j eq|j].
    by congr ('X__)%:P; apply/val_inj=> /=; rewrite -eq.
  by rewrite ord1 /= addn0 => /eqP /=; rewrite ltn_eqF.
rewrite /mmap1 big_ord_recr /= X1 -mul_polyC.
rewrite mpolyXE_id rmorph_prod /=; congr (_ * _).
by apply/eq_bigr=> i _; rewrite X2 rmorphXn /= mnmE.
Qed.

Lemma muniE p : muni p =
  \sum_(m <- msupp p)
     p@_m *: 'X_[[multinom (m (widen i)) | i < n]] *: 'X^(m ord_max).
Proof.
apply/eq_bigr=> m _; rewrite XE /= -!mul_polyC.
by rewrite mulrA -polyCM mul_mpolyC.
Qed.

Definition mmulti (p : {poly {mpoly R[n]}}) : {mpoly R[n.+1]} :=
  \sum_(i < size p) ((mwiden p`_i) * ('X_ord_max) ^+ i).

Lemma muni_is_additive : additive muni. Proof. exact/mmap_is_additive. Qed.

HB.instance Definition _ :=
  GRing.isAdditive.Build {mpoly R[n.+1]} {poly {mpoly R[n]}} muni
    muni_is_additive.

Lemma muni0     : muni 0 = 0               . Proof. exact: raddf0. Qed.
Lemma muniN     : {morph muni: x / - x}    . Proof. exact: raddfN. Qed.
Lemma muniD     : {morph muni: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma muniB     : {morph muni: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma muniMn  k : {morph muni: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma muniMNn k : {morph muni: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma muni_is_multiplicative : multiplicative muni.
Proof.
apply/commr_mmap_is_multiplicative=> /= [i p|p m1 m2].
  rewrite /X; case: splitP=> j _; last exact/commr_polyX.
  by apply/polyP=> k; rewrite coefCM coefMC; apply/commr_mpolyX.
apply/polyP=> k; rewrite coefCM coefMC XE coefZ coefXn.
case: eqP; rewrite ?(mulr0, mul0r, mulr1, mul1r) //= => _.
exact/commr_mpolyX.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {mpoly R[n.+1]} {poly {mpoly R[n]}} muni
    muni_is_multiplicative.

Lemma muni1 : muni 1 = 1.
Proof. exact: rmorph1. Qed.

Lemma muniM : {morph muni: x y / x * y}.
Proof. exact: rmorphM. Qed.

Lemma muniC c : muni c%:MP = (c%:MP)%:P.
Proof. by rewrite /muni mmapC. Qed.

Lemma muniN1 : muni (-1) = -1.
Proof. by rewrite raddfN /= muniC. Qed.

Lemma muniZ c p : muni (c *: p) = c%:MP *: muni p.
Proof. by rewrite /muni mmapZ /= mul_polyC. Qed.

End MPolyUni.

(* -------------------------------------------------------------------- *)
Section MESymViete.
Local Notation mw  := mwiden.
Local Notation mpw := mpwiden.

Local Notation swiden h :=
  [set widen x | x in h : {set 'I__}]
  (only parsing).

Local Notation S1 n k :=
  [set swiden h | h in {set 'I_n} & #|h| == k.+1]
  (only parsing).

Local Notation S2 n k :=
  [set ord_max |: swiden h | h in {set 'I_n} & #|h| == k]
  (only parsing).

Let inj_widen n : injective (widen : 'I_n -> _).
Proof. by move=> x y /eqP; rewrite eqE /= val_eqE => /eqP. Qed.

Local Hint Resolve inj_widen : core.

Let inj_swiden n : injective (fun h : {set 'I_n} => swiden h).
Proof.
have h m (x : 'I_n): (widen x \in swiden m) = (x \in m).
  apply/imsetP/idP=> /= [[y y_in_m /inj_widen ->//]|].
  by move=> x_in_m; exists x.
move=> m1 m2 /= /setP eq; apply/setP=> /= x.
by have := eq (widen x); rewrite !h.
Qed.

Local Hint Resolve inj_swiden : core.

Let inj_mDswiden n : injective (fun h : {set 'I_n} => ord_max |: swiden h).
Proof.
move=> h1 h2 /= /setP eq; apply/inj_swiden.
apply/setP => /= x; have {eq} := (eq x).
rewrite !inE; case: eqP=> [-> _|//].
have E (h : {set 'I_n}): ord_max \in swiden h = false.
  apply/negP; case/imsetP=> /= y _ /eqP.
  by rewrite eqE /= eq_sym ltn_eqF.
by rewrite !E.
Qed.

Let disjoint_S n k : [disjoint (S1 n k) & (S2 n k)].
Proof.
rewrite -setI_eq0; apply/eqP/setP=> /= x.
rewrite !in_set; apply/negP=> /andP[].
case/imsetP=> /= h1 _ -> /imsetP /= [h2 _].
move/setP/(_ ord_max); rewrite in_set in_set1 eqxx /=.
case/imsetP=> /= {h1 h2} m _ /eqP.
by rewrite eqE /= eq_sym ltn_eqF.
Qed.

Let union_S n k :
  [set h in {set 'I_n.+1} | #|h| == k.+1] = S1 n k :|: S2 n k.
Proof.
apply/eqP; rewrite eq_sym eqEcard; apply/andP; split.
  rewrite subUset; apply/andP; split.
    apply/subsetP=> h /imsetP /= [m]; rewrite inE.
    by move=> eq ->; rewrite inE card_imset //=.
  apply/subsetP=> h /imsetP /= [m]; rewrite inE.
  move=> eq->; rewrite inE cardsU1 card_imset //=.
  rewrite -[k.+1]add1n (eqP eq) eqn_add2r eqb1.
  apply/negP=> /imsetP [/=] x _ /eqP.
  by rewrite eqE /= eq_sym ltn_eqF.
have := disjoint_S n k; rewrite -leq_card_setU=> /eqP->.
rewrite !card_imset //= ?card_draws /=;
  try exact/inj_swiden; try exact/inj_mDswiden.
  (* remove the line above once requiring Coq >= 8.17 *)
by rewrite !card_ord binS.
Qed.

Lemma mesymSS (R : ringType) n k :
  's_(n.+1, k.+1) = mw 's_(n, k.+1) + mw 's_(n, k) * 'X_(ord_max)
  :> {mpoly R[n.+1]}.
Proof.
rewrite /mesym -big_set /= union_S big_set.
rewrite bigU ?disjoint_S //=; congr (_ + _).
+ rewrite big_imset /=; last by move=> ?? _ _; apply/inj_swiden.
  rewrite big_set /= raddf_sum /=; apply/eq_bigr=> h _.
  rewrite !mprodXE mwidenX; congr 'X_[_]; apply/mnmP=> j.
  rewrite mnmwiden_sum !mnm_sumE big_imset //=; last first.
    by move=> ?? _ _; apply/inj_widen.
  by apply/eq_bigr=> i _; rewrite mnmwiden1.
+ rewrite big_imset /=; last by move=> t1 t2 _ _; apply/inj_mDswiden.
  rewrite big_set /= raddf_sum /= mulr_suml; apply/eq_bigr=> h _.
  rewrite !mprodXE mwidenX -mpolyXD; congr 'X_[_].
  rewrite (big_setD1 ord_max) /= ?in_setU1 ?eqxx //=.
  rewrite addmC setU1K //= ?mnmwiden_sum ?big_imset /=.
    by congr (_ + _)%MM; apply/eq_bigr=> i _; rewrite mnmwiden1.
    by move=> ?? _ _; apply/inj_widen.
    apply/negP; case/imsetP=> /= x _ /eqP.
    by rewrite eqE /= eq_sym ltn_eqF.
Qed.

Lemma Viete :
  forall n,
       \prod_(i < n   ) ('X - ('X_i)%:P)
    =  \sum_ (k < n.+1) (-1)^+k *: ('s_(n, k) *: 'X^(n-k))
    :> {poly {mpoly int[n]}}.
Proof.
elim => [|n ih].
  by rewrite !big_ord0 big_ord1 mesym0E expr0 !scale1r.
pose F n k : {poly {mpoly int[n]}} :=
  (-1)^+k *: ('s_(n, k) *: 'X^(n-k)).
have Fn0 l: F l 0%N = 'X^l.
  by rewrite /F expr0 mesym0E !scale1r subn0.
have Fnn l: F l l = (-1)^+l *: \prod_(i < l) ('X_i)%:P.
  by rewrite /F mesymnnE subnn expr0 alg_polyC rmorph_prod.
rewrite big_ord_recr /=; set p := (\prod_(_ < _) _).
have {p}->: p = mpw (\prod_(i < n) ('X - ('X_i)%:P)).
  rewrite /mpwiden rmorph_prod /=; apply/eq_bigr.
  move=> /= i _; rewrite raddfB /= map_polyX map_polyC /=.
  by rewrite mwidenX mnmwiden1.
rewrite {}ih (eq_bigr (F n.+1 \o val)) //; apply/esym.
rewrite (eq_bigr (F n \o val)) // -!(big_mkord xpredT).
rewrite raddf_sum /= mulrBr !mulr_suml.
rewrite big_nat_recl 1?[X in X-_]big_nat_recl //.
rewrite -!addrA !Fn0; congr (_ + _).
  by rewrite rmorphXn /= mpwidenX exprSr.
rewrite big_nat_recr 1?[X in _-X]big_nat_recr //=.
rewrite opprD !addrA; congr (_ + _); last first.
  rewrite !Fnn !mpwidenZ !rmorphXn /= mwidenN1.
  rewrite exprS mulN1r scaleNr -scalerAl; congr (- (_ *: _)).
  rewrite big_ord_recr rmorph_prod /=; congr (_ * _).
  by apply/eq_bigr=> i _; rewrite mpwidenC mwidenX mnmwiden1.
rewrite -sumrB !big_seq; apply/eq_bigr => i /=.
rewrite mem_index_iota => /andP [_ lt_in]; rewrite {Fn0 Fnn}/F.
rewrite subSS mesymSS !mpwidenZ !rmorphXn /= !mwidenN1 !mpwidenX.
rewrite exprS mulN1r !scaleNr mulNr -opprD; congr (-_).
rewrite -!scalerAl -scalerDr; congr (_ *: _).
rewrite -exprSr -subSn // subSS scalerDl; congr (_ + _).
by rewrite -!mul_polyC !mulrA mulrAC polyCM.
Qed.

Lemma mroots_coeff (R : idomainType) n (cs : n.-tuple R) (k : 'I_n.+1) :
    (\prod_(c <- cs) ('X - c%:P))`_(n - k)
  = (-1)^+k * 's_(n, k).@[tnth cs].
Proof.
pose P := (\prod_(i < n) ('X - ('X_i)%:P) : {poly {mpoly int[n]}}).
pose f := mmap intr (tnth cs): {mpoly int[n]} -> R.
pose F := fun i => 'X - (tnth cs i)%:P.
move: (Viete n) => /(congr1 (map_poly f)).
rewrite rmorph_prod /= (eq_bigr F); last first.
  move=> i _; rewrite raddfB /= map_polyX map_polyC /=.
  by rewrite mmapX mmap1U.
rewrite big_tuple => ->; rewrite raddf_sum coef_sum /=.
rewrite (bigD1 k) //= big1 ?addr0; last first.
  case=> i /= lt_iSk; rewrite eqE /= => ne_ik.
  rewrite !map_polyZ /= map_polyXn !coefZ coefXn.
  rewrite -(eqn_add2r i) subnK // addnC.
  rewrite -(eqn_add2r k) -addnA subnK 1?addnC; last first.
    by move: (ltn_ord k); rewrite ltnS.
  by rewrite eqn_add2l (negbTE ne_ik) !mulr0.
rewrite !map_polyZ !rmorphXn /= raddfN /= mmapC !coefZ /=.
congr (_ * _); rewrite map_polyX coefXn eqxx mulr1.
rewrite /mesym; rewrite !raddf_sum /=; apply/eq_bigr.
move=> i _; rewrite !rmorph_prod /=; apply/eq_bigr.
by move=> j _; rewrite mmapX mmap1U mevalXU.
Qed.

Lemma mroots_sum (R : idomainType) (n : nat) (cs : n.+1.-tuple R) :
  \sum_(c <- cs) c = - (\prod_(c <- cs) ('X - c%:P))`_n.
Proof.
move: (mroots_coeff cs) => /(_ 1); rewrite subSS subn0=> ->.
rewrite expr1 mulN1r opprK mesym1E raddf_sum /=.
by rewrite big_tuple; apply/eq_bigr=> /= i _; rewrite mevalXU.
Qed.

End MESymViete.

(* -------------------------------------------------------------------- *)
Section MESymFundamental.
Context (n : nat) (R : comRingType).
Implicit Types (m : 'X_{1..n}).

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Local Notation S := [tuple 's_(R, n, i.+1) | i < n].

Let mlead_XS m :
  mlead ('X_[R, m] \mPo S) = [multinom \sum_(j : 'I_n | i <= j) (m j) | i < n].
Proof.
rewrite comp_mpolyX mlead_prod_proper=> /=; last first.
  move=> i _ _; rewrite tnth_map tnth_ord_tuple.
  rewrite mleadX_proper /= ?mleadc_mesym //; last exact/lreg1.
  by rewrite mleadcX ?mleadc_mesym //; apply/lregX/lreg1.
pose F (i : 'I_n) := [multinom (j <= i) * (m i) | j < n].
rewrite (eq_bigr F) {}/F=> [|i _]; last first.
  rewrite tnth_map tnth_ord_tuple mleadX_proper.
    rewrite mlead_mesym //; apply/mnmP=> j.
    by rewrite mulmnE !mnmE mulnC ltnS.
  by rewrite mleadc_mesym //; apply/lreg1.
apply/mnmP=> i; apply/esym; rewrite mnm_sumE mnmE big_mkcond /=.
apply/eq_bigr=> j _; rewrite mnmE; case: leqP=> _.
  by rewrite mul1n. by rewrite mul0n.
Qed.

Let mleadc_XS l : mleadc ('X_[l] \mPo S) = 1.
Proof.
rewrite comp_mpolyX mlead_prod_proper ?mleadc_prod; last first.
  move=> /= i _ _; rewrite tnth_map tnth_ord_tuple.
  rewrite mleadX_proper // ?mleadcX ?mleadc_mesym //.
    exact/lregX/lreg1. exact/lreg1.
rewrite (eq_bigr (fun _ => 1)) /=; last first.
  move=> i _; rewrite tnth_map tnth_ord_tuple.
  rewrite mleadX_proper ?mleadcX ?mleadc_mesym //.
    by rewrite expr1n. exact/lreg1.
by rewrite prodr_const expr1n.
Qed.

Let free_XS : injective (fun m => mlead ('X_[R, m] \mPo S)).
Proof.
move=> m1 m2; apply: contra_eq.
move=> ne_m1m2; apply/negP=> /eqP eqXS.
pose F m i := (\sum_(j : 'I_n | i <= j) (m j))%N.
have {eqXS} eqF i: F m1 i = F m2 i.
  case: (ssrnat.ltnP i n)=> [lt_in|le_ni]; last first.
    rewrite /F !big1 //= => j /(leq_trans le_ni);
    by rewrite leqNgt ltn_ord.
  by move/mnmP/(_ (Ordinal lt_in)): eqXS; rewrite !mlead_XS !mnmE.
apply/negP: ne_m1m2; rewrite negbK; apply/eqP/mnmP=> i.
rewrite -[i in m1 i]rev_ordK -[i in m2 i]rev_ordK.
pose G m i := nth 0%N m (n-i.+1); rewrite !(mnm_nth 0%N) /=.
apply/(@psumn_eq n (G m1) (G m2)); rewrite ?subnSK ?leq_subr //.
move=> j le_jn; have Geq m: (\sum_(i < n | i < j) G m i = F m (n-j))%N.
  rewrite (reindex_inj rev_ord_inj) /= /F; apply/eq_big=> l /=.
  + by rewrite subnSK // !leq_subLR addnC.
  + by move=> _; rewrite /G subnS subKn //= (mnm_nth 0%N).
by rewrite !Geq.
Qed.

Let mlead_XLS (m : 'X_{1..n}) :
  let c i := nth 0%N m i in
  let F i := (c i - c i.+1)%N in
     (forall i j : 'I_n, i <= j -> m j <= m i)
  -> mlead ('X_[R, F#val] \mPo S) = m.
Proof.
move=> c F srt_m; rewrite mlead_XS; apply/mnmP=> i.
rewrite mnmE; rewrite (eq_bigr (F \o val)); last first.
  by move=> /= j _; rewrite mnmE.
rewrite -big_mkord (big_cat_nat _ (n := i)) // 1?ltnW //=.
rewrite big_nat_cond big_pred0 ?add0n; last first.
  by move=> j /=; rewrite ltnNge andNb.
rewrite big_nat_cond (eq_bigl (fun j => i <= j < n)); last first.
  by move=> j /=; apply/andb_idr=> /andP[].
rewrite -big_nat; rewrite sumn_range 1?ltnW //.
  rewrite /c [X in (_-X)%N]nth_default ?size_tuple //.
  by rewrite subn0 (mnm_nth 0%N).
move=> j1 j2; rewrite ltnS=> /andP[le_j1j2].
rewrite leq_eqVlt ltn_subRL => /predU1P[->|].
  by rewrite subnK ?[i <= _]ltnW // /c nth_default // size_tuple.
rewrite addnC=> lt_j2Di_n; have lt_j1Di_n: j1 + i < n.
  by apply/(@leq_ltn_trans (j2+i)); rewrite // leq_add2r.
have /= := srt_m (Ordinal lt_j1Di_n) (Ordinal lt_j2Di_n).
by rewrite !(mnm_nth 0%N) /=; apply; rewrite leq_add2r.
Qed.

Let mweight_XLS (m : 'X_{1..n}) :
  let c i := nth 0%N m i in
  let F i := (c i - c i.+1)%N in
     (forall i j : 'I_n, i <= j -> m j <= m i)
  -> mweight 'X_[R, F#val] = (mdeg m).+1.
Proof.
move=> c F srt_m; rewrite mmeasureX /mnmwgt /=; congr _.+1.
rewrite (eq_bigr (fun i : 'I_n => (F i) * i.+1))%N; last first.
  by move=> i _; rewrite mnmE.
rewrite mdegE sumn_wgt_range; last first.
  move=> i j /andP[le_ij]; rewrite ltnS leq_eqVlt => /predU1P[->|].
    by rewrite {1}/c nth_default // size_tuple.
  move=> lt_jn; have lt_in: i < n by exact: leq_ltn_trans le_ij _.
  have /(_ le_ij) := srt_m (Ordinal lt_in) (Ordinal lt_jn).
  by rewrite /fun_of_multinom !(tnth_nth 0%N).
rewrite {2}/c nth_default ?size_tuple // muln0 subn0.
by apply/eq_bigr=> /= i _; rewrite /fun_of_multinom (tnth_nth 0%N).
Qed.

Definition symf1 (p : {mpoly R[n]}) : {mpoly R[n]} * {mpoly R[n]} :=
  if p == 0 then (0, 0) else
    let m := mlead p in
    let c := nth 0%N m in
    let F := fun i => (c i - c i.+1)%N in
    (p@_m *: 'X_[F#val], p - p@_m *: ('X_[F#val] \mPo S)).

Fixpoint symfn (k : nat) (p : {mpoly R[n]}) :=
  if k is k'.+1 then
    let (t1, p) := symf1 p in
    let (t2, p) := symfn k' p in
      (t1 + t2, p)
  else symf1 p.

Lemma symf1E0 : symf1 0 = (0, 0).
Proof. by rewrite /symf1 eqxx. Qed.

Lemma symfnE0 k : symfn k 0 = (0, 0).
Proof. by elim: k => /= [|k ih]; rewrite symf1E0 //= ih addr0. Qed.

Lemma symf1P (p : {mpoly R[n]}) : p \is symmetric ->
  [&& ((symf1 p).2 == 0) || (mlead (symf1 p).2 < mlead p)%O
    , (symf1 p).2 \is symmetric
    & p == (symf1 p).1 \mPo S + (symf1 p).2].
Proof.
rewrite /symf1; case: (eqVneq p 0) => [->|nz_p sym_p] /=.
  by rewrite comp_mpoly0 addr0 eqxx andbT.
rewrite addrCA comp_mpolyZ subrr addr0 eqxx andbT rpredB //; last first.
  by apply/rpredZ/mcomp_sym => i; rewrite -tnth_nth tnth_map; apply/mesym_sym.
case: eqVneq; rewrite //= andbT.
have := mlead_XLS (mlead_msym_sorted sym_p).
set c := nth 0%N (mlead p); pose F i := (c i - c i.+1)%N.
rewrite -/(F#val) => mE.
set q : {mpoly R[n]} := p@_(mlead p) *: (_ \mPo _).
rewrite lt_neqAle andbC /= => nz_pBq.
have := mleadB_le p q; rewrite mleadZ_proper; last first.
  by rewrite mE mulrC mulrI_eq0 ?mleadc_eq0 // -mE mleadc_XS; apply/lreg1.
rewrite mE joinxx => -> /=; apply/contraTneq: nz_pBq.
rewrite -mleadc_eq0 => ->; rewrite /q mcoeffB mcoeffZ -{3}mE.
by rewrite mleadc_XS mulr1 subrr eqxx.
Qed.

Lemma symfnP k (p : {mpoly R[n]}) : p \is symmetric ->
  [&& ((symfn k p).2 == 0) || (mlead (symfn k p).2 < mlead p)%O
    , (symfn k p).2 \is symmetric
    & p == (symfn k p).1 \mPo S + (symfn k p).2].
Proof.
elim: k p=> [|k ih] p sym_p /=; first exact/symf1P.
have E T U (z : T * U) : z = (z.1, z.2) by case: z.
rewrite [symf1 p]E [symfn _ _]E /= => {E}.
case/and3P: (symf1P sym_p); case/orP=> [/eqP-> _ /eqP pE|].
  by rewrite symfnE0 /= eqxx rpred0 /= {1}pE !simpm.
move=> le_q1_p /ih /and3P[]; case/orP=> [/eqP-> _|].
  move=> /eqP q1E /eqP pE; rewrite eqxx rpred0 /=.
  by rewrite {1}pE {1}q1E !simpm /= addr0 raddfD.
move=> le_q2_q1 -> /eqP q1E /eqP pE.
rewrite (lt_trans le_q2_q1) ?orbT //= {1}pE {1}q1E.
by rewrite addrA raddfD.
Qed.

Lemma symfnS (p : {mpoly R[n]}) :
  { n : nat | p \is symmetric -> (symfn n p).2 = 0 }.
Proof.
have: p \is symmetric -> { n : nat | (symfn n p).2 = 0 }.
  elim/mleadrect: p => p ih sym_p; case/and3P: (symf1P sym_p).
  case: ((symf1 p).2 =P 0)=> /= [z_q1|nz_q1]; first by exists 0%N.
  move=> le_q1 /ih -/(_ le_q1) [k z_q2] /eqP pE.
  exists k.+1=> /=; have E T U (z : T * U): z = (z.1, z.2) by case: z.
  by rewrite [symf1 _]E [symfn _ _]E z_q2.
by case: (p \is symmetric)=> [[]// k eq|_]; [exists k | exists 0%N].
Qed.

Definition symf (p : {mpoly R[n]}) :=
  nosimpl (symfn (tag (symfnS p)) p).1.

Lemma symfP (p : {mpoly R[n]}) : p \is symmetric -> p = symf p \mPo S.
Proof.
move=> sym_p; rewrite /symf; set k := tag _.
case/and3P: (symfnP k sym_p)=> /= _ _ /eqP {1}->.
by rewrite {}/k; case: symfnS=> /= k -> //; rewrite !simpm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma symf1_wgle (p : {mpoly R[n]}) : p \is symmetric ->
  mweight (symf1 p).1 <= msize p.
Proof.
move=> sym_p; rewrite /symf1; case: (p =P 0).
  by rewrite mmeasure0.
move=> /eqP nz_p; set X := 'X_[_] => /=.
rewrite (@leq_trans (mweight X)) ?mmeasureZ_le //.
rewrite -?mlead_deg ?mleadc_eq0 // mweight_XLS //.
exact/mlead_msym_sorted.
Qed.

Lemma symfn_wgle k (p : {mpoly R[n]}) : p \is symmetric ->
  mweight (symfn k p).1 <= msize p.
Proof.
elim: k p => [|k ih] p sym_p /=; first exact/symf1_wgle.
have E T U (z : T * U): z = (z.1, z.2) by case: z.
rewrite [symf1 p]E [symfn _ _]E /= => {E}.
case/and3P: (symf1P sym_p); case/orP=> [/eqP-> _ /eqP pE|].
  by rewrite symfnE0 /= addr0; apply/symf1_wgle.
move=> le_q1_p sym_q2 /eqP pE.
rewrite (leq_trans (mmeasureD_le _ _ _)) //.
rewrite geq_max symf1_wgle //= (leq_trans (ih _ _)) //.
have [->|nz_p] := eqVneq p 0; first by rewrite symf1E0 msize0.
have [->|nz_f1p] := eqVneq (symf1 p).2 0; first by rewrite msize0.
by rewrite -!mlead_deg // ltnS lemc_mdeg // ltW.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sym_fundamental (p : {mpoly R[n]}) : p \is symmetric ->
  { t | t \mPo S = p /\ mweight t <= msize p}.
Proof. by exists (symf p); rewrite {2}[p]symfP ?symfn_wgle. Qed.

(* -------------------------------------------------------------------- *)
Local Notation XS m := ('X_[R, m] \mPo S) (only parsing).

Lemma msym_fundamental_un0 (t : {mpoly R[n]}) : t \mPo S = 0 -> t = 0.
Proof.
set S := S; move/eqP; apply/contraTeq=> nz_t; rewrite -mleadc_eq0.
have h m: m \in msupp t -> mlead (t@_m *: (XS m)) = mlead (XS m).
  move=> m_in_t; rewrite mleadZ_proper // mleadc_XS.
  by rewrite mulr1 mcoeff_eq0 m_in_t.
rewrite comp_mpolyEX mlead_sum ?filter_predT; last first.
  rewrite (iffLR (eq_in_map _ _ _) h) -/S.
  apply/(@uniqP _ 0%MM) => i j; rewrite size_map.
  move=> lti ltj; rewrite !(nth_map 0%MM) // => /free_XS.
  exact: (can_in_inj (nthK _ _)).
rewrite big_seq (eq_bigr _ h) -big_seq.
case: (eq_bigjoin (fun m => mlead (XS m)) _ (r := msupp t)).
  exact/le_total. by rewrite msupp_eq0.
move=> /= m m_in_t /eqP/esym; rewrite -/S=> lmm.
rewrite -lmm raddf_sum /= (bigD1_seq m) //= mcoeffZ.
rewrite mleadc_XS mulr1 big_seq_cond big1.
  by rewrite addr0 mcoeff_eq0 m_in_t.
move=> /= m' /andP[m'_in_t ne_m'm]; rewrite mcoeffZ.
rewrite [X in _*X]mcoeff_gt_mlead ?mulr0 //.
rewrite lt_neqAle (contra_neq (@free_XS _ _)) //= lmm.
exact: (joins_sup_seq (fun m => mlead (XS m))).
Qed.

Lemma msym_fundamental_un (t1 t2 : {mpoly R[n]}) :
  t1 \mPo S = t2 \mPo S -> t1 = t2.
Proof.
move/eqP; rewrite -subr_eq0 -raddfB /= => /eqP.
by move/msym_fundamental_un0/eqP; rewrite subr_eq0=> /eqP.
Qed.

End MESymFundamental.

(* -------------------------------------------------------------------- *)
Definition ishomog1_pred {n} {R : ringType}
  (d : nat) (mf : measure n) : pred {mpoly R[n]}
  := fun p => all [pred m | mf m == d] (msupp p).
Arguments ishomog1_pred _ _ _ _ _ /.
Definition ishomog1 {n} {R : ringType}
  (d : nat) (mf : measure n) : qualifier 0 {mpoly R[n]}
  := [qualify p | ishomog1_pred d mf p].

(* -------------------------------------------------------------------- *)
Definition ishomog_pred {n} {R : ringType} mf : pred {mpoly R[n]} :=
  fun p => p \is ishomog1 (@mmeasure _ _ mf p).-1 mf.
Arguments ishomog_pred _ _ _ _ /.
Definition ishomog {n} {R : ringType} mf : qualifier 0 {mpoly R[n]} :=
  [qualify p | ishomog_pred mf p].

(* -------------------------------------------------------------------- *)
Section MPolyHomogTheory.
Context (n : nat) (R : ringType) (mf : measure n).
Implicit Types (p q : {mpoly R[n]}).

Local Notation "d .-homog" := (@ishomog1 _ _ d mf)
  (at level 1, format "d .-homog") : form_scope.

Local Notation homog := (@ishomog _ _ mf).

Local Notation "[ 'in' R [ n ] , d .-homog ]" := (@ishomog1 n R d mf)
  (at level 0, R, n at level 2, d at level 0,
     format "[ 'in'  R [ n ] ,  d .-homog ]") : form_scope.

Lemma dhomogE d p: (p \is d.-homog) = all [pred m | mf m == d] (msupp p).
Proof. by []. Qed.

Lemma dhomogP d p: reflect {in msupp p, forall m, mf m = d} (p \is d.-homog).
Proof. by apply/(iffP allP)=> /= h m /h => [/eqP|->]. Qed.

Lemma dhomog_mf d p: p \is d.-homog -> {in msupp p, forall m, mf m = d}.
Proof. by move/dhomogP. Qed.

Lemma dhomog_nemf_coeff d p m: p \is d.-homog -> mf m != d -> p@_m = 0.
Proof.
  move/dhomogP=> hg_p; apply/contraTeq; rewrite -mcoeff_msupp.
  by move/hg_p=> ->; rewrite negbK.
Qed.

Lemma dhomog1 : (1 : {mpoly R[n]}) \is 0.-homog.
Proof.
by apply/dhomogP; rewrite msupp1=> m; rewrite inE=> /eqP ->; exact: mf0.
Qed.

Lemma dhomog_uniq p d e : p != 0 -> p \is d.-homog -> p \is e.-homog -> d = e.
Proof.
by move=> nz_p /dhomogP /(_ _ (mlead_supp nz_p)) <- /dhomogP/(_ _ (mlead_supp nz_p)).
Qed.

Lemma dhomog_submod_closed d : submod_closed [in R[n], d.-homog].
Proof.
split=> [|c p q]; first by rewrite dhomogE msupp0.
move=> /dhomogP hg_p /dhomogP hg_q; apply/dhomogP=> m.
move/msuppD_le; rewrite mem_cat; case/orP=> [/msuppZ_le|].
  by move/hg_p. by move/hg_q.
Qed.

HB.instance Definition _ d :=
  GRing.isSubmodClosed.Build R {mpoly R[n]} (ishomog1_pred d mf)
    (dhomog_submod_closed d).

Lemma dhomog0 d: 0 \is [in R[n], d.-homog].
Proof. exact/rpred0. Qed.

Lemma dhomogX d m: ('X_[m] \is [in R[n], d.-homog]) = (mf m == d).
Proof. by rewrite dhomogE msuppX /= andbT. Qed.

Lemma dhomogD d: {in d.-homog &, forall p q, p + q \is d.-homog}.
Proof. exact/rpredD. Qed.

Lemma dhomogN d: {mono -%R: p / p \in [in R[n], d.-homog]}.
Proof. exact/rpredN. Qed.

Lemma dhomogZ d c p: p \in d.-homog -> (c *: p) \in d.-homog.
Proof. exact/rpredZ. Qed.

Local Notation mfsize p := (@mmeasure _ _ mf p).

Lemma homog_msize p : (p \is homog) = (p \is (mfsize p).-1.-homog).
Proof. by []. Qed.

Lemma dhomog_msize d p : p \is d.-homog -> p \is (mfsize p).-1.-homog.
Proof.
rewrite mmeasureE => /dhomogP h; apply/dhomogP => m m_in_p.
rewrite h // big_seq (eq_bigr (fun _ => d.+1)); last by move=> i /h ->.
rewrite -big_seq (perm_big _ (perm_to_rem m_in_p)) big_cons /=.
elim: (rem _ _)=> [|x s ih]; first by rewrite big_nil maxn0.
by rewrite big_cons maxnA maxnn -ih.
Qed.

Lemma homogE d p : p \is d.-homog -> p \is homog.
Proof. by move/dhomog_msize. Qed.

Lemma homogP p : reflect (exists d, p \is d.-homog) (p \is homog).
Proof.
by apply: (iffP idP)=> [h|[d /dhomog_msize]] //; exists (mfsize p).-1.
Qed.

Lemma dhomogM d p e q :
  p \is d.-homog -> q \is e.-homog -> p * q \is (d + e).-homog.
Proof.
move=> /dhomogP homp /dhomogP homq; apply/dhomogP=> m.
case/msuppM_le/allpairsP=> /= -[m1 m2] [/=].
by move=> /homp <- /homq <- ->; apply/mfD.
Qed.

Lemma dhomogMn d p k : p \is d.-homog -> p ^+ k \is (d * k).-homog.
Proof.
elim: k => [| k ihk] homp; first by rewrite muln0; apply/dhomog1.
by rewrite exprS /= mulnS; apply/dhomogM/ihk.
Qed.

Lemma homog_prod (s : seq {mpoly R[n]}) :
  all (fun p => p \is homog) s -> \prod_(p <- s) p \is homog.
Proof.
move=> homs; apply/homogP; elim: s homs => [_ | p s ihs] /=.
  by exists 0%N; rewrite big_nil; apply/dhomog1.
case/andP=> /homogP [dp p_hdp] {}/ihs [d ih].
by exists (dp + d)%N; rewrite big_cons; apply/dhomogM.
Qed.

Lemma dhomog_prod {l} (dt : l.-tuple nat) (mt : l.-tuple {mpoly R[n]}) :
     (forall i : 'I_l, tnth mt i \is (tnth dt i).-homog)
  -> \prod_(i <- mt) i \is (\sum_(i <- dt) i).-homog.
Proof.
elim: l dt mt => [| l ihl] dt mt hom.
  by rewrite tuple0 big_nil tuple0 big_nil dhomog1.
case/tupleP: dt hom => d dt; case/tupleP: mt => p mt /= hom.
rewrite !big_cons; apply/dhomogM.
  by move: (hom ord0); rewrite (tnth_nth 0) (tnth_nth 0%N).
apply/ihl => i; have:= hom (inord i.+1).
by rewrite !(tnth_nth 0) ?(tnth_nth 0%N) !inordK ?ltnS.
Qed.

End MPolyHomogTheory.

Notation "[ 'in' R [ n ] , d .-homog 'for' mf ]" := (@ishomog1 n R d mf)
  (at level 0, R, n at level 2, d at level 0,
     format "[ 'in'  R [ n ] , d .-homog  'for'  mf ]") : form_scope.

Notation "[ 'in' R [ n ] , d .-homog ]" := [in R[n], d.-homog for mdeg]
  (at level 0, R, n at level 2, d at level 0) : form_scope.

Notation "d .-homog 'for' mf" := (@ishomog1 _ _ d mf)
  (at level 1, format "d .-homog  'for'  mf") : form_scope.

Notation "d .-homog" := (d .-homog for mdeg)
  (at level 1, format "d .-homog") : form_scope.

Notation "'homog' mf" := (@ishomog _ _ mf)
  (at level 1, format "'homog'  mf") : form_scope.

(* -------------------------------------------------------------------- *)
Section HomogNVar0.
Context (n : nat) (R : ringType).

Lemma nvar0_homog (mf : measure 0%N) (p : {mpoly R[0]}) :
  p \is 0.-homog for mf.
Proof. by apply/dhomogP; case=> t; rewrite tuple0 mfE big_ord0. Qed.

Lemma nvar0_homog_eq (mf : measure n) (p : {mpoly R[n]}) :
  n = 0%N -> p \is 0.-homog for mf.
Proof. by move=> z_n; move: mf p; rewrite z_n; apply/nvar0_homog. Qed.

End HomogNVar0.

(* -------------------------------------------------------------------- *)
Section ProjHomog.
Context (n : nat) (R : ringType) (mf : measure n).
Implicit Types (p q r : {mpoly R[n]}) (m : 'X_{1..n}).

Local Notation mfsize p := (@mmeasure _ _ mf p).

Section Def.
Variable (d : nat).

Definition pihomog p : {mpoly R[n]} :=
  \sum_(m <- msupp p | mf m == d) p@_m *: 'X_[m].

Lemma pihomogE p : pihomog p =
  \sum_(m <- msupp p | mf m == d) p@_m *: 'X_[m].
Proof. by []. Qed.

Lemma pihomogwE k p : msize p <= k ->
  pihomog p = \sum_(m : 'X_{1..n < k} | mf m == d) p@_m *: 'X_[m].
Proof.
move=> lt_pk; pose I : subFinType _ := 'X_{1..n < k}.
rewrite pihomogE (big_mksub_cond I) //=; first last.
+ by move=> x /msize_mdeg_lt /leq_trans /(_ lt_pk) ->.
+ by rewrite msupp_uniq.
rewrite -big_filter_cond big_rmcond ?big_filter //=.
by move=> m /memN_msupp_eq0 ->; rewrite scale0r.
Qed.

Lemma pihomogX m : pihomog 'X_[m] = if mf m == d then 'X_[m] else 0.
Proof.
by rewrite pihomogE msuppX big_mkcond /= big_seq1 mcoeffX eqxx scale1r.
Qed.

Lemma pihomog_is_linear : linear pihomog.
Proof.
move=> c p q /=; pose_big_enough l.
  rewrite (pihomogwE _ (k := l)) //.
  rewrite (pihomogwE _ (k := l) (p := p)) //.
  rewrite (pihomogwE _ (k := l) (p := q)) //.
  rewrite scaler_sumr -big_split /=; apply: eq_bigr => m _.
  by rewrite linearP /= scalerDl scalerA.
by close.
Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R {mpoly R[n]} {mpoly R[n]} _ pihomog
    pihomog_is_linear.

Lemma pihomog0     : pihomog 0 = 0               . Proof. exact: raddf0. Qed.
Lemma pihomogN     : {morph pihomog: x / - x}    . Proof. exact: raddfN. Qed.
Lemma pihomogD     : {morph pihomog: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma pihomogB     : {morph pihomog: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma pihomogMn  k : {morph pihomog: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma pihomogMNn k : {morph pihomog: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma pihomog_dE p : p \is d.-homog for mf -> pihomog p = p.
Proof.
move/dhomogP => hom_p; rewrite pihomogE big_seq_cond.
rewrite (eq_bigl [pred m | m \in msupp p]); last first.
  by move=> m /=; rewrite andb_idr // => /hom_p ->.
by rewrite -big_seq -mpolyE.
Qed.

Lemma pihomogP p : pihomog p \is d.-homog for mf.
Proof.
apply/rpred_sum=> m /eqP eqd_mfm; apply/rpredZ.
by apply/dhomogP => m0 /mem_msuppXP <-.
Qed.

Lemma pihomog_id p : pihomog (pihomog p) = pihomog p.
Proof. by rewrite pihomog_dE; last exact: pihomogP. Qed.

Lemma homog_piE p : p \is d.-homog for mf = (pihomog p == p).
Proof.
apply: (sameP idP); apply: (iffP idP); last by move /pihomog_dE ->.
by move=> /eqP <-; apply/pihomogP.
Qed.

End Def.

Lemma pihomog_ne0 d b p : d != b ->
  p \is d.-homog for mf -> pihomog b p = 0.
Proof.
move=> ne /dhomogP hom; rewrite pihomogE big_seq_cond.
by apply/big_pred0 => m; apply/contraNF: ne=> /andP[/hom->].
Qed.

Lemma pihomog_partitionE k p :
  mfsize p <= k -> p = \sum_(d < k) pihomog d p.
Proof.
move=> h; rewrite (exchange_big_dep predT) //= {1}[p]mpolyE.
apply/eq_bigr => m _; rewrite -scaler_sumr.
case: (ssrnat.leqP k (mf m)) => [|lt_mk].
  move/(leq_trans h)/mmeasure_mnm_ge/memN_msupp_eq0.
  by move=> ->; by rewrite !scale0r.
rewrite (eq_bigl (fun i : 'I_k => i == Ordinal lt_mk)).
  by rewrite big_pred1_eq. by move=> i /=; rewrite eq_sym.
Qed.

End ProjHomog.

(* -------------------------------------------------------------------- *)
Section MPolyHomogType.
Context (n : nat) (R : ringType) (d : nat).

Record dhomog :=
  DHomog { mpoly_of_dhomog :> {mpoly R[n]}; _ : mpoly_of_dhomog \is d.-homog }.

HB.instance Definition _ := [isSub for @mpoly_of_dhomog].
HB.instance Definition _ := [Choice of dhomog by <:].
HB.instance Definition _ := [SubChoice_isSubLmodule of dhomog by <:].

Lemma mpoly_of_dhomog_is_linear: linear mpoly_of_dhomog.
Proof. by []. Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R dhomog {mpoly R[n]} _ mpoly_of_dhomog
    mpoly_of_dhomog_is_linear.

End MPolyHomogType.

Lemma dhomog_is_dhomog n (R : ringType) d (p : dhomog n R d) :
  val p \is d.-homog.
Proof. by case: p. Qed.

#[global] Hint Extern 0 (is_true (_ \is _.-homog)) =>
  (by apply/dhomog_is_dhomog) : core.

Definition indhomog n (R : ringType) d : {mpoly R[n]} -> dhomog n R d :=
  fun p => insubd (0 : dhomog n R d) p.

Notation "[ ''dhomog_' d p ]" := (@indhomog _ _ d p)
  (at level 8, d, p at level 2, format "[ ''dhomog_' d p ]").

(* -------------------------------------------------------------------- *)
Section MPolyHomogVec.
Local Notation isorted s := (sorted leq [seq val i | i <- s]).

Definition basis n d : {set (d.-tuple 'I_n)} :=
  [set t in {: d.-tuple 'I_n } | isorted t].

Definition s2m n (m : seq 'I_n) :=
  [multinom count_mem i m | i < n].

Definition m2s n (m : 'X_{1..n}) :=
  flatten [seq nseq (m i) i | i <- enum 'I_n].

Lemma inj_s2m n d: {in basis n d &, injective (@s2m n \o val)}.
Proof.
move=> t1 t2; rewrite !inE=> srt_t1 srt_t2 eq_tm.
apply/val_inj/(inj_map val_inj).
apply/(sorted_eq leq_trans anti_leq srt_t1 srt_t2).
apply/perm_map/allP=> /= i _; move/mnmP/(_ i): eq_tm.
by rewrite !mnmE => ->.
Qed.

Lemma srt_m2s n (m : 'X_{1..n}): isorted (m2s m).
Proof.
have h (T : eqType) (leT : rel T) (s : seq T) (F : T -> nat) x:
  reflexive leT -> transitive leT ->
     path leT x s
  -> path leT x (flatten [seq nseq (F x) x | x <- s]).
* move=> leTxx leT_tr; elim: s x => //= y s ih x /andP[le_xy pt_ys].
  case: (F y)=> /= [|k]; first apply/ih.
    rewrite path_min_sorted; do ?apply: (introT allP).
      exact/(path_sorted (x := y)).
    move=> z z_in_s /=; apply/(leT_tr y)=> //.
    by move/order_path_min: pt_ys => /(_ leT_tr) /allP /(_ _ z_in_s).
  rewrite le_xy /= cat_path; apply/andP; split.
    by elim: k=> //= k ->; rewrite leTxx.
  by have ->: last y (nseq k y) = y; [elim: k | apply/ih].
case: n m=> [|n] m.
  case: m => t /=; rewrite /m2s; have ->//: enum 'I_0 = [::].
  by apply/size0nil; rewrite size_enum_ord.
apply/(path_sorted (x := val (0 : 'I_n.+1))).
pose P := [rel i j : 'I_n.+1 | i <= j].
rewrite (map_path (e' := P) (b := xpred0)) //=; last first.
  by apply/hasP; case.
apply/h; try solve [exact/leqnn | exact/leq_trans].
rewrite -(map_path (h := val) (e := leq) (b := xpred0)) //.
  rewrite val_enum_ord /= path_min_sorted ?iota_sorted//;
  do ?exact: (introT allP).
by apply/hasP; case.
Qed.

Lemma size_m2s n (m : 'X_{1..n}): size (m2s m) = mdeg m.
Proof.
rewrite /m2s size_flatten /shape -map_comp /=.
rewrite (eq_map (_ : _ =1 m)); first by rewrite mdegE sumnE !big_map.
by move=> i /=; rewrite size_nseq.
Qed.

Lemma s2mK n (m : 'X_{1..n}): s2m (m2s m) = m.
Proof.
apply/mnmP=> i; rewrite mnmE /m2s /=.
rewrite count_flatten sumnE !big_map (bigD1 i) //=.
rewrite -sum1_count /= big_nseq_cond eqxx iter_succn.
rewrite add0n big1 ?addn0 // => j ne_ji; apply/count_memPn.
by apply/negP=> /nseqP [/esym/eqP]; rewrite (negbTE ne_ji).
Qed.

Local Notation sbasis n d :=
  [seq s2m t | t : d.-tuple 'I_n <- enum (basis n d)].

Lemma basis_cover n d (m : 'X_{1..n}): (mdeg m == d) = (m \in sbasis n d).
Proof.
apply/eqP/idP=> [eq_szm_d|].
  apply/mapP; have /eqP := size_m2s m; rewrite -eq_szm_d => sz_tm.
  exists (Tuple sz_tm); first by rewrite mem_enum inE /= srt_m2s.
  by rewrite s2mK.
case/mapP=> /= t _ ->; pose F i := count_mem i t.
  rewrite mdegE (eq_bigr F) {}/F; last first.
  by move=> /= i _; rewrite mnmE.
transitivity (\sum_i \sum_(j <- t | j == i) 1)%N.
  by apply: eq_bigr => i _; rewrite -big_filter sum1_size size_filter.
rewrite (exchange_big_dep predT)//=.
transitivity (\sum_(j <- t) 1)%N; last by rewrite sum1_size size_tuple.
by apply: eq_bigr => i _; rewrite (eq_bigl _ _ (eq_sym _)) big_pred1_eq.
Qed.

Lemma size_basis n d: size (sbasis n.+1 d) = 'C(d + n, d).
Proof. by rewrite size_map -cardE; apply/card_sorted_tuples. Qed.

Lemma uniq_basis n d: uniq (sbasis n d).
Proof.
rewrite map_inj_in_uniq ?enum_uniq // => t1 t2.
by rewrite !mem_enum; apply/inj_s2m.
Qed.

(* -------------------------------------------------------------------- *)
Context (n : nat) (R : ringType) (d : nat).

Lemma dhomog_vecaxiom: vector_axiom 'C(d + n, d) (dhomog n.+1 R d).
Proof.
pose b := sbasis n.+1 d.
pose t := [tuple of nseq d (0 : 'I_n.+1)].
pose M := fun i => nth 0%MM b i.
pose f (p : dhomog n.+1 R d) :=
  \row_(i < 'C(d + n, d)) p@_(nth 0%MM b i).
exists f => /= [c p q|].
  by apply/matrixP=> i j; rewrite !mxE /= mcoeffD mcoeffZ.
pose g (r : 'rV[R]_('C(d + n, d))) : {mpoly R[_]} :=
  \sum_(i < 'C(d + n, d)) (r 0 i) *: 'X_[M i].
have dhg r: g r \is d.-homog.
  rewrite rpred_sum //= => i _; apply/rpredZ.
  rewrite dhomogX basis_cover /M (nth_map t); last first.
    by rewrite -cardE card_sorted_tuples.
  by apply/map_f/mem_nth; rewrite -cardE card_sorted_tuples.
exists (fun r => DHomog (dhg r)); last first.
  move=> r; rewrite /g /f /=; apply/matrixP=> i j.
  rewrite mxE ord1 raddf_sum /= -/(M _) (bigD1 j) //=.
  rewrite mcoeffZ mcoeffX eqxx mulr1 big1 ?addr0 //.
  move=> k ne_kj; rewrite mcoeffZ mcoeffX /M.
  rewrite nth_uniq ?size_basis ?uniq_basis //.
  by rewrite (inj_eq (val_inj)) (negbTE ne_kj) mulr0.
move=> p; apply/val_inj/mpolyP=> m /=; rewrite /g /f.
pose P := fun (p : {mpoly R[n.+1]}) m => p@_m *: 'X_[m].
rewrite (eq_bigr (P p \o M \o val)) /P /=; last first.
  by move=> /= i _; rewrite mxE.
rewrite -(big_map (M \o val) xpredT (P p)) {}/P /M /=.
rewrite /index_enum -enumT /= map_comp val_enum_ord.
set r := map _ _; have {r}->: r = b; rewrite ?raddf_sum /=.
  apply/(@eq_from_nth _ 0%MM).
    by rewrite size_map size_iota size_basis.
  rewrite size_map size_iota=> i lt_i_C.
  by rewrite (nth_map 0%N) ?size_iota // nth_iota.
case: (mdeg m =P d)=> /eqP; rewrite basis_cover -/b.
  move=> m_in_b; rewrite (bigD1_seq m) ?uniq_basis //=.
  rewrite mcoeffZ mcoeffX eqxx mulr1 big1 ?addr0 // => m' ne.
  by rewrite mcoeffZ mcoeffX (negbTE ne) mulr0.
move=> m_notin_b; rewrite big_seq big1 /=.
  apply/esym/(@dhomog_nemf_coeff _ _ mdeg d).
    exact/dhomog_is_dhomog. by rewrite basis_cover.
move=> m'; apply/contraTeq; rewrite mcoeffZ mcoeffX.
by case: (m' =P m)=> [->|_]; last rewrite mulr0 eqxx.
Qed.

#[hnf] HB.instance Definition _ := Lmodule_hasFinDim.Build R (dhomog n.+1 R d)
  dhomog_vecaxiom.

End MPolyHomogVec.

(* -------------------------------------------------------------------- *)
Section MSymHomog.
Context (n : nat) (R : comRingType).
Implicit Types (p q r : {mpoly R[n]}).

Lemma msym_pihomog d p (s : 'S_n) :
  msym s (pihomog mdeg d p) = pihomog mdeg d (msym s p).
Proof.
rewrite (mpolyE p) ![_ (\sum_(m <- msupp p) _)]linear_sum /=.
rewrite [msym s _]linear_sum linear_sum /=.
apply: eq_bigr => m _; rewrite !linearZ /=; congr (_ *: _).
rewrite msymX !pihomogX /=.
have -> : mdeg [multinom m ((s^-1)%g i) | i < n] = mdeg m.
  by apply/perm_big/tuple_permP; exists (s^-1)%g.
by case: (mdeg m == d); rewrite ?msym0 ?msymX.
Qed.

Lemma pihomog_sym d p : p \is symmetric -> pihomog mdeg d p \is symmetric.
Proof. by move=> /issymP Hp; apply/issymP => s; rewrite msym_pihomog Hp. Qed.

End MSymHomog.

(* -------------------------------------------------------------------- *)
Section MESymFundamentalHomog.
Context (n : nat) (R : comRingType).

Local Notation S := [tuple mesym n R i.+1  | i < n].

Lemma dhomog_mesym d : mesym n R d \is d.-homog.
Proof.
apply/dhomogP => m; rewrite msupp_mesymP => /existsP [/= s].
by case/andP=> /eqP<- {d} /eqP -> {m}; exact/mdeg_mesym1.
Qed.

Lemma dhomog_XS (m : 'X_{1..n}) : 'X_[m] \mPo S \is (mnmwgt m).-homog.
Proof.
pose dt := [tuple (i.+1 * m i)%N | i < n].
pose mt := [tuple (mesym n R i.+1) ^+ m i | i < n].
rewrite [X in X \is _](_ : _ = \prod_(i <- mt) i); last first.
  rewrite comp_mpolyX (eq_bigr (tnth mt)) ?big_tuple //.
  by move=> i _ /=; rewrite !tnth_mktuple.
rewrite [X in X.-homog](_ : _ = (\sum_(i <- dt) i)%N); last first.
  rewrite /mnmwgt big_tuple (eq_bigr (tnth dt)) //.
  by move=> i _ /=; rewrite !tnth_mktuple mulnC.
apply/dhomog_prod => i; rewrite !tnth_mktuple => {mt dt}.
exact/dhomogMn/dhomog_mesym.
Qed.

Lemma pihomog_mPo p d : pihomog mdeg d (p \mPo S) = pihomog mnmwgt d p \mPo S.
Proof.
elim/mpolyind: p; first by rewrite !linear0.
move=> c m p msupp cn0 ihp; rewrite !linearP /= {}ihp.
congr (c *: _ + _); case: (eqVneq (mnmwgt m) d) => wgtm.
+ have /eqP := wgtm; rewrite -(dhomogX R) => /pihomog_dE ->.
  by have := dhomog_XS m; rewrite wgtm => /pihomog_dE ->.
rewrite (pihomog_ne0 wgtm (dhomog_XS m)).
by rewrite (pihomog_ne0 wgtm) ?linear0 // dhomogX.
Qed.

Lemma mwmwgt_homogE (p : {mpoly R[n]}) d :
  (p \is d.-homog for mnmwgt) = (p \mPo S \is d.-homog).
Proof.
by rewrite !homog_piE pihomog_mPo; apply/eqP/eqP=> [->|/msym_fundamental_un ->].
Qed.

Lemma sym_fundamental_homog (p : {mpoly R[n]}) (d : nat) :
  p \is symmetric -> p \is d.-homog ->
  { t | t \mPo S = p /\ t \is d.-homog for mnmwgt }.
Proof.
move/sym_fundamental => [t [tSp _]] homp.
exists (pihomog mnmwgt d t); split.
+ by rewrite -pihomog_mPo tSp pihomog_dE.
+ exact: pihomogP.
Qed.

End MESymFundamentalHomog.
