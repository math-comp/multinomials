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
(*              p@`_m == the coefficient of 'X_[m] in p.                      *)
(*            msize p == 1 + the degree of p, or 0 if p = 0.                  *)
(*            mlead p == the leading monomial of p; this is the maximum       *)
(*                       monomial of p for the degrevlex monimial ordering.   *)
(*                       mlead p defaults to 0%MM when p is 0.                *)
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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun tuple bigop ssralg ssrint matrix.
Require Import vector fingroup perm zmodp binomial bigenough poly.
Require Import ssrcomplements poset freeg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Monoid GRing.Theory BigEnough.

Local Open Scope ring_scope.

Delimit Scope mpoly_scope with MP.
Delimit Scope multi_scope with MM.

Local Notation simpm := Monoid.simpm.
Local Notation ilift := fintype.lift.

Local Notation efst := (@fst _ _) (only parsing).
Local Notation esnd := (@snd _ _) (only parsing).

Local Infix "@@" := product (at level 60, right associativity).
Local Notation widen := (widen_ord (leqnSn _)).

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
  (at level 0, n at level 2, no associativity).
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
  (at level 2, format "c %:MP").
Reserved Notation "c %:MP_[ n ]"
  (at level 2, n at level 50, format "c %:MP_[ n ]").
Reserved Notation "c %:IP"
  (at level 2, format "c %:IP").
Reserved Notation "s @_ i"
   (at level 3, i at level 2, left associativity, format "s @_ i").
Reserved Notation "e .@[ x ]"
  (at level 2, left associativity, format "e .@[ x ]").
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
Variable n : nat.

Inductive multinom : predArgType :=
  Multinom of n.-tuple nat.

Coercion multinom_val M := let: Multinom m := M in m.

Canonical multinom_subType := Eval hnf in [newType for multinom_val].

Definition fun_of_multinom M (i : 'I_n) := tnth (multinom_val M) i.

Coercion fun_of_multinom : multinom >-> Funclass.

Lemma multinomE M : (Multinom M) =1 tnth M.
Proof. by []. Qed.
End MultinomDef.

Notation "[ 'multinom' s ]" := (@Multinom _ s) : form_scope.
Notation "[ 'multinom' 'of'  s ]" := [multinom [tuple of s]] : form_scope.
Notation "[ 'multinom' E | i < n ]" := [multinom [tuple E | i < n]] : form_scope.

(* -------------------------------------------------------------------- *)
Notation "''X_{1..' n '}'" := (multinom n).

Definition multinom_eqMixin n :=
  Eval hnf in [eqMixin of 'X_{1..n} by <:].
Canonical multinom_eqType n :=
  Eval hnf in EqType 'X_{1..n} (multinom_eqMixin n).
Definition multinom_choiceMixin n :=
  [choiceMixin of 'X_{1..n} by <:].
Canonical multinom_choiceType n :=
  Eval hnf in ChoiceType 'X_{1..n} (multinom_choiceMixin n).
Definition multinom_countMixin n :=
  [countMixin of 'X_{1..n} by <:].
Canonical multinom_countType n :=
  Eval hnf in CountType 'X_{1..n} (multinom_countMixin n).
Canonical multinom_subCountType n :=
  Eval hnf in [subCountType of 'X_{1..n}].

Bind Scope multi_scope with multinom.

(* -------------------------------------------------------------------- *)
Definition lem n (m1 m2 : 'X_{1..n}) :=
  [forall i, m1%MM i <= m2%MM i].

Definition ltm n (m1 m2 : 'X_{1..n}) :=
  (m1 != m2) && (lem m1 m2).

(* -------------------------------------------------------------------- *)
Section MultinomTheory.
Context {n : nat}.

Implicit Types t : n.-tuple nat.
Implicit Types m : 'X_{1..n}.

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
case: m1 m2 => [m1] [m2] /=; split=> [[->]//|] h.
apply/val_eqP/eqP/eq_from_tnth => i /=.
by rewrite -!multinomE.
Qed.
End MultinomTheory.

(* -------------------------------------------------------------------- *)
Section MultinomMonoid.
Context {n : nat}.

Implicit Types t : n.-tuple nat.
Implicit Types m : 'X_{1..n}.

Definition mnm0 :=
  [multinom 0%N | _ < n].

Definition mnm1 (c : 'I_n) :=
  [multinom ((c == i) : nat) | i < n].

Definition mnm_add m1 m2 :=
  [multinom (m1 i + m2 i)%N | i < n].

Definition mnm_sub m1 m2 :=
  [multinom (m1 i - m2 i)%N | i < n].

Definition mnm_muln m i :=
  nosimpl iterop _ i mnm_add m mnm0.

Local Notation "0"         := mnm0 : multi_scope.
Local Notation "'U_(' n )" := (mnm1 n) : multi_scope.
Local Notation "m1 + m2"   := (mnm_add m1 m2) : multi_scope.
Local Notation "m1 - m2"   := (mnm_sub m1 m2) : multi_scope.
Local Notation "x *+ n"    := (mnm_muln x n) : multi_scope.

Local Notation "+%MM" := (@mnm_add).
Local Notation "-%MM" := (@mnm_sub).

Local Notation "m1 <= m2" := (lem m1 m2) : multi_scope.
Local Notation "m1 < m2"  := (ltm m1 m2) : multi_scope.

Lemma mnm0E i : 0%MM i = 0%N.
Proof. by apply/mnmE. Qed.

Lemma mnm1E i j : U_(i)%MM j = (i == j)%N.
Proof. by apply/mnmE. Qed.

Lemma mnmDE i m1 m2 : (m1 + m2)%MM i = (m1 i + m2 i)%N.
Proof. by apply/mnmE. Qed.

Lemma mnmBE i m1 m2 : (m1 - m2)%MM i = (m1 i - m2 i)%N.
Proof. by apply/mnmE. Qed.

Lemma mnm_sumE (I : Type) i (r : seq I) P F :
    (\big[+%MM/0%MM]_(x <- r | P x) (F x)) i
  = (\sum_(x <- r | P x) (F x i))%N.
Proof. by apply/(big_morph (fun m => m i)) => [x y|]; rewrite mnmE. Qed.

(*-------------------------------------------------------------------- *)
Lemma mnm_lepP m1 m2 : reflect (forall i, m1 i <= m2 i) (m1 <= m2)%MM.
Proof. by apply: (iffP forallP). Qed.

Lemma lepm_refl m : (m <= m)%MM.
Proof. by apply/mnm_lepP=> i. Qed.

Lemma lepm_trans m3 m1 m2 : (m1 <= m2 -> m2 <= m3 -> m1 <= m3)%MM.
Proof.
move=> /mnm_lepP h1 /mnm_lepP h2; apply/mnm_lepP.
by move=> i; apply/(leq_trans (h1 i) (h2 i)).
Qed.

Lemma lep1mP i m : (U_(i) <= m)%MM = (m i != 0)%N.
Proof.
apply/mnm_lepP/idP=> [/(_ i)|]; rewrite ?mnm1E -?lt0n.
  by case: eqP.
  by move=> lt0_mi j; rewrite mnm1E; case: eqP=> // <-.
Qed.

Lemma addmC : commutative mnm_add.
Proof. by move=> m1 m2; apply/mnmP=> i; rewrite !mnmE addnC. Qed.

Lemma addmA : associative mnm_add.
Proof. by move=> m1 m2 m3; apply/mnmP=> i; rewrite !mnmE addnA. Qed.

Lemma add0m : left_id 0%MM mnm_add.
Proof. by move=> m; apply/mnmP=> i; rewrite !mnmE add0n. Qed.

Lemma addm0 : right_id 0%MM mnm_add.
Proof. by move=> m; rewrite addmC add0m. Qed.

Canonical mnm_monoid := Monoid.Law addmA add0m addm0.
Canonical mnm_comoid := Monoid.ComLaw addmC.

Lemma subm0 m : (m - 0 = m)%MM.
Proof. by apply/mnmP=> i; rewrite !mnmE subn0. Qed.

Lemma sub0m m : (0 - m = 0)%MM.
Proof. by apply/mnmP=> i; rewrite !mnmE sub0n. Qed.

Lemma eqm_add2l m n1 n2 :
  ((m + n1)%MM == (m + n2)%MM) = (n1 == n2).
Proof.
apply/eqP/eqP=> [|->//] /mnmP h; apply/mnmP.
by move=> i; move: (h i); rewrite !mnmE => /addnI.
Qed.

Lemma eqm_add2r m n1 n2 :
  ((n1 + m)%MM == (n2 + m)%MM) = (n1 == n2).
Proof. by rewrite ![(_ + m)%MM]addmC eqm_add2l. Qed.

Lemma addmK m : cancel (mnm_add^~ m) (mnm_sub^~ m).
Proof. by move=> m' /=; apply/mnmP=> i; rewrite !mnmE addnK. Qed.

Lemma submK m m' : (m <= m')%MM -> (m' - m + m = m')%MM.
Proof. by move/mnm_lepP=> h; apply/mnmP=> i; rewrite !mnmE subnK. Qed.

Lemma addmBA m1 m2 m3 :
  (m3 <= m2)%MM -> (m1 + (m2 - m3))%MM = (m1 + m2 - m3)%MM.
Proof. by move/mnm_lepP=> h; apply/mnmP=> i; rewrite !mnmE addnBA. Qed.

Lemma submDA m1 m2 m3 : (m1 - m2 - m3)%MM = (m1 - (m2 + m3))%MM.
Proof. by apply/mnmP=> i; rewrite !mnmE subnDA. Qed.

Lemma submBA m1 m2 m3 :
  (m3 <= m2)%MM -> (m1 - (m2 - m3) = m1 + m3 - m2)%MM.
Proof. by move/mnm_lepP=> h; apply/mnmP=> i; rewrite !mnmE subnBA. Qed.

Lemma lem_subr m1 m2 : (m1 - m2 <= m1)%MM.
Proof. by apply/mnm_lepP=> i; rewrite !mnmE leq_subr. Qed.

(* -------------------------------------------------------------------- *)
Lemma mulm0n m : (m *+ 0 = 0)%MM.
Proof. by []. Qed.

Lemma mulm1n m : (m *+ 1 = m)%MM.
Proof. by []. Qed.

Lemma mulmS m i : ((m *+ i.+1) = (m + m *+ i))%MM.
Proof. by rewrite /mnm_muln !Monoid.iteropE iterS /=. Qed.

Lemma mulmSr m i : ((m *+ i.+1) = (m *+ i + m))%MM.
Proof. by rewrite mulmS mulmC. Qed.

Lemma mulmnE m k i : ((m *+ k) i)%MM = (k * (m i))%N.
Proof.
elim: k => [|k ih]; first by rewrite mul0n mulm0n !mnmE.
by rewrite mulmS mulSn mnmDE ih.
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

Lemma mnm_sumUE {n : nat} (m : 'X_{1..n}) : m = (\sum_(i < n) U_(i) *+ (m i))%MM.
Proof.
  rewrite mnmP => i; rewrite mnm_sumE.
  rewrite (bigID (xpred1 i)) /= big_pred1_eq big1; first last.
    move=> j; rewrite mulmnE mnm1E => /negbTE ->; by rewrite muln0.
  by rewrite addn0 mulmnE mnm1E eq_refl muln1.
Qed.

(* -------------------------------------------------------------------- *)
Section MultinomDeg.
Context {n : nat}.

Implicit Types m : 'X_{1..n}.

Definition mdeg m := (\sum_(i <- m) i)%N.

Lemma mdegE m : mdeg m = (\sum_i (m i))%N.
Proof. by rewrite /mdeg big_tuple. Qed.

Lemma mdeg0 : mdeg 0%MM = 0%N.
Proof. by rewrite mdegE big1 // => i; rewrite mnmE. Qed.

Lemma mdeg1 i : mdeg U_(i) = 1%N.
Proof.
rewrite mdegE (bigD1 i) //= big1 => [|j].
  by rewrite mnmE eqxx addn0.
by apply/contraNeq; rewrite mnmE eqb0 negbK eq_sym.
Qed.

Lemma mdegD m1 m2 : mdeg (m1 + m2) = (mdeg m1 + mdeg m2)%N.
Proof. by rewrite !mdegE -big_split //=; apply/eq_bigr=> i _; rewrite mnmE. Qed.

Lemma mdegB m1 m2 : mdeg (m1 - m2) <= mdeg m1.
Proof. by rewrite !mdegE; apply/leq_sum => i _; rewrite mnmE leq_subr.  Qed.

Lemma mdeg_sum (I : Type) (r : seq I) P F :
    mdeg (\big[+%MM/0%MM]_(x <- r | P x) (F x))
  = (\sum_(x <- r | P x) (mdeg (F x)))%N.
Proof. by apply/big_morph; [apply/mdegD | apply/mdeg0]. Qed.

Lemma mdeg_eq0 m : (mdeg m == 0%N) = (m == 0%MM).
Proof.
apply/idP/eqP=> [|->]; last by rewrite mdeg0.
move=> h; apply/mnmP=> i; move: h; rewrite mdegE mnm0E.
by rewrite (bigD1 i) //= addn_eq0 => /andP [/eqP-> _].
Qed.

Lemma mnmD_eq0 m1 m2 : (m1 + m2 == 0)%MM = (m1 == 0%MM) && (m2 == 0%MM).
Proof. by rewrite -!mdeg_eq0 mdegD addn_eq0. Qed.

Lemma mnm1_eq0 i : (U_(i) == 0 :> 'X_{1..n})%MM = false.
Proof. by rewrite -mdeg_eq0 mdeg1. Qed.
End MultinomDeg.

(* -------------------------------------------------------------------- *)
Section MultinomOrder.
Context {n : nat}.

Implicit Types t : n.-tuple nat.
Implicit Types m : 'X_{1..n}.

Definition mnmc_le m1 m2 :=
  @lex [posetType of nat] (mdeg m1 :: m1) (mdeg m2 :: m2).

Definition mnmc_lt m1 m2 :=
  @ltx [posetType of nat] (mdeg m1 :: m1) (mdeg m2 :: m2).

Lemma lemc_refl : reflexive mnmc_le.
Proof. by case=> t; apply/lex_refl. Qed.

Lemma lemc_antisym : antisymmetric mnmc_le.
Proof.
case=> [[m1 /= h1]] [[m2 /= h2]] /=.
rewrite /mnmc_le => /lex_antisym [_ h].
by apply/eqP; do 2! rewrite -val_eqE /= ?h.
Qed.

Lemma lemc_trans : transitive mnmc_le.
Proof. by case=> [m1] [m2] [m3]; apply/lex_trans. Qed.

Lemma lemc_total : total mnmc_le.
Proof.
case=> [m1] [m2]; apply/lex_total.
by move=> n1 n2; rewrite !lenP leq_total.
Qed.

Definition multinom_posetMixin :=
  POSetMixin lemc_refl lemc_antisym lemc_trans.
Canonical multinom_posetType :=
  Eval hnf in (POSetType 'X_{1..n} multinom_posetMixin).

Lemma le0m (m : 'X_{1..n}) : (0%MM <= m)%O.
Proof.
rewrite /le /= /mnmc_le /=; case: (mdeg m =P 0%N).
  move/eqP; rewrite mdeg_eq0=> /eqP->.
  by rewrite ltoo eqxx /= lex_refl.
by move/eqP; rewrite -lt0n mdeg0 ltnP => ->.
Qed.

Lemma lem_total: total (@le multinom_posetType).
Proof. exact/lemc_total. Qed.

Local Hint Resolve lem_total.

Definition multinom_CPOMixin :=
  CPOMixin le0m.
Canonical multinom_CPOType :=
  Eval hnf in (CPOType 'X_{1..n} multinom_CPOMixin).

Lemma lem_mdeg (m1 m2 : 'X_{1..n}) : (m1 <= m2)%O -> mdeg m1 <= mdeg m2.
Proof.
rewrite /le /= /mnmc_le /= leq_eqVlt ltnP.
by case/orP=> [->|/andP [->//]]; rewrite orbC.
Qed.

Lemma mdeg_max (m1 m2 : 'X_{1..n}) :
  mdeg (maxo m1 m2) = maxn (mdeg m1) (mdeg m2).
Proof.
apply/esym; rewrite /maxo; case: (boolP (_ < _)%O).
  by move/ltoW/lem_mdeg/maxn_idPr.
by rewrite -letNgt // => /lem_mdeg/maxn_idPl.
Qed.

Lemma mdeg_bigmax (r : seq 'X_{1..n}) :
  mdeg (\max_(m <- r) m)%O = \max_(m <- r) mdeg m.
Proof.
elim: r => [|m r ih]; first by rewrite !big_nil mdeg0.
by rewrite !big_cons mdeg_max ih.
Qed.

Lemma ltm_ltx (m m' : 'X_{1..n}) :
  (m < m')%O = ltx (mdeg m :: m) (mdeg m' :: m').
Proof.
apply/idP/idP.
+ rewrite lto_neqAle /le /= /mnmc_le lex_eqVlt.
  case/andP=> ne_mm' /orP [] //; rewrite eqseq_cons /=.
  by rewrite !(inj_eq val_inj) (negbTE ne_mm') andbF.
+ rewrite /ltx; case/andP; rewrite eqseq_cons => ne.
  have {ne}ne: m != m'; first apply/negP=> /eqP.
    by move=> eq_mm'; rewrite eq_mm' !eqxx in ne.
  by move=> lex; rewrite lto_neqAle (negbTE ne).
Qed.

Lemma ltm_lem_add (m1 m2 n1 n2 : 'X_{1..n}) :
  (m1 < n1 -> m2 <= n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
Proof.
have eq (m m' : 'X_{1..n}):
    [seq (x.1 + x.2 )%N | x <- zip m m']
  = [seq (m i + m' i)%N | i <- enum 'I_n].
+ have sz_mm': size (zip m m') = n.
    by rewrite size_zip !size_tuple minnn.
  apply/(@eq_from_nth _ 0%N).
    by rewrite !size_map sz_mm' -enumT size_enum_ord.
  move=> i; rewrite size_map sz_mm' => lt_in.
  rewrite (nth_map (0, 0)%N) ?sz_mm' //=.
  rewrite nth_zip ?size_tuple //=.
  rewrite (nth_map (Ordinal lt_in)) ?size_enum_ord //.
  by rewrite !(mnm_nth 0%N) !nth_enum_ord.
rewrite /le /= /mnmc_le ltm_ltx => ltx1 lex2.
have := (ltx_lex_nat_sum ltx1 lex2) => /= lt.
by rewrite ltm_ltx /= !mdegD -!eq.
Qed.

Lemma lem_ltm_add (m1 m2 n1 n2 : 'X_{1..n}) :
  (m1 <= n1 -> m2 < n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
Proof.
move=> le /ltm_lem_add /(_ le).
by rewrite [(m1+_)%MM]addmC [(n1+_)%MM]addmC.
Qed.

Lemma ltm_add (m1 m2 n1 n2 : 'X_{1..n}) :
  (m1 < n1 -> m2 < n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
Proof. by move=> lt1 /ltoW /(ltm_lem_add lt1). Qed.

Lemma lem_add (m1 m2 n1 n2 : 'X_{1..n}) :
  (m1 <= n1 -> m2 <= n2 -> (m1 + m2)%MM <= (n1 + n2)%MM)%O.
Proof.
rewrite leo_eqVlt; case/orP=> [/eqP->|].
  rewrite leo_eqVlt; case/orP=> [/eqP->|]; first by rewrite leoo.
  by move/(lem_ltm_add (leoo n1))/ltoW.
by move=> lt; move/(ltm_lem_add lt)/ltoW.
Qed.

Lemma lemP m1 m2 : mdeg m1 = mdeg m2 ->
  reflect
    (exists2 i : 'I_n,
          forall (j : 'I_n), (j < i)%N -> m1 j = m2 j
        & m1 i < m2 i)
    (m1 < m2)%O.
Proof.
move=> eq_mdeg; rewrite lto_neqAle /le /=.
rewrite /mnmc_le /= eq_mdeg ltoo eqxx /=.
apply: (iffP idP) => [/ltxP|].
+ case=> i h1 h2; exists i => [j|].
  by apply/h1. by rewrite -ltnP; apply/h2.
+ case=> i h1 h2; apply/ltxP; exists i.
   by apply/h1. by rewrite ltnP; apply/h2.
Qed.

Section WF.
Variable P : 'X_{1..n} -> Type.

Lemma ltmwf :
     (forall m1, (forall m2, (m2 < m1)%O -> P m2) -> P m1)
  -> forall m, P m.
Proof.
pose tof m := [tuple of mdeg m :: m].
move=> ih m; move: {2}(tof _) (erefl (tof m))=> t.
elim/ltxwf: t m=> //=; last first.
  move=> t wih m Em; apply/ih=> m' lt_m'm.
  by apply/(wih (tof m'))=> //; rewrite -Em -ltm_ltx.
move=> Q {ih} ih x; elim: x {-2}x (leqnn x).
  move=> x; rewrite leqn0=> /eqP->; apply/ih.
  by move=> y; rewrite ltnP ltn0.
move=> k wih l le_l_Sk; apply/ih=> y; rewrite ltnP=> lt_yl.
by apply/wih; have := leq_trans lt_yl le_l_Sk; rewrite ltnS.
Qed.
End WF.
End MultinomOrder.

Lemma poset_lem_total n: @total [posetType of 'X_{1..n}] <=%O.
Proof. by apply/lem_total. Qed.

Local Hint Extern 0 (total _) => by apply/poset_lem_total.

(* -------------------------------------------------------------------- *)
Section DegBoundMultinom.
Variable n bound : nat.

Record bmultinom := BMultinom { bmnm :> 'X_{1..n}; _ : mdeg bmnm < bound }.

Canonical bmultinom_subType := Eval hnf in [subType for bmnm].

Definition bmultinom_eqMixin      := Eval hnf in [eqMixin of bmultinom by <:].
Canonical  bmultinom_eqType       := Eval hnf in EqType bmultinom bmultinom_eqMixin.
Definition bmultinom_choiceMixin  := [choiceMixin of bmultinom by <:].
Canonical  bmultinom_choiceType   := Eval hnf in ChoiceType bmultinom bmultinom_choiceMixin.
Definition bmultinom_countMixin   := [countMixin of bmultinom by <:].
Canonical  bmultinom_countType    := Eval hnf in CountType bmultinom bmultinom_countMixin.
Canonical  bmultinom_subCountType := Eval hnf in [subCountType of bmultinom].

Lemma bmeqP (m1 m2 : bmultinom) : (m1 == m2) = (m1 == m2 :> 'X_{1..n}).
Proof. by rewrite eqE. Qed.

Lemma bmdeg (m : bmultinom) : mdeg m < bound.
Proof. by case: m. Qed.

Lemma bm0_proof : mdeg (0%MM : 'X_{1..n}) < bound.+1.
Proof. by rewrite mdeg0. Qed.
End DegBoundMultinom.

Definition bm0 n b := BMultinom (bm0_proof n b).
Implicit Arguments bm0 [n b].

Notation "''X_{1..' n  <  b '}'"       := (bmultinom n b).
Notation "''X_{1..' n  <  b1 , b2 '}'" := ('X_{1..n < b1} * 'X_{1..n < b2})%type.

(* -------------------------------------------------------------------- *)
Section FinDegBound.
Variables n b : nat.

Definition bmnm_enum : seq 'X_{1..n < b} :=
  let project (x : n.-tuple 'I_b) := [multinom of map val x] in
  pmap insub [seq (project x) | x <- enum {: n.-tuple 'I_b }].

Lemma bmnm_enumP : Finite.axiom bmnm_enum.
Proof.
case=> m lt_dm_b /=; rewrite count_uniq_mem; last first.
  rewrite (pmap_uniq (@insubK _ _ _)) 1?map_inj_uniq ?enum_uniq //.
  by move=> t1 t2 [] /(inj_map val_inj) /eqP; rewrite val_eqE => /eqP->.
apply/eqP; rewrite eqb1 mem_pmap_sub /=; apply/mapP.
case: b m lt_dm_b=> // b' [m] /= lt_dm_Sb; exists [tuple of map inord m].
  by rewrite mem_enum.
apply/mnmP=> i; rewrite !multinomE !tnth_map inordK //.
move: lt_dm_Sb; rewrite mdegE (bigD1 i) //= multinomE.
by move/(leq_trans _)=> ->//; rewrite ltnS leq_addr.
Qed.

Canonical bmnm_finMixin   := Eval hnf in FinMixin bmnm_enumP.
Canonical bmnm_finType    := Eval hnf in FinType 'X_{1..n < b} bmnm_finMixin.
Canonical bmnm_subFinType := Eval hnf in [subFinType of 'X_{1..n < b}].
End FinDegBound.

(* -------------------------------------------------------------------- *)
Section MPolyDef.
Variable n : nat.
Variable R : ringType.

Record mpoly := MPoly of {freeg 'X_{1..n} / R}.

Coercion mpoly_val p := let: MPoly D := p in D.

Canonical  mpoly_subType     := Eval hnf in [newType for mpoly_val].
Definition mpoly_eqMixin     := Eval hnf in [eqMixin of mpoly by <:].
Canonical  mpoly_eqType      := Eval hnf in EqType mpoly mpoly_eqMixin.
Definition mpoly_choiceMixin := [choiceMixin of mpoly by <:].
Canonical  mpoly_choiceType  := Eval hnf in ChoiceType mpoly mpoly_choiceMixin.

Definition mpoly_of of phant R := mpoly.

Identity Coercion type_mpoly_of : mpoly_of >-> mpoly.
End MPolyDef.

Bind Scope ring_scope with mpoly_of.
Bind Scope ring_scope with mpoly.

Notation "{ 'mpoly' T [ n ] }" := (mpoly_of n (Phant T)).
Notation "[ 'mpoly' D ]" := (@MPoly _ _ D : {mpoly _[_]}).

(* -------------------------------------------------------------------- *)
Section MPolyTheory.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types D : {freeg 'X_{1..n} / R}.

Lemma mpoly_valK D : [mpoly D] = D :> {freeg _ / _}.
Proof. by []. Qed.

Lemma mpoly_eqP p q : (p = q) <-> (p = q :> {freeg _ / _}).
Proof.
split=> [->//|]; case: p q => [p] [q].
by rewrite !mpoly_valK=> ->.
Qed.

Definition mpolyC (c : R) : {mpoly R[n]} :=
  [mpoly << c *g 0%MM >>].

Local Notation "c %:MP" := (mpolyC c) : ring_scope.

Lemma mpolyC_eq (c1 c2 : R) : (c1%:MP == c2%:MP) = (c1 == c2).
Proof.
apply/eqP/eqP=> [|->//] /eqP/freeg_eqP.
by move/(_ 0%MM); rewrite !coeffU eqxx !simpm.
Qed.

Definition mcoeff (m : 'X_{1..n}) p : R :=
  coeff m p.

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
Proof. by rewrite msuppE /mcoeff mem_dom inE. Qed.

Lemma memN_msupp_eq0 p m : m \notin msupp p -> p@_m = 0.
Proof. by rewrite !msuppE /mcoeff => /coeff_outdom. Qed.

Lemma mcoeff_eq0 p m : (p@_m == 0) = (m \notin msupp p).
Proof. by rewrite msuppE mem_dom inE /mcoeff negbK. Qed.

Lemma msupp0 : msupp 0%:MP = [::].
Proof. by rewrite msuppE /= freegU0 dom0. Qed.

Lemma msupp1 : msupp 1%:MP = [:: 0%MM].
Proof. by rewrite msuppE /= domU1. Qed.

Lemma msuppC (c : R) :
  msupp c%:MP = if c == 0 then [::] else [:: 0%MM].
Proof.
case: (c =P 0)=> [->|/eqP nz_c]; first by rewrite msupp0.
by rewrite msuppE domU //.
Qed.

Lemma mpolyP p q : (forall m, mcoeff m p = mcoeff m q) <-> (p = q).
Proof. by split=> [|->] // h; apply/mpoly_eqP/eqP/freeg_eqP/h. Qed.

Lemma freeg_mpoly p: p = [mpoly \sum_(m <- msupp p) << p@_m *g m >>].
Proof. by case: p=> p; apply/mpoly_eqP=> /=; rewrite -{1}[p]freeg_sumE. Qed.
End MPolyTheory.

Notation "c %:MP" := (mpolyC _ c) : ring_scope.
Notation "c %:MP_[ n ]" := (mpolyC n c) : ring_scope.

Notation "p @_ i" := (mcoeff i p) : ring_scope.

Hint Resolve msupp_uniq.

(* -------------------------------------------------------------------- *)
Section MPolyZMod.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

Definition mpoly_opp p := [mpoly -(mpoly_val p)].

Definition mpoly_add p q := [mpoly mpoly_val p + mpoly_val q].

Lemma add_mpoly0 : left_id 0%:MP mpoly_add.
Proof. by move=> p; apply/mpoly_eqP; rewrite !mpoly_valK freegU0 add0r. Qed.

Lemma add_mpolyN : left_inverse 0%:MP mpoly_opp mpoly_add.
Proof. by move=> p; apply/mpoly_eqP; rewrite !mpoly_valK freegU0 addrC subrr. Qed.

Lemma add_mpolyC : commutative mpoly_add.
Proof. by move=> p q; apply/mpoly_eqP; rewrite !mpoly_valK addrC. Qed.

Lemma add_mpolyA : associative mpoly_add.
Proof. by move=> p q r; apply/mpoly_eqP; rewrite !mpoly_valK addrA. Qed.

Definition mpoly_zmodMixin :=
  ZmodMixin add_mpolyA add_mpolyC add_mpoly0 add_mpolyN.

Canonical mpoly_zmodType :=
  Eval hnf in ZmodType {mpoly R[n]} mpoly_zmodMixin.
Canonical mpolynomial_zmodType :=
  Eval hnf in ZmodType (mpoly n R) mpoly_zmodMixin.

Definition mpoly_scale c p := [mpoly c *: (mpoly_val p)].

Local Notation "c *:M p" := (mpoly_scale c p)
  (at level 40, left associativity).

Lemma scale_mpolyA c1 c2 p :
  c1 *:M (c2 *:M p) = (c1 * c2) *:M p.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerA. Qed.

Lemma scale_mpoly1m p : 1 *:M p = p.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scale1r. Qed.

Lemma scale_mpolyDr c p1 p2 :
  c *:M (p1 + p2) = c *:M p1 + c *:M p2.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerDr. Qed.

Lemma scale_mpolyDl p c1 c2 :
  (c1 + c2) *:M p = c1 *:M p + c2 *:M p.
Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerDl. Qed.

Definition mpoly_lmodMixin :=
  LmodMixin scale_mpolyA scale_mpoly1m scale_mpolyDr scale_mpolyDl.

Canonical mpoly_lmodType :=
  Eval hnf in LmodType R {mpoly R[n]} mpoly_lmodMixin.
Canonical mpolynomial_lmodType :=
  Eval hnf in LmodType R (mpoly n R) mpoly_lmodMixin.

Local Notation mcoeff := (@mcoeff n R).

Lemma mcoeff_is_additive m : additive (mcoeff m).
Proof. by move=> p q /=; rewrite /mcoeff raddfB. Qed.

Canonical mcoeff_additive m: {additive {mpoly R[n]} -> R} :=
  Additive (mcoeff_is_additive m).

Lemma mcoeff0   m   : mcoeff m 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mcoeffN   m   : {morph mcoeff m: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mcoeffD   m   : {morph mcoeff m: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mcoeffB   m   : {morph mcoeff m: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mcoeffMn  m k : {morph mcoeff m: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mcoeffMNn m k : {morph mcoeff m: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma mcoeffZ c p m : mcoeff m (c *: p) = c * (mcoeff m p).
Proof. by rewrite /mcoeff coeffZ. Qed.

Canonical mcoeff_linear m : {scalar {mpoly R[n]}} :=
  AddLinear ((fun c => (mcoeffZ c)^~ m) : scalable_for *%R (mcoeff m)).

Local Notation mpolyC := (@mpolyC n R).

Lemma mpolyC_is_additive : additive mpolyC.
Proof. by move=> p q; apply/mpoly_eqP; rewrite /= freegUB. Qed.

Canonical mpolyC_additive : {additive R -> {mpoly R[n]}} :=
  Additive mpolyC_is_additive.

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
rewrite eqE /=; apply/idP/eqP=> [|->//].
by move/freeg_eqP/(_ 0%MM); rewrite !coeffU eqxx !mulr1.
Qed.
End MPolyZMod.

(* -------------------------------------------------------------------- *)
Section MMeasureDef.
Variable n : nat.

Structure measure := Measure {
  mf : 'X_{1..n} -> nat;
  _  : mf 0 = 0%N;
  _  : {morph mf : m1 m2 / (m1 + m2)%MM >-> (m1 + m2)%N}
}.

Coercion mf : measure >-> Funclass.

Let measure_id (mf1 mf2 : 'X_{1..n} -> nat) := phant_id mf1 mf2.

Definition clone_measure mf :=
  fun (mfL : measure) & measure_id mfL mf =>
  fun mf0 mfD (mfL' := @Measure mf mf0 mfD)
    & phant_id mfL' mfL => mfL'.
End MMeasureDef.

Notation "[ 'measure' 'of' f ]" := (@clone_measure _ f _ id _ _ id)
  (at level 0, format"[ 'measure'  'of'  f ]") : form_scope.

(* -------------------------------------------------------------------- *)
Canonical mdeg_measure n := Eval hnf in @Measure n _ mdeg0 mdegD.

(* -------------------------------------------------------------------- *)
Section MMeasure.
Variable n : nat.
Variable R : ringType.

Implicit Types m : 'X_{1..n}.
Implicit Types p q : {mpoly R[n]}.

Variable mf : measure n.

Lemma mf0 : mf 0%MM = 0%N.
Proof. by case: mf. Qed.

Lemma mfD : {morph mf : m1 m2 / (m1 + m2)%MM >-> (m1 + m2)%N}.
Proof. by case: mf. Qed.

Definition mmeasure p := (\max_(m <- msupp p) (mf m).+1)%N.

Lemma mmeasureE p : mmeasure p = (\max_(m <- msupp p) (mf m).+1)%N.
Proof. by []. Qed.

Lemma mmeasure0 : mmeasure 0 = 0%N.
Proof. by rewrite /mmeasure msupp0 big_nil. Qed.

Lemma mmeasure_mnm_lt p m : m \in msupp p -> mf m < mmeasure p.
Proof.
move=> m_in_p; rewrite /mmeasure (bigD1_seq m) //=.
by rewrite leq_max ltnS leqnn.
Qed.

Lemma mmeasure_mnm_ge p m : mmeasure p <= mf m -> m \notin msupp p.
Proof.
move=> h; apply/negP=> /mmeasure_mnm_lt.
by rewrite leqNgt ltnS h.
Qed.

Lemma measureE m : mf m = (\sum_(i < n) (m i) * mf U_(i)%MM )%N.
Proof.
  rewrite {1}(mnm_sumUE m) (big_morph mf mfD mf0); apply eq_bigr => i _.
  elim: (m i) => [// | d IHd] /=; first by rewrite mul0n mulm0n mf0.
  by rewrite mulmS mulSn mfD IHd.
Qed.

End MMeasure.


(* -------------------------------------------------------------------- *)
Section MSuppZMod.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types D : {freeg 'X_{1..n} / R}.

Lemma msuppN p : perm_eq (msupp (-p)) (msupp p).
Proof. by apply/domN_perm_eq. Qed.

Lemma msuppD_le p q : {subset msupp (p + q) <= msupp p ++ msupp q}.
Proof. by move=> x => /domD_subset. Qed.

Lemma msuppB_le p q : {subset msupp (p - q) <= msupp p ++ msupp q}.
Proof. by move=> x /msuppD_le; rewrite !mem_cat (perm_eq_mem (msuppN _)). Qed.

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
case: (P x)=> //; last apply/ih=> //; last first.
  by move=> y1 y2 y1_in_r y2_in_r; apply/h; rewrite 1?mem_behead.
move/(_ uq_r): ih; rewrite -(perm_cat2l (msupp (F x))) => h'.
rewrite -(perm_eqrP (h' _)); first apply/msuppD.
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
Notation msize p := (@mmeasure _ _ [measure of mdeg] p).

(* -------------------------------------------------------------------- *)
Section MWeight.
Context {n : nat}.

Implicit Types m : 'X_{1..n}.

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

Canonical mnmwgt_measure n :=
  Eval hnf in @Measure n _ mnmwgt0 mnmwgtD.

(* -------------------------------------------------------------------- *)
Notation mweight p := (@mmeasure _ _ [measure of mnmwgt] p).

Section MSize.
Variable n : nat.
Variable R : ringType.

Implicit Types m : 'X_{1..n}.
Implicit Types p : {mpoly R[n]}.

Lemma msizeE p : msize p = (\max_(m <- msupp p) (mdeg m).+1)%N.
Proof. by apply/mmeasureE. Qed.

Definition msize0 := mmeasure0 R [measure of @mdeg n].

Lemma msize_mdeg_lt p m : m \in msupp p -> mdeg m < msize p.
Proof. by apply/mmeasure_mnm_lt. Qed.

Lemma msize_mdeg_ge p m : msize p <= mdeg m -> m \notin msupp p.
Proof. by apply/mmeasure_mnm_ge. Qed.
End MSize.

(* -------------------------------------------------------------------- *)
Section MMeasureZMod.
Variable n : nat.
Variable R : ringType.

Implicit Types c : R.
Implicit Types m : 'X_{1..n}.
Implicit Types p q : {mpoly R[n]}.

Variable mf : measure n.

Local Notation mmeasure := (@mmeasure n R mf).

Lemma mmeasureC c : mmeasure c%:MP = (c != 0%R) :> nat.
Proof.
rewrite mmeasureE msuppC; case: (_ == 0)=> /=.
by rewrite big_nil. by rewrite big_seq1 mf0.
Qed.

Lemma mmeasureD_le p q :
  mmeasure (p + q) <= maxn (mmeasure p) (mmeasure q).
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
Proof. by rewrite mmeasureE (eq_big_perm _ (msuppN _)). Qed.

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

Lemma mmeasure_msupp0 (p : {mpoly R[n]}) :
  (mmeasure p == 0%N) = (msupp p == [::]).
Proof.
rewrite mmeasureE; case: (msupp _) => [|m s].
  by rewrite big_nil !eqxx.
rewrite big_cons /= -[_::_==_]/false; apply/negbTE.
by rewrite -lt0n leq_max.
Qed.
End MMeasureZMod.

(* -------------------------------------------------------------------- *)
Definition msizeC    n R := @mmeasureC n R [measure of mdeg].
Definition msizeD_le n R := @mmeasureD_le n R [measure of mdeg].
Definition msize_sum n R := @mmeasure_sum n R [measure of mdeg].
Definition msizeN    n R := @mmeasureN n R [measure of mdeg].

Definition msize_poly_eq0 n R := @mmeasure_poly_eq0 n R [measure of mdeg].
Definition msize_msupp0   n R := @mmeasure_msupp0 n R [measure of mdeg].

(* -------------------------------------------------------------------- *)
Section IterPoly.
Variable R : ringType.

Fixpoint polyn n :=
  if n is p.+1 then [ringType of {poly (polyn p)}] else R.
End IterPoly.

Definition ipoly (T : Type) : Type := T.

Notation "{ 'ipoly' T [ n ] }"   := (polyn T n).
Notation "{ 'ipoly' T [ n ] }^p" := (ipoly {ipoly T[n]}).

Section IPoly.
Variable R : ringType.
Variable n : nat.

Canonical ipoly_eqType     := [eqType     of {ipoly R[n]}^p].
Canonical ipoly_choiceType := [choiceType of {ipoly R[n]}^p].
Canonical ipoly_zmodType   := [zmodType   of {ipoly R[n]}^p].
Canonical ipoly_ringType   := [ringType   of {ipoly R[n]}^p].
End IPoly.

(* -------------------------------------------------------------------- *)
Section Inject.
Variable R : ringType.

Fixpoint inject n m (p : {ipoly R[n]}) : {ipoly R[m + n]} :=
  if m is m'.+1 return {ipoly R[m + n]} then (inject m' p)%:P else p.

Lemma inject_inj n m : injective (@inject n m).
Proof. by elim: m=> [|m ih] p q //= /polyC_inj /ih. Qed.

Lemma inject_is_rmorphism n m : rmorphism (@inject n m).
Proof.
elim: m => [|m ih] //=; rewrite -/(_ \o _).
have ->: inject m = RMorphism ih by [].
by apply/rmorphismP.
Qed.

Canonical inject_rmorphism n m := RMorphism (inject_is_rmorphism n m).
Canonical inject_additive  n m := Additive (inject_is_rmorphism n m).

Definition inject_cast n m k E : {ipoly R[n]} -> {ipoly R[k]} :=
  ecast k (_ -> {ipoly R[k]}) E (@inject n m).

Lemma inject_cast_inj n m k E :
  injective (@inject_cast n m k E).
Proof. by case: k / E; apply/inject_inj. Qed.

Lemma inject_cast_is_rmorphism n m k E :
  rmorphism (@inject_cast n m k E).
Proof. by case: k / E; apply/rmorphismP. Qed.

Canonical inject_cast_rmorphism n m k e := RMorphism (@inject_cast_is_rmorphism n m k e).
Canonical inject_cast_additive  n m k e := Additive  (@inject_cast_is_rmorphism n m k e).

Lemma inject1_proof n (i : 'I_n.+1) : (n - i + i = n)%N.
Proof. by rewrite subnK // -ltnS. Qed.

Definition inject1 n (i : 'I_n.+1) (p : {ipoly R[i]}) : {ipoly R[n]} :=
  inject_cast (inject1_proof i) p.

Local Notation "c %:IP" := (inject_cast (inject1_proof ord0) c).

Section IScale.
Variable n : nat.

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

Definition ipoly_lmodMixin :=
  let mkMixin := @GRing.Lmodule.Mixin R (ipoly_zmodType R n) iscale in
  mkMixin iscaleA iscale1r iscaleDr iscaleDl.

Canonical ipoly_lmodType := LmodType R {ipoly R[n]}^p ipoly_lmodMixin.
End IScale.

Definition injectX n (m : 'X_{1..n}) : {ipoly R[n]} :=
  \prod_(i < n) (@inject1 _ (rshift 1 i) 'X)^+(m i).

Definition minject n (p : {mpoly R[n]}) : {ipoly R[n]} :=
  fglift (@injectX n : _ -> {ipoly R[n]}^p) p.
End Inject.

(* -------------------------------------------------------------------- *)
Section MPolyRing.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types m : 'X_{1..n}.

Local Notation "`| p |" := (msize p) : ring_scope.
Local Notation "!| m |" := (mdeg  m) (format "!| m |"): ring_scope.

Local Notation "p *M_[ m ] q" :=
  << (p@_m.1)%MM * (q@_m.2)%MM *g (m.1 + m.2)%MM >>
  (at level 40, no associativity, format "p  *M_[ m ]  q").

Definition mpoly_mul p q : {mpoly R[n]} := [mpoly
  \sum_(m <- msupp p @@ msupp q) (p *M_[m] q)
].

Local Notation "p *M q" := (mpoly_mul p q)
  (at level 40, left associativity, format "p  *M  q").

Lemma mul_poly1_eq0L p q (m : 'X_{1..n} * 'X_{1..n}) :
  m.1 \notin msupp p -> p *M_[m] q = 0.
Proof. by move/memN_msupp_eq0=> ->; rewrite mul0r freegU0. Qed.

Lemma mul_poly1_eq0R p q (m : 'X_{1..n} * 'X_{1..n}) :
  m.2 \notin msupp q -> p *M_[m] q = 0.
Proof. by move/memN_msupp_eq0=> ->; rewrite mulr0 freegU0. Qed.

Lemma mpoly_mulwE p q kp kq : msize p <= kp -> msize q <= kq ->
  p *M q = [mpoly \sum_(m : 'X_{1..n < kp, kq}) (p *M_[m] q)].
Proof.
pose Ip := [subFinType of 'X_{1..n < kp}].
pose Iq := [subFinType of 'X_{1..n < kq}].
move=> lep leq; apply/mpoly_eqP/esym=> /=.
rewrite -pair_bigA_curry -pair_bigA_seq_curry /=.
rewrite (big_mksub Ip) ?msupp_uniq //=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
rewrite [X in _=X]big_uncond /=; last first.
  move=> i /memN_msupp_eq0=> ->; rewrite big1=> //.
  by move=> j _; rewrite mul0r freegU0.
apply/eq_bigr=> i _; rewrite (big_mksub Iq) /=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
  by rewrite msupp_uniq.
rewrite [X in _=X]big_uncond //= => j /memN_msupp_eq0.
by move=> ->; rewrite mulr0 freegU0.
Qed.

Implicit Arguments mpoly_mulwE [p q].

Lemma mpoly_mul_revwE p q kp kq : msize p <= kp -> msize q <= kq ->
  p *M q = [mpoly \sum_(m : 'X_{1..n < kq, kp}) (p *M_[(m.2, m.1)] q)].
Proof.
move=> lep leq;  rewrite -pair_bigA_curry exchange_big /=.
by rewrite pair_bigA /= -mpoly_mulwE //.
Qed.

Implicit Arguments mpoly_mul_revwE [p q].

Lemma mcoeff_poly_mul p q m k : !|m| < k ->
  (p *M q)@_m =
    \sum_(k : 'X_{1..n < k, k} | m == (k.1 + k.2)%MM)
      (p@_k.1 * q@_k.2).
Proof.
pose_big_enough i; first rewrite (mpoly_mulwE i i) // => lt_mk.
  rewrite mcoeff_MPoly raddf_sum /=; have lt_mi: k < i by [].
  apply/esym; rewrite big_cond_mulrn -!pair_bigA_curry /=.
  pose Ik := [subFinType of 'X_{1..n < k}].
  pose Ii := [subFinType of 'X_{1..n < i}].
  pose F i j := (p@_i * q@_j) *+ (m == (i + j))%MM.
  pose G i   := \sum_(j : 'X_{1..n < k}) (F i j).
  rewrite (big_sub_widen Ik Ii xpredT G) /=; last first.
    by move=> x /leq_trans; apply.
  rewrite big_uncond /=; last first.
    case=> /= j _; rewrite -leqNgt => /(leq_trans lt_mk).
    move=> h; rewrite {}/G {}/F big1 // => /= l _.
    case: eqP h => [{1}->|]; last by rewrite mulr0n.
    by rewrite mdegD ltnNge leq_addr.
  apply/eq_bigr=> j _; rewrite {}/G.
  rewrite (big_sub_widen Ik Ii xpredT (F _)) /=; last first.
    by move=> x /leq_trans; apply.
  rewrite big_uncond => //=; last first.
    move=> l; rewrite -leqNgt => /(leq_trans lt_mk).
    move=> h; rewrite {}/F; case: eqP h; rewrite ?mulr0n //.
    by move=> ->; rewrite mdegD ltnNge leq_addl.
  by apply/eq_bigr=> l _; rewrite {}/F coeffU eq_sym mulr_natr.
by close.
Qed.

Lemma mcoeff_poly_mul_rev p q m k : !|m| < k ->
  (p *M q)@_m =
    \sum_(k : 'X_{1..n < k, k} | m == (k.1 + k.2)%MM)
      (p@_k.2 * q@_k.1).
Proof.
move=> /mcoeff_poly_mul=> ->; rewrite big_cond_mulrn.
rewrite -pair_bigA_curry /= exchange_big pair_bigA /=.
rewrite /= -big_cond_mulrn; apply/eq_big=> //.
by move=> i /=; rewrite Monoid.mulmC.
Qed.

Lemma mcoeff_poly_mul_lin p q m k : !|m| < k ->
  (p *M q)@_m = \sum_(k : 'X_{1..n < k} | (k <= m)%MM) p@_k * q@_(m-k).
Proof.
move=> lt_m_k; rewrite (mcoeff_poly_mul _ _ (k := k)) //.
pose P (k1 k2 : 'X_{1..n < k}) := m == (k1 + k2)%MM.
pose Q (k : 'X_{1..n < k}) := [forall i, k i <= m i].
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
Implicit Arguments mcoeff_poly_mul_lin [p q m].

Local Notation mcoeff_pml := mcoeff_poly_mul_lin.

Lemma mcoeff_poly_mul_lin_rev p q m k : !|m| < k ->
  (p *M q)@_m = \sum_(k : 'X_{1..n < k} | (k <= m)%MM) p@_(m-k) * q@_k.
Proof.
move=> lt; have/mcoeff_pml := lt => ->.
have pr (h : 'X_{1..n}) : !|m - h| < k.
  by apply/(leq_ltn_trans (mdegB _ _)).
pose F (k : 'X_{1..n < k}) := BMultinom (pr k).
have inv_F (h : 'X_{1..n}): (h <= m)%MM -> (m - (m - h) = h)%MM.
  by move=> le_hm; rewrite submBA // addmC addmK.
rewrite (reindex_onto F F) //=; last first.
  by move=> h /inv_F eqh; apply/eqP; rewrite eqE /= eqh.
apply/esym/eq_big; last by move=> h /inv_F ->.
move=> h /=; apply/esym; rewrite lem_subr eqE /=.
case: (boolP (h <= m)%MM); first by move/inv_F=> /eqP ->.
rewrite negb_forall => /existsP [/= i]; rewrite -ltnNge.
rewrite ltn_neqAle -subn_eq0 => /andP [ne_mhi /eqP le_mhi].
apply/negbTE/eqP/mnmP=> /(_ i); rewrite !mnmBE => /eqP.
by rewrite le_mhi subn0 (negbTE ne_mhi).
Qed.
Implicit Arguments mcoeff_poly_mul_lin_rev [p q m].

Local Notation mcoeff_pmlr := mcoeff_poly_mul_lin_rev.

Lemma poly_mulA : associative mpoly_mul.
Proof.
move=> p q r; apply/mpolyP=> mi; pose_big_enough b.
rewrite (mcoeff_pml b) // (mcoeff_pmlr b) //. 2: by close.
have h m: !|mi - m| < b by apply/(leq_ltn_trans (mdegB mi m)).
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
+ apply/eq_bigl=> m /=; apply/idP/idP.
  * case/andP=> /mnm_lepP le1 /mnm_lepP le2; apply/mnm_lepP.
    move=> i; rewrite mnmBE /leq subnBA // addnC -subnBA //.
    by rewrite -mnmBE; apply/le2.
  * move=> le1; have le2: (m <= mi)%MM by rewrite (lepm_trans le1) ?lem_subr.
    rewrite le2; apply/mnm_lepP=> i; rewrite mnmBE /leq.
    move/mnm_lepP: le2 => le2; rewrite subnBA // addnC.
    rewrite -subnBA // -/(leq _ _); move/mnm_lepP: le1.
    by move/(_ i); rewrite mnmBE.
rewrite (mcoeff_pml b) /coef3 1?big_distrl //=.
by apply/eq_bigr=> mj le_mj_miBk; rewrite !mulrA !submDA addmC.
Qed.

Lemma poly_mul1m : left_id 1%:MP mpoly_mul.
Proof.
move=> p; apply/mpoly_eqP/esym; rewrite /mpoly_mul /=.
rewrite msupp1 -pair_bigA_seq_curry /=.
rewrite big_seq1 {1}[p]freeg_mpoly /=; apply: eq_bigr.
by move=> i _; rewrite mpolyCK !simpm.
Qed.

Lemma poly_mulm1 : right_id 1%:MP mpoly_mul.
Proof.
move=> p; apply/mpoly_eqP/esym; rewrite /mpoly_mul /=.
rewrite msupp1 -pair_bigA_seq_curry /=.
rewrite exchange_big big_seq1 {1}[p]freeg_mpoly /=.
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

Definition mpoly_ringMixin :=
  RingMixin poly_mulA poly_mul1m poly_mulm1
            poly_mulDl poly_mulDr poly_oner_neq0.
Canonical mpoly_ringType :=
  Eval hnf in RingType {mpoly R[n]} mpoly_ringMixin.
Canonical mpolynomial_ringType :=
  Eval hnf in RingType (mpoly n R) mpoly_ringMixin.

Lemma mcoeff1 m : 1@_m = (m == 0%MM)%:R.
Proof. by rewrite mcoeffC mul1r. Qed.

Lemma mcoeffM p q m :
  (p * q)@_m =
    \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 + k.2)%MM)
      (p@_k.1 * q@_k.2).
Proof. by apply: mcoeff_poly_mul. Qed.

Lemma mcoeffMr p q m :
  (p * q)@_m =
    \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 + k.2)%MM)
      (p@_k.2 * q@_k.1).
Proof.
rewrite mcoeffM big_cond_mulrn -pair_bigA_curry /=.
rewrite exchange_big pair_bigA /= -big_cond_mulrn.
by apply: eq_bigl=> k /=; rewrite Monoid.mulmC.
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
apply/mpoly_eqP=> /=; rewrite -pair_bigA_seq_curry /=.
rewrite msuppC (negbTE nz_c) big_seq1; apply/eq_bigr.
by move=> i _; rewrite mpolyCK !simpm.
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

Canonical mpolyC_rmorphism : {rmorphism R -> {mpoly R[n]}} :=
  AddRMorphism mpolyC_is_multiplicative.

Lemma mpolyC1 : mpolyC n 1 = 1.
Proof. exact: rmorph1. Qed.

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
Proof. by apply/mmeasure1. Qed.

Lemma mmeasureZ_le mf (p : {mpoly R[n]}) c :
  mmeasure mf (c *: p) <= mmeasure mf p.
Proof.
rewrite {1}mmeasureE big_tnth; apply/bigmax_leqP=> /= i _.
set m := tnth _ _; have: m \in msupp (c *: p) by apply/mem_tnth.
by move/msuppZ_le=> /mmeasure_mnm_lt->.
Qed.

Lemma mpoly_scaleAl c p q : c *: (p * q) = (c *: p) * q.
Proof. by rewrite -!mul_mpolyC mulrA. Qed.

Canonical mpoly_lalgType :=
  Eval hnf in LalgType R {mpoly R[n]} mpoly_scaleAl.
Canonical mpolynomial_lalgType :=
  Eval hnf in LalgType R (mpoly n R) mpoly_scaleAl.

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

Canonical mcoeff0_rmorphism  := AddRMorphism mcoeff0_is_multiplicative.
Canonical mcoeff0_lrmorphism := [lrmorphism of mcoeff 0%MM].
End MPolyRing.

(* -------------------------------------------------------------------- *)
Section MPolyVar.
Variable n : nat.
Variable R : ringType.

Definition mpolyX_def (m : 'X_{1..n}) : {mpoly R[n]} :=
  [mpoly << m >>].

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
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types m : 'X_{1..n}.

Local Notation "'X_[ m ]" := (@mpolyX n R m).

Lemma msuppX m : msupp 'X_[m] = [:: m].
Proof. by rewrite unlock /msupp domU1. Qed.

Lemma mem_msuppXP m m' : reflect (m = m') (m' \in msupp 'X_[m]).
Proof. by rewrite msuppX mem_seq1; apply: (iffP eqP). Qed.

Lemma mcoeffX m k : 'X_[m]@_k = (m == k)%:R.
Proof. by rewrite unlock /mpolyX_def mcoeff_MPoly coeffU mul1r. Qed.

Lemma mmeasureX mf m : mmeasure mf 'X_[R, m] = (mf m).+1.
Proof. by rewrite mmeasureE msuppX big_seq1. Qed.

Lemma msizeX m : msize 'X_[R, m] = (mdeg m).+1.
Proof. by apply/mmeasureX. Qed.

Lemma msupp_rem (p : {mpoly R[n]}) m :
  perm_eq (msupp (p - p@_m *: 'X_[m])) (rem m (msupp p)).
Proof.
case: (boolP (m \in msupp p)) => h.
  apply/uniq_perm_eq; rewrite ?rem_uniq //.
  move=> m'; rewrite mem_rem_uniq // inE /=.
  rewrite !mcoeff_msupp mcoeffB mcoeffZ mcoeffX.
  rewrite [m==m']eq_sym; case: (m' =P m) => [->|].
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

Lemma mprodXnE (F : 'I_n -> 'X_{1..n}) P m (r : seq _) :
    \prod_(i <- r | P i) 'X_[R, F i] ^+ m i
  = 'X_[\sum_(i <- r | P i) (F i *+ m i)].
Proof.
elim: r => [|x r ih]; first by rewrite !big_nil mpolyX0.
by rewrite !big_cons; case: (P x); rewrite ?(mpolyXD, mpolyXn) ih.
Qed.

Lemma mprodXE (F : 'I_n -> 'X_{1..n}) P (r : seq _) :
    \prod_(i <- r | P i) 'X_[R, F i] = 'X_[\sum_(i <- r | P i) F i].
Proof.
pose m   := [multinom 1%N | i < n].
pose G i := 'X_[R, F i] ^+ m i.
rewrite (eq_bigr G) => [|i _]; last first.
  by rewrite /G /m mnmE expr1.
rewrite mprodXnE; congr 'X_[_]; apply/eq_bigr=> i _.
by rewrite /m mnmE.
Qed.

Lemma mpolyXE (s : 'S_n) m :
  'X_[m] = \prod_(i < n) 'X_(s i) ^+ m (s i).
Proof.
pose sI := (s^-1)%g; pose h := fun (m : 'X_{1..n}) => 'X_[m].
pose G := fun (i : 'I_n) => (U_(s i) *+ m (s i))%MM.
rewrite (eq_bigr (h \o G)) => [|i _]; last by rewrite mpolyXn.
rewrite -(big_map G xpredT) /index_enum -enumT /=.
rewrite mpolyX_prod; congr 'X_[_]; rewrite big_map.
rewrite enumT -/(index_enum _) {}/G (reindex sI) /=; last first.
  by exists s=> i _; rewrite /sI ?(permK, permKV).
rewrite (eq_bigr (fun i => (U_(i) *+ (m i))%MM)); last first.
  by move=> i _; rewrite permKV.
apply/mnmP=> i; rewrite mnm_sumE (bigD1 i) ?big1 //=; last first.
  by move=> j ne_ij; rewrite mulmnE mnm1E (negbTE ne_ij) muln0.
by rewrite addn0 mulmnE mnm1E eqxx muln1.
Qed.

Lemma mpolyXE_id m :
  'X_[m] = \prod_(i < n) 'X_i ^+ m i.
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
move=> lt_pk; pose I := [subFinType of 'X_{1..n < k}].
rewrite {1}[p]mpolyE (big_mksub I) //=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
  by rewrite msupp_uniq.
rewrite big_uncond //= => i.
by move/memN_msupp_eq0 ->; rewrite scale0r.
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
move=> ltpk ltqk; rewrite mpolyME; pose I := [subFinType of 'X_{1..n < k}].
rewrite -pair_bigA_seq_curry (big_mksub I) /=; last first.
  by move=> m /msize_mdeg_lt /leq_trans; apply. by rewrite msupp_uniq.
rewrite big_uncond /= => [|i]; last first.
  by move/memN_msupp_eq0=> ->; rewrite big1 // => j _; rewrite mul0r scale0r.
rewrite -pair_bigA_curry /=; apply/eq_bigr=> i _.
rewrite (big_mksub I) /=; last first.
  by move=> m /msize_mdeg_lt /leq_trans; apply. by rewrite msupp_uniq.
rewrite big_uncond /= => [//|j].
by move/memN_msupp_eq0=> ->; rewrite mulr0 scale0r.
Qed.

Lemma commr_mpolyX m p : GRing.comm p 'X_[m].
Proof.
apply/mpolyP=> k; rewrite mcoeffM mcoeffMr.
by apply/eq_bigr=> /= i _; rewrite !mcoeffX GRing.commr_nat.
Qed.

Lemma mcoeffMX p m k : (p * 'X_[m])@_(m + k) = p@_k.
Proof.
rewrite commr_mpolyX mpolyME msuppX -pair_bigA_seq_curry /=.
rewrite big_seq1 [X in _=X@__]mpolyE !raddf_sum /=.
apply/eq_bigr=> i _; rewrite !mcoeffZ !mcoeffX eqxx mul1r.
by rewrite eqm_add2l.
Qed.

Lemma msuppMX p m :
  perm_eq (msupp (p * 'X_[m])) [seq (m + m')%MM | m' <- msupp p].
Proof.
apply/uniq_perm_eq=> //; first rewrite map_inj_uniq //.
  move=> m1 m2 /=; rewrite ![(m+_)%MM]Monoid.mulmC /=.
  by apply/(can_inj (addmK _)).
move=> m'; apply/idP/idP; last first.
  case/mapP=> mp mp_in_p ->; rewrite mcoeff_msupp.
  by rewrite mcoeffMX -mcoeff_msupp.
move/msuppM_le; rewrite msuppX /= => /allpairsP.
case=> [[p1 p2]] /=; rewrite mem_seq1; case=> p1_in_p.
move/eqP=> <- ->; apply/mapP; exists p1=> //.
by rewrite Monoid.mulmC.
Qed.

Lemma msuppMCX c m : c != 0 -> msupp (c *: 'X_[m]) = [:: m].
Proof.
move=> nz_c; rewrite -mul_mpolyC; apply/perm_eq_small=> //.
rewrite (perm_eqlP (msuppMX _ _)) msuppC (negbTE nz_c) /=.
by rewrite Monoid.mulm1.
Qed.

Lemma msupp_sumX (r : seq 'X_{1..n}) (f : 'X_{1..n} -> R) :
  uniq r -> {in r, forall m, f m != 0} ->
  perm_eq (msupp (\sum_(m <- r) (f m) *: 'X_[m])) r.
Proof.
move=> uq_r h; set F := fun m => (f m *: 'X_[m] : {mpoly R[n]}).
have msFm m: m \in r -> msupp (f m *: 'X_[m]) = [:: m].
  by move=> m_in_r; rewrite msuppMCX // h.
rewrite (perm_eqlP (msupp_sum xpredT _ _)) //.
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

Canonical MPoly_additive := Additive MPoly_is_linear.
Canonical MPoly_linear   := Linear   MPoly_is_linear.

Lemma MPolyU c m : MPoly << c *g m >> = c *: 'X_[m].
Proof.
apply/mpolyP=> k; rewrite mcoeff_MPoly.
by rewrite mcoeffZ mcoeffX coeffU.
Qed.

Lemma mpolyrect (P : {mpoly R[n]} -> Type) :
     P 0
  -> (forall c m p,
        m \notin msupp p -> c != 0 ->
          P p -> P (c *: 'X_[m] + p))
  -> forall p, P p.
Proof.
move=> h0 hS [p] /=; elim/freeg_rect_dom0: p => /=.
  by rewrite raddf0.
move=> c q m mdom nz_c /hS h.
by rewrite raddfD /= MPolyU; apply h.
Qed.

Lemma mpolyind (P : {mpoly R[n]} -> Prop) :
     P 0
  -> (forall c m p,
        m \notin msupp p -> c != 0 ->
          P p -> P (c *: 'X_[m] + p))
  -> forall p, P p.
Proof. by apply/(@mpolyrect P). Qed.
End MPolyVarTheory.

(* -------------------------------------------------------------------- *)
Section MPolyLead.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

Definition mlead p : 'X_{1..n} :=
  (\max_(m <- msupp p) m)%O.

Lemma mleadC (c : R) : mlead c%:MP = 0%MM.
Proof.
rewrite /mlead msuppC; case: eqP=> _.
  by rewrite big_nil.
  by rewrite unlock /= maxo0.
Qed.

Lemma mlead0 : mlead 0 = 0%MM.
Proof. by rewrite mleadC. Qed.

Lemma mlead1 : mlead 1 = 0%MM.
Proof. by rewrite mleadC. Qed.

Lemma mleadXm m : mlead 'X_[m] = m.
Proof. by rewrite /mlead msuppX big_seq1. Qed.

Lemma mlead_supp p : p != 0 -> mlead p \in msupp p.
Proof.
move=> nz_p; case: (eq_bigmaxo id (r := msupp p)) => /=.
  by rewrite msupp_eq0.
by rewrite /mlead=> m /andP [m_in_p /eqP ->].
Qed.

Lemma mlead_deg p : p != 0 -> (mdeg (mlead p)).+1 = msize p.
Proof.
move=> /mlead_supp lc_in_p; rewrite /mlead msizeE mdeg_bigmax.
have: msupp p != [::] by case: (msupp p) lc_in_p.
elim: (msupp p)=> [|m [|m' r] ih] // _; first by rewrite !big_seq1.
by rewrite big_cons -maxnSS {}ih // !big_cons.
Qed.

Lemma msupp_le_mlead p m : m \in msupp p -> (m <= mlead p)%O.
Proof. by move=> m_in_p; apply/(leo_bigmax id). Qed.

Lemma mleadN p : mlead (-p) = mlead p.
Proof.
have [->|nz_p] := eqVneq p 0; first by rewrite oppr0.
by rewrite /mlead (eq_big_perm _ (msuppN p)).
Qed.

Lemma mleadD_le p q : (mlead (p + q) <= maxo (mlead p) (mlead q))%O.
Proof.
have [->|] := eqVneq (p+q) 0; first by rewrite mlead0 le0o.
move/mlead_supp/msuppD_le; rewrite mem_cat.
rewrite leo_max //; case/orP.
+ by move/msupp_le_mlead=> ->; rewrite orTb.
+ by move/msupp_le_mlead=> ->; rewrite orbT.
Qed.

Lemma mleadB_le p q : (mlead (p - q) <= maxo (mlead p) (mlead q))%O.
Proof. by rewrite -(mleadN q); apply/mleadD_le. Qed.

Lemma mleadc_eq0 p : (p@_(mlead p) == 0) = (p == 0).
Proof.
apply/idP/idP => [|/eqP->]; last by rewrite mcoeff0.
by case: (p =P 0) => // /eqP /mlead_supp; rewrite mcoeff_eq0 => ->.
Qed.

Lemma mcoeff_gt_mlead p m : (mlead p < m)%O -> p@_m = 0.
Proof.
move=> lt_lcp_m; apply/eqP; rewrite mcoeff_eq0; apply/negP.
by move/msupp_le_mlead/leoNgt; rewrite lt_lcp_m.
Qed.

Lemma mleadDr (p1 p2 : {mpoly R[n]}) :
  (mlead p1 < mlead p2)%O -> mlead (p1 + p2) = mlead p2.
Proof.
move=> lt_p1p2; apply/eqP; rewrite eqo_leq.
move: (mleadD_le p1 p2); rewrite /maxo lt_p1p2=> ->/=.
rewrite letNgt //; apply/negP=> /mcoeff_gt_mlead.
rewrite mcoeffD mcoeff_gt_mlead // add0r => /eqP.
rewrite mleadc_eq0=> /eqP z_p2; move: lt_p1p2.
by rewrite z_p2 mlead0 lto0.
Qed.

Lemma mleadDl (p1 p2 : {mpoly R[n]}) :
  (mlead p2 < mlead p1)%O -> mlead (p1 + p2) = mlead p1.
Proof. by move/mleadDr; rewrite addrC => ->. Qed.

Lemma mleadD (p1 p2 : {mpoly R[n]}) : mlead p1 != mlead p2 ->
  mlead (p1 + p2) = maxo (mlead p1) (mlead p2).
Proof.
move=> ne_p1p2; rewrite /maxo; case: (boolP (_ < _))%O.
  by move/mleadDr.
rewrite lttNge // negbK leo_eqVlt eq_sym (negbTE ne_p1p2).
by move/mleadDl.
Qed.

Lemma mlead_sum_le (T : Type) (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}) :
  (mlead (\sum_(p <- r | P p) F p) <= \max_(p <- r | P p) (mlead (F p)))%O.
Proof.
elim/big_rec2: _ => /= [|x m p Px le]; first by rewrite mlead0.
apply/(leo_trans (mleadD_le _ _)); rewrite geo_max //.
by rewrite leo_maxl //= leo_max // le orbT.
Qed.

Lemma mlead_sum (T : Type) (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}) :
     (uniq [seq mlead (F p) | p <- r & P p])
  -> (mlead (\sum_(p <- r | P p) F p) = \max_(p <- r | P p) (mlead (F p)))%O.
Proof.                        (* FIXME: far too convoluted *)
elim: r=> [|p r ih]; first by rewrite !big_nil mlead0.
rewrite !big_cons /=; case: (P p)=> //= /andP[Fp_ml uq_ml].
pose Q i := P (nth p r i); rewrite !(big_nth p) -!(big_filter _ Q).
set itg := [seq _ <- _ | _]; have [|nz_szr] := eqVneq (size itg) 0%N.
  by move/size0nil=> ->; rewrite !big_nil maxo0 addr0.
move: {ih}(ih uq_ml); rewrite !(big_nth p) -!(big_filter _ Q) -/itg.
move=> ih; rewrite mleadD ih //; pose G i := mlead (F (nth p r i)).
case: (eq_bigmaxo G (r := itg)); first by rewrite -size_eq0.
move=> /= x /andP[]; rewrite {1}/itg mem_filter=> /andP[Px].
rewrite mem_iota add0n subn0 {}/G=> /andP[_ lt_x_szr] /eqP->.
apply/contra: Fp_ml=> /eqP-> {Q itg uq_ml nz_szr ih}.
elim: r x Px lt_x_szr=> [|y r ih] [|x] //=.
  by move=> -> /=; rewrite mem_head.
rewrite ltnS=> Px lt_x_szr; case: (P y)=> /=.
  by rewrite 1?mem_behead //=; apply/ih. by apply/ih.
Qed.

Lemma mleadM_le p q : (mlead (p * q) <= (mlead p + mlead q)%MM)%O.
Proof.
have [->|] := eqVneq (p * q) 0; first by rewrite mlead0 le0o.
move/mlead_supp/msuppM_le/allpairsP => [[m1 m2] /=] [m1_in_p m2_in_q ->].
by apply/lem_add; apply/msupp_le_mlead.
Qed.

Lemma mlead_prod_le T (r : seq T) (P : pred T) F :
  (mlead (\prod_(p <- r | P p) F p) <= (\sum_(p <- r | P p) mlead (F p))%MM)%O.
Proof.
elim/big_rec2: _ => /= [|x m p Px ih]; first by rewrite mlead1.
by apply/(leo_trans (mleadM_le (F x) p)); apply/lem_add.
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
+ by rewrite product_uniq // !msupp_uniq.
+ by rewrite product_mem /= !mlead_supp.
rewrite mcoeffD mcoeffZ mcoeffX eqxx mulr1.
rewrite big_seq_cond raddf_sum /= big1 ?addr0 //.
case=> m1 m2; rewrite product_mem /= -andbA; case/and3P.
move=> m1_in_p m2_in_q ne_m_lc; rewrite mcoeffZ mcoeffX.
move/msupp_le_mlead: m1_in_p; move/msupp_le_mlead: m2_in_q.
rewrite leo_eqVlt; case/orP=> [/eqP m2E|]; last first.
  by move=> lt /lem_ltm_add /(_ lt) /lto_eqF ->; rewrite mulr0.
move: ne_m_lc; rewrite m2E xpair_eqE eqxx andbT.
rewrite leo_eqVlt=> /negbTE => -> /=; rewrite eqm_add2r.
by move/lto_eqF=> ->; rewrite mulr0.
Qed.

Lemma mleadcMW p q (mp mq : 'X_{1..n}) :
     (mlead p <= mp)%O -> (mlead q <= mq)%O
  -> (p * q)@_(mp + mq)%MM = p@_mp * q@_mq.
Proof.
move=> lep leq; case: (boolP ((mlead p < mp) || (mlead q < mq)))%O.
  move=> lt_lm; have lt_lmD: ((mlead p + mlead q)%MM < (mp + mq)%MM)%O.
    by case/orP: lt_lm=> lt; [apply/ltm_lem_add | apply/lem_ltm_add].
  move/(leo_lto_trans (mleadM_le p q))/mcoeff_gt_mlead: lt_lmD.
  by case/orP: lt_lm=> /mcoeff_gt_mlead ->; rewrite ?(mul0r, mulr0).
case/norP; rewrite -!letNgt // => gep geq.
move: (eqo_leq (mlead p) mp) (eqo_leq (mlead q) mq).
by rewrite lep leq gep geq=> /= /eqP<- /eqP<-; apply/mleadcM.
Qed.

Lemma mleadc_prod T (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}) :
     (\prod_(p <- r | P p) F p)@_(\sum_(p <- r | P p) mlead (F p))%MM
  =  \prod_(p <- r | P p) (mleadc (F p)).
Proof.
elim: r => [|p r ih]; first by rewrite !big_nil mcoeff1 eqxx.
rewrite !big_cons; case: (P p)=> //; rewrite mleadcMW //.
  by rewrite ih. by apply/mlead_prod_le.
Qed.

Lemma mleadcZ c p : (c *: p)@_(mlead p) = c * (mleadc p).
Proof. by rewrite mcoeffZ. Qed.

Lemma mleadM_proper p q : mleadc p * mleadc q != 0 ->
  mlead (p * q) = (mlead p + mlead q)%MM.
Proof.
move: (mleadM_le p q); rewrite leo_eqVlt; case/orP=> [/eqP->//|].
rewrite -mleadcM mcoeff_eq0 negbK => ltm /msupp_le_mlead lem.
by move: (lto_leo_trans ltm lem); rewrite ltoo.
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
Variable T : eqType.
Variable r : seq T.
Variable P : pred T.
Variable F : T -> {mpoly R[n]}.

Lemma mlead_prod_proper :
       (forall x, x \in r -> P x -> GRing.lreg (mleadc (F x)))
  ->   mlead (\prod_(p <- r | P p) F p)
     = (\sum_(p <- r | P p) mlead (F p))%MM.
Proof.
pose Q (s : seq T) := forall x, x \in s -> P x -> GRing.lreg (mleadc (F x)).
rewrite -/(Q r); elim: r => [|x s ih] h; first by rewrite !big_nil mleadC.
have lreg_s: Q s.
  by move=> y y_in_s; apply: (h y); rewrite mem_behead.
rewrite !big_cons; case: (boolP (P x))=> Px; last by apply/ih.
have lreg_x := (h x (mem_head _ _) Px).
rewrite mleadM_proper; first by rewrite ih.
by rewrite mulrI_eq0 ?ih // mleadc_prod; apply/lreg_neq0/lreg_prod.
Qed.

Lemma mleadc_prod_proper :
       (forall x, x \in r -> P x -> GRing.lreg (mleadc (F x)))
  ->   mleadc (\prod_(p <- r | P p) F p)
     = \prod_(p <- r | P p) mleadc (F p).
Proof. by move/mlead_prod_proper=> ->; rewrite mleadc_prod. Qed.
End MLeadProd.

Lemma mleadX_le p k : (mlead (p ^+ k) <= (mlead p *+ k)%MM)%O.
Proof.
rewrite -[k](card_ord k) -prodr_const /mnm_muln.
by rewrite iteropE -big_const; apply/mlead_prod_le.
Qed.

Lemma mleadcX p k : (p ^+ k)@_(mlead p *+ k) = (mleadc p) ^+ k.
Proof.
rewrite -[k](card_ord k) -prodr_const /mnm_muln.
by rewrite iteropE -big_const mleadc_prod prodr_const.
Qed.

Lemma mleadX_proper p k : GRing.lreg (mleadc p) ->
  mlead (p ^+ k) = (mlead p *+ k)%MM.
Proof.
move=> h; rewrite -[k](card_ord k) -prodr_const.
rewrite /mnm_muln iteropE -big_const.
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
by have /lem_mdeg := mleadM_le p q; rewrite mdegD.
Qed.

Lemma msizeM_proper p q : mleadc p * mleadc q != 0->
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
have [->|] := eqVneq (c *: p) 0; first by rewrite mlead0 le0o.
by move/mlead_supp/msuppZ_le/msupp_le_mlead.
Qed.

Lemma mleadZ_proper c p : c * mleadc p != 0 ->
  mlead (c *: p) = mlead p.
Proof.
move: (mleadZ_le c p); rewrite leo_eqVlt; case/orP=> [/eqP->//|].
rewrite -mleadcZ mcoeff_eq0 negbK => ltm /msupp_le_mlead lem.
by move: (lto_leo_trans ltm lem); rewrite ltoo.
Qed.

Lemma msizeZ_le (p : {mpoly R[n]}) c : msize (c *: p) <= msize p.
Proof. by apply/mmeasureZ_le. Qed.

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
     (forall p, (forall q, (mlead q < mlead p)%O -> P q) -> P p)
  -> forall p, P p.
Proof.
move=> ih p; move: {2}(mlead p) (leoo (mlead p))=> m.
elim/(ltmwf (n := n)): m p=> m1 wih p lt_pm1.
apply/ih=> q lt_pq; apply/(wih (mlead q))=> //.
by apply/(lto_leo_trans lt_pq).
Qed.
End MPolyLead.

Notation mleadc p := (p@_(mlead p)).

(* -------------------------------------------------------------------- *)
Section MPoly0.
Variable R : ringType.

Lemma mpolyKC : cancel (@mcoeff 0 R 0%MM) (@mpolyC 0 R).
Proof.
  move=> p; apply/mpolyP=> m; rewrite mcoeffC.
  case: (m =P 0%MM)=> [->|/eqP]; first by rewrite mulr1.
  by apply/contraNeq=> _; apply/eqP/mnmP; case.
Qed.
End MPoly0.

(* -------------------------------------------------------------------- *)
Section MPolyDeriv.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types m : 'X_{1..n}.

Definition mderiv (i : 'I_n) p :=
  \sum_(m <- msupp p) ((m i)%:R * p@_m) *: 'X_[m - U_(i)].

Local Notation "p ^`M ( i )" := (mderiv i p).

Lemma mderivwE i p k : msize p <= k ->
  p^`M(i) = \sum_(m : 'X_{1..n < k}) ((m i)%:R * p@_m) *: 'X_[m - U_(i)].
Proof.
pose I := [subFinType of 'X_{1..n < k}].
move=> le_pk; rewrite /mderiv (big_mksub I) /=; first last.
  by move=> x /msize_mdeg_lt/leq_trans/(_ le_pk).
  by rewrite msupp_uniq.
rewrite big_uncond //= => j /memN_msupp_eq0 ->.
by rewrite mulr0 scale0r.
Qed.
Implicit Arguments mderivwE [p i].

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

Canonical mderiv_additive i := Additive (mderiv_is_linear i).
Canonical mderiv_linear   i := Linear   (mderiv_is_linear i).

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
Proof.
pose_big_enough k; first pose mderivE := (mderivwE k).
  rewrite ![p^`M(_)]mderivE // !raddf_sum /=; apply/eq_bigr.
  move=> l _; rewrite !mderivZ !mderivX !scalerA.
  rewrite !submDA addmC -!commr_nat -!mulrA -!natrM.
  congr (_ * _%:R *: _); rewrite !mnmBE !mnm1E eq_sym.
  by case: eqP=> [->//|_] /=; rewrite !subn0 mulnC.
by close.
Qed.

Lemma mderiv_perm (s1 s2 : seq 'I_n) p :
  perm_eq s1 s2 -> foldr mderiv p s1 = foldr mderiv p s2.
Proof.
pose M q s := foldr mderiv q s; rewrite -!/(M _ _).
have h (s : seq 'I_n) (x : 'I_n) q: x \in s ->
  M q s = M q (x :: rem x s).
+ elim: s=> [|y s ih] //; rewrite in_cons.
  case: eqP=> /= [->|/eqP]; first by rewrite eqxx.
  move=> ne_xy /ih {ih}->; rewrite eq_sym.
  by rewrite (negbTE ne_xy) /= mderiv_comm.
elim: s1 s2 => [|x s1 ih] s2.
  by rewrite perm_eq_sym=> /perm_eq_small=> ->.
move=> peq_xDs1_s2; have x_in_s2: x \in s2.
  by rewrite -(perm_eq_mem peq_xDs1_s2) mem_head.
have /h ->/= := x_in_s2; rewrite -ih // -(perm_cons x).
by rewrite (perm_eqlP peq_xDs1_s2) perm_to_rem.
Qed.

Definition mderivm (m : 'X_{1..n}) p : {mpoly R[n]} :=
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
rewrite mderivm_foldr (eq_map (f2 := fun _ => [::])).
  by elim: (enum _). by move=> i /=; rewrite mnm0E.
Qed.

Lemma mderivmDm m1 m2 p : p^`M[m1 + m2] = p^`M[m1]^`M[m2].
Proof.
rewrite !mderivm_foldr -foldr_cat; apply/mderiv_perm.
apply/perm_eqP=> /= a; rewrite count_cat !count_flatten.
rewrite -big_split /=; apply/eq_bigr=> i _.
by rewrite mnmDE nseqD count_cat addnC.
Qed.

Lemma mderiv_summ (T : Type) (r : seq T) (P : pred T) F p :
    p^`M[\sum_(x <- r | P x) (F x)]
  = foldr mderivm p [seq F x | x <- r & P x].
Proof.
elim: r => //= [|x s ih]; first by rewrite big_nil mderivm0m.
rewrite big_cons; case: (P x)=> //=.
by rewrite mulmC /= mderivmDm ih.
Qed.

Lemma mderivmU1m i p : p^`M[U_(i)] = p^`M(i).
Proof.
rewrite mderivm_foldr (@mderiv_perm _ [:: i]) //.
apply/perm_eqP=> /= a; rewrite addn0 count_flatten.
rewrite enumT -/(index_enum _) (bigD1 i) //=.
rewrite mnm1E eqxx /= addn0 big1 // => j ne_ji.
by rewrite mnm1E eq_sym (negbTE ne_ji).
Qed.

Lemma mderivm_is_linear m : linear (mderivm m).
Proof.
move=> c p q; rewrite /mderivm; elim: (enum _)=> //= i s ih.
by elim: (m i) => //= {ih}k ->; rewrite mderivD mderivZ.
Qed.

Canonical mderivm_additive m := Additive (mderivm_is_linear m).
Canonical mderivm_linear   m := Linear   (mderivm_is_linear m).

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
Proof. by rewrite mulmS mulmC mderivmDm mderivmU1m. Qed.

Lemma mderivn_iter i k p :
  p^`M(i, k) = iter k (mderiv i) p.
Proof. by elim: k => /= [|k ih]; rewrite ?mderivn0 // mderivnS ih. Qed.

Lemma mderivmX m1 m2 :
  ('X_[m1])^`M[m2] = (\prod_(i < n) (m1 i)^_(m2 i))%:R *: 'X_[m1-m2].
Proof.
have h m: m = (\sum_(i < n) U_(i) *+ (m i))%MM.
  apply/mnmP=> i; rewrite mnm_sumE (bigD1 i) //=.
  rewrite mulmnE mnm1E eqxx /= muln1 big1 ?addn0 //.
  by move=> j ne_ji; rewrite mulmnE mnm1E (negbTE ne_ji) muln0.
rewrite [m2]h mderiv_summ filter_predT /index_enum -enumT /=.
elim: (enum _) (enum_uniq 'I_n) => /= [|i s ih /andP [i_notin_s uq_s]].
  by move=> _; rewrite !big_nil scale1r subm0.
pose F j := (m1 j) ^_ (m2 j); rewrite ih // mderivmZ.
rewrite big_seq [X in X%:R](eq_bigr F) -?big_seq; last first.
  move=> j j_in_s; rewrite (bigD1_seq j) //=.
  rewrite mnmDE mnm_sumE mulmnE mnm1E eqxx muln1.
  rewrite big1 ?mulm1 // => j' ne_j'j; rewrite mulmnE.
  by rewrite mnm1E (negbTE ne_j'j) muln0.
rewrite big_cons mulnC natrM -scalerA; apply/esym.
rewrite 2![X in X%:R*:(_*:_)](big_seq, eq_bigr F); last first.
  move=> j j_in_s; rewrite big_cons mnmDE mnm_sumE.
  rewrite (bigD1_seq j) //= big1 ?mulm1=> [|j' ne_j'j].
    rewrite !mulmnE !mnm1E eqxx muln1; move/memPn: i_notin_s.
    rewrite eq_sym; move/(_ j j_in_s) => /negbTE=> ->.
    by rewrite muln0 add0n.
  by rewrite mulmnE mnm1E (negbTE ne_j'j) muln0.
rewrite -big_seq; congr (_ *: _); rewrite !big_cons.
rewrite mnmDE mnm_sumE big_seq big1 ?mulm1; last first.
  move=> /= j j_in_s; rewrite mulmnE mnm1E; move/memPn: i_notin_s.
  by move/(_ j j_in_s)=> /negbTE->; rewrite muln0.
rewrite mulmnE mnm1E eqxx muln1; elim: (m2 i)=> /= [|k ihk].
  by rewrite ffactn0 scale1r mulm0n mul1m mderivm0m.
rewrite mderivnS -ihk mderivZ mderivX scalerA -natrM.
rewrite submDA mulmAC /= mulmSr; congr (_%:R *: 'X_[_]).
rewrite mnmBE mnmDE mnm_sumE big_seq big1; last first.
  move=> /= j j_in_s; rewrite mulmnE mnm1E; move: i_notin_s.
  by move/memPn/(_ j j_in_s)=> /negbTE->; rewrite muln0.
by rewrite mulm1 mulmnE mnm1E eqxx muln1 ffactnSr.
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
rewrite mderivmE (big_mksub [subFinType of 'X_{1..n < k}]) //=.
  by apply/msupp_uniq.
by move=> m' /msize_mdeg_lt /leq_trans; apply.
Qed.

Lemma mderivnE i k p : p^`M(i, k) =
  \sum_(m <- msupp p) (((m i)^_k)%:R * p@_m) *: 'X_[m - U_(i) *+ k].
Proof.
rewrite mderivmE; apply/eq_bigr=> /= m _.
rewrite -commr_nat (bigD1 i) //= big1 ?muln1.
  by rewrite mulmnE mnm1E eqxx muln1.
move=> j ne_ji; rewrite mulmnE mnm1E eq_sym.
by rewrite (negbTE ne_ji) muln0 ffactn0.
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
      by rewrite [(m+j)%MM]mulmC /= addmK eqxx.
    rewrite negb_forall; case/existsP=> /= k Nle_mj.
    by rewrite (bigD1 k) //= ffact_small ?simpm // ltnNge.
  rewrite addr0 mcoeffZ mcoeffX {3}[(m+m')%MM]mulmC addmK.
  by rewrite eqxx mulr1 mulr_natr.
by close.
Qed.

Lemma mcoeff_mderiv i p m : (p^`M(i))@_m = p@_(m + U_(i)) *+ (m i).+1.
Proof.
rewrite -mderivmU1m mcoeff_mderivm mulmC /=.
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
Variable n : nat.
Variable R : ringType.
Variable S : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types m : 'X_{1..n}.

Section Defs.
Variable f : R -> S.
Variable h : 'I_n -> S.

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
Variable h : 'I_n -> S.
Variable f : {additive R -> S}.

Lemma mmapE p i : msize p <= i ->
  p^[f,h] = \sum_(m : 'X_{1..n < i}) (f p@_m) * m^[h].
Proof.
move=> le_pi; set I := [subFinType of 'X_{1..n < i}].
rewrite /mmap (big_mksub I) ?msupp_uniq //=; first last.
  by move=> x /msize_mdeg_lt /leq_trans; apply.
rewrite big_uncond //= => j /memN_msupp_eq0 ->.
by rewrite raddf0 mul0r.
Qed.
Implicit Arguments mmapE [p].

Lemma mmap_is_additive : additive (mmap f h).
Proof.
move=> p q /=; pose_big_enough i.
  rewrite !(mmapE i) // -sumrB; apply/eq_bigr.
  by case=> /= [m _] _; rewrite !raddfB /= mulrDl mulNr.
by close.
Qed.

Canonical mmap_additive := Additive mmap_is_additive.

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

Implicit Arguments mmapE [f h p].

Section Multiplicative.
Variable h : 'I_n -> S.
Variable f : {rmorphism R -> S}.

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

Implicit Arguments mmapE [n R S h f p].

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
Variable n : nat.
Variable R : ringType.
Variable S : comRingType.

Implicit Types p q r : {mpoly R[n]}.

Variable h : 'I_n -> S.
Variable f : {rmorphism R -> S}.

Lemma mmap_is_multiplicative : multiplicative (mmap f h).
Proof.
  apply/commr_mmap_is_multiplicative.
  + by move=> i x; apply/mulrC.
  + by move=> p m m'; apply/mulrC.
Qed.

Canonical mmap_rmorphism := AddRMorphism mmap_is_multiplicative.
End MPolyMorphismComm.

(* -------------------------------------------------------------------- *)
Section MPolyComRing.
Variable n : nat.
Variable R : comRingType.

Implicit Types p q r : {mpoly R[n]}.

Lemma mpoly_mulC p q : p * q = q * p.
Proof.
apply/mpolyP=> /= m; rewrite mcoeffM mcoeffMr.
by apply: eq_bigr=> /= i _; rewrite mulrC.
Qed.

Canonical mpoly_comRingType :=
  Eval hnf in ComRingType {mpoly R[n]} mpoly_mulC.
Canonical mpolynomial_comRingType :=
  Eval hnf in ComRingType (mpoly n R) mpoly_mulC.

Canonical mpoly_algType :=
  Eval hnf in CommAlgType R {mpoly R[n]}.
Canonical mpolynomial_algType :=
  Eval hnf in [algType R of mpoly n R for mpoly_algType].
End MPolyComRing.

(* -------------------------------------------------------------------- *)
Section MPolyComp.
Variable n : nat.
Variable R : ringType.
Variable k : nat.

Implicit Types  p  q : {mpoly R[n]}.
Implicit Types lp lq : n.-tuple {mpoly R[k]}.

Definition comp_mpoly lq p : {mpoly R[k]}:=
  mmap (@mpolyC _ R) (tnth lq) p.

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

Canonical comp_mpoly_additive lq := Additive (comp_mpoly_is_additive lq).

Lemma comp_mpoly0   lq   : 0 \mPo lq = 0                     . Proof. exact: raddf0. Qed.
Lemma comp_mpolyN   lq   : {morph comp_mpoly lq: x / - x}    . Proof. exact: raddfN. Qed.
Lemma comp_mpolyD   lq   : {morph comp_mpoly lq: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma comp_mpolyB   lq   : {morph comp_mpoly lq: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma comp_mpolyMn  lq l : {morph comp_mpoly lq: x / x *+ l} . Proof. exact: raddfMn. Qed.
Lemma comp_mpolyMNn lq l : {morph comp_mpoly lq: x / x *- l} . Proof. exact: raddfMNn. Qed.

Lemma comp_mpoly_is_linear lq : linear (comp_mpoly lq).
Proof.
move=> c p q; rewrite comp_mpolyD /comp_mpoly.
by rewrite mmapZ mul_mpolyC.
Qed.

Canonical comp_mpoly_linear lq := Linear (comp_mpoly_is_linear lq).

Lemma comp_mpoly1 lq : 1 \mPo lq = 1.
Proof. by rewrite /comp_mpoly -mpolyC1 mmapC. Qed.

Lemma comp_mpolyC c lq : c%:MP \mPo lq = c%:MP.
Proof. by rewrite /comp_mpoly mmapC. Qed.

Lemma comp_mpolyZ c p lq : (c *: p) \mPo lq = c *: (p \mPo lq).
Proof. by apply/linearZ. Qed.

Lemma comp_mpolyXU i lq : 'X_i \mPo lq = lq`_i.
Proof. by rewrite /comp_mpoly mmapX mmap1U -tnth_nth. Qed.

Lemma comp_mpolyX m lq :
  'X_[m] \mPo lq = \prod_(i < n) (tnth lq i)^+(m i).
Proof. by rewrite /comp_mpoly mmapX. Qed.

Lemma comp_mpolyEX p lq :
  p \mPo lq = \sum_(m <- msupp p) (p@_m *: ('X_[m] \mPo lq)).
Proof. by apply/eq_bigr=> m _; rewrite mul_mpolyC comp_mpolyX. Qed.
End MPolyComp.

Notation "p \mPo lq" := (@comp_mpoly _ _ _ lq p).

(* -------------------------------------------------------------------- *)
Section MPolyCompHomo.
Variable n : nat.
Variable R : ringType.

Implicit Types  p  q : {mpoly R[n]}.
Implicit Types lp lq : n.-tuple {mpoly R[n]}.

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
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types v : n.-tuple R.

Definition meval v p := mmap idfun (tnth v) p.

Lemma mevalE v p : meval v p =
  \sum_(m <- msupp p) p@_m * (\prod_i (tnth v i)^+(m i)).
Proof. by []. Qed.

Lemma meval_is_additive v : additive (meval v).
Proof. by apply/mmap_is_additive. Qed.

Canonical meval_additive v := Additive (meval_is_additive v).

Lemma meval0   v   : meval v 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mevalN   v   : {morph meval v: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mevalD   v   : {morph meval v: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mevalB   v   : {morph meval v: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mevalMn  v k : {morph meval v: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mevalMNn v k : {morph meval v: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma mevalC v c : meval v c%:MP = c.
Proof. by rewrite /meval mmapC. Qed.

Lemma meval1 v : meval v 1 = 1.
Proof. by apply/mevalC. Qed.

Lemma mevalX v i : meval v 'X_i = tnth v i.
Proof. by rewrite /meval mmapX mmap1U. Qed.

Lemma meval_is_scalable v : scalable_for *%R (meval v).
Proof. by move=> /= c p; rewrite /meval mmapZ. Qed.

Lemma mevalZ v c p : meval v (c *: p) = c * (meval v p).
Proof. exact: meval_is_scalable. Qed.
End MEval.

Notation "p .@[ v ]" := (@meval _ _ v p).

(* -------------------------------------------------------------------- *)
Section MEvalCom.
Variable n : nat.
Variable R : comRingType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types v : n.-tuple R.

Lemma meval_is_lrmorphism v : lrmorphism_for *%R (meval v).
Proof.
  split; first split.
  + by apply/mmap_is_additive.
  + by apply/mmap_is_multiplicative.
  by move=> /= c p; rewrite /meval mmapZ /=.
Qed.

Canonical meval_rmorphism  v := RMorphism (meval_is_lrmorphism v).
Canonical meval_linear     v := AddLinear (meval_is_lrmorphism v).
Canonical meval_lrmorphism v := [lrmorphism of meval v].

Lemma mevalM v : {morph meval v: x y / x * y}.
Proof. exact: rmorphM. Qed.
End MEvalCom.

(* -------------------------------------------------------------------- *)
Section MPolyMap.
Variable n   : nat.
Variable R S : ringType.

Implicit Types p q r : {mpoly R[n]}.

Section Defs.
Variable f : R -> S.

Definition map_mpoly p : {mpoly S[n]} :=
  mmap ((@mpolyC n _) \o f) (fun i => 'X_i) p.
End Defs.

Section Additive.
Variable f : {additive R -> S}.

Local Notation "p ^f" := (map_mpoly f p).

Lemma map_mpoly_is_additive : additive (map_mpoly f).
Proof. by apply/mmap_is_additive. Qed.

Canonical map_mpoly_additive := Additive map_mpoly_is_additive.

Lemma map_mpolyE p k : msize p <= k ->
  p^f = \sum_(m : 'X_{1..n < k}) (f p@_m) *: 'X_[m].
Proof.
rewrite /map_mpoly; move/mmapE=> -> /=; apply/eq_bigr.
by move=> i _; rewrite mmap1_id mul_mpolyC.
Qed.
Implicit Arguments map_mpolyE [p].

Lemma mcoeff_map_mpoly m p : p^f@_m = f p@_m.
Proof.
pose_big_enough i; first rewrite (map_mpolyE i) //.
  by rewrite (mcoeff_mpoly (fun m => (f p@_m))).
by close.
Qed.
End Additive.

Section Multiplicative.
Variable f : {rmorphism R -> S}.

Local Notation "p ^f" := (map_mpoly f p).

Lemma map_mpoly_is_multiplicative : multiplicative (map_mpoly f).
Proof.
apply/commr_mmap_is_multiplicative => /=.
+ by move=> i x; apply/commr_mpolyX.
+ by move=> p m m'; rewrite mmap1_id; apply/commr_mpolyX.
Qed.

Canonical map_mpoly_multiplicative :=
  AddRMorphism map_mpoly_is_multiplicative.
End Multiplicative.
End MPolyMap.

(* -------------------------------------------------------------------- *)
Section MPolyOver.
Variable n : nat.
Variable R : ringType.

Definition mpolyOver (S : pred_class) :=
  [qualify a p : {mpoly R[n]} | all (mem S) [seq p@_m | m <- msupp p]].

Fact mpolyOver_key S : pred_key (mpolyOver S). Proof. by []. Qed.
Canonical mpolyOver_keyed S := KeyedQualifier (mpolyOver_key S).

Lemma mpolyOverS (S1 S2 : pred_class) :
  {subset S1 <= S2} -> {subset mpolyOver S1 <= mpolyOver S2}.
Proof.
move=> sS12 p /(all_nthP 0)S1p.
by apply/(all_nthP 0)=> i /S1p; apply: sS12.
Qed.

Lemma mpolyOver0 S: 0 \is a mpolyOver S.
Proof. by rewrite qualifE msupp0. Qed.

Lemma mpolyOver_mpoly (S : pred_class) E :
     (forall m : 'X_{1..n}, m \in dom E -> coeff m E \in S)
  -> [mpoly E] \is a mpolyOver S.
Proof.
move=> S_E; apply/(all_nthP 0)=> i; rewrite size_map /= => lt.
by rewrite (nth_map 0%MM) // mcoeff_MPoly S_E ?mem_nth.
Qed.

Section MPolyOverAdd.
Variable (S : predPredType R).
Variable (addS : addrPred S).
Variable (kS : keyed_pred addS).

Lemma mpolyOverP {p} : reflect (forall m, p@_m \in kS) (p \in mpolyOver kS).
Proof.
case: p=> E; rewrite qualifE /=; apply: (iffP allP); last first.
  by move=> h x /mapP /= [m m_in_E] ->; apply/h.
move=> h m; case: (boolP (m \in msupp (MPoly E))).
  by move=> m_in_E; apply/h/map_f.
  by rewrite -mcoeff_eq0 => /eqP->; rewrite rpred0.
Qed.

Lemma mpolyOverC c : (c%:MP \in mpolyOver kS) = (c \in kS).
Proof.
rewrite qualifE msuppC; case: eqP=> [->|] //=;
by rewrite ?rpred0 // andbT mcoeffC eqxx mulr1.
Qed.

Lemma mpolyOver_addr_closed : addr_closed (mpolyOver kS).
Proof.
split=> [|p q Sp Sq]; first exact: mpolyOver0.
by apply/mpolyOverP=> i; rewrite mcoeffD rpredD ?(mpolyOverP _).
Qed.

Canonical mpolyOver_addrPred := AddrPred mpolyOver_addr_closed.
End MPolyOverAdd.

Lemma mpolyOverNr S (addS : zmodPred S) (kS : keyed_pred addS) :
  oppr_closed (mpolyOver kS).
Proof.
by move=> p /mpolyOverP Sp; apply/mpolyOverP=> i; rewrite mcoeffN rpredN.
Qed.

Canonical mpolyOver_opprPred S addS kS := OpprPred (@mpolyOverNr S addS kS).
Canonical mpolyOver_zmodPred S addS kS := ZmodPred (@mpolyOverNr S addS kS).

Section MPolyOverSemiring.
Variable (S : predPredType R).
Variable (ringS : semiringPred S).
Variable (kS : keyed_pred ringS).

Lemma mpolyOver_mulr_closed : mulr_closed (mpolyOver kS).
Proof.
split=> [|p q /mpolyOverP Sp /mpolyOverP Sq].
  by rewrite mpolyOverC rpred1.
apply/mpolyOverP=> i; rewrite mcoeffM rpred_sum //.
by move=> j _; apply: rpredM.
Qed.

Canonical mpolyOver_mulrPred := MulrPred mpolyOver_mulr_closed.
Canonical pmolyOver_semiringPred := SemiringPred mpolyOver_mulr_closed.

Lemma mpolyOverZ :
  {in kS & mpolyOver kS, forall c p, c *: p \is a mpolyOver kS}.
Proof.
move=> c p Sc /mpolyOverP Sp; apply/mpolyOverP=> i.
by rewrite mcoeffZ rpredM ?Sp.
Qed.

Lemma mpolyOverX m : 'X_[m] \in mpolyOver kS.
Proof. by rewrite qualifE msuppX /= mcoeffX eqxx rpred1. Qed.

Lemma rpred_mhorner :
  {in mpolyOver kS, forall p (v : n.-tuple R),
     (all [pred x | x \in kS] v) -> p.@[v] \in kS}.
Proof.
move=> p /mpolyOverP Sp v Sv; rewrite mevalE rpred_sum // => m _.
rewrite rpredM // rpred_prod //= => /= i _.
by rewrite rpredX //; move/allP: Sv; apply; apply/mem_tnth.
Qed.
End MPolyOverSemiring.

Section MPolyOverRing.
Variable (S : predPredType R).
Variable (ringS : subringPred S).
Variable (kS : keyed_pred ringS).

Canonical mpolyOver_smulrPred := SmulrPred (mpolyOver_mulr_closed kS).
Canonical mpolyOver_subringPred := SubringPred (mpolyOver_mulr_closed kS).

Lemma mpolyOverXaddC m c : ('X_[m] + c%:MP \in mpolyOver kS) = (c \in kS).
Proof. by rewrite rpredDl ?mpolyOverX ?mpolyOverC. Qed.
End MPolyOverRing.
End MPolyOver.

(* -------------------------------------------------------------------- *)
Section MPolyIdomain.
Variable n : nat.
Variable R : idomainType.

Implicit Types p q r : {mpoly R[n]}.

Lemma mleadM p q : p != 0 -> q != 0 ->
  mlead (p * q) = (mlead p + mlead q)%MM.
Proof.
move=> nz_p nz_q; rewrite mleadM_proper //.
by rewrite mulf_neq0 // mleadc_eq0.
Qed.

Lemma mlead_prod (T : eqType) (r : seq T) (P : pred T) (F : T -> {mpoly R[n]}) :
     (forall x, x \in r -> P x -> F x != 0)
  ->   mlead (\prod_(p <- r | P p) F p)
     = (\sum_(p <- r | P p) mlead (F p))%MM.
Proof.
move=> nz_Fr; rewrite mlead_prod_proper //.
move=> x x_in_r Px; apply/lregP; rewrite mleadc_eq0.
by apply/nz_Fr.
Qed.

Lemma mleadX p k : p != 0 -> mlead (p ^+ k) = (mlead p *+ k)%MM.
Proof.
move=> nz_p; rewrite mleadX_proper //.
by apply/lregP; rewrite mleadc_eq0.
Qed.

Lemma mleadZ c p : c != 0 -> mlead (c *: p) = mlead p.
Proof.
move=> nz_c; have [->|nz_p] := eqVneq p 0.
  by rewrite scaler0.
by rewrite mleadZ_proper // mulf_neq0 // mleadc_eq0.
Qed.

Lemma msizeM p q : p != 0 -> q != 0 ->
  msize (p * q) = (msize p + msize q).-1.
Proof.
move=> nz_p nz_q; rewrite msizeM_proper ?mulf_neq0 //.
  by rewrite mleadc_eq0. by rewrite mleadc_eq0.
Qed.

Lemma msuppZ c p : c != 0 -> perm_eq (msupp (c *: p)) (msupp p).
Proof.
move=> nz_c; apply/uniq_perm_eq=> // m.
by rewrite !mcoeff_msupp mcoeffZ mulf_eq0 (negbTE nz_c).
Qed.

Lemma mmeasureZ c p mf : c != 0 -> mmeasure mf (c *: p) = mmeasure mf p.
Proof. by move=> nz_c; rewrite !mmeasureE; apply/eq_big_perm/msuppZ. Qed.

Lemma msizeZ c p : c != 0 -> msize (c *: p) = msize p.
Proof. by apply/mmeasureZ. Qed.

Lemma mpoly_idomainAxiom p q :
  p * q = 0 -> (p == 0) || (q == 0).
Proof.
move=> z_pq; apply/norP; case=> [nz_p nz_q].
move/eqP: (msizeM nz_p nz_q); rewrite eq_sym z_pq.
by rewrite msize0 (mpolySpred _ nz_p) (mpolySpred _ nz_q) addnS.
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

Definition mpoly_comUnitMixin :=
  ComUnitRingMixin mpoly_mulVp mpoly_intro_unit mpoly_inv_out.

Canonical mpoly_unitRingType :=
  Eval hnf in UnitRingType {mpoly R[n]} mpoly_comUnitMixin.
Canonical mpolynomial_unitRingType :=
  Eval hnf in [unitRingType of mpoly n R for mpoly_unitRingType].

Canonical mpoly_unitAlgType :=
  Eval hnf in [unitAlgType R of {mpoly R[n]}].
Canonical mpolynomial_unitAlgType :=
  Eval hnf in [unitAlgType R of mpoly n R].

Canonical mpoly_comUnitRingType :=
  Eval hnf in [comUnitRingType of {mpoly R[n]}].
Canonical mpolynomial_comUnitRingType :=
  Eval hnf in [comUnitRingType of mpoly n R].

Canonical mpoly_idomainType :=
  Eval hnf in IdomainType {mpoly R[n]} mpoly_idomainAxiom.
Canonical mpolynomial_idomainType :=
  Eval hnf in [idomainType of mpoly n R for mpoly_idomainType].
End MPolyIdomain.

(* -------------------------------------------------------------------- *)
Section MWeightTheory.
Variable n : nat.
Variable R : ringType.

Implicit Types m : 'X_{1..n}.
Implicit Types p : {mpoly R[n]}.

Lemma leq_mdeg_mnmwgt m : mdeg m <= mnmwgt m.
Proof.
rewrite /mnmwgt mdegE leq_sum //= => i _.
by apply/leq_pmulr.
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
Variable n : nat.
Variable R : ringType.

Implicit Types p q : {mpoly R[n]}.
Implicit Types m : 'X_{1..n}.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma mperm_inj (s : 'S_n) : injective (fun m => m#s).
Proof.
move=> m1 m2 /= /mnmP h; apply/mnmP=> i.
by move: (h (s^-1 i)%g); rewrite !mnmE permKV.
Qed.

Lemma mperm1 (m : 'X_{1..n}) : m#(1 : 'S_n)%g = m.
Proof. by apply/mnmP=> i; rewrite mnmE perm1. Qed.

Lemma mpermM (m : 'X_{1..n}) (s1 s2 : 'S_n) : m#(s1 * s2)%g = m#s2#s1.
Proof. by apply/mnmP=> i; rewrite !mnmE permM. Qed.

Lemma mpermKV (s : 'S_n) :
  cancel (fun m => m#s) (fun m => m#(s^-1))%g.
Proof. by move=> m /=; apply/mnmP=> i; rewrite !mnmE permKV. Qed.

Lemma mpermK (s : 'S_n) :
  cancel (fun m => m#(s^-1))%g (fun m => m#s).
Proof. by move=> m /=; apply/mnmP=> i; rewrite !mnmE permK. Qed.

Lemma mdeg_mperm m (s : 'S_n) : mdeg (m#s) = mdeg m.
Proof.
rewrite !mdegE (reindex_inj (h := s^-1))%g /=; last first.
  by apply/perm_inj.
by apply/eq_bigr=> j _; rewrite !mnmE permKV.
Qed.
End MPerm.

(* -------------------------------------------------------------------- *)
Section MPolySym.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

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

Implicit Arguments msymE [p].

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
Proof. by apply/mmap_is_additive. Qed.

Canonical msym_additive s := Additive (msym_is_additive s).

Lemma msym0   s   : msym s 0 = 0               . Proof. exact: raddf0. Qed.
Lemma msymN   s   : {morph msym s: x / - x}    . Proof. exact: raddfN. Qed.
Lemma msymD   s   : {morph msym s: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma msymB   s   : {morph msym s: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma msymMn  s k : {morph msym s: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma msymMNn s k : {morph msym s: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma msym_is_multiplicative s : multiplicative (msym s).
Proof.
apply/commr_mmap_is_multiplicative=> /=.
+ by move=> i  x; apply/commr_mpolyX.
+ move=> p m1 m2 /=; rewrite /mmap1; elim/big_rec: _.
    by apply/commr1.
    by move=> /= i q _; apply/commrM/commrX/commr_mpolyX.
Qed.

Canonical msym_multiplicative s := AddRMorphism (msym_is_multiplicative s).

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

Canonical msym_linear (s : 'S_n) : {linear {mpoly R[n]} -> {mpoly R[n]}} :=
  AddLinear ((fun c => (msymZ c)^~ s) : scalable_for *:%R (msym s)).

Canonical msym_lrmorphism s := [lrmorphism of msym s].

Definition symmetric : qualifier 0 {mpoly R[n]} :=
  [qualify p | [forall s, msym s p == p]].

Fact symmetric_key : pred_key symmetric. Proof. by []. Qed.
Canonical symmetric_keyed := KeyedQualifier symmetric_key.

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

Canonical sym_opprPred := OpprPred sym_zmod.
Canonical sym_addrPred := AddrPred sym_zmod.
Canonical sym_zmodPred := ZmodPred sym_zmod.

Lemma sym_mulr_closed : mulr_closed symmetric.
Proof.
split=> [|p q /issymP sp /issymP sq]; apply/issymP=> s.
  by rewrite msym1.
by rewrite msymM sp sq.
Qed.

Canonical sym_mulrPred     := MulrPred     sym_mulr_closed.
Canonical sym_smulrPred    := SmulrPred    sym_mulr_closed.
Canonical sym_semiringPred := SemiringPred sym_mulr_closed.
Canonical sym_subringPred  := SubringPred  sym_mulr_closed.

Lemma sym_submod_closed : submod_closed symmetric.
Proof.
split=> [|c p q /issymP sp /issymP sq]; apply/issymP=> s.
  by rewrite msym0.
by rewrite msymD msymZ sp sq.
Qed.

Canonical sym_submodPred := SubmodPred sym_submod_closed.
Canonical sym_subalgPred := SubalgPred sym_submod_closed.

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
  apply/lemP; first by rewrite mdeg_mperm.
  exists i=> [k lt_ki|]; last by rewrite mnmE tpermL.
  rewrite mnmE tpermD // neq_ltn orbC ?lt_ki //.
  by move/leq_trans: lt_ki => /(_ _ le_ij) ->.
have: ms \in msupp p by rewrite issym_msupp // mlead_supp.
by move/msupp_le_mlead/leoNgt/negbTE=> ->.
Qed.
End MPolySym.

Implicit Arguments inj_msym [n R].
Implicit Arguments symmetric [n R].

(* -------------------------------------------------------------------- *)
Section MPolySymComp.
Variable n : nat.
Variable R : ringType.

Lemma mcomp_sym k (p : {mpoly R[n]}) (t : n.-tuple {mpoly R[k]}) :
     (forall i : 'I_n, t`_i \is symmetric)
  -> p \mPo t \is symmetric.
Proof.
move=> sym_t; pose_big_enough l.
  rewrite (comp_mpolywE _ (w := l)) //. 2: by close.
apply/rpred_sum=> m _; apply/rpredZ/rpred_prod=> i _.
by rewrite (tnth_nth 0); apply/rpredX/sym_t.
Qed.
End MPolySymComp.

(* -------------------------------------------------------------------- *)
Section MPolySymCompCom.
Variable n : nat.
Variable R : comRingType.

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
case/tuple_perm_eqP: (sym_t s^-1)%g => s' tE.
pose F (m : 'X_{1..n < l}) := insubd m [multinom m (s' i) | i < n].
have FE m: F m = [multinom m (s' i) | i < n] :> 'X_{1..n}.
  by rewrite insubdK // -topredE /= mdeg_mperm ?bmdeg.
rewrite raddf_sum {1}(reindex_inj (h := F)) /=; last first.
  move=> m1 m2 /(congr1 (@bmnm _ _)); rewrite !FE.
  by move/mperm_inj=> /val_inj.
apply/eq_bigr=> m _; rewrite linearZ /= FE msym_coeff //.
rewrite rmorph_prod /= (reindex_inj (perm_inj (s := s'^-1))) /=.
congr (_ *: _); apply/eq_bigr=> i _; rewrite rmorphX /=.
rewrite mnmE permKV (tnth_nth 0) {1}tE -!tnth_nth.
rewrite !tnth_map !tnth_ord_tuple permKV -msymMm.
by rewrite mulVg msym1m -tnth_nth.
Qed.
End MPolySymCompCom.

(* -------------------------------------------------------------------- *)
Section MPolySymUnit.
Variable n : nat.
Variable R : idomainType.

Implicit Types p q r : {mpoly R[n]}.

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

Canonical sym_divringPred  := DivringPred sym_divring.
End MPolySymUnit.

(* -------------------------------------------------------------------- *)
Section MElemPolySym.
Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types h : {set 'I_n}.

Definition mesym (k : nat) : {mpoly R[n]} :=
  \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i.

Local Notation "''s_' k" := (@mesym k).

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Definition mesym1 (h : {set 'I_n}) :=
  [multinom (i \in h : nat) | i < n].

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
by case: (_ \in _)=> //; rewrite mnmE (negbTE ne_ji).
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

Local Hint Resolve inj_mesym1.

Lemma msupp_mesym k :
  perm_eq
    (msupp 's_k)
    [seq mesym1 h | h : {set 'I_n} <- enum {set 'I_n} & #|h| == k].
Proof.
rewrite mesymE; apply/(perm_eq_trans (msupp_sum _ _ _))=> /=.
+ by rewrite /index_enum -enumT enum_uniq.
+ move=> h1 h2 _ _ ne_h1h2 m /=; rewrite !msuppX !mem_seq1.
  apply/negbTE/negP=> /andP[/eqP->] /eqP /inj_mesym1.
  by move/eqP; rewrite (negbTE ne_h1h2).
rewrite /index_enum -enumT /= (eq_map (fun h => msuppX _ (mesym1 h))).
by rewrite (map_comp (cons^~ [::])) flatten_seq1.
Qed.

Lemma msupp_mesymP (k : nat) m :
    (m \in msupp 's_k)
  = [exists h : {set 'I_n}, (#|h| == k) && (m == mesym1 h)].
Proof.
rewrite (perm_eq_mem (msupp_mesym _)); apply/idP/existsP=> /=.
+ case/mapP=> /= h; rewrite mem_filter=> /andP[/eqP<- _ ->].
  by exists h; rewrite !eqxx.
+ case=> h /andP[/eqP<- /eqP->]; apply/mapP; exists h=> //.
  by rewrite mem_filter eqxx /= mem_enum.
Qed.

Definition mechar k (m : 'X_{1..n}) :=
  (mdeg m == k) && [forall i, m i <= 1%N].

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
rewrite mecharP; case: (boolP [exists _, _]) => /=.
+ case/existsP=> /= h /andP[/eqP-> /eqP<-]; rewrite mesymE.
  rewrite raddf_sum (bigD1 h) //= mcoeffX eqxx big1 ?addr0 //.
  move=> h' /andP[_ ne_h]; rewrite mcoeffX -[0]/0%:R.
  by congr _%:R; apply/eqP; rewrite eqb0 inj_eq.
rewrite negb_exists=> /forallP /= ne; rewrite mesymE.
rewrite raddf_sum big1 //= => h cardh; have := ne h.
by rewrite cardh andbT mcoeffX eq_sym => /negbTE->.
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
  by apply/imsetP; exists i=> //.
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
apply/ltoW/lemP; first by rewrite !mdeg_mesym1 card_mesymlmnm.
exists i0; rewrite {}/i0; case: arg_minP => //=.
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
rewrite -mesymlmE /mesymlm /mlead; set m := mesym1 _.
rewrite (bigD1_seq (mesymlm k)) //=; last first.
  rewrite mem_msupp_mesym mecharP; apply/existsP.
  by exists (mesymlmnm k); rewrite card_mesymlmnm ?eqxx.
apply/maxo_idPl=> //; apply/bigmax_leoP=> //=.
move=> {m} m; rewrite msupp_mesymP => /existsP[/=].
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

Lemma eq_tmono (h1 h2 : seq 'I_n) :
  tmono h1 -> tmono h2 -> h1 =i h2 -> h1 = h2.
Proof.
move=> tm1 tm2 h; apply/(inj_map val_inj).
apply/(eq_sorted_irr (leT := ltn))=> //.
  by apply/ltn_trans.
  by move=> ?; rewrite /ltn /= ltnn.
move=> m; apply/mapP/mapP; case=> /= x;
  by rewrite (h, =^~ h)=> {h} h ->; exists x.
Qed.

Lemma mesym_tupleE (k : nat) : 's_k =
  \sum_(h : k.-tuple 'I_n | tmono h) \prod_(i <- h) 'X_i.
Proof.
have tval_tcast T k1 k2 (eq : k1 = k2) (x : k1.-tuple T):
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
        by apply/ltn_trans.
        by apply/map_subseq; rewrite /enum_mem -enumT; apply/filter_subseq.
        by rewrite val_enum_ord iota_ltn_sorted.
    * by apply/setP=> i; rewrite !(inE, memtE) tval_tcast mem_enum.
rewrite -h {h}/E big_imset 1?big_set /=; last first.
  move=> t1 t2; rewrite !inE => tmono_t1 tmono_t2 /setP eq.
  apply/eqP; rewrite eqE /=; apply/eqP/eq_tmono => // i.
  by move/(_ i): eq; rewrite /t2s !inE.
apply/eq_big=> // i; rewrite inE 1?big_set /=.
case: i => i sz_i /= tmono_i; rewrite (eq_bigl (mem i)) //=.
by rewrite !mprodXE big_uniq //; apply/uniq_tmono.
Qed.
End MElemPolySym.

Local Notation "''s_' ( K , n , k )" := (@mesym n K k).
Local Notation "''s_' ( n , k )" := (@mesym n _ k).

(* -------------------------------------------------------------------- *)
Section MWiden.
Variable n : nat.
Variable R : ringType.

Definition mwiden (p : {mpoly R[n]}) : {mpoly R[n.+1]} :=
  mmap (@mpolyC _ _) (fun i => 'X_(widen i)) p.

Definition mnmwiden (m : 'X_{1..n}) : 'X_{1..n.+1} :=
  [multinom of rcons m 0%N].

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
Proof. by apply/big_morph; [apply/mnmwidenD | apply/mnmwiden0]. Qed.

Lemma mnmwiden1 i : (mnmwiden U_(i) = U_(widen i))%MM.
Proof.
apply/mnmP; case=> j /= lt; rewrite /mnmwiden !mnmE; apply/esym.
rewrite eqE multinomE /tnth /=; move: (tnth_default _ _) => x.
rewrite nth_rcons size_map size_enum_ord; move: lt.
rewrite ltnS leq_eqVlt; case/orP => [/eqP->|lt].
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
Proof. by apply/mmap_is_additive. Qed.

Lemma mwiden0     : mwiden 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mwidenN     : {morph mwiden: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mwidenD     : {morph mwiden: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mwidenB     : {morph mwiden: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mwidenMn  k : {morph mwiden: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma mwidenMNn k : {morph mwiden: x / x *- k} . Proof. exact: raddfMNn. Qed.

Canonical mwiden_additive := Additive mwiden_is_additive.

Lemma mwiden_is_multiplicative : multiplicative mwiden.
Proof.
apply/commr_mmap_is_multiplicative=> /=.
+ by move=> i p; apply/commr_mpolyX.
+ move=> p m m'; rewrite /mmap1; elim/big_rec: _ => /=.
    by apply/commr1.
  by move=> i q _; apply/commrM/commrX/commr_mpolyX.
Qed.

Canonical mwiden_rmorphism := AddRMorphism mwiden_is_multiplicative.

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

Canonical mpwiden_additive := Additive mpwiden_is_additive.

Lemma mpwiden_is_rmorphism : rmorphism mpwiden.
Proof. exact: map_poly_is_rmorphism. Qed.

Canonical mpwiden_rmorphism := RMorphism mpwiden_is_rmorphism.

Lemma mpwidenX : mpwiden 'X = 'X.
Proof. by rewrite /mpwiden map_polyX. Qed.

Lemma mpwidenC c : mpwiden c%:P = (mwiden c)%:P.
Proof. by rewrite /mpwiden map_polyC. Qed.

Lemma mpwidenZ c p : mpwiden (c *: p) = mwiden c *: (mpwiden p).
Proof. by rewrite /mpwiden map_polyZ. Qed.
End MWiden.

(* -------------------------------------------------------------------- *)
Section MPolyUni.
Variable n : nat.
Variable R : ringType.

Implicit Types p q : {mpoly R[n.+1]}.

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
by apply/eq_bigr=> i _; rewrite X2 rmorphX /= mnmE.
Qed.

Lemma muniE p : muni p =
  \sum_(m <- msupp p)
     p@_m *: 'X_[[multinom (m (widen i)) | i < n]] *: 'X^(m ord_max).
Proof.
apply/eq_bigr=> m _; rewrite XE /= -!mul_polyC.
by rewrite mulrA -polyC_mul mul_mpolyC.
Qed.

Definition mmulti (p : {poly {mpoly R[n]}}) : {mpoly R[n.+1]} :=
  \sum_(i < size p) ((mwiden p`_i) * ('X_ord_max) ^+ i).

Lemma muni_is_additive : additive muni.
Proof. by apply/mmap_is_additive. Qed.

Canonical muni_additive := Additive muni_is_additive.

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
  apply/polyP=> k; rewrite coefCM coefMC.
  by apply/commr_mpolyX.
apply/polyP=> k; rewrite coefCM coefMC XE coefZ coefXn.
case: eqP; rewrite ?(mulr0, mul0r, mulr1, mul1r) //= => _.
by apply/commr_mpolyX.
Qed.

Canonical muni_rmorphism : {rmorphism {mpoly R[n.+1]} -> {poly {mpoly R[n]}}} :=
  AddRMorphism muni_is_multiplicative.

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

Local Hint Resolve inj_widen.

Let inj_swiden n : injective (fun h : {set 'I_n} => swiden h).
Proof.
have h m (x : 'I_n): (widen x \in swiden m) = (x \in m).
  apply/imsetP/idP=> /= [[y y_in_m /inj_widen ->//]|].
  by move=> x_in_m; exists x.
move=> m1 m2 /= /setP eq; apply/setP=> /= x.
by have := eq (widen x); rewrite !h.
Qed.

Local Hint Resolve inj_swiden.

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
move/setP/(_ ord_max); rewrite !in_set eqxx /=.
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
rewrite !card_imset //= ?card_draws /=; first last.
  by apply/inj_swiden. by apply/inj_mDswiden.
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
  rewrite mulmC setU1K //= ?mnmwiden_sum ?big_imset /=.
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
  by rewrite rmorphX /= mpwidenX exprSr.
rewrite big_nat_recr 1?[X in _-X]big_nat_recr //=.
rewrite opprD !addrA; congr (_ + _); last first.
  rewrite !Fnn !mpwidenZ !rmorphX /= mwidenN1.
  rewrite exprS mulN1r scaleNr -scalerAl; congr (- (_ *: _)).
  rewrite big_ord_recr rmorph_prod /=; congr (_ * _).
  by apply/eq_bigr=> i _; rewrite mpwidenC mwidenX mnmwiden1.
rewrite -sumrB !big_seq; apply/eq_bigr => i /=.
rewrite mem_index_iota => /andP [_ lt_in]; rewrite {Fn0 Fnn}/F.
rewrite subSS mesymSS !mpwidenZ !rmorphX /= !mwidenN1 !mpwidenX.
rewrite exprS mulN1r !scaleNr mulNr -opprD; congr (-_).
rewrite -!scalerAl -scalerDr; congr (_ *: _).
rewrite -exprSr -subSn // subSS scalerDl; congr (_ + _).
by rewrite -!mul_polyC !mulrA mulrAC polyC_mul.
Qed.

Lemma mroots_coeff (R : idomainType) n (cs : n.-tuple R) (k : 'I_n.+1) :
    (\prod_(c <- cs) ('X - c%:P))`_(n - k)
  = (-1)^+k * 's_(n, k).@[cs].
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
rewrite !map_polyZ !rmorphX raddfN /= mmapC !coefZ /=.
congr (_ * _); rewrite map_polyX coefXn eqxx mulr1.
rewrite /mesym; rewrite !raddf_sum /=; apply/eq_bigr.
move=> i _; rewrite !rmorph_prod /=; apply/eq_bigr.
by move=> j _; rewrite mmapX mmap1U mevalX.
Qed.

Lemma mroots_sum (R : idomainType) (n : nat) (cs : n.+1.-tuple R) :
  \sum_(c <- cs) c = - (\prod_(c <- cs) ('X - c%:P))`_n.
Proof.
move: (mroots_coeff cs) => /(_ 1); rewrite subSS subn0=> ->.
rewrite expr1 mulN1r opprK mesym1E raddf_sum /=.
by rewrite big_tuple; apply/eq_bigr=> /= i _; rewrite mevalX.
Qed.
End MESymViete.

(* -------------------------------------------------------------------- *)
Section MESymFundamental.
Variable n : nat.
Variable R : comRingType.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Local Notation S := [tuple 's_(R, n, i.+1) | i < n].

Implicit Types m : 'X_{1..n}.

Let mlead_XS :
  forall m,
      mlead ('X_[R, m] \mPo S)
    = [multinom \sum_(j : 'I_n | i <= j) (m j) | i < n]%N.
Proof.
move=> m; rewrite comp_mpolyX mlead_prod_proper=> /=; last first.
  move=> i _ _; rewrite tnth_map tnth_ord_tuple.
  rewrite mleadX_proper /= ?mleadc_mesym //; last by apply/lreg1.
  by rewrite mleadcX ?mleadc_mesym //; apply/lregX/lreg1.
pose F (i : 'I_n) := [multinom (j <= i) * (m i) | j < n]%N.
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
    by apply/lregX/lreg1. by apply/lreg1.
rewrite (eq_bigr (fun _ => 1)) /=; last first.
  move=> i _; rewrite tnth_map tnth_ord_tuple.
  rewrite mleadX_proper ?mleadcX ?mleadc_mesym //.
    by rewrite expr1n. by apply/lreg1.
by rewrite prodr_const expr1n.
Qed.

Let free_XS m1 m2 : m1 != m2 ->
  mlead ('X_[R, m1] \mPo S) != mlead ('X_[R, m2] \mPo S).
Proof.
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
rewrite -big_mkord (big_cat_nat _ (n := i%N)) // 1?ltnW //=.
rewrite big_nat_cond big_pred0 ?add0n; last first.
  by move=> j /=; rewrite ltnNge andNb.
rewrite big_nat_cond (eq_bigl (fun j => i <= j < n)); last first.
  by move=> j /=; apply/andb_idr=> /andP[].
rewrite -big_nat; rewrite sumn_range 1?ltnW //.
  rewrite /c [X in (_-X)%N]nth_default ?size_tuple //.
  by rewrite subn0 (mnm_nth 0%N).
move=> j1 j2; rewrite ltnS=> /andP[le_j1j2].
rewrite leq_eqVlt ltn_subRL; case/orP=> [/eqP->|].
  rewrite subnK ?[i <= _]ltnW // /c nth_default //.
  by rewrite size_tuple.
rewrite addnC=> lt_j2Di_n; have lt_j1Di_n: j1 + i < n.
  by apply/(@leq_ltn_trans (j2+i))=> //; rewrite leq_add2r.
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
  move=> i j /andP[le_ij]; rewrite ltnS leq_eqVlt.
  case/orP=> [/eqP->|].
    by rewrite {1}/c nth_default // size_tuple.
  move=> lt_jn; have lt_in: i < n.
    by apply (leq_ltn_trans le_ij).
  have /(_ le_ij) := (srt_m (Ordinal lt_in) (Ordinal lt_jn)).
  by rewrite /fun_of_multinom !(tnth_nth 0%N).
rewrite {2}/c nth_default ?size_tuple // muln0 subn0.
by apply/eq_bigr=> /= i _; rewrite /fun_of_multinom (tnth_nth 0%N).
Qed.

Lemma sym_fundamental (p : {mpoly R[n]}) : p \is symmetric ->
  { t | t \mPo S = p /\ mweight t <= msize p}.
Proof.
set S := [tuple 's_(n, i.+1) | i < n].
elim/mleadrect: p=> p ih sym_p; have [->|nz_p] := eqVneq p 0.
  by exists 0; rewrite comp_mpoly0 mmeasure0.
set m := mlead p; pose c := nth 0%N m.
pose F i := (c i - c i.+1)%N; pose l := F#val.
pose q := p - p@_m *: ('X_[l] \mPo S); have [z_q|nz_q] := eqVneq q 0.
  exists (p@_m *: 'X_[l]); move/eqP: z_q; rewrite /q subr_eq0.
  move/eqP/esym; rewrite comp_mpolyZ=> ->; split=> //.
  rewrite (@leq_trans (mweight 'X_[R, l])) ?mmeasureZ_le //.
  rewrite -?mlead_deg ?mleadc_eq0 //.
  by rewrite (mweight_XLS (mlead_msym_sorted sym_p)).
have lt_pq: (mlead q < mlead p)%O.
  have mE := (mlead_XLS (mlead_msym_sorted sym_p)).
  rewrite -/m -/c -/l -/S in mE; rewrite lto_neqAle andbC.
  have := mleadB_le p (p@_m *: ('X_[l] \mPo S)).
  rewrite mleadZ_proper ?mE ?maxoo // => [->/=|]; last first.
    rewrite mulrC mulrI_eq0 ?mleadc_eq0 // -mE.
    rewrite mleadc_XS; apply/lreg1.
  apply/eqP=> eq_lm_pq; have := nz_q; rewrite -mleadc_eq0.
  rewrite eq_lm_pq /q mcoeffB mcoeffZ -/m -{3}mE mleadc_XS.
  by rewrite mulr1 subrr eqxx.
elim: (ih q)=> //; first last.
  rewrite /q rpredB // rpredZ // mcomp_sym // => i.
  by rewrite -tnth_nth tnth_map mesym_sym.
move=> t [/esym qE] wgt_t; exists (t + p@_m *: 'X_[l]).
rewrite comp_mpolyD comp_mpolyZ -qE /q.
rewrite addrAC -addrA subrr addr0; split=> //.
apply/(leq_trans (mmeasureD_le _ _ _)); rewrite geq_max.
rewrite (leq_trans (mmeasureZ_le _ _ _)) ?andbT.
  rewrite (leq_trans wgt_t) // -!mlead_deg //.
  by rewrite ltnS lem_mdeg // ltoW.
rewrite mweight_XLS -?mlead_deg //.
by apply/mlead_msym_sorted.
Qed.

Local Notation XS m := ('X_[R, m] \mPo S) (only parsing).

Lemma msym_fundamental_un0 (t : {mpoly R[n]}) :
  t \mPo S = 0 -> t = 0.
Proof.
set S := S; move/eqP; apply/contraTeq=> nz_t; rewrite -mleadc_eq0.
have h m: m \in msupp t -> mlead (t@_m *: (XS m)) = mlead (XS m).
  move=> m_in_t; rewrite mleadZ_proper // mleadc_XS.
  by rewrite mulr1 mcoeff_eq0 m_in_t.
rewrite comp_mpolyEX mlead_sum ?filter_predT; last first.
  rewrite (iffLR (eq_in_map _ _ _) h) -/S.
  apply/(@uniq_nth _ 0%MM) => i j; rewrite size_map.
  move=> lti ltj ne_ij; rewrite !(nth_map 0%MM) //.
  by apply/free_XS; rewrite nth_uniq.
rewrite big_seq (eq_bigr _ h) -big_seq.
case: (eq_bigmaxo (fun m => mlead (XS m)) (r := msupp t)).
  by rewrite msupp_eq0.
move=> /= m /andP[m_in_t /eqP/esym]; rewrite -/S=> lmm.
rewrite -lmm raddf_sum /= (bigD1_seq m) //= mcoeffZ.
rewrite mleadc_XS mulr1 big_seq_cond big1.
  by rewrite addr0 mcoeff_eq0 m_in_t.
move=> /= m' /andP[m'_in_t ne_m'm]; rewrite mcoeffZ.
rewrite [X in _*X]mcoeff_gt_mlead ?mulr0 //.
rewrite lto_neqAle free_XS //= lmm.
by apply (leo_bigmax (fun m => mlead (XS m))).
Qed.

Lemma msym_fundamental_un (t1 t2 : {mpoly R[n]}) :
  t1 \mPo S = t2 \mPo S -> t1 = t2.
Proof.
move/eqP; rewrite -subr_eq0 -raddfB /= => /eqP.
by move/msym_fundamental_un0/eqP; rewrite subr_eq0=> /eqP.
Qed.
End MESymFundamental.

(* -------------------------------------------------------------------- *)
Local Notation count_flatten :=
  SsrMultinomials.ssrcomplements.count_flatten.

(* -------------------------------------------------------------------- *)
Definition ishomog1 {n} {R : ringType}
           (d : nat) (mf : measure n) : qualifier 0 {mpoly R[n]} :=
  [qualify p | all [pred m | mf m == d] (msupp p)].

(* -------------------------------------------------------------------- *)
Module MPolyHomog1Key.
Fact homog1_key {n} {R : ringType} d mf : pred_key (@ishomog1 n R d mf).
Proof. by []. Qed.

Definition homog1_keyed {n R} d mf := KeyedQualifier (@homog1_key n R d mf).
End MPolyHomog1Key.

Canonical MPolyHomog1Key.homog1_keyed.


(* -------------------------------------------------------------------- *)
Definition ishomog {n} {R : ringType} mf : qualifier 0 {mpoly R[n]} :=
  [qualify p | p \is ishomog1 (@mmeasure _ _ mf p).-1 mf].
(* -------------------------------------------------------------------- *)
Module MPolyHomogKey.
Fact homog_key {n} {R : ringType} mf : pred_key (@ishomog n R mf).
Proof. by []. Qed.

Definition homog_keyed {n R} mf := KeyedQualifier (@homog_key n R mf).
End MPolyHomogKey.

Canonical MPolyHomogKey.homog_keyed.

(* -------------------------------------------------------------------- *)
Section MPolyHomogTheory.
Variable n : nat.
Variable R : ringType.

Implicit Types p q : {mpoly R[n]}.

Variable mf : measure n.

Local Notation "d .-homog" := (@ishomog1 _ _ d mf)
  (at level 1, format "d .-homog") : form_scope.

Local Notation homog := (@ishomog _ _ mf).

Local Notation "[ 'in' R [ n ] , d .-homog ]" := (@ishomog1 n R d mf)
  (at level 0, R, n at level 2, d at level 0,
     format "[ 'in'  R [ n ] ,  d .-homog ]") : form_scope.

Lemma dhomogE d p:
  (p \is d.-homog) = (all [pred m | mf m == d] (msupp p)).
Proof. by []. Qed.

Lemma dhomogP d p:
  reflect
    {in msupp p, forall m, mf m = d}
    (p \is d.-homog).
Proof. by apply/(iffP allP)=> /= h m /h => [/eqP|->]. Qed.

Lemma dhomog_mf d p:
  p \is d.-homog -> {in msupp p, forall m, mf m = d}.
Proof. by move/dhomogP. Qed.

Lemma dhomog_nemf_coeff d p m:
  p \is d.-homog -> mf m != d -> p@_m = 0.
Proof.
  move/dhomogP=> hg_p; apply/contraTeq; rewrite -mcoeff_msupp.
  by move/hg_p=> ->; rewrite negbK.
Qed.

Lemma dhomog1 : (1 : {mpoly R[n]}) \is 0.-homog.
Proof. apply/dhomogP; rewrite msupp1=> m; rewrite inE=> /eqP ->; exact: mf0. Qed.

Lemma dhomog_uniq p d e : p != 0 -> p \is d.-homog -> p \is e.-homog -> d = e.
Proof.
  by move=> Hp /dhomogP/(_ _ (mlead_supp Hp)) <- /dhomogP/(_ _ (mlead_supp Hp)).
Qed.

Lemma dhomog_submod_closed d : submod_closed [in R[n], d.-homog].
Proof.
  split=> [|c p q]; first by rewrite dhomogE msupp0.
  move=> /dhomogP hg_p /dhomogP hg_q; apply/dhomogP=> m.
  move/msuppD_le; rewrite mem_cat; case/orP=> [/msuppZ_le|].
    by move/hg_p. by move/hg_q.
Qed.

Canonical dhomog_addPred    d := AddrPred   (dhomog_submod_closed d).
Canonical dhomog_oppPred    d := OpprPred   (dhomog_submod_closed d).
Canonical dhomog_zmodPred   d := ZmodPred   (dhomog_submod_closed d).
Canonical dhomog_submodPred d := SubmodPred (dhomog_submod_closed d).

Lemma dhomog0 d: 0 \is [in R[n], d.-homog].
Proof. by apply/rpred0. Qed.

Lemma dhomogX d m: ('X_[m] \is [in R[n], d.-homog]) = (mf m == d).
Proof. by rewrite dhomogE msuppX /= andbT. Qed.

Lemma dhomogD d: {in d.-homog &, forall p q, p + q \is d.-homog}.
Proof. by apply/rpredD. Qed.

Lemma dhomogN d: {mono -%R: p / p \in [in R[n], d.-homog]}.
Proof. by apply/rpredN. Qed.

Lemma dhomogZ d c p: p \in d.-homog -> (c *: p) \in d.-homog.
Proof. by apply/rpredZ. Qed.

Local Notation mfsize p := (@mmeasure _ _ mf p).

Lemma homog_msize p : (p \is homog) = (p \is (mfsize p).-1.-homog).
Proof. by []. Qed.

Lemma dhomog_msize d p : p \is d.-homog -> p \is (mfsize p).-1.-homog.
Proof.
  rewrite mmeasureE.
  case Hsupp : (size (msupp p)) => [| sz].
    move: Hsupp => /eqP/nilP Hsupp _; rewrite Hsupp big_nil /=.
    move: Hsupp => /msuppnil0 ->; exact: dhomog0.
  rewrite -(in_tupleE (msupp p)) big_tuple; set f := BIG_F.
  have /(eq_bigmax f) : 0 < #|'I_(size (msupp p))| by rewrite card_ord Hsupp.
  move=> [] imx ->; rewrite {}/f /= => Hhom.
  set mx := tnth _ _; suff <- : d = mf mx :> nat by [].
  move/dhomogP : Hhom => Hhom.
  by rewrite (Hhom _ (mem_tnth imx (in_tuple (msupp p)))).
Qed.

Lemma homogE d p : p \is d.-homog -> p \is homog.
Proof. by move/dhomog_msize. Qed.

Lemma homogP p : reflect (exists d, p \is d.-homog) (p \is homog).
Proof.
  rewrite unfold_in; apply (iffP idP).
  - move=> H; by exists (mfsize p).-1.
  - move=> [] d; exact: dhomog_msize.
Qed.

Lemma mpoly0 p : n = 0%N -> p = (p@_0%MM)%:MP.
Proof.
  move=> Hn; subst n; rewrite -mpolyP => m.
  rewrite mcoeffC.
  suff -> : m = 0%MM by rewrite eq_refl /= mulr1.
  rewrite mnmP => i; exfalso.
  by have := ltn_ord i.
Qed.

Lemma mpoly0_homog p : n = 0%N -> p \is 0.-homog.
Proof.
  move/(mpoly0 p) ->.
  case: (altP (p@_0 =P 0)) => [-> | /negbTE H]; first exact: dhomog0.
  apply/dhomogP => m; rewrite msuppC H inE => /eqP ->.
  exact: mf0.
Qed.

Lemma dhomogM d p e q :
  p \is d.-homog -> q \is e.-homog -> p * q \is (d + e).-homog.
Proof.
  move=> /dhomogP homp /dhomogP homq.
  apply/dhomogP => m /msuppM_le/allpairsP [[m1 m2]] [] /= /homp <- /homq <- ->.
  exact: mfD.
Qed.

Lemma dhomog_expr d p k :
  p \is d.-homog -> p ^+ k \is (d * k).-homog.
Proof.
  elim: k => [| k IHk] Hp.
    rewrite expr0 muln0; exact: dhomog1.
  rewrite exprS /= mulnS; by apply: dhomogM; last exact: IHk.
Qed.

Lemma prod_homog (s : seq {mpoly R[n]}) :
  all (fun p => p \is homog) s -> \prod_(p <- s) p \is homog.
Proof.
  move=> H; apply/homogP.
  elim: s H => [_ | p s IHs] /=.
    exists 0%N; rewrite big_nil; exact: dhomog1.
  move=> /andP [] /homogP [] dp Hdp /IHs{IHs} [] drec Hrec.
  exists (dp + drec)%N; rewrite big_cons.
  exact: dhomogM.
Qed.

End MPolyHomogTheory.

Notation "[ 'in' R [ n ] , d .-homog 'for' mf ]" := (@ishomog1 n R d mf)
  (at level 0, R, n at level 2, d at level 0,
     format "[ 'in'  R [ n ] , d .-homog 'for' mf ]") : form_scope.

Notation "[ 'in' R [ n ] , d .-homog ]" := [in R[n], d.-homog for [measure of mdeg]]
  (at level 0, R, n at level 2, d at level 0) : form_scope.

Notation "d .-homog 'for' mf" := (@ishomog1 _ _ d mf)
  (at level 1, format "d .-homog 'for' mf") : form_scope.

Notation "d .-homog" := (d .-homog for [measure of mdeg])
  (at level 1, format "d .-homog") : form_scope.

Notation "'homog' mf" := (@ishomog _ _ mf)
  (at level 1, format "'homog' mf") : form_scope.

(* -------------------------------------------------------------------- *)
Section ProjHomog.

Variable n : nat.
Variable R : ringType.
Variable mf : measure n.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types m : 'X_{1..n}.

Local Notation mfsize p := (@mmeasure _ _ mf p).

Section Def.
Variable d : nat.

Definition pihomog p : {mpoly R[n]} :=
  \sum_(m <- msupp p | mf m == d) p@_m *: 'X_[m].

Lemma pihomogE k p : mfsize p <= k ->
  pihomog p = \sum_(m <- msupp p | mf m == d) p@_m *: 'X_[m].
Proof. by []. Qed.

Lemma pihomogwE k p : msize p <= k ->
  pihomog p = \sum_(m : 'X_{1..n < k} | mf m == d) p@_m *: 'X_[m].
Proof.
  move=> lt_pk.
  pose I := [subFinType of 'X_{1..n < k}].
  rewrite /pihomog.
  rewrite [LHS](big_mksub_cond I) //=; first last.
    - by move=> x /msize_mdeg_lt/leq_trans/(_ lt_pk) ->.
    - by rewrite msupp_uniq.
  rewrite [RHS](bigID (fun x  : 'X_{1..n < k} => val x \in msupp p)) /=.
  rewrite [X in _ = _ + X]big1 ?addr0 // => m /andP [] _ /memN_msupp_eq0 ->.
  by rewrite scale0r.
Qed.

Lemma pihomog_is_linear : linear pihomog.
Proof.
  move=> c p q /=.
  pose_big_enough l.
    rewrite [LHS](pihomogwE _ (k := l)) //.
    rewrite (pihomogwE _ (k := l) (p := p)) //.
    rewrite (pihomogwE _ (k := l) (p := q)) //.
    2: by close.
  rewrite scaler_sumr -big_split /=; apply eq_bigr => m _.
  by rewrite linearP /= scalerDl scalerA.
Qed.
Canonical pihomog_additive : {additive {mpoly R[n]} -> {mpoly R[n]}} :=
  Additive pihomog_is_linear.
Canonical pihomog_linear   := Linear   pihomog_is_linear.

Lemma pihomog0     : pihomog 0 = 0               . Proof. exact: raddf0. Qed.
Lemma pihomogN     : {morph pihomog: x / - x}    . Proof. exact: raddfN. Qed.
Lemma pihomogD     : {morph pihomog: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma pihomogB     : {morph pihomog: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma pihomogMn  k : {morph pihomog: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma pihomogMNn k : {morph pihomog: x / x *- k} . Proof. exact: raddfMNn. Qed.

Lemma pihomog_dE p : p \is d.-homog for mf-> pihomog p = p.
Proof.
  move/dhomogP => hom_p.
  rewrite /pihomog {3}(mpolyE p) [LHS]big_seq_cond [RHS]big_seq_cond.
  apply eq_bigl => m /=; rewrite andbT.
  case: (boolP (m \in msupp p)) => //= /hom_p ->.
  by rewrite eq_refl.
Qed.

Lemma pihomogP p : pihomog p \is d.-homog for mf.
Proof.
  apply rpred_sum => m /eqP Hdeg; apply rpredZ.
  by apply/dhomogP => m0 /mem_msuppXP <-.
Qed.

Lemma pihomog_id p : pihomog (pihomog p) = pihomog p.
Proof. by rewrite pihomog_dE; last exact: pihomogP. Qed.

Lemma homog_piE p : p \is d.-homog for mf = (pihomog p == p).
Proof.
  apply (sameP idP); apply (iffP idP); last by move /pihomog_dE ->.
  move=> /eqP <-; exact: pihomogP.
Qed.

End Def.

Lemma pihomog_ne0 d b p : d != b -> p \is d.-homog for mf-> pihomog b p = 0.
Proof.
  move=> ne /dhomogP hom; rewrite /pihomog big_seq_cond.
  apply big_pred0 => m; apply negbTE.
  by move: ne; apply contra => /andP [] /hom ->.
Qed.

Lemma pihomog_partitionE k p : mfsize p <= k -> p = \sum_(d < k) pihomog d p.
Proof.
  move=> Hk; rewrite /pihomog (exchange_big_dep predT) //= {1}(mpolyE p).
  apply eq_bigr => m _.
  rewrite -scaler_sumr.
  case: (ssrnat.leqP k (mf m)) => [|Hmk].
    move/(leq_trans Hk)/mmeasure_mnm_ge/memN_msupp_eq0 ->; by rewrite !scale0r.
  rewrite (eq_bigl (fun i : 'I_k => i == Ordinal Hmk)); first last.
    by move=> i /=; rewrite eq_sym.
  by rewrite big_pred1_eq.
Qed.

End ProjHomog.

(* -------------------------------------------------------------------- *)
Section MPolyHomogType.

Variable n : nat.
Variable R : ringType.
Variable d : nat.

Inductive dhomog := DHomog (p : {mpoly R[n]}) of p \is d.-homog.

Coercion mpoly_of_dhomog (p : dhomog) :=
  let: DHomog p _ := p in p.

Canonical  dhomog_subType := Eval hnf in [subType for @mpoly_of_dhomog].
Definition dhomog_eqMixin := Eval hnf in [eqMixin of dhomog by <:].
Canonical  dhomog_eqType  := Eval hnf in EqType dhomog dhomog_eqMixin.

Definition dhomog_choiceMixin := [choiceMixin of dhomog by <:].
Canonical  dhomog_choiceType  := Eval hnf in ChoiceType dhomog dhomog_choiceMixin.

Definition dhomog_zmodMixin := [zmodMixin of dhomog by <:].
Canonical  dhomog_zmodType  := Eval hnf in ZmodType dhomog dhomog_zmodMixin.

Definition dhomog_lmodMixin := [lmodMixin of dhomog by <:].
Canonical  dhomog_lmodType  := Eval hnf in LmodType R dhomog dhomog_lmodMixin.

Lemma mpoly_of_dhomog_is_linear: linear mpoly_of_dhomog.
Proof. by []. Qed.

Canonical mpoly_of_dhomog_additive := Additive mpoly_of_dhomog_is_linear.
Canonical mpoly_of_dhomog_linear   := Linear   mpoly_of_dhomog_is_linear.
End MPolyHomogType.

Lemma dhomog_is_dhomog n (R : ringType) d (p : dhomog n R d) :
  (val p) \is [in R[n], d.-homog for [measure of mdeg]].
Proof. by case: p. Qed.

Hint Extern 0 (is_true (_ \is _.-homog mf)) => by apply/dhomog_is_dhomog.

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
  apply/(eq_sorted leq_trans anti_leq srt_t1 srt_t2).
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
      rewrite path_min_sorted; first by apply/(path_sorted (x := y)).
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
    by rewrite val_enum_ord /= path_min_sorted // iota_sorted.
  by apply/hasP; case.
Qed.

Lemma size_m2s n (m : 'X_{1..n}): size (m2s m) = mdeg m.
Proof.
  rewrite /m2s size_flatten /shape -map_comp /=.
  rewrite (eq_map (f2 := fun i : 'I_n => m i)).
    by rewrite mdegE bignat_sumn enumT.
  by move=> i /=; rewrite size_nseq.
Qed.

Lemma s2mK n (m : 'X_{1..n}): s2m (m2s m) = m.
Proof.
  apply/mnmP=> i; rewrite mnmE /m2s /=.
  rewrite count_flatten enumT (bigD1 i) //=.
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
  have {2}->: d = (\sum_(i <- t) 1)%N.
    by rewrite sum1_size size_tuple.
  rewrite -(eq_big_perm _ (perm_undup_count t)) /=.
  rewrite big_flatten /= big_map; apply/esym.
  transitivity (\sum_(i <- undup t) (count_mem i) t)%N.
    by apply/eq_bigr=> i _; rewrite big_nseq iter_succn add0n.
  apply/esym; rewrite (bigID (mem (undup t))) /= addnC.
  rewrite big1 ?add0n => [|i]; last first.
    by rewrite mem_undup => /count_memPn.
  by rewrite big_uniq ?undup_uniq.
Qed.

Lemma size_basis n d: size (sbasis n.+1 d) = 'C(d + n, d).
Proof. by rewrite size_map -cardE; apply/card_sorted_tuples. Qed.

Lemma uniq_basis n d: uniq (sbasis n d).
Proof.
  rewrite map_inj_in_uniq ?enum_uniq // => t1 t2.
  by rewrite !mem_enum; apply/inj_s2m.
Qed.

(* -------------------------------------------------------------------- *)
Variable n : nat.
Variable R : ringType.
Variable d : nat.

Lemma dhomog_vecaxiom: Vector.axiom 'C(d + n, d) (dhomog n.+1 R d).
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
    apply/esym/(dhomog_nemf_coeff (d := d)).
      by apply/dhomog_is_dhomog. by rewrite basis_cover.
  move=> m'; apply/contraTeq; rewrite mcoeffZ mcoeffX.
  by case: (m' =P m)=> [->|_]; last rewrite mulr0 eqxx.
Qed.

Definition dhomog_vectMixin :=
  VectMixin dhomog_vecaxiom.

Canonical dhomog_vectType :=
  Eval hnf in VectType R (dhomog n.+1 R d) dhomog_vectMixin.
End MPolyHomogVec.
