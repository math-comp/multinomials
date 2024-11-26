(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq path choice finset fintype finfun.
From mathcomp Require Import tuple bigop ssralg ssrint ssrnum.

Require Import xfinmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory BigEnoughFSet.

Local Open Scope fset.
Local Open Scope fmap.
Local Open Scope ring_scope.

Declare Scope monom_scope.
Delimit Scope monom_scope with M.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'cmonom' I }"
  (at level 0, I at level 2, format "{ 'cmonom'  I }").
Reserved Notation "[ 'cmonom' E | i 'in' P ]" (at level 0, i at level 99).
Reserved Notation "[ 'cmonom' E | i : P ]" (at level 0, i at level 99).
Reserved Notation "{ 'fmonom' I }"
  (at level 0, I at level 2, format "{ 'fmonom'  I }").
Reserved Notation "{ 'malg' G [ K ] }"
  (at level 0, K, G at level 2, format "{ 'malg'  G [ K ] }").
Reserved Notation "{ 'malg' K }"
  (at level 0, K at level 2, format "{ 'malg'  K }").
Reserved Notation "[ 'malg' g ]"
  (at level 0, g at level 2, format "[ 'malg'  g ]").
Reserved Notation "[ 'malg' x 'in' aT => E ]"
  (at level 0, x ident, format "[ 'malg'  x  'in'  aT  =>  E ]").
Reserved Notation "[ 'malg' x => E ]"
  (at level 0, x ident, format "[ 'malg'  x  =>  E ]").
Reserved Notation "{ 'mpoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'mpoly'  T [ n ] }").
Reserved Notation "<< z *p k >>"
  (at level 0, format "<< z *p k >>").
Reserved Notation "<< k >>"
  (at level 0, format "<< k >>").
Reserved Notation "g @_ k"
  (at level 3, k at level 2, left associativity, format "g @_ k").
Reserved Notation "c %:MP"
  (at level 2, left associativity, format "c %:MP").
Reserved Notation "''X_{1..' n '}'"
  (at level 0, n at level 2).
Reserved Notation "'U_(' n )"
  (at level 0, n at level 2, no associativity, format "'U_(' n )").
Reserved Notation "x ^[ f , g ]"
  (at level 2, left associativity, format "x ^[ f , g ]").

Reserved Notation "'{' 'mmorphism' M '->' S '}'"
  (at level 0, M at level 98, S at level 99,
   format "{ 'mmorphism'  M  ->  S }").

(* -------------------------------------------------------------------- *)
HB.mixin Record Choice_isMonomialDef V of Choice V := {
  one : V;
  mul : V -> V -> V;
  mulmA : associative mul;
  mul1m : left_id one mul;
  mulm1 : right_id one mul;
  unitm : forall x y, mul x y = one -> x = one /\ y = one
}.

HB.structure Definition MonomialDef :=
  { V of Choice V & Choice_isMonomialDef V }.

Module MonomialDefExports.
Bind Scope monom_scope with MonomialDef.sort.
Notation monomType := MonomialDef.type.
End MonomialDefExports.
Export MonomialDefExports.

(* -------------------------------------------------------------------- *)
Notation mone := one.
Notation mmul := mul.

Local Notation "1" := (@mone _) : monom_scope.
Local Notation "*%M" := (@mmul _) : function_scope.
Local Notation "x * y" := (mmul x y) : monom_scope.

(* -------------------------------------------------------------------- *)
HB.mixin Record MonomialDef_isConomialDef V of MonomialDef V := {
  mulmC : commutative (@mul V)
}.

HB.structure Definition ConomialDef :=
  { V of MonomialDef V & MonomialDef_isConomialDef V }.

Module ConomialDefExports.
Bind Scope monom_scope with ConomialDef.sort.
Notation conomType := ConomialDef.type.
End ConomialDefExports.
Export ConomialDefExports.

(* -------------------------------------------------------------------- *)
Section Monomial.
Context (M : monomType).

Local Open Scope monom_scope.

#[export]
HB.instance Definition _ := Monoid.isLaw.Build M 1 mmul mulmA mul1m mulm1.

Lemma unitmP (x y : M) : reflect (x == 1 /\ y == 1) (x * y == 1).
Proof.
by apply: (iffP eqP)=> [/unitm[-> ->]|[/eqP-> /eqP->]] //; rewrite mulm1.
Qed.
End Monomial.

#[export]
HB.instance Definition _ (M : conomType) := Monoid.isComLaw.Build M mone mmul
  (@mulmA M) mulmC (@mul1m M).

Module Exports. HB.reexport. End Exports.
Export Exports.

(* -------------------------------------------------------------------- *)
Definition mmorphism (M : monomType) (S : ringType) (f : M -> S) : Prop :=
  (f 1%M = 1) * {morph f : x y / (x * y)%M >-> (x * y)%R}.

HB.mixin Record isMultiplicative
    (M : monomType) (S : ringType) (apply : M -> S) := {
  mmorphism_subproof : mmorphism apply;
}.

#[mathcomp(axiom="multiplicative")]
HB.structure Definition MMorphism (M : monomType) (S : ringType) :=
  {f of isMultiplicative M S f}.

Module MMorphismExports.
Notation "{ 'mmorphism' M -> S }" := (@MMorphism.type M S) : type_scope.
#[deprecated(since="multinomials 2.2.0", note="Use MMorphism.clone instead.")]
Notation "[ 'mmorphism' 'of' f 'as' g ]" := (MMorphism.clone _ _ f g)
  (at level 0, only parsing) : form_scope.
#[deprecated(since="multinomials 2.2.0", note="Use MMorphism.clone instead.")]
Notation "[ 'mmorphism' 'of' f ]" := (MMorphism.clone _ _ f _)
  (at level 0, only parsing) : form_scope.
End MMorphismExports.
Export MMorphismExports.

(* -------------------------------------------------------------------- *)
Section MMorphismTheory.
Variables (M : monomType) (S : ringType) (f : {mmorphism M -> S}).

Lemma mmorph1 : f 1%M = 1.
Proof. exact: mmorphism_subproof.1. Qed.

Lemma mmorphM : {morph f : x y / (x * y)%M >-> (x * y)%R}.
Proof. exact: mmorphism_subproof.2. Qed.
End MMorphismTheory.

(* -------------------------------------------------------------------- *)
Section MalgDef.
Variable (K : choiceType) (G : zmodType).

Record malg : predArgType := Malg { malg_val : {fsfun K -> G with 0} }.

Fact malg_key : unit. Proof. by []. Qed.

Definition malg_of_fsfun   k := locked_with k Malg.
Canonical  malg_unlockable k := [unlockable fun malg_of_fsfun k].

HB.instance Definition _ := [isNew for @malg_val].
HB.instance Definition _ := [Choice of malg by <:].

End MalgDef.

(* -------------------------------------------------------------------- *)
Bind Scope ring_scope with malg.

Notation "{ 'malg' G [ K ] }" := (@malg K G) : type_scope.
Notation "{ 'malg' K }" := {malg int[K]} : type_scope.

(* -------------------------------------------------------------------- *)
Section MalgBaseOp.

Context {K : choiceType} {G : zmodType}.

Definition mcoeff (x : K) (g : {malg G[K]}) : G := malg_val g x.

Definition mkmalg : {fsfun K -> G with 0} -> {malg G[K]} := @Malg K G.

Definition mkmalgU (k : K) (x : G) := mkmalg [fsfun y => [fmap].[k <- x] y].

Definition msupp (g : {malg G[K]}) : {fset K} := finsupp (malg_val g).

End MalgBaseOp.

Arguments mcoeff  {K G} x%monom_scope g%ring_scope.
Arguments mkmalg  {K G} _.
Arguments mkmalgU {K G} k%monom_scope x%ring_scope.
Arguments msupp   {K G} g%ring_scope.

(* -------------------------------------------------------------------- *)
Notation "g @_ k" := (mcoeff k g).

Notation "[ 'malg' g ]" := (mkmalg g) : ring_scope.
Notation "[ 'malg' x 'in' aT => E ]" :=
  (mkmalg [fsfun x in aT => E]) : ring_scope.
Notation "[ 'malg' x => E ]" := (mkmalg [fsfun x => E]) : ring_scope.
Notation "<< z *g k >>" := (mkmalgU k z) : ring_scope.
Notation "<< k >>" := << 1 *g k >> : ring_scope.

Notation malgC := (mkmalgU 1).
Notation "@ 'malgC' K G" := (@mkmalgU K G 1)
  (at level 10, K at level 8, G at level 8, only parsing) : function_scope.
Notation "c %:MP" := (malgC c) : ring_scope.

(* -------------------------------------------------------------------- *)
Section MalgTheory.
Variable (K : choiceType) (G : zmodType).

Lemma mkmalgK (g : {fsfun K -> G with 0}) : malg_val (mkmalg g) = g.
Proof. by []. Qed.

Lemma malgP (g1 g2 : {malg G[K]}) : (forall k, g1@_k = g2@_k) <-> g1 = g2.
Proof.
by case: g1 g2 => [g1] [g2]; split=> [h|->//]; congr Malg; apply/fsfunP/h.
Qed.

Lemma mcoeff_fnd (g : {fmap K -> G}) k : [malg x => g x]@_k = odflt 0 g.[?k].
Proof. exact/fsfun_ffun. Qed.

Lemma mcoeffE (domf : {fset K}) (E : K -> G) k :
  [malg k in domf => E k]@_k = if k \in domf then E k else 0.
Proof. exact/fsfun_fun. Qed.

Lemma mcoeff_eq0 (g : {malg G[K]}) (k : K) : (g@_k == 0) = (k \notin msupp g).
Proof. by rewrite memNfinsupp. Qed.

Lemma mcoeff_neq0 (g : {malg G[K]}) (k : K) : (g@_k != 0) = (k \in msupp g).
Proof. by rewrite mcoeff_eq0 negbK. Qed.

Lemma mcoeff_outdom (g : {malg G[K]}) (k : K) : k \notin msupp g -> g@_k = 0.
Proof. exact: fsfun_dflt. Qed.

Variant msupp_spec (g : {malg G[K]}) (k : K) : bool -> G -> Type :=
| MsuppIn  (_ : k \in    msupp g) : msupp_spec g k true  g@_k
| MsuppOut (_ : k \notin msupp g) : msupp_spec g k false 0.

Lemma msuppP (g : {malg G[K]}) (k : K) : msupp_spec g k (k \in msupp g) g@_k.
Proof. by rewrite /mcoeff; case: finsuppP => h; constructor. Qed.
End MalgTheory.

(* -------------------------------------------------------------------- *)
Section MalgZMod.
Variable (K : choiceType) (G : zmodType).

Implicit Types (g : {malg G[K]}) (k : K).

Definition fgzero : {malg G[K]} := [malg x => [fmap] x].
Definition fgopp g := [malg k in msupp g => - g@_k].
Definition fgadd g1 g2 := [malg k in msupp g1 `|` msupp g2 => g1@_k + g2@_k].

Lemma fgzeroE k : fgzero@_k = 0.
Proof. by rewrite mcoeff_fnd !(in_fsetE, not_fnd). Qed.

Lemma fgoppE g k : (fgopp g)@_k = - g@_k.
Proof. by rewrite mcoeffE; case: msuppP; rewrite ?oppr0. Qed.

Lemma fgaddE g1 g2 k : (fgadd g1 g2)@_k = g1@_k + g2@_k.
Proof.
rewrite mcoeffE in_fsetE.
by case: (msuppP g1); case: (msuppP g2); rewrite ?addr0.
Qed.

Lemma fgaddA : associative fgadd.
Proof. by move=> x y z; apply/malgP=> k; rewrite !fgaddE addrA. Qed.

Lemma fgaddC : commutative fgadd.
Proof. by move=> x y; apply/malgP=> k; rewrite !fgaddE addrC. Qed.

Lemma fgadd0g : left_id fgzero fgadd.
Proof. by move=> x; apply/malgP=> k; rewrite fgaddE fgzeroE add0r. Qed.

Lemma fgaddg0 : right_id fgzero fgadd.
Proof. by move=> x; rewrite fgaddC fgadd0g. Qed.

Lemma fgaddNg : left_inverse fgzero fgopp fgadd.
Proof. by move=> x; apply/malgP=> k; rewrite !fgaddE fgzeroE fgoppE addNr. Qed.

Lemma fgaddgN : right_inverse fgzero fgopp fgadd.
Proof. by move=> x; rewrite fgaddC fgaddNg. Qed.

HB.instance Definition _ := GRing.isZmodule.Build (malg K G)
  fgaddA fgaddC fgadd0g fgaddNg.
HB.instance Definition _ := GRing.Zmodule.on {malg G[K]}.
End MalgZMod.

Section MAlgZModTheory.
Context {K : choiceType} {G : zmodType}.

Implicit Types (g : {malg G[K]}) (k : K) (x y : G).

Local Notation mcoeff  := (@mcoeff  K G) (only parsing).
Local Notation msupp   := (@msupp   K G).
Local Notation mkmalgU := (@mkmalgU K G) (only parsing).

Let fgE := (fgzeroE, fgoppE, fgaddE).

(* -------------------------------------------------------------------- *)
Lemma malgD_def g1 g2 : g1 + g2 = fgadd g1 g2.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeff_is_additive k: additive (mcoeff k).
Proof. by move=> g1 g2 /=; rewrite fgaddE fgoppE. (* !fgE *) Qed.

HB.instance Definition _ k := GRing.isAdditive.Build {malg G[K]} G (mcoeff k)
  (mcoeff_is_additive k).

Lemma mcoeff0   k   : 0@_k = 0 :> G                . Proof. exact: raddf0. Qed.
Lemma mcoeffN   k   : {morph mcoeff k: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mcoeffD   k   : {morph mcoeff k: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mcoeffB   k   : {morph mcoeff k: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mcoeffMn  k n : {morph mcoeff k: x / x *+ n} . Proof. exact: raddfMn. Qed.
Lemma mcoeffMNn k n : {morph mcoeff k: x / x *- n} . Proof. exact: raddfMNn. Qed.

Lemma mcoeffU k x k' : << x *g k >>@_k' = x *+ (k == k').
Proof. by rewrite mcoeff_fnd fnd_set fnd_fmap0; case: eqVneq. Qed.

Lemma mcoeffUU k x : << x *g k >>@_k = x.
Proof. by rewrite mcoeffU eqxx. Qed.

Let mcoeffsE := (mcoeff0, mcoeffU, mcoeffB, mcoeffD, mcoeffN, mcoeffMn).

(* -------------------------------------------------------------------- *)
Lemma msupp0 : msupp 0 = fset0 :> {fset K}.
Proof.
apply/fsetP=> k; rewrite in_fset0; apply/negbTE.
by rewrite -mcoeff_eq0 mcoeff0.
Qed.

Lemma msuppU k x : msupp << x *g k >> = if x == 0 then fset0 else [fset k].
Proof.
apply/fsetP=> k'; rewrite -mcoeff_neq0 mcoeffU 2!fun_if !inE.
by have [//|_] := eqVneq k k'; rewrite eqxx if_same.
Qed.

Lemma msuppU_le {k x} : msupp << x *g k >> `<=` [fset k].
Proof. by rewrite msuppU; case: eqP. Qed.

Lemma msuppN g : msupp (-g) = msupp g.
Proof. by apply/fsetP=> k; rewrite -!mcoeff_neq0 mcoeffN oppr_eq0. Qed.

Lemma msuppD_le g1 g2 : msupp (g1 + g2) `<=` msupp g1 `|` msupp g2.
Proof.
apply/fsubsetP=> k; rewrite in_fsetU -mcoeff_neq0 mcoeffD.
by case: (msuppP g1); case: (msuppP g2); rewrite //= addr0 eqxx.
Qed.

Lemma msuppB_le g1 g2 : msupp (g1 - g2) `<=` msupp g1 `|` msupp g2.
Proof. by rewrite -[msupp g2]msuppN; apply/msuppD_le. Qed.

Lemma msuppD g1 g2 : [disjoint msupp g1 & msupp g2] ->
  msupp (g1 + g2) = msupp g1 `|` msupp g2.
Proof.
move=> dj_g1g2; apply/fsetP=> k; move/fdisjointP/(_ k): dj_g1g2.
rewrite in_fsetU -!mcoeff_neq0 mcoeffD negbK.
have [->|] //= := eqVneq (g1@_k) 0; first by rewrite add0r.
by move=> + /(_ isT) /eqP ->; rewrite addr0.
Qed.

Lemma msuppB g1 g2 : [disjoint msupp g1 & msupp g2] ->
  msupp (g1 - g2) = msupp g1 `|` msupp g2.
Proof. by move=> dj_g1g2; rewrite msuppD msuppN. Qed.

Lemma msuppMn_le g n : msupp (g *+ n) `<=` msupp g.
Proof.
apply/fsubsetP=> k; rewrite -!mcoeff_neq0 mcoeffMn.
by apply/contra_neq => ->; rewrite mul0rn.
Qed.

Lemma msuppMNm_le g n : msupp (g *- n) `<=` msupp g.
Proof. by rewrite msuppN msuppMn_le. Qed.

(* -------------------------------------------------------------------- *)
Lemma monalgU_is_additive k : additive (mkmalgU k).
Proof. by move=> x1 x2 /=; apply/malgP=> k'; rewrite !mcoeffsE mulrnBl. Qed.

HB.instance Definition _ k := GRing.isAdditive.Build G {malg G[K]} (mkmalgU k)
  (monalgU_is_additive k).

Lemma monalgU0   k   : << (0 : G) *g k >> = 0        . Proof. exact: raddf0. Qed.
Lemma monalgUN   k   : {morph mkmalgU k: x / - x}    . Proof. exact: raddfN. Qed.
Lemma monalgUD   k   : {morph mkmalgU k: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma monalgUB   k   : {morph mkmalgU k: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma monalgUMn  k n : {morph mkmalgU k: x / x *+ n} . Proof. exact: raddfMn. Qed.
Lemma monalgUMNn k n : {morph mkmalgU k: x / x *- n} . Proof. exact: raddfMNn. Qed.

Lemma monalgU_eq0 x k: (<< x *g k >> == 0) = (x == 0).
Proof.
apply/eqP/eqP => [/(congr1 (mcoeff k))|->]; last by rewrite monalgU0.
by rewrite !mcoeffsE eqxx.
Qed.

Definition monalgUE :=
  (monalgU0, monalgUB, monalgUD, monalgUN, monalgUMn).

(* -------------------------------------------------------------------- *)
Lemma monalgEw (g : {malg G[K]}) (domg : {fset K}) : msupp g `<=` domg ->
  g = \sum_(k <- domg) << g@_k *g k >>.
Proof.
move/fsubsetP=> le_gd; apply/malgP=> k; have [/le_gd kg|k_notin_g] := msuppP.
  rewrite raddf_sum (big_fsetD1 k) //= mcoeffUU big1_fset ?addr0 // => k'.
  by rewrite in_fsetD1 mcoeffU; case: eqP.
rewrite raddf_sum /= big1_fset // => k' _ _.
by rewrite mcoeffU; case: eqP k_notin_g => // <- /mcoeff_outdom ->.
Qed.

Lemma monalgE (g : {malg G[K]}) : g = \sum_(k <- msupp g) << g@_k *g k >>.
Proof. exact/monalgEw. Qed.
End MAlgZModTheory.

(* -------------------------------------------------------------------- *)
Section MalgMonomTheory.
Context {K : monomType} {G : zmodType}.

(* -------------------------------------------------------------------- *)
Lemma msuppC (c : G) :
  msupp c%:MP = (if c == 0 then fset0 else [fset 1%M]) :> {fset K}.
Proof. exact/msuppU. Qed.

Lemma msuppC_le (c : G) : msupp c%:MP `<=` ([fset 1%M] : {fset K}).
Proof. by rewrite msuppC; case: eqP=> _; rewrite ?fsubset_refl // fsub0set. Qed.

Lemma mcoeffC (c : G) k : c%:MP@_k = c *+ (k == 1%M :> K).
Proof. by rewrite mcoeffU eq_sym. Qed.

Lemma mcoeffC0 (k : K) : 0%:MP@_k = 0 :> G.
Proof. by rewrite mcoeffC mul0rn. Qed.

Lemma msuppC0 : msupp (0 : G)%:MP = fset0 :> {fset K}.
Proof. by rewrite msuppC eqxx. Qed.

Lemma malgC0E : 0%:MP = 0 :> {malg G[K]}.
Proof. by apply/malgP=> k; rewrite mcoeffC0 mcoeff0. Qed.

Lemma malgCK : cancel malgC (@mcoeff K G 1%M).
Proof. by move=> c; rewrite mcoeffC eqxx mulr1n. Qed.

Lemma malgC_eq (c1 c2 : G) : (c1%:MP == c2%:MP :> {malg G[K]}) = (c1 == c2).
Proof. by apply/eqP/eqP=> [|->//] /malgP/(_ 1%M); rewrite !mcoeffU eqxx. Qed.

Lemma msupp_eq0 (g : {malg G[K]}) : (msupp g == fset0) = (g == 0).
Proof.
apply/eqP/eqP=> [/fsetP z_g|->]; last exact: msupp0.
by apply/malgP=> i; rewrite mcoeff0 mcoeff_outdom // z_g.
Qed.
End MalgMonomTheory.

(* -------------------------------------------------------------------- *)
Section MAlgLMod.
Context (K : choiceType) (R : ringType).

Definition fgscale c g : {malg R[K]} := \sum_(k <- msupp g) << c * g@_k *g k >>.

Local Notation "c *:g g" := (fgscale c g) (at level 40, left associativity).

Lemma fgscaleE c g k : (c *:g g)@_k = c * g@_k.
Proof.
rewrite {2}[g]monalgE !raddf_sum mulr_sumr.
by apply/eq_bigr=> /= i _; rewrite !mcoeffU mulrnAr.
Qed.

Lemma fgscaleA c1 c2 g : c1 *:g (c2 *:g g) = (c1 * c2) *:g g.
Proof. by apply/malgP=> x; rewrite !fgscaleE mulrA. Qed.

Lemma fgscale1r D: 1 *:g D = D.
Proof. by apply/malgP=> k; rewrite !fgscaleE mul1r. Qed.

Lemma fgscaleDr c g1 g2 : c *:g (g1 + g2) = c *:g g1 + c *:g g2.
Proof. by apply/malgP=> k; rewrite !(mcoeffD, fgscaleE) mulrDr. Qed.

Lemma fgscaleDl g c1 c2: (c1 + c2) *:g g = c1 *:g g + c2 *:g g.
Proof. by apply/malgP=> x; rewrite !(mcoeffD, fgscaleE) mulrDl. Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R (malg K R)
  fgscaleA fgscale1r fgscaleDr fgscaleDl.
HB.instance Definition _ := GRing.Lmodule.on {malg R[K]}.
End MAlgLMod.

(* -------------------------------------------------------------------- *)
Section MAlgLModTheory.
Context {K : choiceType} {R : ringType}.

Implicit Types (g : {malg R[K]}).

Lemma malgZ_def c g : c *: g = fgscale c g.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeffZ c g k : (c *: g)@_k = c * g@_k.
Proof. exact/fgscaleE. Qed.

(* FIXME: make the production of a LRMorphism fail below *)
(* HB.instance Definition _ m := *)
(*   GRing.isLinear.Build R [lmodType R of {malg R[K]}] R *%R (mcoeff m) *)
(*     (fun c g => mcoeffZ c g m). *)

(* -------------------------------------------------------------------- *)
Lemma msuppZ_le c g : msupp (c *: g) `<=` msupp g.
Proof.
apply/fsubsetP=> k; rewrite -!mcoeff_neq0 mcoeffZ.
by apply/contraTneq=> ->; rewrite mulr0 negbK.
Qed.
End MAlgLModTheory.

(* -------------------------------------------------------------------- *)
Section MAlgLModTheoryIntegralDomain.
Context {K : choiceType} {R : idomainType}.

Implicit Types (g : {malg R[K]}).

(* -------------------------------------------------------------------- *)
Lemma msuppZ c g : msupp (c *: g) = if c == 0 then fset0 else msupp g.
Proof.
case: eqP=> [->|/eqP nz_c]; first by rewrite scale0r msupp0.
by apply/fsetP=> k; rewrite -!mcoeff_neq0 mcoeffZ mulf_eq0 negb_or nz_c.
Qed.
End MAlgLModTheoryIntegralDomain.

(* -------------------------------------------------------------------- *)
Definition mcoeffsE :=
  (@mcoeff0, @mcoeffUU, @mcoeffU, @mcoeffB, @mcoeffD,
   @mcoeffN, @mcoeffMn, @mcoeffZ).

(* -------------------------------------------------------------------- *)
Section MAlgRingType.
Context (K : monomType) (R : ringType).

Implicit Types (g : {malg R[K]}) (k l : K).

Definition fgone : {malg R[K]} := << 1%M >>.

Local Notation "g1 *M_[ k1 , k2 ] g2" :=
  << g1@_k1%M * g2@_k2%M *g (k1 * k2)%M >>
  (at level 40, no associativity, format "g1  *M_[ k1 ,  k2 ]  g2").

Local Notation "g1 *gM_[ k2 ] g2" :=
  (\sum_(k1 <- msupp g1) g1 *M_[k1, k2] g2)
  (at level 40, no associativity, only parsing).

Local Notation "g1 *Mg_[ k1 ] g2" :=
  (\sum_(k2 <- msupp g2) g1 *M_[k1, k2] g2)
  (at level 40, no associativity, only parsing).

Definition fgmul g1 g2 : {malg R[K]} :=
  \sum_(k1 <- msupp g1) \sum_(k2 <- msupp g2) g1 *M_[k1, k2] g2.

Lemma fgmull g1 g2 :
  fgmul g1 g2 = \sum_(k1 <- msupp g1) \sum_(k2 <- msupp g2) g1 *M_[k1, k2] g2.
Proof. by []. Qed.

Lemma fgmulr g1 g2 :
  fgmul g1 g2 = \sum_(k2 <- msupp g2) \sum_(k1 <- msupp g1) g1 *M_[k1, k2] g2.
Proof. by rewrite fgmull exchange_big. Qed.

(* big_fset_incl has (op : com_law idx) as first non automatic argument *)
Lemma fgmullw (d1 d2 : {fset K}) g1 g2 :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 ->
  fgmul g1 g2 = \sum_(k1 <- d1) \sum_(k2 <- d2) g1 *M_[k1, k2] g2.
Proof.
move=> le_d1 le_d2; rewrite fgmull (big_fset_incl _ le_d1) /=.
  apply/eq_bigr=> k1 _; apply/big_fset_incl => // k _ /mcoeff_outdom ->.
  by rewrite mulr0 monalgU0.
move=> k _ /mcoeff_outdom g1k.
by rewrite big1 => // k' _; rewrite g1k mul0r monalgU0.
Qed.

Lemma fgmulrw (d1 d2 : {fset K}) g1 g2 : msupp g1 `<=` d1 -> msupp g2 `<=` d2
  -> fgmul g1 g2 = \sum_(k2 <- d2) \sum_(k1 <- d1) g1 *M_[k1, k2] g2.
Proof. by move=> le_d1 le_d2; rewrite (fgmullw le_d1 le_d2) exchange_big. Qed.

Definition fgmullwl (d1 : {fset K}) {g1 g2} (le : msupp g1 `<=` d1) :=
  @fgmullw _ _ g1 g2 le (fsubset_refl _).

Definition fgmulrwl (d2 : {fset K}) {g1 g2} (le : msupp g2 `<=` d2) :=
  @fgmulrw _ _ g1 g2 (fsubset_refl _) le.

Lemma fgmul0g : left_zero 0 fgmul.
Proof. by move=> g; rewrite fgmull msupp0 big_seq_fset0. Qed.

Lemma fgmulg0 : right_zero 0 fgmul.
Proof. by move=> g; rewrite fgmulr msupp0 big_seq_fset0. Qed.

Lemma fgmulUg c k g :
  fgmul << c *g k >> g = \sum_(k' <- msupp g) << c * g@_k' *g k * k' >>.
Proof.
rewrite (fgmullw msuppU_le (fsubset_refl _)) big_seq_fset1.
by apply/eq_bigr => k' _; rewrite mcoeffUU.
Qed.

Lemma fgmulgU c k g :
  fgmul g << c *g k >> = \sum_(k' <- msupp g) << g@_k' * c *g k' * k >>.
Proof.
rewrite (fgmulrw (fsubset_refl _) msuppU_le) big_seq_fset1.
by apply/eq_bigr=> k' _; rewrite mcoeffUU.
Qed.

Lemma fgmulUU c1 c2 k1 k2 :
  fgmul << c1 *g k1 >> << c2 *g k2 >> = << c1 * c2 *g k1 * k2 >>.
Proof. by rewrite (fgmulrw msuppU_le msuppU_le) !big_seq_fset1 !mcoeffUU. Qed.

Lemma fgmulEl1 g1 g2 :
  fgmul g1 g2 = \sum_(k1 <- msupp g1) fgmul << g1@_k1 *g k1 >> g2.
Proof. by apply/eq_bigr=> k _; rewrite fgmulUg. Qed.

Lemma fgmulEr1 g1 g2 :
  fgmul g1 g2 = \sum_(k2 <- msupp g2) fgmul g1 << g2@_k2 *g k2 >>.
Proof. by rewrite fgmulr; apply/eq_bigr=> k _; rewrite fgmulgU. Qed.

Lemma fgmul1g : left_id fgone fgmul.
Proof.
move=> g; rewrite fgmulUg [RHS]monalgE.
by apply/eq_bigr=> kg _; rewrite mul1r mul1m.
Qed.

Lemma fgmulg1 : right_id fgone fgmul.
Proof.
move=> g; rewrite fgmulgU [RHS]monalgE.
by apply/eq_bigr=> k _; rewrite mulr1 mulm1.
Qed.


Lemma fgmulgDl : left_distributive fgmul +%R.
Proof.
move=> g1 g2 g; rewrite [in RHS](fgmullwl (fsubsetUl _ (msupp g2))).
rewrite [in RHS](fgmullwl (fsubsetUr (msupp g1) _)) (fgmullwl (msuppD_le _ _)).
rewrite -big_split /=; apply/eq_bigr=> k1 _.
rewrite -big_split /=; apply/eq_bigr=> k2 _.
by rewrite mcoeffD mulrDl monalgUD.
Qed.

Lemma fgmulgDr : right_distributive fgmul +%R.
Proof.
move=> g g1 g2; rewrite [in RHS](fgmulrwl (fsubsetUl _ (msupp g2))).
rewrite [in RHS](fgmulrwl (fsubsetUr (msupp g1) _)) (fgmulrwl (msuppD_le _ _)).
rewrite -big_split /=; apply/eq_bigr => k1 _.
rewrite -big_split /=; apply/eq_bigr => k2 _.
by rewrite mcoeffD mulrDr monalgUD.
Qed.

Lemma fgmulA : associative fgmul.
Proof.
move=> g1 g2 g3.
rewrite [RHS](big_morph (fgmul^~ _) (fun _ _ => fgmulgDl _ _ _) (fgmul0g _)).
rewrite fgmulEl1; apply/eq_bigr=> k1 _.
rewrite [LHS](big_morph (fgmul _) (fun _ _ => fgmulgDr _ _ _) (fgmulg0 _)).
rewrite [RHS](big_morph (fgmul^~ _) (fun _ _ => fgmulgDl _ _ _) (fgmul0g _)).
apply/eq_bigr=> k2 _.
rewrite [LHS](big_morph (fgmul _) (fun _ _ => fgmulgDr _ _ _) (fgmulg0 _)).
by rewrite fgmulEr1; apply/eq_bigr=> k3 _; rewrite !fgmulUU mulrA mulmA.
Qed.

Lemma fgoner_eq0 : fgone != 0.
Proof. by apply/eqP/malgP=> /(_ 1%M) /eqP; rewrite !mcoeffsE oner_eq0. Qed.

HB.instance Definition _ := GRing.Zmodule_isRing.Build (malg K R)
  fgmulA fgmul1g fgmulg1 fgmulgDl fgmulgDr fgoner_eq0.
HB.instance Definition _ := GRing.Ring.on {malg R[K]}.

End MAlgRingType.

(* -------------------------------------------------------------------- *)
Section MAlgRingTheory.
Context (K : monomType) (R : ringType).

Implicit Types (g : {malg R[K]}) (k l : K).

Lemma malgM_def g1 g2 : g1 * g2 = fgmul g1 g2.
Proof. by []. Qed.

Lemma mcoeffU1 k k' : (<< k >> : {malg R[K]})@_k' = (k == k')%:R.
Proof. by rewrite mcoeffU. Qed.

Lemma msuppU1 k : @msupp _ R << k >> = [fset k].
Proof. by rewrite msuppU oner_eq0. Qed.

Lemma malgME g1 g2 :
  g1 * g2 = \sum_(k1 <- msupp g1) \sum_(k2 <- msupp g2)
    << g1@_k1 * g2@_k2 *g k1 * k2 >>.
Proof. by []. Qed.

Lemma malgMEw (d1 d2 : {fset K}) g1 g2 :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 ->
  g1 * g2 = \sum_(k1 <- d1) \sum_(k2 <- d2) << g1@_k1 * g2@_k2 *g k1 * k2 >>.
Proof. exact/fgmullw. Qed.

Lemma mcoeffMlw (d1 d2 : {fset K}) g1 g2 k :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 ->
  (g1 * g2)@_k = \sum_(k1 <- d1) \sum_(k2 <- d2)
    (g1@_k1 * g2@_k2) *+ (k1 * k2 == k)%M.
Proof.
move=> le1 le2; rewrite (malgMEw le1 le2) raddf_sum /=.
apply/eq_bigr=> k1 _; rewrite raddf_sum /=; apply/eq_bigr=> k2 _.
by rewrite mcoeffsE.
Qed.

Lemma mcoeffMrw (d1 d2 : {fset K}) g1 g2 k :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 ->
  (g1 * g2)@_k = \sum_(k2 <- d2) \sum_(k1 <- d1)
    (g1@_k1 * g2@_k2) *+ (k1 * k2 == k)%M.
Proof. by move=> le1 le2; rewrite (mcoeffMlw _ le1 le2) exchange_big. Qed.

Lemma mcoeffMl g1 g2 k :
  (g1 * g2)@_k = \sum_(k1 <- msupp g1) \sum_(k2 <- msupp g2)
    (g1@_k1 * g2@_k2) *+ (k1 * k2 == k)%M.
Proof. exact: mcoeffMlw. Qed.

Lemma mcoeffMr g1 g2 k :
  (g1 * g2)@_k = \sum_(k2 <- msupp g2) \sum_(k1 <- msupp g1)
    (g1@_k1 * g2@_k2) *+ (k1 * k2 == k)%M.
Proof. exact: mcoeffMrw. Qed.

Lemma mcoeff1 k : 1@_k = (k == 1%M)%:R :> R.
Proof. by rewrite mcoeffC. Qed.

Lemma mul_malgC c g : c%:MP * g = c *: g.
Proof.
by rewrite malgM_def malgZ_def fgmulUg; apply/eq_bigr=> /= k _; rewrite mul1m.
Qed.

Lemma mcoeffCM c g k : (c%:MP * g)@_k = c * g@_k :> R.
Proof. by rewrite mul_malgC mcoeffZ. Qed.

Lemma msuppM_le_finType g1 g2 k :
  k \in msupp (g1 * g2) ->
        exists (k1 : msupp g1) (k2 : msupp g2), k = (val k1 * val k2)%M.
Proof.
move=> k_in_g1Mg2; apply/(existsPP (fun _ => exists_eqP)).
apply/contraLR: k_in_g1Mg2=> hk; rewrite -mcoeff_eq0.
rewrite mcoeffMl big_seq big1 // => /= k1 Hk1.
rewrite big_seq big1 // => k2 Hk2.
case: eqP=> // kE; case/negP: hk.
by apply/existsP; exists [` Hk1]; apply/existsP; exists [` Hk2]; rewrite kE.
Qed.

Lemma msuppM_le g1 g2 k :
  k \in msupp (g1 * g2) ->
    exists k1 k2, [/\ k1 \in msupp g1, k2 \in msupp g2 & k = (k1 * k2)%M].
Proof.
move/msuppM_le_finType => [] [k1 Hk1] [] [k2 Hk2] /= Hk.
by exists k1; exists k2.
Qed.

(* Alternative equivalent statement *)
Lemma msuppM_incl g1 g2 :
  msupp (g1 * g2) `<=` [fset (k1 * k2)%M | k1 in msupp g1, k2 in msupp g2].
Proof.
apply/fsubsetP => k /msuppM_le [k1 [k2 [k1g1 k2g2 ->]]].
by apply/imfset2P; exists k1; last exists k2.
Qed.

Lemma malgC_is_multiplicative : multiplicative (@malgC K R).
Proof.
by split=> // g1 g2; apply/malgP=> k; rewrite mcoeffCM !mcoeffC mulrnAr.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build R {malg R[K]} (@malgC K R)
    malgC_is_multiplicative.

Lemma mpolyC1E : 1%:MP = 1 :> {malg R[K]}.
Proof. exact: rmorph1. Qed.

Lemma mpolyC_nat (n : nat) : (n%:R)%:MP = n%:R :> {malg R[K]}.
Proof. by apply/malgP=> i; rewrite mcoeffC mcoeffMn mcoeffC mulrnAC. Qed.

Lemma mpolyCM : {morph @malgC K R : p q / p * q}.
Proof. exact: rmorphM. Qed.

Lemma mcoeff1g_is_multiplicative :
  multiplicative (mcoeff 1%M : {malg R[K]} -> R).
Proof.
split=> [g1 g2|]; rewrite ?malgCK //; pose_big_fset K E.
have E1: 1%M \in E by rewrite -fsub1set.
rewrite (@malgMEw E E) // (big_fsetD1 1%M) //=. 2: by close.
rewrite (big_fsetD1 1%M) //= mulm1 2!mcoeffD mcoeffUU.
rewrite ![\sum_(i <- E `\ 1%M) _]big_seq.
rewrite !raddf_sum !big1 ?addr0 //= => k; rewrite in_fsetD1 => /andP [ne1_k _].
  rewrite raddf_sum big1 ?mcoeff0 //= => k'; rewrite mcoeffU.
  by case: eqP=> // /eqP /unitmP []; rewrite (negbTE ne1_k).
by rewrite mcoeffU mul1m (negbTE ne1_k).
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {malg R[K]} R (@mcoeff K R 1%M)
    mcoeff1g_is_multiplicative.

(* FIXME: building Linear instance here so as to not trigger the creation
   of a LRMorphism that fails on above command (but is built just below anyway) *)
HB.instance Definition _ m :=
  GRing.isScalable.Build R {malg R[K]} R *%R (mcoeff m)
    (fun c => (mcoeffZ c)^~ m).

Lemma fgscaleAl c g1 g2 : c *: (g1 * g2) = (c *: g1) * g2.
Proof. by rewrite -!mul_malgC mulrA. Qed.

HB.instance Definition _ := GRing.Lmodule_isLalgebra.Build R (malg K R)
  fgscaleAl.
HB.instance Definition _ := GRing.Lalgebra.on {malg R[K]}.

End MAlgRingTheory.

(* -------------------------------------------------------------------- *)
Section MalgComRingType.
Context (K : conomType) (R : comRingType).

Lemma fgmulC : @commutative {malg R[K]} _ *%R.
Proof.
move=> g1 g2; apply/malgP=> k; rewrite mcoeffMl mcoeffMr.
apply/eq_bigr=> /= k1 _; apply/eq_bigr=> /= k2 _.
by rewrite mulrC [X in X==k]mulmC.
Qed.

HB.instance Definition _ := GRing.Ring_hasCommutativeMul.Build (malg K R)
  fgmulC.

HB.instance Definition _ := GRing.Lalgebra_isComAlgebra.Build R (malg K R).

HB.instance Definition _ := GRing.ComAlgebra.on {malg R[K]}.

End MalgComRingType.

(* -------------------------------------------------------------------- *)
Section MalgMorphism.
Section Defs.
Context (K : choiceType) (G : zmodType) (S : ringType).
Context (f : G -> S) (h : K -> S).

Definition mmap g := \sum_(k <- msupp g) f g@_k * h k.

Lemma mmapE g : mmap g = \sum_(k <- msupp g) f g@_k * h k.
Proof. by []. Qed.
End Defs.

Local Notation "g ^[ f , h ]" := (mmap f h g).

Section BaseTheory.
Context (K : choiceType) (G : zmodType) (S : ringType).
Context {f : {additive G -> S}} {h : K -> S}.

Lemma mmapEw (d : {fset K}) g : msupp g `<=` d ->
  g^[f, h] = \sum_(k <- d) f g@_k * h k.
Proof.
move=> le; rewrite [LHS](big_fset_incl _ le) => //= x xd /mcoeff_outdom ->.
by rewrite raddf0 mul0r.
Qed.

Lemma mmapU (c : G) (m : K) : mmap f h << c *g m >> = f c * h m.
Proof. by rewrite (mmapEw msuppU_le) big_seq_fset1 mcoeffUU. Qed.
End BaseTheory.

Section Additive.
Context (K : choiceType) (G : zmodType) (S : ringType).
Context {f : {additive G -> S}} {h : K -> S}.

Lemma mmap_is_additive : additive (mmap f h).
Proof.
move=> g1 g2 /=; pose_big_fset K E; rewrite 3?(mmapEw (d := E)) //.
  by rewrite -sumrB; apply/eq_bigr=> k _; rewrite !raddfB /= mulrBl.
by close.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build {malg G[K]} S (mmap f h)
  mmap_is_additive.

Local Notation mmap := (mmap f h).

Lemma mmap0     : mmap 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mmapN     : {morph mmap: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mmapD     : {morph mmap: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mmapB     : {morph mmap: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mmapMn  n : {morph mmap: x / x *+ n} . Proof. exact: raddfMn. Qed.
Lemma mmapMNn n : {morph mmap: x / x *- n} . Proof. exact: raddfMNn. Qed.
End Additive.

Section CommrMultiplicative.
Context (K : monomType) (R : ringType) (S : ringType).
Context {f : {rmorphism R -> S}} {h : {mmorphism K -> S}}.

Implicit Types (g : {malg R[K]}).

Lemma mmapZ c g : (c *: g)^[f,h] = f c * g^[f,h].
Proof.
rewrite (mmapEw (msuppZ_le _ _)) mmapE big_distrr /=.
by apply/eq_bigr=> k _; rewrite linearZ rmorphM /= mulrA.
Qed.

Lemma mmapC c : c%:MP^[f,h] = f c.
Proof. by rewrite mmapU mmorph1 mulr1. Qed.

Lemma mmap1 : 1^[f,h] = 1.
Proof. by rewrite mmapC rmorph1. Qed.

Hypothesis commr_f: forall g m m', GRing.comm (f g@_m) (h m').

Lemma commr_mmap_is_multiplicative: multiplicative (mmap f h).
Proof.
split => [g1 g2|]; last by rewrite mmap1.
rewrite malgME raddf_sum mulr_suml /=; apply: eq_bigr=> i _.
rewrite raddf_sum mulr_sumr /=; apply: eq_bigr=> j _.
by rewrite mmapU /= rmorphM mmorphM -mulrA [X in _*X=_]mulrA commr_f !mulrA.
Qed.
End CommrMultiplicative.

(* -------------------------------------------------------------------- *)
Section Multiplicative.
Context (K : monomType) (R : ringType) (S : comRingType).
Context {f : {rmorphism R -> S}} {h : {mmorphism K -> S}}.

Implicit Types (g : {malg R[K]}).

Lemma mmap_is_multiplicative : multiplicative (mmap f h).
Proof. by apply/commr_mmap_is_multiplicative=> g m m'; apply/mulrC. Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build {malg R[K]} S (mmap f h)
    mmap_is_multiplicative.
End Multiplicative.

(* -------------------------------------------------------------------- *)
Section Linear.
Context (K : monomType) (R : comRingType) {h : {mmorphism K -> R}}.

Lemma mmap_is_linear : scalable_for *%R (mmap idfun h).
Proof. by move=> /= c g; rewrite -mul_malgC rmorphM /= mmapC. Qed.

HB.instance Definition _ :=
  GRing.isScalable.Build R {malg R[K]} R *%R (mmap idfun h)
    mmap_is_linear.

End Linear.
End MalgMorphism.

(* -------------------------------------------------------------------- *)
Section MonalgOver.
Section Def.
Context {K : choiceType} {G : zmodType}.

Definition monalgOver_pred (S : {pred G}) :=
  fun g : {malg G[K]} => all (fun m => g@_m \in S) (msupp g).
Definition monalgOver (S : {pred G}) := [qualify a g| monalgOver_pred S g].
End Def.
Arguments monalgOver_pred _ _ _ _ /.

(* -------------------------------------------------------------------- *)
Section Theory.
Context (K : choiceType) (G : zmodType).

Local Notation monalgOver := (@monalgOver K G).

Lemma monalgOverS (S1 S2 : {pred G}) :
  {subset S1 <= S2} -> {subset monalgOver S1 <= monalgOver S2}.
Proof.
move=> le_S1S2 g /allP /= S1g; apply/allP => /= x Hx.
exact/le_S1S2/S1g.
Qed.

Lemma monalgOverU c k S :
  << c *g k >> \in monalgOver S = (c == 0) || (c \in S).
Proof.
rewrite qualifE /= msuppU; have [->|nz_c] //= := eqVneq c 0.
apply/allP/idP => [h|h x]; last by rewrite in_fset1=> /eqP->; rewrite mcoeffUU.
by move: (h k); rewrite mcoeffUU in_fset1 eqxx; apply.
Qed.

Lemma monalgOver0 S: 0 \is a monalgOver S.
Proof. by rewrite qualifE /= msupp0; apply/allP. Qed.

End Theory.

(* -------------------------------------------------------------------- *)
Section MonalgOverAdd.
Context (K : choiceType) (G : zmodType) (S : addrClosed G).

Implicit Types (g : {malg G[K]}).

Local Notation monalgOver := (@monalgOver K G).

Lemma monalgOverP {g} : reflect (forall m, g@_m \in S) (g \in monalgOver S).
Proof.
apply: (iffP allP)=> /= h k; last by rewrite h.
by case: msuppP=> [kg|]; rewrite ?rpred0 // (h k).
Qed.

Lemma monalgOver_addr_closed : addr_closed (monalgOver S).
Proof.
split=> [|g1 g2 Sg1 Sg2]; rewrite ?monalgOver0 //.
by apply/monalgOverP=> m; rewrite mcoeffD rpredD ?(monalgOverP _).
Qed.

HB.instance Definition _ := GRing.isAddClosed.Build _ (monalgOver_pred S)
  monalgOver_addr_closed.
End MonalgOverAdd.

(* -------------------------------------------------------------------- *)
Section MonalgOverOpp.
Context (K : choiceType) (G : zmodType) (zmodS : zmodClosed G).

Local Notation monalgOver := (@monalgOver K G).

Lemma monalgOver_oppr_closed : oppr_closed (monalgOver zmodS).
Proof.
move=> g Sg; apply/monalgOverP=> n; rewrite mcoeffN.
by rewrite rpredN; apply/(monalgOverP zmodS).
Qed.

HB.instance Definition _ := GRing.isOppClosed.Build _ (monalgOver_pred zmodS)
  monalgOver_oppr_closed.
End MonalgOverOpp.

(* -------------------------------------------------------------------- *)
Section MonalgOverSemiring.
Context (K : monomType) (R : ringType) (S : semiringClosed R).

Local Notation monalgOver := (@monalgOver K R).

Lemma monalgOverC c : (c%:MP \in monalgOver S) = (c \in S).
Proof. by rewrite monalgOverU; case: eqP=> // ->; rewrite rpred0. Qed.

Lemma monalgOver1 : 1 \in monalgOver S.
Proof. by rewrite monalgOverC rpred1. Qed.

Lemma monalgOver_mulr_closed : mulr_closed (monalgOver S).
Proof.
split=> [|g1 g2 /monalgOverP Sg1 /monalgOverP sS2].
  by rewrite monalgOver1.
apply/monalgOverP=> m; rewrite mcoeffMl rpred_sum //=.
move=> k1 _; rewrite rpred_sum // => k2 _.
by case: eqP; rewrite ?mulr0n (rpred0, rpredM).
Qed.

HB.instance Definition _ := GRing.isMulClosed.Build _ (monalgOver_pred S)
  monalgOver_mulr_closed.

Lemma monalgOverZ :
  {in S & monalgOver S, forall c g, c *: g \is a monalgOver S}.
Proof.
move=> c g Sc Sg; apply/monalgOverP=> k.
by rewrite mcoeffZ rpredM //; apply/(monalgOverP S).
Qed.

Lemma rpred_meval :
  {in monalgOver S, forall g (v : K -> R),
     (forall x, v x \in S) -> mmap idfun v g \in S}.
Proof.
move=> g /monalgOverP Sg v Sv; rewrite mmapE rpred_sum //.
by move=> /= k; rewrite rpredM.
Qed.
End MonalgOverSemiring.

Section MonalgOverRing.
Context (K : monomType) (R : ringType) (ringS : subringClosed R).

HB.instance Definition _ := GRing.isMulClosed.Build _ (monalgOver_pred ringS)
  (monalgOver_mulr_closed K ringS).
End MonalgOverRing.
End MonalgOver.
Arguments monalgOver_pred _ _ _ _ /.

(* -------------------------------------------------------------------- *)
HB.mixin Record isMeasure (M : monomType) (mf : M -> nat) := {
  mf0 : mf 1%M = 0%N;
  mfM : {morph mf : m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N};
  mf_eq0I : forall m, mf m = 0%N -> m = 1%M
}.

#[short(type="measure")]
HB.structure Definition Measure (M : monomType) := {mf of isMeasure M mf}.

Notation "[ 'measure' 'of' f ]" := (Measure.clone _ f _)
  (at level 0, only parsing) : form_scope.

(* -------------------------------------------------------------------- *)
Section MMeasure.
Context (M : monomType) (G : zmodType) (mf : measure M).

Implicit Types (g : {malg G[M]}).

Lemma mf_eq0 m : (mf m == 0%N) = (m == 1%M).
Proof. by apply/eqP/eqP=> [|->]; rewrite ?mf0 // => /mf_eq0I. Qed.

Definition mmeasure g := (\max_(m <- msupp g) (mf m).+1)%N.

Lemma mmeasureE g : mmeasure g = (\max_(m <- msupp g) (mf m).+1)%N.
Proof. by []. Qed.

Lemma mmeasure0 : mmeasure 0 = 0%N.
Proof. by rewrite mmeasureE msupp0 big_seq_fset0. Qed.

Lemma mmeasure_mnm_lt g m : m \in msupp g -> (mf m < mmeasure g)%N.
Proof.
move=> km; rewrite mmeasureE (big_fsetD1 m) //=.
by rewrite leq_max ltnS leqnn.
Qed.

Lemma mmeasure_mnm_ge g m : (mmeasure g <= mf m)%N -> m \notin msupp g.
Proof. by apply/contraTN=> /mmeasure_mnm_lt; rewrite leqNgt ltnS. Qed.

Lemma mmeasureC c : mmeasure c%:MP = (c != 0%R) :> nat.
Proof.
rewrite mmeasureE msuppC; case: (_ == 0)=> /=.
by rewrite big_nil. by rewrite big_seq_fset1 mf0.
Qed.

Lemma mmeasureN g : mmeasure (-g) = mmeasure g.
Proof. by rewrite mmeasureE msuppN. Qed.

Lemma mmeasureD_le g1 g2 :
  (mmeasure (g1 + g2) <= maxn (mmeasure g1) (mmeasure g2))%N.
Proof.
rewrite {1}mmeasureE big_seq_fsetE /=.
(* Going briefly through finType as lemmas about max apply only to them *)
apply/bigmax_leqP=> [[i ki]] _ /=.
have /fsubsetP /(_ i ki) := (msuppD_le g1 g2); rewrite in_fsetU.
by rewrite leq_max; case/orP=> /mmeasure_mnm_lt->; rewrite ?orbT.
Qed.

Lemma mmeasure_sum (T : Type) (r : seq _) (F : T -> {malg G[M]}) (P : pred T) :
  (mmeasure (\sum_(i <- r | P i) F i) <= \max_(i <- r | P i) mmeasure (F i))%N.
Proof.
elim/big_rec2: _ => /= [|i k p _ le]; first by rewrite mmeasure0.
apply: leq_trans (mmeasureD_le _ _) _; rewrite geq_max.
by rewrite leq_maxl /= leq_max le orbC.
Qed.

Lemma mmeasure_eq0 g : (mmeasure g == 0%N) = (g == 0).
Proof.
apply/idP/eqP=> [z_g|->]; last by rewrite mmeasure0.
apply/malgP=> k; rewrite mcoeff0; apply/contraTeq: z_g.
rewrite mcoeff_neq0 => kg; rewrite mmeasureE.
by rewrite (big_fsetD1 k) //= -lt0n leq_max.
Qed.

Lemma malgSpred g : g != 0 -> mmeasure g = (mmeasure g).-1.+1.
Proof. by rewrite -mmeasure_eq0 -lt0n => /prednK. Qed.

Lemma mmeasure_msupp0 g : (mmeasure g == 0%N) = (msupp g == fset0).
Proof. by rewrite mmeasure_eq0 msupp_eq0. Qed.
End MMeasure.

(* -------------------------------------------------------------------- *)
Section CmonomDef.
Context (I : choiceType).

Record cmonom : predArgType := CMonom { cmonom_val : {fsfun of _ : I => 0%N} }.

Coercion cmonom_val : cmonom >-> fsfun.

Fact cmonom_key : unit. Proof. by []. Qed.

Definition cmonom_of_fsfun   k := locked_with k CMonom.
Canonical  cmonom_unlockable k := [unlockable fun cmonom_of_fsfun k].
End CmonomDef.

Notation "{ 'cmonom' I }" := (cmonom I) : type_scope.
Notation "''X_{1..' n '}'" :=  (cmonom 'I_n) : type_scope.
Notation "{ 'mpoly' R [ n ] }" := {malg R['X_{1..n}]} : type_scope.

Notation mkcmonom := (cmonom_of_fsfun cmonom_key).
Notation "[ 'cmonom' E | i 'in' P ]" :=
  (mkcmonom [fsfun i in P%fset => E%N | 0%N]) : monom_scope.
Notation "[ 'cmonom' E | i : P ]" :=
  (mkcmonom [fsfun i : P%fset => E%N | 0%N]) : monom_scope.

(* -------------------------------------------------------------------- *)
Section CmonomCanonicals.
Context (I : choiceType).

HB.instance Definition _ := [isNew for @cmonom_val I].
HB.instance Definition _ := [Choice of cmonom I by <:].

(* -------------------------------------------------------------------- *)
Implicit Types (m : cmonom I).

Lemma cmE (f : {fsfun of _ : I => 0%N}) : mkcmonom f =1 CMonom f.
Proof. by rewrite unlock. Qed.

Lemma cmP m1 m2 : reflect (forall i, m1 i = m2 i) (m1 == m2).
Proof. by apply: (iffP eqP) => [->//|eq]; apply/val_inj/fsfunP. Qed.

Definition onecm : cmonom I := mkcmonom [fsfun of _ => 0%N].

Definition ucm (i : I) : cmonom I := [cmonom 1 | _ in fset1 i]%M.

Definition mulcm m1 m2 : cmonom I :=
  [cmonom m1 i + m2 i | i in finsupp m1 `|` finsupp m2]%M.

Definition divcm m1 m2 : cmonom I := [cmonom m1 i - m2 i | i in finsupp m1]%M.

Definition expcmn m n : cmonom I := iterop n mulcm m onecm.

Lemma onecmE i : onecm i = 0%N.
Proof. by rewrite cmE fsfun_ffun insubF. Qed.

Lemma ucmE i j : ucm i j = (i == j) :> nat.
Proof. by rewrite cmE fsfun_fun in_fsetE; case: eqVneq. Qed.

Lemma mulcmE m1 m2 i : mulcm m1 m2 i = (m1 i + m2 i)%N.
Proof.
by rewrite cmE fsfun_fun in_fsetE; case: (finsuppP m1); case: (finsuppP m2).
Qed.

Lemma divcmE m1 m2 i : divcm m1 m2 i = (m1 i - m2 i)%N.
Proof. by rewrite cmE fsfun_fun; case: finsuppP. Qed.

Lemma mulcmA : associative mulcm.
Proof. by move=> m1 m2 m3; apply/eqP/cmP=> i; rewrite !mulcmE addnA. Qed.

Lemma mulcmC : commutative mulcm.
Proof. by move=> m1 m2; apply/eqP/cmP=> i; rewrite !mulcmE addnC. Qed.

Lemma mul0cm : left_id onecm mulcm.
Proof. by move=> m; apply/eqP/cmP=> i; rewrite mulcmE onecmE add0n. Qed.

Lemma mulcm0 : right_id onecm mulcm.
Proof. by move=> m; apply/eqP/cmP=> i; rewrite mulcmE onecmE addn0. Qed.

Lemma mulcm_eq0 m1 m2 : mulcm m1 m2 = onecm -> m1 = onecm /\ m2 = onecm.
Proof.
move: m1 m2; have gen m1 m2 : mulcm m1 m2 = onecm -> m1 = onecm.
  move/eqP/cmP=> h; apply/eqP/cmP=> i; move/eqP: (h i).
  by rewrite mulcmE onecmE addn_eq0 => /andP[] /eqP->.
by move=> m1 m2 h; split; move: h; last rewrite mulcmC; apply/gen.
Qed.

HB.instance Definition _ := Choice_isMonomialDef.Build (cmonom I)
  mulcmA mul0cm mulcm0 mulcm_eq0.
HB.instance Definition _ := MonomialDef_isConomialDef.Build (cmonom I) mulcmC.
End CmonomCanonicals.

(* -------------------------------------------------------------------- *)
Definition mdeg {I : choiceType} (m : cmonom I) :=
  (\sum_(k <- finsupp m) m k)%N.

Definition mnmwgt {n} (m : cmonom 'I_n) :=
  (\sum_i m i * i.+1)%N.

(* -------------------------------------------------------------------- *)
Section CmonomTheory.
Context {I : choiceType}.

Implicit Types (m : cmonom I) (i : I).

Local Notation "'U_(' i )" := (@ucm I i) : monom_scope.
Local Notation mdeg := (@mdeg I).

Lemma cm1 i : (1%M : cmonom I) i = 0%N.
Proof. exact/onecmE. Qed.

Lemma cmU i j : U_(i)%M j = (i == j) :> nat.
Proof. exact/ucmE. Qed.

Lemma cmUU i : U_(i)%M i = 1%N.
Proof. by rewrite cmU eqxx. Qed.

Lemma cmM i m1 m2 : (m1 * m2)%M i = (m1 i + m2 i)%N.
Proof. exact/mulcmE. Qed.

Lemma cmE_eq0 m i : (m i == 0%N) = (i \notin finsupp m).
Proof. by rewrite memNfinsupp. Qed.

Lemma cmE_neq0 m i : (m i != 0%N) = (i \in finsupp m).
Proof. by rewrite cmE_eq0 negbK. Qed.

Variant mdom_spec m (i : I) : bool -> nat -> Type :=
| MdomIn  (_ : i \in    finsupp m) : mdom_spec m i true  (m i)
| MdomOut (_ : i \notin finsupp m) : mdom_spec m i false 0%N.

Lemma mdomP m i : mdom_spec m i (i \in finsupp m) (m i).
Proof. by case: finsuppP=> h; constructor. Qed.

Lemma mdom1 : finsupp (1 : cmonom I)%M = fset0 :> {fset I}.
Proof. by apply/fsetP=> i; rewrite in_fset0 -cmE_neq0 cm1 eqxx. Qed.

Lemma mdomU i : finsupp U_(i)%M = [fset i].
Proof. by apply/fsetP=> j; rewrite -!cmE_neq0 cmU in_fset1 eqb0 negbK. Qed.

Lemma mdomD m1 m2 : finsupp (m1 * m2)%M = finsupp m1 `|` finsupp m2.
Proof.
by apply/fsetP=> i; rewrite in_fsetU -!cmE_neq0 cmM addn_eq0 negb_and.
Qed.

Lemma mdegE m : mdeg m = (\sum_(i <- finsupp m) (m i))%N.
Proof. by []. Qed.

Lemma mdegEw m (d : {fset I}) : finsupp m `<=` d ->
  mdeg m = (\sum_(i <- d) (m i))%N.
Proof.
move=> le; rewrite mdegE (big_fset_incl _ le) //.
by move=> i i_in_d; rewrite -cmE_neq0 negbK => /eqP.
Qed.

Lemma mdeg1 : mdeg 1%M = 0%N.
Proof. by rewrite mdegE mdom1 big_seq_fset0. Qed.

Lemma mdegU k : mdeg U_(k)%M = 1%N.
Proof. by rewrite mdegE mdomU big_seq_fset1 cmUU. Qed.

Lemma mdegM : {morph mdeg: m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N }.
Proof.
move=> m1 m2 /=; rewrite mdegE mdomD.
rewrite
  (mdegEw (fsubsetUl _ (finsupp m2)))
  (mdegEw (fsubsetUr (finsupp m1) _)).
by rewrite -big_split /=; apply/eq_bigr=> /= i _; rewrite cmM.
Qed.

Lemma mdeg_prod (T : Type) r P (F : T -> cmonom I) :
    mdeg (\big[mmul/1%M]_(x <- r | P x) (F x))
  = (\sum_(x <- r | P x) (mdeg (F x)))%N.
Proof. exact/big_morph/mdeg1/mdegM. Qed.

Lemma mdeg_eq0I m : mdeg m = 0%N -> m = 1%M.
Proof.
move=> h; apply/eqP/cmP=> i; move: h; rewrite mdegE cm1.
by case: mdomP=> // ki /eqP; rewrite (big_fsetD1 i) //= addn_eq0 => /andP[/eqP].
Qed.

(* -------------------------------------------------------------------- *)
#[hnf] HB.instance Definition _ := isMeasure.Build (cmonom I)
  mdeg mdeg1 mdegM mdeg_eq0I.

Lemma mdeg_eq0 m : (mdeg m == 0%N) = (m == 1%M).
Proof. exact/mf_eq0. Qed.

Lemma cmM_eq1 m1 m2 : (m1 * m2 == 1)%M = (m1 == 1%M) && (m2 == 1%M).
Proof. by rewrite -!mdeg_eq0 mdegM addn_eq0. Qed.

Lemma cm1_eq1 i : (U_(i) == 1)%M = false.
Proof. by rewrite -mdeg_eq0 mdegU. Qed.
End CmonomTheory.

(* -------------------------------------------------------------------- *)
Section MWeight.
Context (n : nat).

Implicit Types (m : 'X_{1..n}).

Local Notation mnmwgt := (@mnmwgt n).
Local Notation "'U_(' i )" := (@ucm 'I_n i).

Lemma mnmwgtE m : mnmwgt m = (\sum_i m i * i.+1)%N.
Proof. by []. Qed.

Lemma mnmwgt1 : mnmwgt 1%M = 0%N.
Proof. by rewrite mnmwgtE big1 // => /= i _; rewrite cm1. Qed.

Lemma mnmwgtU i : mnmwgt U_(i) = i.+1.
Proof.
rewrite mnmwgtE (bigD1 i) //= cmUU mul1n big1 ?addn0 //.
by move=> j ne_ij; rewrite cmU eq_sym (negbTE ne_ij).
Qed.

Lemma mnmwgtM : {morph mnmwgt: m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N}.
Proof.
move=> m1 m2 /=; rewrite !mnmwgtE -big_split /=.
by apply/eq_bigr=> i _; rewrite cmM mulnDl.
Qed.

Lemma mnmwgt_eq0I m : mnmwgt m = 0%N -> m = 1%M.
Proof.
move=> h; apply/eqP/cmP=> /= i; move: h; rewrite mnmwgtE cm1 => /eqP.
rewrite sum_nat_eq0 => /forallP /(_ i) /implyP.
by rewrite muln_eq0 orbF => z_mi; apply/eqP/z_mi.
Qed.

(* -------------------------------------------------------------------- *)
#[hnf] HB.instance Definition _ := isMeasure.Build 'X_{1..n}
  mnmwgt mnmwgt1 mnmwgtM mnmwgt_eq0I.

Lemma mnmwgt_eq0 m : (mnmwgt m == 0%N) = (m == 1%M).
Proof. exact/mf_eq0. Qed.
End MWeight.

(* -------------------------------------------------------------------- *)
Notation msize := (@mmeasure _ _ mdeg).
Notation mweight := (@mmeasure _ _ mnmwgt).

Section MSize.
Context (I : choiceType) (G : zmodType).

Implicit Types (m : cmonom I) (g : {malg G[cmonom I]}).

Local Notation mdeg := (@mdeg I).

Lemma msizeE g : msize g = (\max_(m <- msupp g) (mdeg m).+1)%N.
Proof. exact/mmeasureE. Qed.

Lemma msize_mdeg_lt g m : m \in msupp g -> (mdeg m < msize g)%N.
Proof. exact/mmeasure_mnm_lt. Qed.

Lemma msize_mdeg_ge g m : (msize g <= mdeg m)%N -> m \notin msupp g.
Proof. exact/mmeasure_mnm_ge. Qed.

Definition msize0       := @mmeasure0       _ G mdeg.
Definition msizeC       := @mmeasureC       _ G mdeg.
Definition msizeD_le    := @mmeasureD_le    _ G mdeg.
Definition msize_sum    := @mmeasure_sum    _ G mdeg.
Definition msizeN       := @mmeasureN       _ G mdeg.
Definition msize_eq0    := @mmeasure_eq0    _ G mdeg.
Definition msize_msupp0 := @mmeasure_msupp0 _ G mdeg.
End MSize.

(* -------------------------------------------------------------------- *)
Section FmonomDef.
Context (I : choiceType).

Record fmonom : predArgType := FMonom { fmonom_val : seq I }.

Coercion fmonom_val : fmonom >-> seq.

Fact fmonom_key : unit. Proof. by []. Qed.

Definition fmonom_of_seq     k := locked_with k FMonom.
Canonical  fmonom_unlockable k := [unlockable fun fmonom_of_seq k].
End FmonomDef.

Notation "{ 'fmonom' I }" := (fmonom I) : type_scope.

Local Notation mkfmonom s := (fmonom_of_seq fmonom_key s).

(* -------------------------------------------------------------------- *)
Section FmonomCanonicals.
Context (I : choiceType).

HB.instance Definition _ := [isNew for @fmonom_val I].
HB.instance Definition _ := [Choice of fmonom I by <:].

(* -------------------------------------------------------------------- *)
Implicit Types (m : fmonom I).

Lemma fmE (s : seq I) : mkfmonom s = FMonom s.
Proof. by rewrite unlock. Qed.

Lemma fmP m1 m2 : (m1 == m2) = (m1 == m2 :> seq I).
Proof. by rewrite val_eqE. Qed.

Lemma fmK m : FMonom m = m.
Proof. exact/innew_val. Qed.

Definition fmone : fmonom I := mkfmonom [::].
Definition fmu i : fmonom I := mkfmonom [:: i].
Definition fmmul m1 m2 : fmonom I := mkfmonom (m1 ++ m2).

Lemma fmoneE : fmone = FMonom [::].
Proof. by apply/eqP; rewrite fmP /fmone fmE. Qed.

Lemma fmuE i : fmu i = FMonom [:: i].
Proof. by apply/eqP; rewrite fmP /fmu fmE. Qed.

Lemma fmmulE m1 m2 : fmmul m1 m2 = FMonom (m1 ++ m2).
Proof. by apply/eqP; rewrite fmP /fmmul fmE. Qed.

Let fmE := (fmoneE, fmuE, fmmulE, fmE).

Lemma fmmulA : associative fmmul.
Proof. by move=> m1 m2 m3; rewrite !fmE catA. Qed.

Lemma fmmul1m : left_id fmone fmmul.
Proof. by move=> m; rewrite !fmE cat0s fmK. Qed.

Lemma fmmulm1 : right_id fmone fmmul.
Proof. by move=> m; rewrite !fmE cats0 fmK. Qed.

Lemma fmmul_eq1 m1 m2 : fmmul m1 m2 = fmone -> m1 = fmone /\ m2 = fmone.
Proof. by case: m1 m2 => [[|? ?]] [[|? ?]]; rewrite !fmE. Qed.

HB.instance Definition _ := Choice_isMonomialDef.Build (fmonom I)
  fmmulA fmmul1m fmmulm1 fmmul_eq1.
End FmonomCanonicals.

(* -------------------------------------------------------------------- *)
Definition fdeg (I : choiceType) (m : fmonom I) := size m.

(* -------------------------------------------------------------------- *)
Section FmonomTheory.
Context {I : choiceType}.

Implicit Types (m : fmonom I).

Local Notation "'U_(' i )" := (@fmu I i).
Local Notation fdeg := (@fdeg I).

Lemma fm1 : (1%M : fmonom I) = [::] :> seq I.
Proof. by rewrite /mone /one /= fmoneE. Qed.

Lemma fmU i : U_(i) = [:: i] :> seq I.
Proof. by rewrite fmuE. Qed.

Lemma fmM m1 m2 : (m1 * m2)%M = (m1 ++ m2) :> seq I.
Proof. by rewrite /mmul /mul /= fmmulE. Qed.

Lemma fdegE m : fdeg m = size m.
Proof. by []. Qed.

Lemma fdeg1 : fdeg 1%M = 0%N.
Proof. by rewrite fdegE fm1. Qed.

Lemma fdegU k : fdeg U_(k) = 1%N.
Proof. by rewrite fdegE fmU. Qed.

Lemma fdegM : {morph fdeg: m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N }.
Proof. by move=> m1 m2; rewrite !fdegE fmM size_cat. Qed.

Lemma fdeg_prod (T : Type) r P (F : T -> fmonom I) :
    fdeg (\big[mmul/1%M]_(x <- r | P x) (F x))
  = (\sum_(x <- r | P x) (fdeg (F x)))%N.
Proof. by apply/big_morph; [apply/fdegM|apply/fdeg1]. Qed.

Lemma fdeg_eq0I m : fdeg m = 0%N -> m = 1%M.
Proof.
rewrite fdegE => /size0nil z_m; apply/eqP.
by rewrite -val_eqE /= z_m fm1.
Qed.

(* -------------------------------------------------------------------- *)
#[hnf] HB.instance Definition _ := isMeasure.Build (fmonom I)
  fdeg fdeg1 fdegM fdeg_eq0I.

Lemma fdeg_eq0 m : (fdeg m == 0%N) = (m == 1%M).
Proof. exact/mf_eq0. Qed.

Lemma fmM_eq1 m1 m2 : (m1 * m2 == 1)%M = (m1 == 1%M) && (m2 == 1%M).
Proof. by rewrite -!fdeg_eq0 fdegM addn_eq0. Qed.

Lemma fm1_eq1 i : (U_(i) == 1)%M = false.
Proof. by rewrite -fdeg_eq0 fdegU. Qed.
End FmonomTheory.
