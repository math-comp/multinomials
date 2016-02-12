(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq path choice finset fintype finfun.
From mathcomp Require Import tuple bigop ssralg ssrint ssrnum.

Require Import xfinmap fsfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Monoid GRing.Theory Num.Theory BigEnoughFSet.

Local Open Scope fset.
Local Open Scope fmap.
Local Open Scope ring_scope.

Delimit Scope malg_scope with MP.

Local Notation simpm := Monoid.simpm.
Local Notation ilift := fintype.lift.

Local Notation efst := (@fst _ _) (only parsing).
Local Notation esnd := (@snd _ _) (only parsing).

Delimit Scope m_scope with M.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'cmonom' I }"
  (at level 0, I at level 2, format "{ 'cmonom'  I }").
Reserved Notation "{ 'fmonom' I }"
  (at level 0, I at level 2, format "{ 'fmonom'  I }").
Reserved Notation "{ 'malg' G [ K ] }"
  (at level 0, K, G at level 2, format "{ 'malg'  G [ K ] }").
Reserved Notation "{ 'malg' K }"
  (at level 0, K at level 2, format "{ 'malg'  K }").
Reserved Notation "[ 'malg' g ]"
  (at level 0, g at level 2, format "[ 'malg'  g ]").
Reserved Notation "[ 'malg' x : aT => E ]"
  (at level 0, x ident, format "[ 'malg'  x : aT  =>  E ]").
Reserved Notation "{ 'mpoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'mpoly'  T [ n ] }").
Reserved Notation "<< z *p k >>"
  (at level 0).
Reserved Notation "<< k >>"
  (at level 0).
Reserved Notation "g @_ k"
  (at level 3, k at level 2, left associativity, format "g @_ k").
Reserved Notation "c %:MP"
  (at level 2, format "c %:MP").
Reserved Notation "''X_{1..' n '}'"
  (at level 0, n at level 2).
Reserved Notation "'U_(' n )"
  (at level 0, n at level 2, no associativity).
Reserved Notation "x ^[ f , g ]"
   (at level 2, left associativity, format "x ^[ f , g ]").

(* -------------------------------------------------------------------- *)
Module MonomialDef.

Record mixin_of (V : Type) : Type := Mixin {
  one : V;
  mul : V -> V -> V;
  _   : associative mul;
  _   : left_id one mul;
  _   : right_id one mul;
  _   : forall x y, mul x y = one -> x = one /\ y = one
}.

Section ClassDef.

Record class_of T := Class
 { base : Choice.class_of T; mixin : mixin_of T }.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.

Local Coercion base : class_of >-> Choice.class_of.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.

Coercion  eqType : type >-> Equality.type.
Canonical eqType.
Coercion  choiceType : type >-> Choice.type.
Canonical choiceType.

Bind Scope m_scope with sort.

Notation monomType := type.
Notation MonomType T m := (@pack T m _ _ id).
Notation MonomMixin := Mixin.

Notation "[ 'monomType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'monomType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'monomType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'monomType'  'of'  T ]") : form_scope.
End Exports.
End MonomialDef.

(* -------------------------------------------------------------------- *)
Import MonomialDef.Exports.

Definition mone {M} := MonomialDef.one (MonomialDef.class M).
Definition mmul {M} := MonomialDef.mul (MonomialDef.class M).

(* -------------------------------------------------------------------- *)
Module ConomialDef.

Section ClassDef.

Record class_of (M : Type) : Type := Class {
  base  : MonomialDef.class_of M;
  mixin : commutative (MonomialDef.mul base)
}.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.

Local Coercion base : class_of >-> MonomialDef.class_of.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (MonomialDef.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType     := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition monomType  := @MonomialDef.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base  : class_of >-> MonomialDef.class_of.
Coercion mixin : class_of >-> commutative.
Coercion sort  : type >-> Sortclass.

Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion monomType : type >-> MonomialDef.type.

Canonical eqType.
Canonical choiceType.
Canonical monomType.

Bind Scope m_scope with sort.

Notation conomType := type.
Notation ConomType T m := (@pack T _ m _ _ id _ id).
Notation ConomMixin := MonomialDef.Mixin.

Notation "[ 'conomType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'conomType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'conomType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'conomType'  'of'  T ]") : form_scope.
End Exports.

End ConomialDef.

(* -------------------------------------------------------------------- *)
Export MonomialDef.Exports.
Export ConomialDef.Exports.

Local Notation "1" := (@mone _) : m_scope.
Local Notation "*%R" := (@mmul _) : m_scope.
Local Notation "x * y" := (mmul x y) : m_scope.

(* -------------------------------------------------------------------- *)
Module MonomialTheory.
Section Monomial.
Variable M : monomType.

Lemma mulmA : associative  (@mmul M). Proof. by case M => T [? []]. Qed.
Lemma mul1m : left_id  1%M (@mmul M). Proof. by case M => T [? []]. Qed.
Lemma mulm1 : right_id 1%M (@mmul M). Proof. by case M => T [? []]. Qed.

Local Open Scope m_scope.

Lemma unitm (x y : M) : x * y = 1 -> x = 1 /\ y = 1.
Proof. by case: M x y => T [? []]. Qed.

Canonical monom_monoid := Monoid.Law mulmA mul1m mulm1.

Lemma unitmP (x y : M) : reflect (x == 1 /\ y == 1) (x * y == 1).
Proof.
apply: (iffP idP)=> [|[/eqP-> /eqP->]]; rewrite ?mulm1 //.
by move/eqP/unitm=> [-> ->]; rewrite !eqxx.
Qed.
End Monomial.

Section Conomial.
Variable M : conomType.

Local Open Scope m_scope.

Lemma mulmC : commutative (@mmul M).
Proof. by case M => T []. Qed.

Canonical conom_monoid := Monoid.Law (@mulmA M) (@mul1m M) (@mulm1 M).
Canonical conom_comoid := Monoid.ComLaw mulmC.
End Conomial.

Module Exports.
Canonical monom_monoid.
Canonical conom_monoid.
Canonical conom_comoid.
End Exports.
End MonomialTheory.

Export MonomialTheory.Exports.

(* -------------------------------------------------------------------- *)
Module MMorphism.
Section ClassDef.

Variables (M : monomType) (S : ringType).

Definition axiom (f : M -> S) :=
  {morph f : x y / (x * y)%M >-> (x * y)%R} * (f 1%M = 1) : Prop.

Structure map (phR : phant (M -> S)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phR : phant (M -> S)) (f g : M -> S) (cF : map phR).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phR f fA.
End ClassDef.

Module Exports.
Notation mmorphism f := (axiom f).
Coercion apply : map >-> Funclass.
Notation MMorphism fA := (Pack (Phant _) fA).
Notation "{ 'mmorphism' fR }" := (map (Phant fR))
  (at level 0, format "{ 'mmorphism'  fR }") : ring_scope.
Notation "[ 'mmorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'mmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'mmorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'mmorphism'  'of'  f ]") : form_scope.
End Exports.
End MMorphism.
Export MMorphism.Exports.

(* -------------------------------------------------------------------- *)
Section MMorphismTheory.
Variables (M : monomType) (S : ringType) (f : {mmorphism M -> S}).

Lemma mmorph1 : f 1%M = 1.
Proof. by case: f=> [? []]. Qed.

Lemma mmorphM : {morph f : x y / (x * y)%M >-> (x * y)%R}.
Proof. by case: f=> [? []]. Qed.
End MMorphismTheory.

(* -------------------------------------------------------------------- *)
Section MalgDef.
Variable (K : choiceType) (G : zmodType).

Inductive malg : predArgType := Malg of {fsfun K -> G / 0}.

Definition malg_val g := let: Malg g := g in g.
Definition malg_of (_ : phant K) (_ : phant G) := malg.

Coercion malg_val : malg >-> fsfun_of.

Fact malg_key : unit. Proof. by []. Qed.

Definition malg_of_fsfun   k := locked_with k Malg.
Canonical  malg_unlockable k := [unlockable fun malg_of_fsfun k].
End MalgDef.

(* -------------------------------------------------------------------- *)
Bind Scope ring_scope with malg.
Bind Scope ring_scope with malg_of.

Notation "{ 'malg' G [ K ] }" :=
  (@malg_of _ _ (Phant K) (Phant G)) : type_scope.
Notation "{ 'malg' K }" :=
  {malg int[K]} : type_scope.

(* -------------------------------------------------------------------- *)
Section MalgCanonicals.
Variable (K : choiceType) (G : zmodType).

Canonical  malgType := Eval hnf in [newType for (@malg_val K G)].
Definition malg_eqMixin := Eval hnf in [eqMixin of {malg G[K]} by <:].
Canonical  malg_eqType := Eval hnf in EqType {malg G[K]} malg_eqMixin.
Definition malg_choiceMixin := Eval hnf in [choiceMixin of {malg G[K]} by <:].
Canonical  malg_choiceType := Eval hnf in ChoiceType {malg G[K]} malg_choiceMixin.
End MalgCanonicals.

(* -------------------------------------------------------------------- *)
Section MkMalg.
Variable (K : choiceType) (G : zmodType).

Definition mkmalg (g : {fsfun K -> G / 0}) : {malg G[K]} :=
  nosimpl (Malg g).

Definition mkmalgU (k : K) (x : G) :=
  nosimpl (mkmalg [fsfun [fmap].[k <- x] / 0]).
End MkMalg.

(* -------------------------------------------------------------------- *)
Notation "[ 'malg' g ]"
  := (mkmalg [fsfun g / 0]) : ring_scope.
Notation "[ 'malg' x : aT => E ]"
  := (mkmalg [fsfun [fmap x : aT => E] / 0]) : ring_scope.
Notation "<< z *g k >>"
  := (mkmalgU k z).
Notation "<< k >>"
  := << 1 *g k >> : ring_scope.

(* -------------------------------------------------------------------- *)
Section MalgBaseOp.
Variable (K : choiceType) (G : zmodType).

Definition msupp (g : {malg G[K]}) :=
  nosimpl (domf (malg_val g)).

Definition mcoeff (x : K) (g : {malg G[K]}) :=
  nosimpl (malg_val g x).
End MalgBaseOp.

Notation "g @_ k" := (mcoeff k g).

(* -------------------------------------------------------------------- *)
Section MalgBaseOpMonom.
Variable (K : monomType) (G : zmodType).

Definition malgC (c : G) : {malg G[K]} :=
  nosimpl << c *g 1%M >>.

Lemma malgCE (c : G) : malgC c = << c *g 1%M >>.
Proof. by []. Qed.
End MalgBaseOpMonom.

Notation "c %:MP" := (@malgC _ _ c).

(* -------------------------------------------------------------------- *)
Section MalgTheory.
Variable (K : choiceType) (G : zmodType).

Lemma mkmalgK (g : {fsfun K -> G / 0}) :
  mkmalg g = g :> {fsfun _ -> _ / _}.
Proof. by []. Qed.

Lemma malgP (g1 g2 : {malg G[K]}) :
  reflect (forall k, g1@_k = g2@_k) (g1 == g2).
Proof.
apply: (iffP eqP)=> [->//|]; move: g1 g2.
case=> [g1] [g2] h; apply/eqP; rewrite -val_eqE /=.
by apply/fsfunP=> k; move/(_ k): h.
Qed.

Lemma mcoeff_fnd (g : {fmap K -> G}) k :
  (mkmalg [fsfun g / 0])@_k = odflt 0 g.[?k].
Proof. by apply/fsfun_fnd. Qed.

Lemma mcoeffE (domf : {fset K}) (E : K -> G) k :
    [malg k : domf => E (val k)]@_k
  = if k \in domf then E k else 0.
Proof. by apply/fsfunE. Qed.

Lemma mcoeff_eq0 (g : {malg G[K]}) (k : K) :
  (g@_k == 0) = (k \notin msupp g).
Proof. by apply/fsfun_eqdfl. Qed.

Lemma mcoeff_neq0 (g : {malg G[K]}) (k : K) :
  (g@_k != 0) = (k \in msupp g).
Proof. by rewrite mcoeff_eq0 negbK. Qed.

Lemma mcoeff_outdom (g : {malg G[K]}) (k : K) :
  k \notin msupp g -> g@_k = 0.
Proof. by apply/fsfun_outdom. Qed.

CoInductive msupp_spec (g : {malg G[K]}) (k : K) : bool -> G -> Type :=
| MsuppIn  (_ : k \in    msupp g) : msupp_spec g k true  g@_k
| MsuppOut (_ : k \notin msupp g) : msupp_spec g k false 0.

Lemma msuppP (g : {malg G[K]}) (k : K) : msupp_spec g k (k \in msupp g) g@_k.
Proof. by rewrite /msupp /mcoeff; case: fsfunEP; constructor. Qed.
End MalgTheory.

(* -------------------------------------------------------------------- *)
Section MalgZMod.
Variable (K : choiceType) (G : zmodType).

Implicit Types g : {malg G[K]}.
Implicit Types k : K.

Let EN g     k := - g@_k.
Let ED g1 g2 k := g1@_k + g2@_k.

Definition fgzero : {malg G[K]} :=
  [malg [fmap]].

Definition fgopp g :=
  [malg k : msupp g => - g@_(val k)].

Definition fgadd g1 g2 :=
  [malg k : (msupp g1 `|` msupp g2) => g1@_(val k) + g2@_(val k)].

Lemma fgzeroE k : fgzero@_k = 0.
Proof. by rewrite mcoeff_fnd !(in_fsetE, not_fnd). Qed.

Lemma fgoppE g k : (fgopp g)@_k = - g@_k.
Proof. by rewrite (mcoeffE _ (EN g)); case: msuppP; rewrite ?oppr0. Qed.

Lemma fgaddE g1 g2 k : (fgadd g1 g2)@_k = g1@_k + g2@_k.
Proof.
rewrite (mcoeffE _ (ED g1 g2)); rewrite in_fsetE /ED.
by case: (msuppP g1); case: (msuppP g2); rewrite !simpm.
Qed.

Let fgE := (fgzeroE, fgoppE, fgaddE).

Lemma fgaddA : associative fgadd.
Proof. by move=> x y z; apply/eqP/malgP=> k; rewrite !fgE addrA. Qed.

Lemma fgaddC : commutative fgadd.
Proof. by move=> x y; apply/eqP/malgP=> k; rewrite !fgaddE addrC. Qed.

Lemma fgadd0g : left_id fgzero fgadd.
Proof. by move=> x; apply/eqP/malgP=> k; rewrite !fgE add0r. Qed.

Lemma fgaddg0 : right_id fgzero fgadd.
Proof. by move=> x; rewrite fgaddC fgadd0g. Qed.

Lemma fgaddNg : left_inverse fgzero fgopp fgadd.
Proof. by move=> x; apply/eqP/malgP=> k; rewrite !fgE addNr. Qed.

Lemma fgaddgN : right_inverse fgzero fgopp fgadd.
Proof. by move=> x; rewrite fgaddC fgaddNg. Qed.

Definition malg_ZmodMixin := ZmodMixin fgaddA fgaddC fgadd0g fgaddNg.
Canonical  malg_ZmodType  := Eval hnf in ZmodType {malg G[K]} malg_ZmodMixin.
End MalgZMod.

Section MAlgZModTheory.
Context {K : choiceType} {G : zmodType}.

Implicit Types g   : {malg G[K]}.
Implicit Types k   : K.
Implicit Types x y : G.

Local Notation mcoeff  := (@mcoeff  K G) (only parsing).
Local Notation msupp   := (@msupp   K G).
Local Notation mkmalgU := (@mkmalgU K G) (only parsing).

Let fgE := (fgzeroE, fgoppE, fgaddE).

(* -------------------------------------------------------------------- *)
Lemma malgD_def g1 g2 : g1 + g2 = fgadd g1 g2.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeff_is_additive k: additive (mcoeff k).
Proof. by move=> g1 g2 /=; rewrite !fgE. Qed.

Canonical mcoeff_additive k := Additive (mcoeff_is_additive k).

Lemma mcoeff0   k   : 0@_k = 0 :> G                . Proof. exact: raddf0. Qed.
Lemma mcoeffN   k   : {morph mcoeff k: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mcoeffD   k   : {morph mcoeff k: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mcoeffB   k   : {morph mcoeff k: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mcoeffMn  k n : {morph mcoeff k: x / x *+ n} . Proof. exact: raddfMn. Qed.
Lemma mcoeffMNn k n : {morph mcoeff k: x / x *- n} . Proof. exact: raddfMNn. Qed.

Lemma mcoeffU k x k' : << x *g k >>@_k' = x *+ (k == k').
Proof. by rewrite mcoeff_fnd fnd_set fnd_fmap0 eq_sym; case: eqP. Qed.

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
apply/fsetP=> k'; rewrite -mcoeff_neq0 mcoeffU 2!fun_if.
rewrite in_fset0 in_fset1 [k'==_]eq_sym; case: (x =P 0).
  by move=> ->; rewrite mul0rn eqxx.
  by move=> /eqP nz_x; case: (k =P k')=> //=; rewrite eqxx.
Qed.

Lemma msuppU_le {k x} : msupp << x *g k >> `<=` [fset k].
Proof. by rewrite msuppU; case: eqP=> _; rewrite (fsub0set, fsubset_refl). Qed.

Lemma msuppN g : msupp (-g) = msupp g.
Proof. by apply/fsetP=> k; rewrite -!mcoeff_neq0 mcoeffN oppr_eq0. Qed.

Lemma msuppD_le g1 g2 : msupp (g1 + g2) `<=` msupp g1 `|` msupp g2.
Proof.
apply/fsubsetP=> k; rewrite in_fsetU -mcoeff_neq0 mcoeffD.
by case: (msuppP g1); case: (msuppP g2)=> //=; rewrite addr0 eqxx.
Qed.

Lemma msuppB_le g1 g2 : msupp (g1 - g2) `<=` msupp g1 `|` msupp g2.
Proof. by rewrite -[msupp g2]msuppN; apply/msuppD_le. Qed.

Lemma msuppD g1 g2 : [disjoint msupp g1 & msupp g2] ->
  msupp (g1 + g2) = msupp g1 `|` msupp g2.
Proof.
move=> dj_g1g2; apply/fsetP=> k; rewrite in_fsetU.
rewrite -!mcoeff_neq0 mcoeffD; case: (boolP (_ || _)); last first.
  by rewrite negb_or !negbK => /andP[/eqP-> /eqP->]; rewrite addr0 eqxx.
wlog: g1 g2 dj_g1g2 / (k \notin msupp g2) => [wlog h|].
  case/orP: {+}h; rewrite mcoeff_neq0; last rewrite addrC.
    by move/(fdisjointP dj_g1g2)/wlog; apply.
  move/(fdisjointP_sym dj_g1g2)/wlog; apply.
    by rewrite fdisjoint_sym. by rewrite orbC.
by move=> /mcoeff_outdom ->; rewrite eqxx orbF addr0.
Qed.

Lemma msuppB g1 g2 : [disjoint msupp g1 & msupp g2] ->
  msupp (g1 - g2) = msupp g1 `|` msupp g2.
Proof. by move=> dj_g1g2; rewrite msuppD msuppN. Qed.

Lemma msuppMn_le g n : msupp (g *+ n) `<=` msupp g.
Proof.
elim: n => [|n ih]; first by rewrite mulr0n msupp0 fsub0set.
rewrite mulrS (fsubset_trans (msuppD_le _ _)) //.
by rewrite fsubUset fsubset_refl.
Qed.

Lemma msuppMNm_le g n : msupp (g *- n) `<=` msupp g.
Proof. by rewrite msuppN msuppMn_le. Qed.

(* -------------------------------------------------------------------- *)
Lemma monalgU_is_additive k : additive (mkmalgU k).
Proof. by move=> x1 x2 /=; apply/eqP/malgP=> k'; rewrite !mcoeffsE mulrnBl. Qed.

Canonical monalgU_additive k := Additive (monalgU_is_additive k).

Lemma monalgU0   k   : << (0 : G) *g k >> = 0        . Proof. exact: raddf0. Qed.
Lemma monalgUN   k   : {morph mkmalgU k: x / - x}    . Proof. exact: raddfN. Qed.
Lemma monalgUD   k   : {morph mkmalgU k: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma monalgUB   k   : {morph mkmalgU k: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma monalgUMn  k n : {morph mkmalgU k: x / x *+ n} . Proof. exact: raddfMn. Qed.
Lemma monalgUMNn k n : {morph mkmalgU k: x / x *- n} . Proof. exact: raddfMNn. Qed.

Lemma monalgU_eq0 x k: (<< x *g k >> == 0) = (x == 0).
Proof.
apply/eqP/eqP; last by move=> ->; rewrite monalgU0.
by move/(congr1 (mcoeff k)); rewrite !mcoeffsE eqxx.
Qed.

Definition monalgUE :=
  (monalgU0, monalgUB, monalgUD, monalgUN, monalgUMn).

(* -------------------------------------------------------------------- *)
Lemma monalgEw (g : {malg G[K]}) (domg : {fset K}) : msupp g `<=` domg ->
  g = \sum_(k : domg) << g@_(val k) *g val k >>.
Proof.
move=> le_gd; apply/eqP/malgP=> k /=; case: msuppP=> [kg|k_notin_g].
  rewrite raddf_sum /= (bigD1 (fincl le_gd (FSetSub kg))) //=.
  rewrite mcoeffUU big1 ?addr0 //; case=> [k' k'_in_g] /=.
  by rewrite eqE /= mcoeffU => /negbTE ->.
rewrite raddf_sum /= big1 //; case=> [k' k'g] _ /=.
by rewrite mcoeffU; case: eqP k_notin_g=> // <- /mcoeff_outdom ->.
Qed.

Lemma monalgE (g : {malg G[K]}) :
  g = \sum_(k : msupp g) << g@_(val k) *g val k >>.
Proof. by apply/monalgEw/fsubset_refl. Qed.
End MAlgZModTheory.

(* -------------------------------------------------------------------- *)
Section MalgMonomTheory.
Context {K : monomType} {G : zmodType}.

(* -------------------------------------------------------------------- *)
Lemma msuppC (c : G) :
  msupp c%:MP = (if c == 0 then fset0 else [fset 1%M]) :> {fset K}.
Proof. by apply/msuppU. Qed.

Lemma msuppC_le (c : G) : msupp c%:MP `<=` ([fset 1%M] : {fset K}).
Proof. by rewrite msuppC; case: eqP=> _; rewrite ?fsubset_refl // fsub0set. Qed.

Lemma mcoeffC (c : G) k : c%:MP@_k = c *+ (k == (1%M : K)).
Proof. by rewrite mcoeffU eq_sym. Qed.

Lemma mcoeffC0 (k : K) : 0%:MP@_k = 0 :> G.
Proof. by rewrite mcoeffC mul0rn. Qed.

Lemma msuppC0 : msupp (0 : G)%:MP = fset0 :> {fset K}.
Proof. by rewrite msuppC eqxx. Qed.

Lemma malgC0E : 0%:MP = 0 :> {malg G[K]}.
Proof. by apply/eqP/malgP=> k; rewrite mcoeffC0 mcoeff0. Qed.

Lemma malgCK : cancel (@malgC K G) (@mcoeff K G 1%M).
Proof. by move=> c; rewrite mcoeffC eqxx mulr1n. Qed.

Lemma malgC_eq (c1 c2 : G) :
  (c1%:MP == c2%:MP :> {malg G[K]}) = (c1 == c2).
Proof. by apply/eqP/eqP=> [|->//] /eqP/malgP/(_ 1%M); rewrite !mcoeffU eqxx. Qed.

Lemma msupp_eq0 (g : {malg G[K]}) : (msupp g == fset0) = (g == 0).
Proof.
apply/eqP/eqP=> [/fsetP z_g|->]; rewrite ?msupp0 //.
apply/eqP/malgP=> i; rewrite mcoeff0; case: msuppP=> //.
by rewrite z_g in_fset0.
Qed.

(* -------------------------------------------------------------------- *)
Local Notation malgC := (@malgC K G) (only parsing).

Lemma malgC_is_additive : additive malgC.
Proof. by move=> g1 g2; apply/eqP/malgP=> k; rewrite malgCE monalgUB. Qed.

Canonical malgC_additive : {additive G -> {malg G[K]}} :=
  Additive malgC_is_additive.

Lemma malgC0     : malgC 0 = 0               . Proof. exact: raddf0. Qed.
Lemma malgCN     : {morph malgC: x / - x}    . Proof. exact: raddfN. Qed.
Lemma malgCD     : {morph malgC: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma malgCB     : {morph malgC: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma malgCMn  k : {morph malgC: x / x *+ k} . Proof. exact: raddfMn. Qed.
Lemma malgCMNn k : {morph malgC: x / x *- k} . Proof. exact: raddfMNn. Qed.
End MalgMonomTheory.

(* -------------------------------------------------------------------- *)
Section MAlgLMod.
Variable (K : choiceType) (R : ringType).

Implicit Types g       : {malg R[K]}.
Implicit Types c x y z : R.
Implicit Types k l     : K.

Definition fgscale c g : {malg R[K]} :=
  \sum_(k : msupp g) << c * g@_(val k) *g val k >>.

Local Notation "c *:g g" := (fgscale c g)
  (at level 40, left associativity).

Lemma fgscaleE c g k :
  (c *:g g)@_k = c * g@_k.
Proof.
rewrite {2}[g]monalgE !raddf_sum mulr_sumr.
by apply/eq_bigr=> /= i _; rewrite !mcoeffU mulrnAr.
Qed.

Lemma fgscaleA c1 c2 g :
  c1 *:g (c2 *:g g) = (c1 * c2) *:g g.
Proof. by apply/eqP/malgP=> x; rewrite !fgscaleE mulrA. Qed.

Lemma fgscale1r D: 1 *:g D = D.
Proof. by apply/eqP/malgP=> k; rewrite !fgscaleE mul1r. Qed.

Lemma fgscaleDr c g1 g2 :
  c *:g (g1 + g2) = c *:g g1 + c *:g g2.
Proof. by apply/eqP/malgP=> k; rewrite !(mcoeffD, fgscaleE) mulrDr. Qed.

Lemma fgscaleDl g c1 c2:
  (c1 + c2) *:g g = c1 *:g g + c2 *:g g.
Proof. by apply/eqP/malgP=> x; rewrite !(mcoeffD, fgscaleE) mulrDl. Qed.

Definition malg_lmodMixin :=
  LmodMixin fgscaleA fgscale1r fgscaleDr fgscaleDl.
Canonical malg_lmodType :=
  Eval hnf in LmodType R {malg R[K]} malg_lmodMixin.
End MAlgLMod.

(* -------------------------------------------------------------------- *)
Section MAlgLModTheory.
Context {K : choiceType} {R : ringType}.

Implicit Types g       : {malg R[K]}.
Implicit Types c x y z : R.
Implicit Types k l     : K.

Lemma malgZ_def c g : c *: g = fgscale c g.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeffZ c g k : (c *: g)@_k = c * g@_k.
Proof. by apply/fgscaleE. Qed.

Canonical mcoeff_linear m : {scalar {malg R[K]}} :=
  AddLinear ((fun c => (mcoeffZ c)^~ m) : scalable_for *%R (mcoeff m)).

(* -------------------------------------------------------------------- *)
Lemma msuppZ_le c g : msupp (c *: g) `<=` msupp g.
Proof.
apply/fsubsetP=> k; rewrite -!mcoeff_neq0 mcoeffZ.
by apply/contraTneq=> ->; rewrite mulr0 negbK.
Qed.
End MAlgLModTheory.

(* -------------------------------------------------------------------- *)
Section MAlgLModTheoryIdDomain.
Context {K : choiceType} {R : idomainType}.

Implicit Types g       : {malg R[K]}.
Implicit Types c x y z : R.
Implicit Types k l     : K.

(* -------------------------------------------------------------------- *)
Lemma msuppZ c g : msupp (c *: g) = if c == 0 then fset0 else msupp g.
Proof.
case: eqP=> [->|/eqP nz_c]; first by rewrite scale0r msupp0.
by apply/fsetP=> k; rewrite -!mcoeff_neq0 mcoeffZ mulf_eq0 negb_or nz_c.
Qed.
End MAlgLModTheoryIdDomain.

(* -------------------------------------------------------------------- *)
Definition mcoeffsE :=
  (@mcoeff0, @mcoeffUU, @mcoeffU, @mcoeffB, @mcoeffD,
   @mcoeffN, @mcoeffMn, @mcoeffZ).

(* -------------------------------------------------------------------- *)
Section MAlgRingType.
Variable (K : monomType) (R : ringType).

Implicit Types g       : {malg R[K]}.
Implicit Types c x y z : R.
Implicit Types k l     : K.

Lemma mcoeffU1 k k' : (<< k >> : {malg R[K]})@_k' = (k == k')%:R.
Proof. by rewrite mcoeffU. Qed.

Lemma msuppU1 k : @msupp _ R << k >> = [fset k].
Proof. by rewrite msuppU oner_eq0. Qed.

Definition fgone : {malg R[K]} := << 1%M >>.

Local Notation "g1 *M_[ k1 , k2 ] g2" :=
  << g1@_k1%M * g2@_k2%M *g (k1 * k2)%M >>
  (at level 40, no associativity, format "g1  *M_[ k1 ,  k2 ]  g2").

Local Notation "g1 *gM_[ k2 ] g2" :=
  (\sum_(k1 : msupp g1) g1 *M_[val k1, k2] g2)
  (at level 40, no associativity, only parsing).

Local Notation "g1 *Mg_[ k1 ] g2" :=
  (\sum_(k2 : msupp g2) g1 *M_[k1, val k2] g2)
  (at level 40, no associativity, only parsing).

Local Notation fg1mull_r g1 g2 k2 :=
  (fun k1 => g1 *M_[k1, k2] g2) (only parsing).

Local Notation fg1mulr_r g1 g2 k1 :=
  (fun k2 => g1 *M_[k1, k2] g2) (only parsing).

Local Notation fg1mull := (fg1mull_r _ _ _) (only parsing).
Local Notation fg1mulr := (fg1mulr_r _ _ _) (only parsing).

Definition fgmul g1 g2 : {malg R[K]} :=
  \sum_(k1 : msupp g1) \sum_(k2 : msupp g2)
    g1 *M_[val k1, val k2] g2.

Lemma fgmull g1 g2 :
  fgmul g1 g2 = \sum_(k1 : msupp g1) \sum_(k2 : msupp g2)
    g1 *M_[val k1, val k2] g2.
Proof. by []. Qed.

Lemma fgmulr g1 g2 :
  fgmul g1 g2 = \sum_(k2 : msupp g2) \sum_(k1 : msupp g1)
    g1 *M_[val k1, val k2] g2.
Proof. by rewrite fgmull exchange_big. Qed.

Let fg1mulzg g1 g2 k1 k2 : k1 \notin msupp g1 -> 
  << g1@_k1 * g2@_k2 *g (k1 * k2)%M >> = 0.
Proof. by move/mcoeff_outdom=> ->; rewrite mul0r monalgU0. Qed.

Let fg1mulgz g1 g2 k1 k2 : k2 \notin msupp g2 -> 
  << g1@_k1 * g2@_k2 *g (k1 * k2)%M >> = 0.
Proof. by move/mcoeff_outdom=> ->; rewrite mulr0 monalgU0. Qed.

Lemma fgmullw (d1 d2 : {fset K}) g1 g2 :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 -> fgmul g1 g2 =
    \sum_(k1 : d1) \sum_(k2 : d2) g1 *M_[val k1, val k2] g2.
Proof.
move=> le_d1 le_d2; pose F k1 := g1 *Mg_[k1] g2.
rewrite fgmull (big_fset_incl F le_d1) {}/F /=; last first.
  by move=> k _ /fg1mulzg ?; rewrite big1.
apply/eq_bigr=> k1 _; rewrite (big_fset_incl fg1mulr le_d2) //.
by move=> x _ /fg1mulgz.
Qed.

Lemma fgmulrw (d1 d2 : {fset K}) g1 g2 : msupp g1 `<=` d1 -> msupp g2 `<=` d2
  -> fgmul g1 g2 = \sum_(k2 : d2) \sum_(k1 : d1) g1 *M_[val k1, val k2] g2.
Proof. by move=> le_d1 le_d2; rewrite (fgmullw le_d1 le_d2) exchange_big. Qed.

Definition fgmullwl (d1 : {fset K}) {g1 g2} (le : msupp g1 `<=` d1) :=
  @fgmullw _ _ g1 g2 le (fsubset_refl _).

Definition fgmulrwl (d2 : {fset K}) {g1 g2} (le : msupp g2 `<=` d2) :=
  @fgmulrw _ _ g1 g2 (fsubset_refl _) le.

Lemma fgmulElw (d1 d2 : {fset K}) g1 g2 k : 
    msupp g1 `<=` d1 -> msupp g2 `<=` d2
  -> (fgmul g1 g2)@_k = \sum_(k1 : d1) \sum_(k2 : d2)
        (g1@_(val k1) * g2@_(val k2)) *+ ((val k1 * val k2)%M == k).
Proof.
move=> le1 le2; rewrite (fgmullw le1 le2) raddf_sum /=.
apply/eq_bigr=> k1 _; rewrite raddf_sum /=; apply/eq_bigr=> k2 _.
by rewrite mcoeffsE.
Qed.

Lemma fgmulErw (d1 d2 : {fset K}) g1 g2 k : msupp g1 `<=` d1 -> msupp g2 `<=` d2
  -> (fgmul g1 g2)@_k = \sum_(k2 : d2) \sum_(k1 : d1)
        (g1@_(val k1) * g2@_(val k2)) *+ ((val k1 * val k2)%M == k).
Proof. by move=> le1 le2; rewrite (fgmulElw _ le1 le2); rewrite exchange_big. Qed.

Lemma fgmul0g g : fgmul 0 g = 0.
Proof. by rewrite fgmull msupp0 big_fset0. Qed.

Lemma fgmulg0 g : fgmul g 0 = 0.
Proof. by rewrite fgmulr msupp0 big_fset0. Qed.

Lemma fgmulUg (d : {fset K}) c k g : msupp g `<=` d ->
 fgmul << c *g k >> g =
   \sum_(k' : d) << c * g@_(val k') *g (k * val k')%M >>.
Proof.
move=> le; rewrite (fgmullw msuppU_le le) big_fset1 /=.
by apply/eq_bigr=> /= k' _; rewrite mcoeffUU.
Qed.

Lemma fgmulgU (d : {fset K}) c k g : msupp g `<=` d ->
 fgmul g << c *g k >> =
   \sum_(k' : d) << g@_(val k') * c *g (val k' * k)%M >>.
Proof.
move=> le; rewrite (fgmulrw le msuppU_le) big_fset1 /=.
by apply/eq_bigr=> /= k' _; rewrite mcoeffUU.
Qed.

Lemma fgmulUU c1 c2 k1 k2 :
  fgmul << c1 *g k1 >> << c2 *g k2 >> = << c1 * c2 *g (k1 * k2)%M >>.
Proof. by rewrite (fgmullw msuppU_le msuppU_le) !big_fset1 /= !mcoeffUU. Qed.

Lemma fgmulEl1w (d1 : {fset K}) {g1 g2}  :
  msupp g1 `<=` d1 -> fgmul g1 g2
    = \sum_(k1 : d1) fgmul << g1@_(val k1) *g val k1 >> g2.
Proof.
move=> le; rewrite (fgmullwl le); apply/eq_bigr=> /= k _.
by rewrite -fgmulUg // fsubset_refl.
Qed.

Lemma fgmulEr1w (d2 : {fset K}) {g1 g2} :
  msupp g2 `<=` d2 -> fgmul g1 g2
    = \sum_(k2 : d2) fgmul g1 << g2@_(val k2) *g val k2 >>.
Proof.
move=> le; rewrite (fgmulrwl le); apply/eq_bigr=> /= k _.
by rewrite -fgmulgU // fsubset_refl.
Qed.

Lemma fgmullUg_is_additive c k : additive (fgmul << c *g k >>).
Proof.
move=> g1 g2 /=; pose_big_fset K E; rewrite 3?(@fgmulUg E) //.
  rewrite -sumrB; apply/eq_bigr=> /= k' _.
  by rewrite mcoeffB -monalgUB mulrBr.
by close.
Qed.

Lemma fgmullgU_is_additive c k : additive (fun g => fgmul^~ << c *g k >> g).
Proof.
move=> g1 g2 /=; pose_big_fset K E; rewrite 3?(@fgmulgU E) //.
  rewrite -sumrB; apply/eq_bigr=> /= k' _.
  by rewrite mcoeffB -monalgUB mulrBl.
by close.
Qed.

Definition fgmullUg_additive c k := Additive (fgmullUg_is_additive c k).
Definition fgmullgU_additive c k := Additive (fgmullgU_is_additive c k).

Lemma fgoneE k : fgone@_k = (k == 1%M)%:R.
Proof. by rewrite mcoeffU1 eq_sym. Qed.

Lemma fgmulA : associative fgmul.
Proof.
move=> g1 g2 g3; pose_big_fset K E.
  transitivity (\sum_(k1 : E) \sum_(k2 : E) \sum_(k3 : E)
    << g1@_(val k1) * g2@_(val k2) * g3@_(val k3) *g
         (val k1 * val k2 * val k3)%M >>).
  + rewrite (@fgmulEl1w E) //; apply/eq_bigr=> /= k1 _.
    rewrite [X in fgmul _ X](@fgmullw E E) //.
    have /= raddf := raddf_sum (fgmullUg_additive g1@_(val k1) (val k1)).
    rewrite raddf; apply/eq_bigr=> /= k2 _; rewrite raddf.
    by apply/eq_bigr=> /= k3 _; rewrite fgmulUU mulrA mulmA.
  2: by close.
rewrite [LHS](eq_bigr _ (fun _ _ => exchange_big _ _ _ _ _ _)) /=.
rewrite exchange_big /=; apply/esym; rewrite (@fgmulEr1w E) //.
apply/eq_bigr=> /= k3 _; rewrite (@fgmullw E E g1) //.
have /= raddf := raddf_sum (fgmullgU_additive g3@_(val k3) (val k3)).
rewrite raddf; apply/eq_bigr=> /= k1 _; rewrite raddf.
by apply/eq_bigr=> /= k2 _; rewrite fgmulUU.
Qed.

Lemma fgmul1g : left_id fgone fgmul.
Proof.
move=> g; rewrite fgmull; apply/eqP/malgP=> k.
rewrite msuppU1 big_fset1 [X in _=X@__]monalgE !raddf_sum /=.
by apply/eq_bigr=> kg _; rewrite fgoneE eqxx mul1r mul1m.
Qed.

Lemma fgmulg1 : right_id fgone fgmul.
Proof.
move=> g; rewrite fgmulr; apply/eqP/malgP=> k.
rewrite msuppU1 big_fset1 [X in _=X@__]monalgE !raddf_sum /=.
by apply/eq_bigr=> kg _; rewrite fgoneE eqxx mulr1 mulm1.
Qed.

Lemma fgmulgDl : left_distributive fgmul +%R.
Proof.
move=> g1 g2 g; apply/esym; rewrite
  (fgmullwl (fsubsetUl _ (msupp g2)))
  (fgmullwl (fsubsetUr (msupp g1) _)).
rewrite -big_split /= (fgmullwl (msuppD_le _ _)).
apply/eq_bigr=> k1 _; rewrite -big_split /=; apply/eq_bigr.
by move=> k2 _; rewrite mcoeffD mulrDl monalgUD.
Qed.

Lemma fgmulgDr : right_distributive fgmul +%R.
Proof.
move=> g g1 g2; apply/esym; rewrite
  (fgmulrwl (fsubsetUl _ (msupp g2)))
  (fgmulrwl (fsubsetUr (msupp g1) _)).
rewrite -big_split /= (fgmulrwl (msuppD_le _ _)).
apply/eq_bigr=> k1 _; rewrite -big_split /=; apply/eq_bigr.
by move=> k2 _; rewrite mcoeffD mulrDr monalgUD.
Qed.

Lemma fgoner_eq0 : fgone != 0.
Proof. by apply/malgP=> /(_ 1%M) /eqP; rewrite !mcoeffsE oner_eq0. Qed.

Definition malg_ringMixin :=
  RingMixin fgmulA fgmul1g fgmulg1 fgmulgDl fgmulgDr fgoner_eq0.
Canonical  malg_ringType :=
  Eval hnf in RingType {malg R[K]} malg_ringMixin.
End MAlgRingType.

(* -------------------------------------------------------------------- *)
Section MAlgRingTheory.
Variable (K : monomType) (R : ringType).

Delimit Scope m_scope with M.

Implicit Types g       : {malg R[K]}.
Implicit Types c x y z : R.
Implicit Types k l     : K.

(* -------------------------------------------------------------------- *)
Lemma malgM_def g1 g2 : g1 * g2 = fgmul g1 g2.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma malgME g1 g2 :
  g1 * g2 = \sum_(k1 : msupp g1) \sum_(k2 : msupp g2)
    << g1@_(val k1) * g2@_(val k2) *g (val k1 * val k2)%M >>.
Proof. by []. Qed.

Lemma malgMEw (d1 d2 : {fset K}) g1 g2 :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 ->
  g1 * g2 = \sum_(k1 : d1) \sum_(k2 : d2)
    << g1@_(val k1) * g2@_(val k2) *g (val k1 * val k2)%M >>.
Proof. by apply/fgmullw. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeffMl g1 g2 k :
  (g1 * g2)@_k = \sum_(k1 : msupp g1) \sum_(k2 : msupp g2)
    (g1@_(val k1) * g2@_(val k2)) *+ (val k1 * val k2 == k)%M.
Proof. by apply/fgmulElw; apply/fsubset_refl. Qed.

Lemma mcoeffMr g1 g2 k :
  (g1 * g2)@_k = \sum_(k2 : msupp g2) \sum_(k1 : msupp g1)
    (g1@_(val k1) * g2@_(val k2)) *+ (val k1 * val k2 == k)%M.
Proof. by apply/fgmulErw; apply/fsubset_refl. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeffMlw (d1 d2 : {fset K}) g1 g2 k :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 ->
  (g1 * g2)@_k = \sum_(k1 : d1) \sum_(k2 : d2)
    (g1@_(val k1) * g2@_(val k2)) *+ (val k1 * val k2 == k)%M.
Proof. by apply/fgmulElw. Qed.

Lemma mcoeffMrw (d1 d2 : {fset K}) g1 g2 k :
  msupp g1 `<=` d1 -> msupp g2 `<=` d2 ->
  (g1 * g2)@_k = \sum_(k2 : d2) \sum_(k1 : d1)
    (g1@_(val k1) * g2@_(val k2)) *+ (val k1 * val k2 == k)%M.
Proof. by apply/fgmulErw. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeff1 k : 1@_k = (k == 1%M)%:R :> R.
Proof. by rewrite mcoeffC. Qed.

Lemma mul_malgC c g : c%:MP * g = c *: g.
Proof.
rewrite malgCE malgM_def malgZ_def (fgmulUg _ _ (fsubset_refl _)).
by apply/eq_bigr=> /= k _; rewrite mul1m.
Qed.

Lemma mcoeffCM c g k : (c%:MP * g)@_k = c * g@_k :> R.
Proof. by rewrite mul_malgC mcoeffZ. Qed.

(* -------------------------------------------------------------------- *)
Lemma msuppM_le g1 g2 k :
  k \in msupp (g1 * g2) ->
    exists k1 : msupp g1, exists k2 : msupp g2, k = (val k1 * val k2)%M.
Proof.
move=> k_in_g1Mg2; apply/(existsPP (fun _ => exists_eqP)).
apply/contraLR: k_in_g1Mg2=> hk; rewrite -mcoeff_eq0.
rewrite mcoeffMl big1 // => /= k1 _; rewrite big1 // => k2 _.
case: eqP=> // kE; case/negP: hk; apply/existsP.
by exists k1; apply/existsP; exists k2; rewrite kE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma malgC_is_multiplicative : multiplicative (@malgC K R).
Proof.
split=> // g1 g2; apply/eqP/malgP=> k.
by rewrite mcoeffCM !mcoeffC mulrnAr.
Qed.

Canonical malgC_rmorphism : {rmorphism R -> {malg R[K]}} :=
  AddRMorphism malgC_is_multiplicative.

(* -------------------------------------------------------------------- *)
Lemma mpolyC1E : 1%:MP = 1 :> {malg R[K]}.
Proof. exact: rmorph1. Qed.

Lemma mpolyC_nat (n : nat) : (n%:R)%:MP = n%:R :> {malg R[K]}.
Proof.
by apply/eqP/malgP=> i; rewrite mcoeffC mcoeffMn mcoeffC mulrnAC.
Qed.

Lemma mpolyCM : {morph @malgC K R : p q / p * q}.
Proof. exact: rmorphM. Qed.

(* -------------------------------------------------------------------- *)
Lemma mcoeff1g_is_multiplicative :
  multiplicative (mcoeff 1%M : {malg R[K]} -> R).
Proof.
split=> [g1 g2|]; rewrite ?malgCK //; pose_big_fset K E.
have E1: 1%M \in E by by rewrite -fsub1set.
rewrite (@malgMEw E E) // (bigD1 (FSetSub E1)) //=. 2: by close.
rewrite (bigD1 (FSetSub E1)) //= mulm1 2!mcoeffD mcoeffUU.
rewrite !raddf_sum !big1 ?simpm //= => k; rewrite -val_eqE /= => ne1_k.
  rewrite raddf_sum big1 ?mcoeff0 //= => k' _; rewrite mcoeffU.
  by case: eqP=> // /eqP /MonomialTheory.unitmP []; rewrite (negbTE ne1_k).
by rewrite mcoeffU mul1m (negbTE ne1_k).
Qed.

Canonical mcoeff1g_rmorphism := AddRMorphism mcoeff1g_is_multiplicative.
End MAlgRingTheory.

(* -------------------------------------------------------------------- *)
Section MalgLAlgType.
Variable (K : monomType) (R : ringType).

Implicit Types g       : {malg R[K]}.
Implicit Types c x y z : R.
Implicit Types k l     : K.

(* -------------------------------------------------------------------- *)
Lemma fgscaleAl c g1 g2 : c *: (g1 * g2) = (c *: g1) * g2.
Proof. by rewrite -!mul_malgC mulrA. Qed.

Canonical malg_lalgType :=
  Eval hnf in LalgType R {malg R[K]} fgscaleAl.

(* -------------------------------------------------------------------- *)
Canonical mcoeff1g_lrmorphism := [lrmorphism of mcoeff 1%M].
End MalgLAlgType.

(* -------------------------------------------------------------------- *)
Section MalgComRingType.
Variable (K : conomType) (R : comRingType).

Implicit Types g       : {malg R[K]}.
Implicit Types c x y z : R.
Implicit Types k l     : K.

Lemma fgmulC : @commutative {malg R[K]} _ *%R.
Proof.
move=> g1 g2; apply/eqP/malgP=> k; rewrite mcoeffMl mcoeffMr.
apply/eq_bigr=> /= k1 _; apply/eq_bigr=> /= k2 _.
by rewrite mulrC [X in X==k]mulmC.
Qed.

Canonical malg_comRingType :=
  Eval hnf in ComRingType {malg R[K]} fgmulC.
Canonical malg_algType :=
  Eval hnf in CommAlgType R {malg R[K]}.
End MalgComRingType.

(* -------------------------------------------------------------------- *)
Section MalgMorphism.
Section Defs.
Variables (K : choiceType) (G : zmodType) (S : ringType).
Variables (f : G -> S) (h : K -> S).

Definition mmap g := \sum_(k : msupp g) (f g@_(val k)) * (h (val k)).

Lemma mmapE g :
  mmap g = \sum_(k : msupp g) (f g@_(val k)) * (h (val k)).
Proof. by []. Qed.
End Defs.

Local Notation "g ^[ f , h ]" := (mmap f h g).

Section BaseTheory.
Variables (K : choiceType) (G : zmodType) (S : ringType).

Context {f : {additive G -> S}} {h : K -> S}.

Lemma mmapEw (d : {fset K}) g : msupp g `<=` d ->
  g^[f, h] = \sum_(k : d) (f g@_(val k)) * (h (val k)).
Proof.
move=> le; pose F k := (f g@_k) * (h k); rewrite mmapE.
rewrite (big_fset_incl F le) {}/F //= => k _ /mcoeff_outdom.
by move=> ->; rewrite raddf0 mul0r.
Qed.

Lemma mmapU (c : G) (m : K) :
  mmap f h << c *g m >> = (f c) * (h m).
Proof. by rewrite (mmapEw msuppU_le) big_fset1 mcoeffUU. Qed.
End BaseTheory.

Section Additive.
Variables (K : choiceType) (G : zmodType) (S : ringType).

Context {f : {additive G -> S}} {h : K -> S}.

Lemma mmap_is_additive : additive (mmap f h).
Proof.
move=> g1 g2 /=; pose_big_fset K E; rewrite 3?(mmapEw (d := E)) //.
  by rewrite -sumrB; apply/eq_bigr=> k _; rewrite !raddfB /= mulrBl.
by close.
Qed.

Canonical mmap_additive := Additive mmap_is_additive.

Local Notation mmap := (mmap f h).

Lemma mmap0     : mmap 0 = 0               . Proof. exact: raddf0. Qed.
Lemma mmapN     : {morph mmap: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mmapD     : {morph mmap: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mmapB     : {morph mmap: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mmapMn  n : {morph mmap: x / x *+ n} . Proof. exact: raddfMn. Qed.
Lemma mmapMNn n : {morph mmap: x / x *- n} . Proof. exact: raddfMNn. Qed.
End Additive.

Section CommrMultiplicative.
Variables (K : monomType) (R : ringType) (S : ringType).

Context {f : {rmorphism R -> S}} {h : {mmorphism K -> S}}.

Implicit Types g : {malg R[K]}.

Lemma mmapZ c (g : {malg R[K]}) : (c *: g)^[f,h] = (f c) * g^[f,h].
Proof.
rewrite (mmapEw (msuppZ_le _ _)) mmapE big_distrr /=.
by apply/eq_bigr=> k _; rewrite linearZ rmorphM /= mulrA.
Qed.

Lemma mmapC c : (c%:MP)^[f,h] = f c.
Proof. by rewrite mmapU mmorph1 mulr1. Qed.

Lemma mmap1 : 1^[f,h] = 1.
Proof. by rewrite mmapC rmorph1. Qed.

Hypothesis commr_f: forall g m m', GRing.comm (f g@_m) (h m').

Lemma commr_mmap_is_multiplicative: multiplicative (mmap f h).
Proof.
split=> [g1 g2|]; [pose_big_fset K E | by rewrite mmap1].
rewrite [_*_](malgMEw (d1 := E) (d2 := E)) //.
  apply/esym; rewrite 2?(mmapEw (d := E)) // raddf_sum /=.
  rewrite big_distrlr /=; apply/eq_bigr=> k1 _; rewrite raddf_sum /=.
  apply/eq_bigr=> k2 _; rewrite mmapU mmorphM /= rmorphM.
  by rewrite -mulrA [X in _*X=_]mulrA -commr_f !mulrA.
by close.
Qed.
End CommrMultiplicative.

(* -------------------------------------------------------------------- *)
Section Multiplicative.
Variables (K : monomType) (R : ringType) (S : comRingType).

Context {f : {rmorphism R -> S}} {h : {mmorphism K -> S}}.

Implicit Types g : {malg R[K]}.

Lemma mmap_is_multiplicative : multiplicative (mmap f h).
Proof. by apply/commr_mmap_is_multiplicative=> g m m'; apply/mulrC. Qed.

Canonical mmap_rmorphism := AddRMorphism mmap_is_multiplicative.
End Multiplicative.

(* -------------------------------------------------------------------- *)
Section Linear.
Variables (K : monomType) (R : comRingType).

Context {h : {mmorphism K -> R}}.

Lemma mmap_is_linear : scalable_for *%R (mmap idfun h).
Proof. by move=> /= c g; rewrite -mul_malgC rmorphM /= mmapC. Qed.

Canonical mmap_linear := AddLinear mmap_is_linear.
Canonical mmap_lrmorphism := [lrmorphism of mmap idfun h].
End Linear.
End MalgMorphism.

(* -------------------------------------------------------------------- *)
Section MonalgOver.
Section Def.
Context {K : choiceType} {G : zmodType}.

Definition monalgOver (S : pred_class) :=
  [qualify a g : {malg G[K]} |
     [forall m : msupp g, g@_(val m) \in S]].

Fact monalgOver_key S : pred_key (monalgOver S). Proof. by []. Qed.
Canonical monalgOver_keyed S := KeyedQualifier (monalgOver_key S).
End Def.

(* -------------------------------------------------------------------- *)
Section Theory.
Variables (K : choiceType) (G : zmodType).

Local Notation monalgOver := (@monalgOver K G).

Lemma monalgOverS (S1 S2 : pred_class) :
  {subset S1 <= S2} -> {subset monalgOver S1 <= monalgOver S2}.
Proof.
move=> le_S1S2 g /forallP /= S1g; apply/forallP.
by move=> /= x; apply/le_S1S2/S1g.
Qed.

Lemma monalgOverU c k S :
  << c *g k >> \in monalgOver S = (c == 0) || (c \in S).
Proof.
rewrite qualifE msuppU; case: (c =P 0)=> [->|] /=.
  by apply/forallP=> [[k']]; rewrite /= monalgU0 in_fset0.
move=> nz_c; apply/forallP/idP=> /= h.
  by move/(_ (FSetSub (fset11 k))): h; rewrite mcoeffUU.
by case=> /= k'; rewrite in_fset1=> /eqP->; rewrite mcoeffUU.
Qed.

Lemma monalgOver0 S: 0 \is a monalgOver S.
Proof.
rewrite qualifE msupp0; apply/forallP=> //=.
by case=> /= x; rewrite in_fset0.
Qed.
End Theory.

(* -------------------------------------------------------------------- *)
Section MonalgOverAdd.
Variables (K : choiceType) (G : zmodType).
Variables (S : predPredType G) (addS : addrPred S) (kS : keyed_pred addS).

Implicit Types c : G.
Implicit Types g : {malg G[K]}.

Local Notation monalgOver := (@monalgOver K G).

Lemma monalgOverP {g} :
  reflect (forall m, g@_m \in kS) (g \in monalgOver kS).
Proof.
apply: (iffP forallP)=> /= h k; last by rewrite h.
by case: msuppP=> [kg|]; rewrite ?rpred0 // (h (FSetSub kg)).
Qed.

Lemma monalgOver_addr_closed : addr_closed (monalgOver kS).
Proof.
split=> [|g1 g2 Sg1 Sg2]; rewrite ?monalgOver0 //.
by apply/monalgOverP=> m; rewrite mcoeffD rpredD ?(monalgOverP _).
Qed.

Canonical monalgOver_addrPred := AddrPred monalgOver_addr_closed.
End MonalgOverAdd.

(* -------------------------------------------------------------------- *)
Section MonalgOverOpp.
Variables (K : choiceType) (G : zmodType).
Variables (S : predPredType G) (zmodS : zmodPred S) (kS : keyed_pred zmodS).

Implicit Types c : G.
Implicit Types g : {malg G[K]}.

Local Notation monalgOver := (@monalgOver K G).

Lemma monalgOver_oppr_closed : oppr_closed (monalgOver kS).
Proof.
move=> g Sg; apply/monalgOverP=> n; rewrite mcoeffN.
by rewrite rpredN; apply/(monalgOverP kS).
Qed.

Canonical monalgOver_opprPred := OpprPred monalgOver_oppr_closed.
Canonical monalgOver_zmodPred := ZmodPred monalgOver_oppr_closed.
End MonalgOverOpp.

(* -------------------------------------------------------------------- *)
Section MonalgOverSemiring.
Variables (K : monomType) (R : ringType).
Variables (S : predPredType R) (ringS : semiringPred S) (kS : keyed_pred ringS).

Implicit Types c : R.
Implicit Types g : {malg R[K]}.

Local Notation monalgOver := (@monalgOver K R).

Lemma monalgOverC c : (c%:MP \in monalgOver kS) = (c \in kS).
Proof. by rewrite monalgOverU; case: eqP=> // ->; rewrite rpred0. Qed.

Lemma monalgOver1 : 1 \in monalgOver kS.
Proof. by rewrite monalgOverC rpred1. Qed.

Lemma monalgOver_mulr_closed : mulr_closed (monalgOver kS).
Proof.
split=> [|g1 g2 /monalgOverP Sg1 /monalgOverP sS2].
  by rewrite monalgOver1.
apply/monalgOverP=> m; rewrite mcoeffMl rpred_sum //=.
move=> k1 _; rewrite rpred_sum // => k2 _.
by case: eqP; rewrite ?mulr0n (rpred0, rpredM).
Qed.

Canonical monalgOver_mulrPred := MulrPred monalgOver_mulr_closed.
Canonical monalgOver_semiringPred := SemiringPred monalgOver_mulr_closed.

Lemma monalgOverZ :
  {in kS & monalgOver kS, forall c g, c *: g \is a monalgOver kS}.
Proof.
move=> c g Sc Sg; apply/monalgOverP=> k.
by rewrite mcoeffZ rpredM //; apply/(monalgOverP kS).
Qed.

Lemma rpred_meval :
  {in monalgOver kS, forall g (v : K -> R),
     (forall x, v x \in kS) -> mmap idfun v g \in kS}.
Proof.
move=> g /monalgOverP Sg v Sv; rewrite mmapE rpred_sum //.
by move=> /= k; rewrite rpredM.
Qed.
End MonalgOverSemiring.

Section MonalgOverRing.
Variables (K : monomType) (R : ringType).
Variables (S : predPredType R) (ringS : subringPred S) (kS : keyed_pred ringS).

Canonical monalgOver_smulrPred := SmulrPred (monalgOver_mulr_closed K kS).
Canonical monalgOver_subringPred := SubringPred (monalgOver_mulr_closed K kS).
End MonalgOverRing.
End MonalgOver.

(* -------------------------------------------------------------------- *)
Section MMeasureDef.
Variable M : monomType.

Structure measure := Measure {
  mf : M -> nat;
  _  : mf 1%M = 0%N;
  _  : {morph mf : m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N};
  _  : forall m, mf m = 0%N -> m = 1%M
}.

Coercion mf : measure >-> Funclass.

Let measure_id (mf1 mf2 : M -> nat) := phant_id mf1 mf2.

Definition clone_measure mf :=
  fun (mfL : measure) & measure_id mfL mf =>
  fun mf1 mfM mfT (mfL' := @Measure mf mf1 mfM mfT)
    & phant_id mfL' mfL => mfL'.
End MMeasureDef.

Notation "[ 'measure' 'of' f ]" := (@clone_measure _ f _ id _ _ _ id)
  (at level 0, format"[ 'measure'  'of'  f ]") : form_scope.

(* -------------------------------------------------------------------- *)
Section MMeasure.
Variable M : monomType.
Variable G : zmodType.

Implicit Types m : M.
Implicit Types g : {malg G[M]}.

Variable mf : measure M.

Lemma mf0 : mf 1%M = 0%N.
Proof. by case: mf. Qed.

Lemma mfM : {morph mf : m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N}.
Proof. by case: mf. Qed.

Lemma mf_eq0I m : mf m = 0%N -> m = 1%M.
Proof. by case: mf=> mf' _ _ h /= mf0; apply/h. Qed.

Lemma mf_eq0 m : (mf m == 0%N) = (m == 1%M).
Proof. by apply/eqP/eqP=> [|->]; rewrite ?mf0 // => /mf_eq0I. Qed.

Definition mmeasure g := (\max_(m : msupp g) (mf (val m)).+1)%N.

Lemma mmeasureE g : mmeasure g = (\max_(m : msupp g) (mf (val m)).+1)%N.
Proof. by []. Qed.

Lemma mmeasure0 : mmeasure 0 = 0%N.
Proof. by rewrite mmeasureE msupp0 big_fset0. Qed.

Lemma mmeasure_mnm_lt g m : m \in msupp g -> (mf m < mmeasure g)%N.
Proof.
move=> km; rewrite mmeasureE (bigD1 (FSetSub km)) //=.
by rewrite leq_max ltnS leqnn.
Qed.

Lemma mmeasure_mnm_ge g m : (mmeasure g <= mf m)%N -> m \notin msupp g.
Proof. by apply/contraTN=> /mmeasure_mnm_lt; rewrite leqNgt ltnS. Qed.

Lemma mmeasureC c : mmeasure c%:MP = (c != 0%R) :> nat.
Proof.
rewrite mmeasureE msuppC; case: (_ == 0)=> /=.
by rewrite big_fset0. by rewrite big_fset1 mf0.
Qed.

Lemma mmeasureN g : mmeasure (-g) = mmeasure g.
Proof. by rewrite mmeasureE msuppN. Qed.

Lemma mmeasureD_le g1 g2 :
  (mmeasure (g1 + g2) <= maxn (mmeasure g1) (mmeasure g2))%N.
Proof.
rewrite {1}mmeasureE; apply/bigmax_leqP=> [[i ki]] _ /=.
have /fsubsetP /(_ i ki) := (msuppD_le g1 g2); rewrite in_fsetU.
by rewrite leq_max; case/orP=> /mmeasure_mnm_lt->; rewrite !simpm.
Qed.

Lemma mmeasure_sum (T : Type) (r : seq _) (F : T -> {malg G[M]}) (P : pred T) :
  (mmeasure (\sum_(i <- r | P i) F i) <= \max_(i <- r | P i) mmeasure (F i))%N.
Proof.
elim/big_rec2: _ => /= [|i k p _ le]; first by rewrite mmeasure0.
apply/(leq_trans (mmeasureD_le _ _)); rewrite geq_max.
by rewrite leq_maxl /= leq_max le orbC.
Qed.

Lemma mmeasure_eq0 g : (mmeasure g == 0%N) = (g == 0).
Proof.
apply/idP/eqP=> [z_g|->]; last by rewrite mmeasure0.
apply/eqP/malgP=> k; rewrite mcoeff0; apply/contraTeq: z_g.
rewrite mcoeff_neq0 => kg; rewrite mmeasureE.
by rewrite (bigD1 (FSetSub kg)) //= -lt0n leq_max.
Qed.

Lemma malgSpred g : g != 0 -> mmeasure g = (mmeasure g).-1.+1.
Proof. by rewrite -mmeasure_eq0 -lt0n => /prednK. Qed.

Lemma mmeasure_msupp0 g : (mmeasure g == 0%N) = (msupp g == fset0).
Proof. by rewrite mmeasure_eq0 msupp_eq0. Qed.
End MMeasure.

(* -------------------------------------------------------------------- *)
Section ComMonomial.
Section Def.
Variable (I : choiceType).

Inductive cmonom : predArgType := CMonom of {fsfun I -> nat / 0%N}.

Definition cmonom_val m := let: CMonom m := m in m.
Definition cmonom_of (_ : phant I) := cmonom.

Coercion cmonom_val : cmonom >-> fsfun_of.

Fact cmonom_key : unit. Proof. by []. Qed.

Definition cmonom_of_fsfun   k := locked_with k CMonom.
Canonical  cmonom_unlockable k := [unlockable fun cmonom_of_fsfun k].
End Def.

Local Notation "{ 'cmonom' I }" :=
  (@cmonom_of _ (Phant I)) : type_scope.
Local Notation "''X_{1..' n '}'" :=
  {cmonom 'I_n} : type_scope.

Local Notation mkcmonom m := (cmonom_of_fsfun cmonom_key m).

(* -------------------------------------------------------------------- *)
Section Canonicals.
Variable (I : choiceType).

Canonical  cmonomType := Eval hnf in [newType for (@cmonom_val I)].
Definition cmonom_eqMixin := Eval hnf in [eqMixin of {cmonom I} by <:].
Definition cmonom_choiceMixin := Eval hnf in [choiceMixin of {cmonom I} by <:].

Canonical cmonom_eqType :=
  Eval hnf in EqType (cmonom I) cmonom_eqMixin.
Canonical cmonom_choiceType :=
  Eval hnf in ChoiceType (cmonom I) cmonom_choiceMixin.

Canonical cmonomof_eqType :=
  Eval hnf in EqType {cmonom I} cmonom_eqMixin.
Canonical cmonomof_choiceType :=
  Eval hnf in ChoiceType {cmonom I} cmonom_choiceMixin.
End Canonicals.

(* -------------------------------------------------------------------- *)
Section Structures.
Context {I : choiceType}.

Implicit Types m : {cmonom I}.
Implicit Types i j : I.

Lemma cmE (f : {fsfun I -> nat / 0%N}) : mkcmonom f =1 CMonom f.
Proof. by move=> i; rewrite unlock. Qed.

Lemma cmP m1 m2 : reflect (forall i, m1 i = m2 i) (m1 == m2).
Proof.
apply: (iffP eqP)=> [->//|]; case: m1 m2 => [m1] [m2] eq.
by apply/val_eqP/fsfunP=> i; rewrite eq.
Qed.

Definition cmone : {cmonom I} :=
  mkcmonom [fsfun [fmap]].

Definition cmu i : {cmonom I} :=
  mkcmonom [fsfun [fmap].[i <- 1%N]].

Definition cmmul m1 m2 : {cmonom I} := mkcmonom [fsfun
  [fmap i : domf m1 `|` domf m2 => (m1 (val i) + m2 (val i))%N]].

Lemma cmoneE i : cmone i = 0%N.
Proof. by rewrite cmE fsfun_fnd fnd_fmap0. Qed.

Lemma cmuE i j : (cmu i) j = (i == j) :> nat.
Proof. by rewrite cmE fsfun_fnd fnd_set eq_sym fnd_fmap0; case: eqP. Qed.

Lemma cmmulE m1 m2 i : (cmmul m1 m2) i = (m1 i + m2 i)%N.
Proof.
rewrite cmE (fsfunE _ _ (fun i => m1 i + m2 i)%N) in_fsetE.
by case: (fsfunEP m1); case: (fsfunEP m2).
Qed.

Let cmE := (cmoneE, cmmulE).

Lemma cmmulA : associative cmmul.
Proof. by move=> m1 m2 m3; apply/eqP/fsfunP=> i; rewrite !cmE addnA. Qed.

Lemma cmmulC : commutative cmmul.
Proof. by move=> m1 m2; apply/eqP/cmP=> i; rewrite !cmE addnC. Qed.

Lemma cmmul0m : left_id cmone cmmul.
Proof. by move=> m; apply/eqP/cmP=> i; rewrite !cmE add0n. Qed.

Lemma cmmulm0 : right_id cmone cmmul.
Proof. by move=> m; apply/eqP/cmP=> i; rewrite !cmE addn0. Qed.

Lemma cmmul_eq0 m1 m2 : cmmul m1 m2 = cmone -> m1 = cmone /\ m2 = cmone.
Proof.
move: m1 m2; have gen m1 m2 : cmmul m1 m2 = cmone -> m1 = cmone.
  move/eqP/fsfunP=> h; apply/eqP/fsfunP=> i; move/(_ i)/eqP: h.
  by rewrite !cmE addn_eq0 => /andP[] /eqP->.
by move=> m1 m2 h; split; move: h; last rewrite cmmulC; apply/gen.
Qed.

Definition cmonom_monomMixin :=
  MonomMixin cmmulA cmmul0m cmmulm0 cmmul_eq0.
Canonical cmonom_monomType :=
  Eval hnf in MonomType {cmonom I} cmonom_monomMixin.
Canonical cmonom_conomType :=
  Eval hnf in ConomType {cmonom I} cmmulC.
End Structures.

(* -------------------------------------------------------------------- *)
Definition mdeg {I : choiceType} (m : {cmonom I}) :=
  nosimpl (\sum_(k : domf m) (m (val k)))%N.

Definition mnmwgt {n} (m : {cmonom 'I_n}) :=
  nosimpl (\sum_i m i * i.+1)%N.

(* -------------------------------------------------------------------- *)
Section Theory.
Context {I : choiceType}.

Implicit Types m : {cmonom I}.

Local Notation "'U_(' i )" := (@cmu I i).
Local Notation mdeg := (@mdeg I).

Lemma cm1 i : (1%M : {cmonom I}) i = 0%N.
Proof. by apply/cmoneE. Qed.

Lemma cmU i j : U_(i) j = (i == j) :> nat.
Proof. by apply/cmuE. Qed.

Lemma cmUU i : U_(i) i = 1%N.
Proof. by rewrite cmU eqxx. Qed.

Lemma cmM i m1 m2 : (m1 * m2)%M i = (m1 i + m2 i)%N.
Proof. by apply/cmmulE. Qed.

Lemma cmE_eq0 m i : (m i == 0%N) = (i \notin domf m).
Proof. by apply/fsfun_eqdfl. Qed.

Lemma cmE_neq0 m i : (m i != 0%N) = (i \in domf m).
Proof. by rewrite cmE_eq0 negbK. Qed.

CoInductive mdom_spec m (i : I) : bool -> nat -> Type :=
| MdomIn  (_ : i \in    domf m) : mdom_spec m i true  (m i)
| MdomOut (_ : i \notin domf m) : mdom_spec m i false 0%N.

Lemma mdomP m i : mdom_spec m i (i \in domf m) (m i).
Proof. by case: fsfunEP; constructor. Qed.

Lemma mdom1 : domf (1 : {cmonom I})%M = fset0 :> {fset I}.
Proof. by apply/fsetP=> i; rewrite in_fset0 -cmE_neq0 cm1 eqxx. Qed.

Lemma mdomU i : domf U_(i) = [fset i].
Proof. by apply/fsetP=> j; rewrite -!cmE_neq0 cmU in_fset1 eqb0 negbK. Qed.

Lemma mdomD m1 m2 : domf (m1 * m2)%M = domf m1 `|` domf m2.
Proof.
apply/fsetP=> i; rewrite in_fsetU -!cmE_neq0 cmM.
by rewrite addn_eq0 negb_and.
Qed.

Lemma mdegE m : mdeg m = (\sum_(i : domf m) (m (val i)))%N.
Proof. by []. Qed.

Lemma mdegEw m (d : {fset I}) : domf m `<=` d ->
  mdeg m = (\sum_(i : d) (m (val i)))%N.
Proof. 
move=> le; pose F i := m i; rewrite mdegE (big_fset_incl F le) //.
by move=> i i_in_d; rewrite -cmE_neq0 negbK => /eqP.
Qed.

Lemma mdeg1 : mdeg 1%M = 0%N.
Proof. by rewrite mdegE mdom1 big_fset0. Qed.

Lemma mdegU k : mdeg U_(k) = 1%N.
Proof. by rewrite mdegE mdomU big_fset1 cmUU. Qed.

Lemma mdegM : {morph mdeg: m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N }.
Proof.
move=> m1 m2 /=; rewrite mdegE mdomD.
rewrite (mdegEw (fsubsetUl _ (domf m2))) (mdegEw (fsubsetUr (domf m1) _)).
by rewrite -big_split /=; apply/eq_bigr=> /= i _; rewrite cmM.
Qed.

Lemma mdeg_prod (T : Type) r P (F : T -> {cmonom I}) :
    mdeg (\big[mmul/1%M]_(x <- r | P x) (F x))
  = (\sum_(x <- r | P x) (mdeg (F x)))%N.
Proof. by apply/big_morph; [apply/mdegM|apply/mdeg1]. Qed.

Lemma mdeg_eq0I m : mdeg m = 0%N -> m = 1%M.
Proof.
move=> h; apply/eqP/cmP=> i; move: h; rewrite mdegE cm1.
case: mdomP=> // ki; rewrite (bigD1 (FSetSub ki)) //= => /eqP.
by rewrite addn_eq0=> /andP[/eqP->].
Qed.

(* -------------------------------------------------------------------- *)
Canonical mdeg_measure := Eval hnf in @Measure [monomType of {cmonom I}]
  mdeg mdeg1 mdegM mdeg_eq0I.

Lemma mdeg_eq0 m : (mdeg m == 0%N) = (m == 1%M).
Proof. by apply/mf_eq0. Qed.

Lemma cmM_eq1 m1 m2 : (m1 * m2 == 1)%M = (m1 == 1%M) && (m2 == 1%M).
Proof. by rewrite -!mdeg_eq0 mdegM addn_eq0. Qed.

Lemma cm1_eq1 i : (U_(i) == 1)%M = false.
Proof. by rewrite -mdeg_eq0 mdegU. Qed.
End Theory.

(* -------------------------------------------------------------------- *)
Section MWeight.
Variable (n : nat).

Implicit Types m : 'X_{1..n}.

Local Notation mnmwgt := (@mnmwgt n).
Local Notation "'U_(' i )" := (@cmu [choiceType of 'I_n] i).

Lemma mnmwgtE m : mnmwgt m = (\sum_i m i * i.+1)%N.
Proof. by []. Qed.

Lemma mnmwgt1 : mnmwgt 1%M = 0%N.
Proof. by rewrite mnmwgtE big1 // => /= i _; rewrite cm1. Qed.

Lemma mnmwgtU i : mnmwgt U_(i) = i.+1.
Proof.
rewrite mnmwgtE (bigD1 i) //= cmUU mul1n big1 ?addn0 //.
by move=> j ne_ij; rewrite cmU eq_sym (negbTE ne_ij).
Qed.

Lemma mnmwgtM : {morph mnmwgt: m1 m2 / (m1 * m2)%M >->  (m1 + m2)%N}.
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
Canonical mnmwgt_measure := Eval hnf in @Measure [monomType of 'X_{1..n}]
  mnmwgt mnmwgt1 mnmwgtM mnmwgt_eq0I.

Lemma mnmwgt_eq0 m : (mnmwgt m == 0%N) = (m == 1%M).
Proof. by apply/mf_eq0. Qed.
End MWeight.
End ComMonomial.

(* -------------------------------------------------------------------- *)
Section FreeMonomial.
Section Def.
Variable (I : choiceType).

Inductive fmonom : predArgType := FMonom of seq I.

Definition fmonom_val m := let: FMonom m := m in m.
Definition fmonom_of (_ : phant I) := fmonom.

Coercion fmonom_val : fmonom >-> seq.

Fact fmonom_key : unit. Proof. by []. Qed.

Definition fmonom_of_seq     k := locked_with k FMonom.
Canonical  fmonom_unlockable k := [unlockable fun fmonom_of_seq k].
End Def.

Local Notation "{ 'fmonom' I }" :=
  (@fmonom_of _ (Phant I)) : type_scope.

Local Notation mkfmonom s :=
  (fmonom_of_seq fmonom_key s).

(* -------------------------------------------------------------------- *)
Section Canonicals.
Variable (I : choiceType).

Canonical  fmonomType := Eval hnf in [newType for (@fmonom_val I)].
Definition fmonom_eqMixin := Eval hnf in [eqMixin of {fmonom I} by <:].
Definition fmonom_choiceMixin := Eval hnf in [choiceMixin of {fmonom I} by <:].

Canonical fmonom_eqType :=
  Eval hnf in EqType (fmonom I) fmonom_eqMixin.
Canonical fmonomof_eqType :=
  Eval hnf in EqType {fmonom I} fmonom_eqMixin.

Canonical fmonom_choiceType :=
  Eval hnf in ChoiceType (fmonom I) fmonom_choiceMixin.
Canonical fmonomof_choiceType :=
  Eval hnf in ChoiceType {fmonom I} fmonom_choiceMixin.
End Canonicals.

(* -------------------------------------------------------------------- *)
Section Structures.
Context {I : choiceType}.

Implicit Types m : {fmonom I}.
Implicit Types i j : I.

Lemma fmE (s : seq I) : mkfmonom s = FMonom s.
Proof. by rewrite unlock. Qed.

Lemma fmP m1 m2 : (m1 == m2) = (m1 == m2 :> seq I).
Proof. by rewrite val_eqE. Qed.

Lemma fmK m : FMonom m = m.
Proof. by apply/innew_val. Qed.

Definition fmone : {fmonom I} := mkfmonom [::].
Definition fmu i : {fmonom I} := mkfmonom [:: i].
Definition fmmul m1 m2 : {fmonom I} := mkfmonom (m1 ++ m2).

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
Proof.
rewrite !fmE; case=> /(congr1 size)/eqP; rewrite size_cat.
rewrite addn_eq0 !size_eq0 => /andP[/eqP zm1 /eqP zm2].
by split; apply/val_eqP; rewrite /= ?(zm1, zm2).
Qed.

Definition fmonom_monomMixin :=
  MonomMixin fmmulA fmmul1m fmmulm1 fmmul_eq1.
Canonical fmonom_monomType :=
  Eval hnf in MonomType {fmonom I} fmonom_monomMixin.
End Structures.

(* -------------------------------------------------------------------- *)
Definition fdeg (I : choiceType) (m : {fmonom I}) :=
  nosimpl (size m).

(* -------------------------------------------------------------------- *)
Section Theory.
Context {I : choiceType}.

Implicit Types m : {fmonom I}.
Implicit Types i j : I.

Local Notation "'U_(' i )" := (@fmu I i).
Local Notation fdeg := (@fdeg I).

Lemma fm1 : (1%M : {fmonom I}) = [::] :> seq I.
Proof. by rewrite /mone /= fmoneE. Qed.

Lemma fmU i : U_(i) = [:: i] :> seq I.
Proof. by rewrite fmuE. Qed.

Lemma fmM m1 m2 : (m1 * m2)%M = (m1 ++ m2) :> seq I.
Proof. by rewrite /mmul /= fmmulE. Qed.

Lemma fdegE m : fdeg m = size m.
Proof. by []. Qed.

Lemma fdeg1 : fdeg 1%M = 0%N.
Proof. by rewrite fdegE fm1. Qed.

Lemma fdegU k : fdeg U_(k) = 1%N.
Proof. by rewrite fdegE fmU. Qed.

Lemma fdegM : {morph fdeg: m1 m2 / (m1 * m2)%M >-> (m1 + m2)%N }.
Proof. by move=> m1 m2; rewrite !fdegE fmM size_cat. Qed.

Lemma fdeg_prod (T : Type) r P (F : T -> {fmonom I}) :
    fdeg (\big[mmul/1%M]_(x <- r | P x) (F x))
  = (\sum_(x <- r | P x) (fdeg (F x)))%N.
Proof. by apply/big_morph; [apply/fdegM|apply/fdeg1]. Qed.

Lemma fdeg_eq0I m : fdeg m = 0%N -> m = 1%M.
Proof.
rewrite fdegE => /size0nil z_m; apply/eqP.
by rewrite -val_eqE /= z_m fm1.
Qed.

(* -------------------------------------------------------------------- *)
Canonical fdeg_measure :=
  Eval hnf in @Measure [monomType of {fmonom I}] fdeg fdeg1 fdegM fdeg_eq0I.

Lemma fdeg_eq0 m : (fdeg m == 0%N) = (m == 1%M).
Proof. by apply/mf_eq0. Qed.

Lemma fmM_eq1 m1 m2 : (m1 * m2 == 1)%M = (m1 == 1%M) && (m2 == 1%M).
Proof. by rewrite -!fdeg_eq0 fdegM addn_eq0. Qed.

Lemma fm1_eq1 i : (U_(i) == 1)%M = false.
Proof. by rewrite -fdeg_eq0 fdegU. Qed.
End Theory.
End FreeMonomial.

(* -------------------------------------------------------------------- *)
Notation "{ 'cmonom' I }" := (@cmonom_of _ (Phant I)) : type_scope.
Notation "{ 'fmonom' I }" := (@fmonom_of _ (Phant I)) : type_scope.
Notation "''X_{1..' n '}'" :=  {cmonom 'I_n} : type_scope.
Notation "{ 'mpoly' R [ n ] }" := {malg R['X_{1..n}]} : type_scope.

Notation "'U_(' i )" := (@cmu _ i) : m_scope.

Notation msize   g := (@mmeasure _ _ [measure of mdeg]   g).
Notation mweight g := (@mmeasure _ _ [measure of mnmwgt] g).

(* -------------------------------------------------------------------- *)
Section MSize.
Variable I : choiceType.
Variable G : zmodType.

Implicit Types m : {cmonom I}.
Implicit Types g : {malg G[{cmonom I}]}.

Local Notation mdeg := (@mdeg I).

Lemma msizeE g : msize g = (\max_(m : msupp g) (mdeg (val m)).+1)%N.
Proof. by apply/mmeasureE. Qed.

Lemma msize_mdeg_lt g m : m \in msupp g -> (mdeg m < msize g)%N.
Proof. by apply/mmeasure_mnm_lt. Qed.

Lemma msize_mdeg_ge g m : (msize g <= mdeg m)%N -> m \notin msupp g.
Proof. by apply/mmeasure_mnm_ge. Qed.

Definition msize0       := @mmeasure0       _ G [measure of mdeg].
Definition msizeC       := @mmeasureC       _ G [measure of mdeg].
Definition msizeD_le    := @mmeasureD_le    _ G [measure of mdeg].
Definition msize_sum    := @mmeasure_sum    _ G [measure of mdeg].
Definition msizeN       := @mmeasureN       _ G [measure of mdeg].
Definition msize_eq0    := @mmeasure_eq0    _ G [measure of mdeg].
Definition msize_msupp0 := @mmeasure_msupp0 _ G [measure of mdeg].
End MSize.
