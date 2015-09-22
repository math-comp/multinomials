(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
Local Open Scope fmap.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'fsfun' K -> T / x }"
  (at level 0, K, T, x at level 2, format "{ 'fsfun'  K  ->  T  /  x }").
Reserved Notation "[ 'fsfun' g ]"
  (at level 0, g at level 2, format "[ 'fsfun'  g ]").
Reserved Notation "[ 'fsfun' g / x ]"
  (at level 0, g, x at level 2, format "[ 'fsfun'  g  /  x ]").

(* -------------------------------------------------------------------- *)
Section FinSuppFunDef.
Variable K : choiceType.
Variable T : eqType.
Variable x : T. 

Definition canonical_fsfun (g : {fmap K -> T}) :=
  [forall k : domf g, g k != x].

Record fsfun : Type := mkFsfun {
  map_of_fsfun : {fmap K -> T};
  _ : canonical_fsfun map_of_fsfun
}.

Definition fsfun_of (_ : phant K) (_ : phant T) := fsfun.

Definition finMap_of_fsfun (g : fsfun) : finMap _ _ :=
  map_of_fsfun g.

Definition fun_of_fsfun (g : fsfun) : K -> T :=
  fun k => odflt x (map_of_fsfun g).[?k].

Coercion fun_of_fsfun : fsfun >-> Funclass.

Coercion map_of_fsfun    : fsfun >-> finmap_of.
Coercion finMap_of_fsfun : fsfun >-> finMap.
End FinSuppFunDef.

Identity Coercion type_of_fsfun : fsfun_of >-> fsfun.

Fact fsfun_key : unit. Proof. by []. Qed.

Definition pred_of_fsfun
  (K : choiceType) (T : eqType) (x : T) (g : @fsfun K T x) : pred K :=
  fun k => k \in locked_with finset_key (map_of_fsfun g).

Canonical fsfunPredType (K : choiceType) (T : eqType) (x : T) :=
  Eval hnf in mkPredType (@pred_of_fsfun K T x).

Notation "{ 'fsfun' K -> T / x }" :=
  (@fsfun_of _ _ x (Phant K) (Phant T)) : type_scope.

(* -------------------------------------------------------------------- *)
Section FsfunCanonicals.
Variable (K : choiceType) (T : eqType) (x : T).

Canonical  fsfunType := Eval hnf in [subType for (@map_of_fsfun K T x)].
Definition fsfun_eqMixin := Eval hnf in [eqMixin of {fsfun K -> T / x} by <:].
Canonical  fsfun_eqType := Eval hnf in EqType {fsfun K -> T / x} fsfun_eqMixin.
End FsfunCanonicals.

(* -------------------------------------------------------------------- *)
Section FsfunChoice.
Variable (K : choiceType) (T : choiceType) (x : T).

Definition fsfun_choiceMixin :=
  Eval hnf in [choiceMixin of {fsfun K -> T / x} by <:].
Canonical  fsfun_choiceType :=
  Eval hnf in ChoiceType {fsfun K -> T / x } fsfun_choiceMixin.
End FsfunChoice.

(* -------------------------------------------------------------------- *)
Section MkFsfun.
Variable (K : choiceType) (T : eqType) (x : T).

Definition fsfun_reduce (g : {fmap K -> T}) : {fmap K -> T} :=
  g.[\ [fset k : domf g | g k == x]].

Lemma canonical_fsfun_reduce (g : {fmap K -> T}) :
  canonical_fsfun x (fsfun_reduce g).
Proof.
apply/forallP=> [[y y_in_rg]]; have := y_in_rg; rewrite mem_remf.
case/andP=> [nz_gy y_in_g]; rewrite getf_restrict //.
by apply/contra: nz_gy=> z_gy; rewrite in_FSet /=.
Qed.

Definition mkfsfun (g : {fmap K -> T}) : {fsfun K -> T / x} :=
  mkFsfun (canonical_fsfun_reduce g).

Lemma mkfsfunE (g : {fmap K -> T}) :
  mkfsfun g = fsfun_reduce g :> {fmap K -> T}.
Proof. by apply/fmapP. Qed.
End MkFsfun.

(* -------------------------------------------------------------------- *)
Notation "[ 'fsfun' g  / x ]" := (mkfsfun x g) : fun_scope.
Notation "[ 'fsfun' g ]" := (mkfsfun _ g) : fun_scope.
