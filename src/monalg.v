(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun finmap tuple bigop ssralg ssrint.
Require Import fsfun ssrcomplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Monoid GRing.Theory.

Local Open Scope fset.
Local Open Scope fmap.
Local Open Scope ring_scope.

Delimit Scope malg_scope with MP.

Local Notation simpm := Monoid.simpm.
Local Notation ilift := fintype.lift.

Local Notation efst := (@fst _ _) (only parsing).
Local Notation esnd := (@snd _ _) (only parsing).

Local Infix "@@" := product (at level 60, right associativity).
Local Notation widen := (widen_ord (leqnSn _)).

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'malg' G [ K ] }"
  (at level 0, K, G at level 2, format "{ 'malg'  G [ K ] }").
Reserved Notation "{ 'malg' K }"
  (at level 0, K at level 2, format "{ 'malg'  K }").
Reserved Notation "[ 'malg' g ]"
  (at level 0, g at level 2, format "[ 'malg'  g ]").
Reserved Notation "[ 'malg' x : aT => E ]"
  (at level 0, x ident, format "[ 'malg'  x : aT  =>  E ]").
Reserved Notation "<< z *p k >>"
  (at level 0).
Reserved Notation "<< k >>"
  (at level 0).
Reserved Notation "g @_ k"
  (at level 3, k at level 2, left associativity, format "g @_ k").

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

Definition mkmalg (g : {fsfun K -> G / 0}) : {malg G[K]} := Malg g.
End MkMalg.

(* -------------------------------------------------------------------- *)
Notation "[ 'malg' g ]"
  := (mkmalg [fsfun g / 0]) : ring_scope.
Notation "[ 'malg' x : aT => E ]"
  := (mkmalg [fsfun [fmap x : aT => E] / 0]) : ring_scope.
Notation "<< z *g k >>"
  := [malg [fmap].[k <- z]] : ring_scope.
Notation "<< k >>"
  := << 1 *g k >> : ring_scope.

(* -------------------------------------------------------------------- *)
Section MalgSupp.
Variable (K : choiceType) (G : zmodType).

Definition msupp (g : {malg G[K]}) :=
  nosimpl (domf (malg_val g)).

Definition mcoeff (x : K) (g : {malg G[K]}) :=
  nosimpl (malg_val g x).
End MalgSupp.

Notation "g @_ k" := (mcoeff k g).

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
Proof.
case: g; elim/fsfunW=> g; rewrite mcoeff_fnd /msupp domf_fsfunE.
case: fndP=> kf /=; first have: k = val (FSetSub kf) by [].
  by move=> {2}->; rewrite val_in_FSet -topredE /= negbK.
by rewrite eqxx; apply/esym/imfsetP=> h; case: h kf=> [[y]] ? _ -> /negP.
Qed.

Lemma mcoeff_neq0 (g : {malg G[K]}) (k : K) :
  (g@_k != 0) = (k \in msupp g).
Proof. by rewrite mcoeff_eq0 negbK. Qed.

Lemma mcoeff_outdom (g : {malg G[K]}) (k : K) :
  k \notin msupp g -> g@_k = 0.
Proof. by rewrite -mcoeff_eq0=> /eqP. Qed.

CoInductive msupp_spec (g : {malg G[K]}) (k : K) : bool -> G -> Type :=
| MsuppIn  (_ : k \in    msupp g) : msupp_spec g k true  g@_k
| MsuppOut (_ : k \notin msupp g) : msupp_spec g k false 0.

Lemma msuppP (g : {malg G[K]}) (k : K) : msupp_spec g k (k \in msupp g) g@_k.
Proof.
case: (boolP (k \in msupp g)); first by apply/MsuppIn.
by move=> k_notin_g; rewrite (mcoeff_outdom k_notin_g); apply/MsuppOut.
Qed.
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

(* -------------------------------------------------------------------- *)
Lemma mcoeff_is_additive k: additive (mcoeff k).
Proof. by move=> g1 g2 /=; rewrite !fgE. Qed.

Canonical mcoeff_additive k := Additive (mcoeff_is_additive k).

Lemma mcoeff0   k   : 0@_k = 0                     . Proof. exact: raddf0. Qed.
Lemma mcoeffN   k   : {morph mcoeff k: x / - x}    . Proof. exact: raddfN. Qed.
Lemma mcoeffD   k   : {morph mcoeff k: x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mcoeffB   k   : {morph mcoeff k: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mcoeffMn  k n : {morph mcoeff k: x / x *+ n} . Proof. exact: raddfMn. Qed.
Lemma mcoeffMNn k n : {morph mcoeff k: x / x *- n} . Proof. exact: raddfMNn. Qed.

(* -------------------------------------------------------------------- *)
Lemma msupp0 : msupp 0 = fset0.
Proof. admit. Qed.

Lemma msuppN g : msupp (-g) = msupp g.
Proof. by apply/fsetP=> k; rewrite -!mcoeff_neq0 mcoeffN oppr_eq0. Qed.


End MalgZMod.
