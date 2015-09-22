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
  (at level 0, S at level 2, format "[ 'malg'  g ]").
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
  := [malg [fsfun [fmap x : aT => E] / 0]] : ring_scope.
Notation "<< z *g k >>"
  := [malg [fmap].[k <- z]] : ring_scope.
Notation "<< k >>"
  := << 1 *g k >> : ring_scope.

(* -------------------------------------------------------------------- *)
Section MalgSupp.
Variable (K : choiceType) (G : zmodType).

Definition msupp (g : {malg G[K]}) :=
  nosimpl (domf (malg_val g)).

Definition mcoeff (g : {malg G[K]}) (x : K) :=
  nosimpl (malg_val g x).
End MalgSupp.

Notation "g @_ k" := (mcoeff g k).

(* -------------------------------------------------------------------- *)
Section MalgTheory.
Variable (K : choiceType) (G : zmodType).

Lemma freegP (g1 g2 : {malg G[K]}) :
  reflect (forall k, g1@_k = g2@_k) (g1 == g2).
Proof. admit. Qed.
End MalgTheory.

(* -------------------------------------------------------------------- *)
Section MalgZMod.
Variable (K : choiceType) (G : zmodType).

Implicit Types g : {malg G[K]}.

Definition fgzero : {malg G[K]} :=
  [malg [fmap]].

Definition fgopp g :=
  [malg k : msupp g => - g@_(val k)].

Definition fgadd g1 g2 :=
  [malg k : (msupp g1 `|` msupp g2) => g1@_(val k) + g2@_(val k)].

Goal associative fgadd.
Proof. Abort.
End MalgZMod.
