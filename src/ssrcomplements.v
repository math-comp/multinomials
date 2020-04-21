(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq path choice finset fintype finfun.
From mathcomp Require Import tuple bigop ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Monoid GRing.Theory.

Local Open Scope ring_scope.

Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Lemma lreg_prod (T : eqType) (R : ringType) (r : seq T) (P : pred T) (F : T -> R):
      (forall x, x \in r -> P x -> GRing.lreg (F x))
   -> GRing.lreg (\prod_(x <- r | P x) F x).
Proof.
  elim: r => [|x r ih] h; first by rewrite !big_nil; apply/lreg1.
  rewrite big_cons; set X := \prod_(_ <- _ | _) _.
  have lreg_X: GRing.lreg X.
    by apply/ih=> y y_in_r; apply: (h y); rewrite mem_behead.
  by case Px: (P x)=> //; apply/lregM=> //; apply/h; rewrite ?mem_head.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sumnB (T : Type) (r : seq T) (a b : T -> nat) (P : pred T):
  (forall i, P i -> b i <= a i) ->
       (\sum_(i <- r | P i) (a i - b i))%N
     = (\sum_(i <- r | P i) a i - \sum_(i <- r | P i) b i)%N.
Proof.
  move=> h; elim: r=> [|x r ih]; first by rewrite !big_nil subn0.
  rewrite !big_cons; case: (boolP (P x)) => // Px.
  rewrite ih addnBA ?subnDA ?leq_sum //.
  by congr (_ - _)%N; rewrite addnC addnBA 1?addnC // h.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sumn_range (k1 k2 : nat) (c : nat -> nat): k1 <= k2 ->
     (forall i j, i <= j < (k2 - k1).+1 -> c (j + k1) <= c (i + k1))%N
  -> (\sum_(k1 <= i < k2) (c i - c i.+1) = c k1 - c k2)%N.
Proof.
  rewrite leq_eqVlt; case/orP=> [/eqP<- h|].
    by rewrite big_geq // subnn.
  rewrite -subn_gt0=> gt0_k2Bk1 h; rewrite -{1}[k1]add0n big_addn.
  case k1Bk2E: (k2-k1)%N  gt0_k2Bk1 h => [|n] // _ h.
  rewrite big_nat sumnB -?big_nat; last first.
    move=> i /andP[_]; rewrite ltnS -addSn => le_in.
    by apply/h; rewrite leqnSn /= !ltnS.
  rewrite big_nat_recl ?big_nat_recr //= subnDA addnK.
  rewrite add0n -addSn -k1Bk2E subnK // leqNgt; apply/negP.
  by move/ltnW; rewrite -subn_eq0 k1Bk2E.
Qed.

Lemma sum0n_range (k : nat) (c : nat -> nat):
     (forall i j, i <= j < k.+1 -> c j <= c i)%N
  -> (\sum_(0 <= i < k) (c i - c i.+1) = c 0 - c k)%N.
Proof.
  move=> h; apply/sumn_range; rewrite ?subn0=> // i j le.
  by rewrite !addn0; apply/h.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sumn_wgt_range (k : nat) (c : nat -> nat):
     (forall i j, i <= j < k.+1 -> c j <= c i)
  -> (  \sum_(i < k) (c i - c i.+1) * i.+1
      = \sum_(i < k) c i - k * (c k))%N.
Proof.
  pose F i := ((c i) * i.+1 - (c i.+1) * i.+1)%N.
  rewrite (eq_bigr (F \o val)) /=; first last.
    by move=> i _; rewrite mulnBl.
  rewrite [(k*_)%N]mulnC; elim: k=> [|k ih] h.
    by rewrite !big_ord0 muln0 subn0.
  rewrite !big_ord_recr /= ih; last first.
    move=> i j /andP[le_ij lt_jSk]; apply/h.
    by rewrite le_ij ltnS ltnW.
  rewrite {ih}/F addnBA ?leq_mul //; last first.
    by apply/h; rewrite leqnn ltnW.
  congr (_ - _)%N; rewrite addnC addnBA 1?addnC -?addnBA.
  + by rewrite -mulnBr subSnn muln1.
  + by rewrite leq_mul.
  elim: k h => [|k ih] h; first by rewrite muln0.
  rewrite big_ord_recr //= mulnS addnC leq_add //; last first.
    by apply/h; rewrite !ltnS !leqnSn.
  apply/(@leq_trans (c k * k)); last apply/ih.
    by rewrite leq_mul=> //; apply/h; rewrite !ltnS !leqnSn.
  move=> i j /andP[le_ij lt_jSSk]; apply/h.
  by rewrite le_ij !ltnS ltnW.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psumn_eq k (F1 F2 : nat -> nat):
     (forall j, j <= k ->
          \sum_(i < k | i < j) F1 i
        = \sum_(i < k | i < j) F2 i)%N
  -> forall j, j < k -> F1 j = F2 j.
Proof.
  pose rw := (big_ord_narrow, big_ord_recr).
  move=> h j; elim: j {-2}j (leqnn j)=> [|j ih] l.
    rewrite leqn0=> /eqP-> lt; have := h 1%N lt.
    by rewrite !rw !big_ord0 /= !add0n=> ->.
  rewrite leq_eqVlt ltnS; case/orP=>[/eqP->|]; last by apply/ih.
  move: {-2}j.+1 (leqnn j.+1)=> x le_xSj lt; have := h _ lt.
  rewrite !rw /=; set S1 := bigop _ _ _; set S2 := bigop _ _ _.
  suff <-: S1 = S2 by move/addnI. apply/eq_bigr=> /=.
  case=> /= i lt_ix _; apply/ih; last by apply/(ltn_trans lt_ix).
  by rewrite -ltnS; apply/(leq_trans lt_ix).
Qed.

(* -------------------------------------------------------------------- *)
Section BigMkSub.
  Context  {S   : Type}.
  Context  {idx : S}.
  Context  {op  : Monoid.com_law idx}.

  Context {T  : choiceType}.
  Context {sT : pred T}.
  Context {rT : pred T}.
  Context (I  : subFinType sT).
  Context (J  : subFinType rT).

  Lemma big_mksub_cond {P : pred T} {F : T -> S} (r : seq T):
      uniq r
   -> (forall x, x \in r -> P x -> sT x)
   -> \big[op/idx]_(x <- r | P x) (F x)
    = \big[op/idx]_(x : I | (P (val x)) && (val x \in r)) (F (val x)).
  Proof.
    move=> uniq_r h; rewrite -big_filter; apply/esym.
    pose Q x := P x && (x \in r); rewrite -(big_map val Q).
    rewrite -big_filter; apply/perm_big/uniq_perm;
      try rewrite filter_uniq // (map_inj_uniq val_inj).
      by rewrite /index_enum -enumT enum_uniq.
    move=> x; rewrite !mem_filter {}/Q; apply/andb_idr.
    rewrite andbC; case/andP=> /h {h}h /h sT_x.
    apply/mapP; exists (Sub x sT_x).
      by rewrite /index_enum -enumT mem_enum.
    by rewrite SubK.
  Qed.

  Lemma big_mksub {F : T -> S} (r : seq T):
      uniq r
   -> (forall x, x \in r -> sT x)
   -> \big[op/idx]_(x <- r) (F x)
    = \big[op/idx]_(x : I | val x \in r) (F (val x)).
  Proof. by move=> uniq_r h; apply/big_mksub_cond=> // x /h. Qed.

  Lemma big_sub_widen {P : pred T} {F : T -> S}:
         (forall x, sT x -> rT x)
    ->   \big[op/idx]_(x : I | P (val x)) (F (val x))
       = \big[op/idx]_(x : J | P (val x) && sT (val x)) (F (val x)).
  Proof.
    move=> h; pose Q := [pred x | P x && sT x].
    rewrite -big_map -(big_map val Q F).
    rewrite -big_filter -[X in _=X]big_filter; apply/perm_big.
    apply/uniq_perm; rewrite ?(filter_uniq, map_inj_uniq val_inj) //;
      try by rewrite /index_enum -enumT enum_uniq.
    move=> x; rewrite !mem_filter {}/Q inE -andbA; congr (_ && _).
    apply/idP/andP; last first.
      by case=> sTx _; apply/mapP; exists (Sub x sTx); rewrite ?SubK.
    case/mapP=> y _ ->; split; first by apply valP.
    apply/mapP; exists (Sub (val y) (h _ (valP y))).
      by rewrite /index_enum -enumT mem_enum.
      by rewrite SubK.
  Qed.

  Lemma eq_big_widen {P : pred T} {F : T -> S}:
         (forall x, sT x -> rT x)
    ->   (forall x, ~~ (sT x) -> F x = idx)
    ->   \big[op/idx]_(x : I | P (val x)) (F (val x))
       = \big[op/idx]_(x : J | P (val x)) (F (val x)).
  Proof.
    move=> h1 h2; rewrite big_sub_widen //; apply/esym.
    rewrite (bigID (sT \o val)) [X in op _ X]big1 ?simpm //.
    by move=> j /andP [_ /h2].
  Qed.
End BigMkSub.

Arguments big_sub_widen [S idx op T sT rT].
Arguments big_sub_widen [S idx op T sT rT].

(* add to mathcomp *)
Lemma prod_inj A B : injective (prod_curry (@pair A B)).
Proof. by move=> [? ?] [? ?]. Qed.
Hint Resolve prod_inj : core.

(* add to mathcomp *)
Lemma in_allpairs (S T R : eqType) (f : S -> T -> R)
  (s : seq S) (t : seq T) x y :
  injective (prod_curry f) ->
  f x y \in [seq f x0 y0 | x0 <- s, y0 <- t] =
  (x \in s) && (y \in t).
Proof.
move=> f_inj; apply/allpairsP/andP => [|[]]; last by exists (x, y).
by case=> -[/= x' y'] [x's y't] /(f_inj (x, y) (x',y')) [-> ->].
Qed.

(* -------------------------------------------------------------------- *)
Section BigOpPair.
  Variables I J : finType.
  Variables R : Type.

  Variable idx : R.
  Variable op  : Monoid.com_law idx.

  Lemma big_pair_dep (P : pred I) (Q : pred (I * J)) (F : I * J -> R) :
    \big[op/idx]_(p | P p.1 && Q p) F p =
     \big[op/idx]_(i | P i) \big[op/idx]_(j | Q (i, j)) F (i, j).
  Proof. by rewrite pair_big_dep; apply: eq_big => -[]. Qed.

  Lemma big_pair (P : pred I) (Q : pred J) (F : I * J -> R) :
    \big[op/idx]_(p | P p.1 && Q p.2) F p =
    \big[op/idx]_(i | P i) \big[op/idx]_(j | Q j) F (i, j).
  Proof. exact: big_pair_dep. Qed.

  Lemma big_pairA (F : I * J -> R):
    \big[op/idx]_p F p = \big[op/idx]_i \big[op/idx]_j F (i, j).
  Proof. exact: (big_pair_dep xpredT xpredT). Qed.

End BigOpPair.

(* -------------------------------------------------------------------- *)
Section BigOpMulrn.
  Variable I : Type.
  Variable R : ringType.

  Variable F : I -> R.
  Variable P : pred I.

  Lemma big_cond_mulrn r:
    \sum_(i <- r | P i) (F i) = \sum_(i <- r) (F i) *+ (P i).
  Proof. by rewrite big_mkcond; apply: eq_bigr => i; rewrite mulrb. Qed.

End BigOpMulrn.

(* -------------------------------------------------------------------- *)
Lemma tval_tcast (T : Type) (n m : nat) (e : n = m) (t : n.-tuple T):
  tval (tcast e t) = tval t.
Proof. by case: m / e. Qed.
