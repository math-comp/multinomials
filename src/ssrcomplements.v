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
Lemma flatten_seq1 (T : Type) (r : seq T):
  flatten [seq [:: x] | x <- r] = r.
Proof. by elim: r=> /= [|x r ->]. Qed.

Lemma count_flatten (T U : Type) (r : seq T) (F : T -> seq U) a:
    count a (flatten [seq F x | x <- r])
  = (\sum_(x <- r) (count a (F x)))%N.
Proof.
  elim: r => /= [|x r ih]; first by rewrite big_nil.
  by rewrite count_cat big_cons ih.
Qed.

(* -------------------------------------------------------------------- *)
Lemma nseqD T n1 n2 (x : T):
  nseq (n1 + n2) x = nseq n1 x ++ nseq n2 x.
Proof. by rewrite cat_nseq /nseq /ncons iter_add. Qed.

(* -------------------------------------------------------------------- *)
Lemma uniq_nth (T : eqType) (x0 : T) s:
     (forall i j, i < size s -> j < size s ->
        i != j -> nth x0 s i != nth x0 s j)
  -> uniq s.
Proof.
  elim: s=> [//|x s ih] h /=; apply/andP; split.
    apply/(nthP x0)=> h_nth; absurd false=> //.
    case: h_nth => i lt_i_szs /esym xE.
    have := h 0%N i.+1; rewrite xE eqxx /=.
    by rewrite !ltnS /= leq0n lt_i_szs=> ->.
  apply/ih=> i j lti ltj ne_ij; have /= := h i.+1 j.+1.
  by move/(_ lti ltj ne_ij).
Qed.

(* -------------------------------------------------------------------- *)
Lemma subnB (T : Type) (r : seq T) (a b : T -> nat) (P : pred T):
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
     (forall i j, i <= j < (k2-k1).+1 -> c (j+k1) <= c (i+k1))%N
  -> (\sum_(k1 <= i < k2) (c i - c i.+1) = c k1 - c k2)%N.
Proof.
  rewrite leq_eqVlt; case/orP=> [/eqP<- h|].
    by rewrite big_geq // subnn.
  rewrite -subn_gt0=> gt0_k2Bk1 h; rewrite -{1}[k1]add0n big_addn.
  case k1Bk2E: (k2-k1)%N  gt0_k2Bk1 h => [|n] // _ h.
  rewrite big_nat subnB -?big_nat; last first.
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
Section BigUncond.
  Variables T : Type.
  Variables R : Type.

  Variable idx : R.
  Variable op  : Monoid.com_law idx.

  Lemma big_uncond (P : pred T) (F : T -> R) r:
       (forall i, ~~ P i -> F i = idx)
    -> \big[op/idx]_(x <- r | P x) F x = \big[op/idx]_(x <- r) F x.
  Proof.
    move=> h; apply/esym; rewrite (bigID P) /= [X in op _ X]big1.
      by rewrite Monoid.mulm1.
    by move=> i /h.
  Qed.
End BigUncond.

(* -------------------------------------------------------------------- *)
Section BigSet.
  Variable T   : Type.
  Variable idx : T.
  Variable op  : Monoid.law idx.

  Lemma big_set (I : finType) (P : pred I) (F : I -> T):
      \big[op/idx]_(x in [set i : I | P i]) (F x)
    = \big[op/idx]_(x : I | P x) (F x).
  Proof. by rewrite /index_enum; apply/eq_bigl=> i; rewrite inE. Qed.
End BigSet.

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
    rewrite -big_filter; apply/eq_big_perm/uniq_perm_eq;
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
    rewrite -big_filter -[X in _=X]big_filter; apply/eq_big_perm.
    apply/uniq_perm_eq; rewrite ?(filter_uniq, map_inj_uniq val_inj) //;
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

Implicit Arguments big_sub_widen [S idx op T sT rT].
Implicit Arguments big_sub_widen [S idx op T sT rT].

(* -------------------------------------------------------------------- *)
Section Product.
  Variables T U : Type.

  Definition product (s1 : seq T) (s2 : seq U) :=
    flatten [seq [seq (x, y) | y <- s2] | x <- s1].

  Lemma product0s (s : seq U): product [::] s = [::].
  Proof. by []. Qed.

  Lemma products0 (s : seq T): product s [::] = [::].
  Proof. by elim: s. Qed.

  Lemma product_cons x s1 s2:
    product (x :: s1) s2 =
      [seq (x, y) | y <- s2] ++ product s1 s2.
  Proof. by []. Qed.
End Product.

Local Infix "@@" := product (at level 60, right associativity).

(* -------------------------------------------------------------------- *)
Section ProductTheory.
  Variable eT eU : eqType.
  Variable T  U  : Type.
  Variable T' U' : Type.
  Variable fT : T -> T'.
  Variable fU : U -> U'.

  Notation f := (fun x => (fT x.1, fU x.2)).

  Lemma product_size (s1 : seq T) (s2 : seq U):
    size (product s1 s2) = (size s1 * size s2)%N.
  Proof.
    elim: s1 => [|x s1 ih] //=; rewrite !product_cons.
    by rewrite size_cat ih size_map mulSn.
  Qed.

  Lemma product_map s1 s2:
    map f (product s1 s2) = product (map fT s1) (map fU s2).
  Proof.
    elim: s1 => [|x s1 ih] //=.
    by rewrite !product_cons map_cat ih -!map_comp.
  Qed.

  Lemma product_mem (s1 : seq eT) (s2 : seq eU) x:
    (x \in product s1 s2) = (x.1 \in s1) && (x.2 \in s2).
  Proof.
    case: x => [x1 x2] /=; elim: s1 => [|x s1 ih] //=.
    rewrite product_cons mem_cat ih in_cons andb_orl.
    congr (_ || _); case: eqP=> [<-|ne_x1_x] /=.
    + by rewrite mem_map // => z1 z2 [].
    + by apply/mapP; case=> x' _ [].
  Qed.

  Lemma product_uniq (s1 : seq eT) (s2 : seq eU):
    (uniq s1) && (uniq s2) -> uniq (product s1 s2).
  Proof.
    elim: s1 => [|x s1 ih] //=; rewrite product_cons -andbA.
    case/and3P=> x_notin_s1 un_s1 un_s2; rewrite cat_uniq.
    rewrite ih ?(un_s1, un_s2) andbT // map_inj_uniq //=; last first.
      by move=> x1 x2 /= [].
    rewrite un_s2 /=; apply/hasPn=> [[x1 x2]] /=.
    rewrite product_mem /= => /andP [x1_in_s1 _].
    apply/memPn=> [[y1 y2] /mapP [x' _ [-> ->]]].
    by apply/eqP=> h; case: h x1_in_s1 x_notin_s1=> -> _ ->.
  Qed.
End ProductTheory.

(* -------------------------------------------------------------------- *)
(* FIXME: move me or replace me                                         *)
Section BigOpProduct.
  Variables T1 T2 R : Type.

  Variable idx : R.
  Variable op  : Monoid.com_law idx.

  Lemma pair_bigA_seq_curry (F : T1 * T2 -> R) s1 s2:
      \big[op/idx]_(i1 <- s1)
        \big[op/idx]_(i2 <- s2) F (i1, i2)
    = \big[op/idx]_(i <- product s1 s2) F i.
  Proof.
    elim: s1 => [|x s1 ih]; first by rewrite product0s !big_nil.
    by rewrite product_cons big_cat big_cons ih big_map.
  Qed.

  Lemma pair_bigA_seq (F : T1 -> T2 -> R) s1 s2:
      \big[op/idx]_(i1 <- s1)
        \big[op/idx]_(i2 <- s2) F i1 i2
    = \big[op/idx]_(i <- product s1 s2) F i.1 i.2.
  Proof. by rewrite -pair_bigA_seq_curry. Qed.
End BigOpProduct.

(* -------------------------------------------------------------------- *)
Section BigOpPair.
  Variables T1 T2 : finType.
  Variables R : Type.

  Variable idx : R.
  Variable op  : Monoid.com_law idx.

  Lemma pair_big_dep_curry (F : T1 * T2 -> R) (P : pred (T1 * T2)):
      \big[op/idx]_i \big[op/idx]_(j | P (i, j)) F (i, j)
    = \big[op/idx]_(x | P x) F x.
  Proof. by rewrite pair_big_dep /=; apply/eq_big; case. Qed.

  Lemma pair_bigA_curry (F : T1 * T2 -> R):
      \big[op/idx]_i \big[op/idx]_j F (i, j)
    = \big[op/idx]_x F x.
  Proof. by apply/pair_big_dep_curry. Qed.
End BigOpPair.

(* -------------------------------------------------------------------- *)
Section BigOpMulrn.
  Variable I : Type.
  Variable R : ringType.

  Variable F : I -> R.
  Variable P : pred I.

  Lemma big_cond_mulrn r:
    \sum_(i <- r | P i) (F i) = \sum_(i <- r) (F i) *+ (P i).
  Proof.
    elim: r => [|x r ih]; first by rewrite !big_nil.
    by rewrite !big_cons ih; case: (P x); rewrite ?(mulr0n, mulr1n, add0r).
  Qed.
End BigOpMulrn.

(* -------------------------------------------------------------------- *)
Lemma bignat_sumn_cond (T : Type) (r : seq T) (P : pred T) (F : T -> nat):
  (\sum_(i <- r | P i) (F i))%N = sumn [seq F i | i <- r & P i].
Proof.
  elim: r => /= [|i r ih]; first by rewrite big_nil.
  by rewrite big_cons; case: (P i); rewrite ih.
Qed.

Lemma bignat_sumn (T : Type) (r : seq T) (F : T -> nat):
  (\sum_(i <- r) (F i))%N = sumn [seq F i | i <- r].
Proof. by rewrite bignat_sumn_cond filter_predT. Qed.

(* -------------------------------------------------------------------- *)
Lemma tval_tcast (T : Type) (n m : nat) (e : n = m) (t : n.-tuple T):
  tval (tcast e t) = tval t.
Proof. by case: m / e. Qed.
