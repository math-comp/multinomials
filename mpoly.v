(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun tuple bigop ssralg ssrint.
Require Import fingroup perm zmodp binomial bigenough poly poset freeg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory BigEnough.

Local Open Scope ring_scope.

Delimit Scope mpoly_scope with MP.
Delimit Scope multi_scope with MM.

Local Notation simpm := Monoid.simpm.
Local Notation ilift := fintype.lift.

Local Notation efst := (@fst _ _) (only parsing).
Local Notation esnd := (@snd _ _) (only parsing).

(* -------------------------------------------------------------------- *)
(* FIXME: move me or replace me                                         *)
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
(* FIXME: move me or replace me                                         *)
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
(* FIXME: move me or replace me                                         *)
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
(* FIXME: move me or replace me                                         *)
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
(* FIXME: move me or replace me                                         *)
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
(* FIXME: move me or replace me                                         *)
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
(* FIXME: move me or replace me                                         *)
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
     format "[ '[hv' 'multinom'  F '/'   |  i  <  n ] ']'").
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
Reserved Notation "''s_' k"
  (at level 8, k at level 2, format "''s_' k").
Reserved Notation "''s_' ( n , k )"
  (at level 8, n, l at level 2, format "''s_' ( n ,  k )").
Reserved Notation "+%MM"
  (at level 0).

(* -------------------------------------------------------------------- *)
Section MultinomDef.
  Context (n : nat).

  Inductive multinom : predArgType :=
    Multinom of n.-tuple nat.

  Coercion multinom_val M := let: Multinom m := M in m.

  Canonical multinom_subType := Eval hnf in [newType for multinom_val].

  Definition fun_of_multinom M (i : 'I_n) := tnth (multinom_val M) i.

  Coercion fun_of_multinom : multinom >-> Funclass.

  Lemma multinomE M: (Multinom M) =1 tnth M.
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
Notation "m1 <= m2" := [forall i, m1%MM i <= m2%MM i] : multi_scope.

(* -------------------------------------------------------------------- *)
Section MultinomTheory.
  Context {n : nat}.

  Implicit Types t : n.-tuple nat.
  Implicit Types m : 'X_{1..n}.

  Lemma mnmE E j: [multinom E i | i < n] j = E j.
  Proof. by rewrite multinomE tnth_mktuple. Qed.

  Lemma mnm_valK t: [multinom t] = t :> n.-tuple nat.
  Proof. by []. Qed.

  Lemma mnmP m1 m2: (m1 = m2) <-> (m1 =1 m2).
  Proof.
    case: m1 m2 => [m1] [m2] /=; split=> [[->]//|] h.
    by apply/val_eqP/eqP/eq_from_tnth => i /=; rewrite -!multinomE.
  Qed.

  Lemma mnm_lepP m1 m2: reflect (forall i, m1 i <= m2 i) (m1 <= m2)%MM.
  Proof. by apply: (iffP forallP). Qed.

  Lemma lepm_refl m: (m <= m)%MM.
  Proof. by apply/mnm_lepP=> i. Qed.

  Lemma lepm_trans m3 m1 m2: (m1 <= m2 -> m2 <= m3 -> m1 <= m3)%MM.
  Proof.
    move=> /mnm_lepP h1 /mnm_lepP h2; apply/mnm_lepP.
    by move=> i; apply/(leq_trans (h1 i) (h2 i)).
  Qed.

  Definition mnm0 := nosimpl [multinom of nseq n 0%N].

  Notation "0" := mnm0 : multi_scope.

  Lemma mnm0E i: 0%MM i = 0%N.
  Proof. by rewrite multinomE (tnth_nth 0%N) nth_nseq if_same. Qed.

  Definition mnm_add m1 m2 :=
    [multinom (m1 i + m2 i)%N | i < n].

  Definition mnm_sub m1 m2 :=
    [multinom (m1 i - m2 i)%N | i < n].

  Definition mnmd (c : 'I_n) :=
    [multinom ((c == i) : nat) | i < n].

  Local Notation "m1 + m2" := (mnm_add m1 m2) : multi_scope.
  Local Notation "m1 - m2" := (mnm_sub m1 m2) : multi_scope.

  Local Notation "+%MM" := (@mnm_add).

  Lemma mnmDE i m1 m2: (m1 + m2)%MM i = (m1 i + m2 i)%N.
  Proof. by rewrite multinomE tnth_map tnth_ord_tuple. Qed.

  Lemma mnm_sum (I : Type) i (r : seq I) P F:
      (\big[+%MM/0%MM]_(x <- r | P x) (F x)) i
    = (\sum_(x <- r | P x) (F x i))%N.
  Proof.
    pose f m := m i; apply/(big_morph f).
      by move=> x y; rewrite /f /= mnmDE.
      by rewrite /f /= mnm0E.
  Qed.

  Lemma mnmBE i m1 m2: (m1 - m2)%MM i = (m1 i - m2 i)%N.
  Proof. by rewrite multinomE tnth_map tnth_ord_tuple. Qed.

  Lemma mnm1E i j: (mnmd i) j = (i == j)%N.
  Proof. by rewrite multinomE tnth_map tnth_ord_tuple. Qed.

  Lemma lep1mP i m: (mnmd i <= m)%MM = (m i != 0)%N.
  Proof.
    apply/mnm_lepP/idP=> [/(_ i)|]; rewrite ?mnm1E -?lt0n.
      by case: eqP.
      by move=> lt0_mi j; rewrite mnm1E; case: eqP=> // <-.
  Qed.

  Lemma mnm_addC: commutative mnm_add.
  Proof. by move=> m1 m2; apply/mnmP=> i; rewrite !mnmE addnC. Qed.

  Lemma mnm_addA: associative mnm_add.
  Proof. by move=> m1 m2 m3; apply/mnmP=> i; rewrite !mnmE addnA. Qed.

  Lemma mnm_add0m: left_id 0%MM mnm_add.
  Proof.
    move=> m; apply/mnmP=> i; rewrite !mnmE multinomE.
    by rewrite (tnth_nth 0%N) /= nth_nseq if_same add0n.
  Qed.

  Lemma mnm_addm0: right_id 0%MM mnm_add.
  Proof. by move=> m; rewrite mnm_addC mnm_add0m. Qed.

  Canonical mnm_monoid := Monoid.Law mnm_addA mnm_add0m mnm_addm0.
  Canonical mnm_comoid := Monoid.ComLaw mnm_addC.

  Lemma eqm_add2l m n1 n2:
    ((m + n1)%MM == (m + n2)%MM) = (n1 == n2).
  Proof.
    apply/eqP/eqP=> [|->//] /mnmP h; apply/mnmP.
    by move=> i; move: (h i); rewrite !mnmDE => /addnI.
  Qed.

  Lemma eqm_add2r m n1 n2:
    ((n1 + m)%MM == (n2 + m)%MM) = (n1 == n2).
  Proof. by rewrite ![(_ + m)%MM]mnm_addC eqm_add2l. Qed.

  Lemma addmK m: cancel (mnm_add^~ m) (mnm_sub^~ m).
  Proof. by move=> m' /=; apply/mnmP=> i; rewrite !(mnmDE, mnmBE) addnK. Qed.

  Lemma submK m m': (m <= m')%MM -> (m' - m + m = m')%MM.
  Proof.
    move=> /mnm_lepP h; apply/mnmP=> i.
    by rewrite !(mnmDE, mnmBE) subnK.
  Qed.

  Lemma addmBA m1 m2 m3: (m3 <= m2)%MM -> (m1 + (m2 - m3))%MM = (m1 + m2 - m3)%MM.
  Proof.
    move/mnm_lepP=> h; apply/mnmP=> i.
    by rewrite !(mnmBE, mnmDE) addnBA.
  Qed.

  Lemma submDA m1 m2 m3: (m1 - m2 - m3)%MM = (m1 - (m2 + m3))%MM.
  Proof. by apply/mnmP=> i; rewrite !(mnmBE, mnmDE) subnDA. Qed.

  Lemma submBA m1 m2 m3: (m3 <= m2)%MM -> (m1 - (m2 - m3) = m1 + m3 - m2)%MM.
  Proof.
    move/mnm_lepP=> h; apply/mnmP=> i.
    by rewrite !(mnmDE, mnmBE) subnBA.
  Qed.

  Lemma lem_subr m1 m2: (m1 - m2 <= m1)%MM.
  Proof. by apply/mnm_lepP=> i; rewrite mnmBE leq_subr. Qed.

  Definition mnm_muln m i := nosimpl iterop _ i mnm_add m 0%MM.

  Local Notation "x *+ n" := (mnm_muln x n) : multi_scope.

  Lemma mnm_mulm0 m: (m *+ 0 = 0)%MM.
  Proof. by []. Qed.

  Lemma mnm_mulmS m i: ((m *+ i.+1) = (m + m *+ i))%MM.
  Proof. by rewrite /mnm_muln !Monoid.iteropE iterS /=. Qed.

  Lemma mnmMn m k i: ((m *+ k) i)%MM = (k * (m i))%N.
  Proof.
    elim: k => [|k ih]; first by rewrite mul0n mnm_mulm0 mnm0E.
    by rewrite mnm_mulmS mulSn mnmDE ih.
  Qed.

  Definition mdeg m := (\sum_(i <- m) i)%N.

  Lemma mdegE m: mdeg m = (\sum_i (m i))%N.
  Proof. by rewrite /mdeg big_tuple. Qed.

  Lemma mdeg0: mdeg 0%MM = 0%N.
  Proof.
    rewrite /mdeg big_seq big1 // => i /tnthP.
    by case=> j ->; rewrite -multinomE mnm0E.
  Qed.

  Lemma mdeg1 i: mdeg (mnmd i) = 1%N.
  Proof.
    rewrite !mdegE (bigD1 i) //= big1; last first.
      by move=> j ne_ji; rewrite mnm1E eq_sym (negbTE ne_ji).
    by rewrite mnm1E eqxx addn0.
  Qed.

  Lemma mdegD m1 m2: mdeg (m1 + m2) = (mdeg m1 + mdeg m2)%N.
  Proof.
    case: m1 m2 => [m1] [m2]; rewrite !mdegE -big_split /=.
    by apply/eq_bigr=> i _; rewrite [X in X=_]multinomE tnth_mktuple.
  Qed.

  Lemma mdegB m1 m2: mdeg (m1 - m2) <= mdeg m1.
  Proof.
    case: m1 m2 => [m1] [m2]; rewrite !mdegE /=; apply/leq_sum.
    by move=> i _ /=; rewrite mnmBE leq_subr.
  Qed.

  Lemma mdeg_sum (I : Type) (r : seq I) P F:
      mdeg (\big[+%MM/0%MM]_(x <- r | P x) (F x))
    = (\sum_(x <- r | P x) (mdeg (F x)))%N.
  Proof. by apply/big_morph; [apply/mdegD | apply/mdeg0]. Qed.

  Lemma mdeg_eq0 m: (mdeg m == 0%N) = (m == 0%MM).
  Proof.
    apply/idP/eqP=> [|->]; last by rewrite mdeg0.
    move=> h; apply/mnmP=> i; move: h; rewrite mdegE mnm0E.
    by rewrite (bigD1 i) //= addn_eq0 => /andP [/eqP-> _].
  Qed.

  Lemma mnmD_eq0 m1 m2: (m1 + m2 == 0)%MM = (m1 == 0%MM) && (m2 == 0%MM).
  Proof. by rewrite -!mdeg_eq0 mdegD addn_eq0. Qed.

  Lemma mnm1_eq0 i: (mnmd i == 0%MM) = false.
  Proof. by rewrite -mdeg_eq0 mdeg1. Qed.
End MultinomTheory.

Notation "+%MM" := (@mnm_add _).

Notation "0"         := (@mnm0 _) : multi_scope.
Notation "'U_(' n )" := (mnmd n) : multi_scope.
Notation "m1 + m2"   := (mnm_add m1 m2) : multi_scope.
Notation "m1 - m2"   := (mnm_sub m1 m2) : multi_scope.
Notation "x *+ n"    := (mnm_muln x n) : multi_scope.

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
Section MultinomOrder.
  Context {n : nat}.

  Implicit Types t : n.-tuple nat.
  Implicit Types m : 'X_{1..n}.

  Definition mnmc_le m1 m2 :=
    @lex [posetType of nat] (mdeg m1 :: m1) (mdeg m2 :: m2).

  Lemma lemc_refl: reflexive mnmc_le.
  Proof. by case=> t; apply/lex_refl. Qed.

  Lemma lemc_antisym: antisymmetric mnmc_le.
  Proof.
    case=> [[m1 /= h1]] [[m2 /= h2]] /=.
    rewrite /mnmc_le => /lex_antisym [_ h].
    by apply/eqP; do 2! rewrite -val_eqE /= ?h.
  Qed.

  Lemma lemc_trans: transitive mnmc_le.
  Proof. by case=> [m1] [m2] [m3]; apply/lex_trans. Qed.

  Lemma lemc_total: total mnmc_le.
  Proof.
    case=> [m1] [m2]; apply/lex_total.
    by move=> n1 n2; rewrite !lenP leq_total.
  Qed.

  Definition multinom_posetMixin :=
    POSetMixin lemc_refl lemc_antisym lemc_trans.
  Canonical multinom_posetType :=
    Eval hnf in (POSetType 'X_{1..n} multinom_posetMixin).

  Lemma le0m (m : 'X_{1..n}): (0%MM <= m)%O.
  Proof.
    rewrite /le /= /mnmc_le /=; case: (mdeg m =P 0%N).
      move/eqP; rewrite mdeg_eq0=> /eqP->.
      by rewrite ltoo eqxx /= lex_refl.
    by move/eqP; rewrite -lt0n mdeg0 ltnP => ->.
  Qed.

  Lemma lem_total: total (@le multinom_posetType).
  Proof. exact/lemc_total. Qed.

  Hint Resolve lem_total.

  Definition multinom_CPOMixin :=
    CPOMixin le0m.
  Canonical multinom_CPOType :=
    Eval hnf in (CPOType 'X_{1..n} multinom_CPOMixin).

  Lemma lem_mdeg (m1 m2 : 'X_{1..n}): (m1 <= m2)%O -> mdeg m1 <= mdeg m2.
  Proof.
    rewrite /le /= /mnmc_le /= leq_eqVlt ltnP.
    by case/orP=> [->|/andP [->//]]; rewrite orbC.
  Qed.

  Lemma mdeg_max (m1 m2 : 'X_{1..n}):
    mdeg (maxo m1 m2) = maxn (mdeg m1) (mdeg m2).
  Proof.
    apply/esym; rewrite /maxo; case: (boolP (_ < _)%O).
      by move/ltoW/lem_mdeg/maxn_idPr.
    by rewrite -letNgt // => /lem_mdeg/maxn_idPl.
  Qed.

  Lemma mdeg_bigmax (r : seq 'X_{1..n}):
    mdeg (\max_(m <- r) m)%O = \max_(m <- r) mdeg m.
  Proof.
    elim: r => [|m r ih]; first by rewrite !big_nil mdeg0.
    by rewrite !big_cons mdeg_max ih.
  Qed.

  Lemma ltm_ltx (m m' : 'X_{1..n}):
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

  Lemma ltm_lem_add (m1 m2 n1 n2 : 'X_{1..n}):
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
      by rewrite /fun_of_multinom !(tnth_nth 0%N) !nth_enum_ord.
    rewrite /le /= /mnmc_le ltm_ltx => ltx1 lex2.
    have := (ltx_lex_nat_sum ltx1 lex2) => /= lt.
    by rewrite ltm_ltx /= !mdegD -!eq.
  Qed.

  Lemma lem_ltm_add (m1 m2 n1 n2 : 'X_{1..n}):
    (m1 <= n1 -> m2 < n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
  Proof.
    move=> le /ltm_lem_add /(_ le).
    by rewrite [(m1+_)%MM]mnm_addC [(n1+_)%MM]mnm_addC.
  Qed.

  Lemma ltm_add (m1 m2 n1 n2 : 'X_{1..n}):
    (m1 < n1 -> m2 < n2 -> (m1 + m2)%MM < (n1 + n2)%MM)%O.
  Proof. by move=> lt1 /ltoW /(ltm_lem_add lt1). Qed.

  Lemma lem_add (m1 m2 n1 n2 : 'X_{1..n}):
    (m1 <= n1 -> m2 <= n2 -> (m1 + m2)%MM <= (n1 + n2)%MM)%O.
  Proof.
    rewrite leo_eqVlt; case/orP=> [/eqP->|].
      rewrite leo_eqVlt; case/orP=> [/eqP->|]; first by rewrite leoo.
      by move/(lem_ltm_add (leoo n1))/ltoW.
    by move=> lt; move/(ltm_lem_add lt)/ltoW.
  Qed.

  Lemma lemP m1 m2: mdeg m1 = mdeg m2 ->
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
End MultinomOrder.

Hint Resolve lem_total.

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

  Lemma bmeqP (m1 m2 : bmultinom): (m1 == m2) = (m1 == m2 :> 'X_{1..n}).
  Proof. by rewrite eqE. Qed.

  Lemma bmdeg (m : bmultinom): mdeg m < bound.
  Proof. by case: m. Qed.

  Lemma bm0_proof: mdeg (0%MM : 'X_{1..n}) < bound.+1.
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

  Lemma bmnm_enumP: Finite.axiom bmnm_enum.
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

  Lemma mpoly_valK D: [mpoly D] = D :> {freeg _ / _}.
  Proof. by []. Qed.

  Lemma mpoly_eqP p q: (p = q) <-> (p = q :> {freeg _ / _}).
  Proof. 
    split=> [->//|]; case: p q => [p] [q].
    by rewrite !mpoly_valK=> ->.
  Qed.

  Definition mpolyC (c : R) : {mpoly R[n]} :=
    [mpoly << c *g 0%MM >>].

  Local Notation "c %:MP" := (mpolyC c) : ring_scope.

  Lemma mpolyC_eq (c1 c2 : R): (c1%:MP == c2%:MP) = (c1 == c2).
  Proof.
    apply/eqP/eqP=> [|->//] /eqP/freeg_eqP.
    by move/(_ 0%MM); rewrite !coeffU eqxx !simpm.
  Qed.

  Definition mcoeff (m : 'X_{1..n}) p : R :=
    coeff m p.

  Lemma mcoeff_MPoly D m: mcoeff m (MPoly D) = coeff m D.
  Proof. by []. Qed.

  Local Notation "p @_ i" := (mcoeff i p) : ring_scope.

  Lemma mcoeffC c m: c%:MP@_m = c * (m == 0%MM)%:R.
  Proof. by rewrite mcoeff_MPoly coeffU eq_sym. Qed.

  Lemma mpolyCK: cancel mpolyC (mcoeff 0%MM).
  Proof. by move=> c; rewrite mcoeffC eqxx mulr1. Qed.

  Definition msupp p : seq 'X_{1..n} :=
    dom p.

  Lemma msuppE p: msupp p = dom p :> seq _.
  Proof. by []. Qed.

  Lemma msupp_uniq p: uniq (msupp p).
  Proof. by rewrite msuppE uniq_dom. Qed.

  Lemma mcoeff_msupp p m: (m \in msupp p) = (p@_m != 0).
  Proof. by rewrite msuppE /mcoeff mem_dom inE. Qed.

  Lemma memN_msupp_eq0 p m: m \notin msupp p -> p@_m = 0.
  Proof. by rewrite !msuppE /mcoeff => /coeff_outdom. Qed.

  Lemma mcoeff_eq0 p m: (p@_m == 0) = (m \notin msupp p).
  Proof. by rewrite msuppE mem_dom inE /mcoeff negbK. Qed.

  Lemma msupp0: msupp 0%:MP = [::].
  Proof. by rewrite msuppE /= freegU0 dom0. Qed.

  Lemma msupp1: msupp 1%:MP = [:: 0%MM].
  Proof. by rewrite msuppE /= domU1. Qed.

  Lemma msuppC (c : R):
    msupp c%:MP = if c == 0 then [::] else [:: 0%MM].
  Proof. 
    case: (c =P 0)=> [->|/eqP nz_c]; first by rewrite msupp0.
    by rewrite msuppE domU //.
  Qed.

  Lemma mpolyP p q: (forall m, mcoeff m p = mcoeff m q) <-> (p = q).
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

  Lemma add_mpoly0: left_id 0%:MP mpoly_add.
  Proof. by move=> p; apply/mpoly_eqP; rewrite !mpoly_valK freegU0 add0r. Qed.

  Lemma add_mpolyN: left_inverse 0%:MP mpoly_opp mpoly_add.
  Proof. by move=> p; apply/mpoly_eqP; rewrite !mpoly_valK freegU0 addrC subrr. Qed.

  Lemma add_mpolyC: commutative mpoly_add.
  Proof. by move=> p q; apply/mpoly_eqP; rewrite !mpoly_valK addrC. Qed.

  Lemma add_mpolyA: associative mpoly_add.
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

  Lemma scale_mpolyA c1 c2 p:
    c1 *:M (c2 *:M p) = (c1 * c2) *:M p.
  Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerA. Qed.

  Lemma scale_mpoly1m p: 1 *:M p = p.
  Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scale1r. Qed.

  Lemma scale_mpolyDr c p1 p2:
    c *:M (p1 + p2) = c *:M p1 + c *:M p2.
  Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerDr. Qed.

  Lemma scale_mpolyDl p c1 c2:
    (c1 + c2) *:M p = c1 *:M p + c2 *:M p.
  Proof. by apply/mpoly_eqP; rewrite !mpoly_valK scalerDl. Qed.

  Definition mpoly_lmodMixin :=
    LmodMixin scale_mpolyA scale_mpoly1m scale_mpolyDr scale_mpolyDl.

  Canonical mpoly_lmodType :=
    Eval hnf in LmodType R {mpoly R[n]} mpoly_lmodMixin.
  Canonical mpolynomial_lmodType :=
    Eval hnf in LmodType R (mpoly n R) mpoly_lmodMixin.

  Local Notation mcoeff := (@mcoeff n R).

  Lemma mcoeff_is_additive m: additive (mcoeff m).
  Proof. by move=> p q /=; rewrite /mcoeff raddfB. Qed.

  Canonical mcoeff_additive m: {additive {mpoly R[n]} -> R} :=
    Additive (mcoeff_is_additive m).

  Lemma mcoeff0   m   : mcoeff m 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma mcoeffN   m   : {morph mcoeff m: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma mcoeffD   m   : {morph mcoeff m: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma mcoeffB   m   : {morph mcoeff m: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma mcoeffMn  m k : {morph mcoeff m: x / x *+ k} . Proof. exact: raddfMn. Qed.
  Lemma mcoeffMNn m k : {morph mcoeff m: x / x *- k} . Proof. exact: raddfMNn. Qed.

  Lemma mcoeffZ c p m: mcoeff m (c *: p) = c * (mcoeff m p).
  Proof. by rewrite /mcoeff coeffZ. Qed.

  Canonical mcoeff_linear m: {scalar {mpoly R[n]}} :=
    AddLinear ((fun c => (mcoeffZ c)^~ m) : scalable_for *%R (mcoeff m)).

  Local Notation mpolyC := (@mpolyC n R).

  Lemma mpolyC_is_additive: additive mpolyC.
  Proof. by move=> p q; apply/mpoly_eqP; rewrite /= freegUB. Qed.

  Canonical mpolyC_additive: {additive R -> {mpoly R[n]}} :=
    Additive mpolyC_is_additive.

  Lemma mpolyC0     : mpolyC 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma mpolyCN     : {morph mpolyC: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma mpolyCD     : {morph mpolyC: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma mpolyCB     : {morph mpolyC: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma mpolyCMn  k : {morph mpolyC: x / x *+ k} . Proof. exact: raddfMn. Qed.
  Lemma mpolyCMNn k : {morph mpolyC: x / x *- k} . Proof. exact: raddfMNn. Qed.

  Lemma msupp_eq0 p: (msupp p == [::]) = (p == 0).
  Proof.
    case: p=> p /=; rewrite msuppE /GRing.zero /= /mpolyC.
    by rewrite dom_eq0 freegU0 /=.
  Qed.
End MPolyZMod.  

(* -------------------------------------------------------------------- *)
Section MSize.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.
  Implicit Types D : {freeg 'X_{1..n} / R}.

  Lemma mpolyC_eq0 c: (c%:MP == 0 :> {mpoly R[n]}) = (c == 0).
  Proof. (* FIXME: coeffU1 / eqU1 *)
    rewrite eqE /=; apply/idP/eqP=> [|->//].
    by move/freeg_eqP/(_ 0%MM); rewrite !coeffU eqxx !mulr1.
  Qed.

  Definition msize p := \max_(m <- msupp p) (mdeg m).+1.

  Lemma msize0: msize 0 = 0%N.
  Proof. by rewrite /msize msupp0 big_nil. Qed.

  Lemma msizeC c: msize c%:MP = (c != 0%R) :> nat.
  Proof.
    rewrite /msize msuppC; case: (_ == 0).
    by rewrite big_nil. by rewrite big_seq1 mdeg0.
  Qed.

  Lemma msize_mdeg_lt p m: m \in msupp p -> mdeg m < msize p.
  Proof.
    move=> m_in_p; rewrite /msize (bigD1_seq m) //=.
    by rewrite leq_max ltnS leqnn.
  Qed.

  Lemma msize_mdeg_ge p m: msize p <= mdeg m -> m \notin msupp p.
  Proof. by move=> h; apply/negP=> /msize_mdeg_lt; rewrite leqNgt ltnS h. Qed.

  Lemma msuppD_le p q: {subset msupp (p + q) <= msupp p ++ msupp q}.
  Proof. by move=> x => /domD_subset. Qed.

  Lemma msupp_sum_le (T : Type) (F : T -> {mpoly R[n]}) P (r : seq T):
    {subset    msupp (\sum_(i <- r | P i) (F i))
            <= flatten [seq msupp (F i) | i <- r & P i]}.
  Proof.
    elim: r => /= [|x r ih]; first by rewrite !big_nil msupp0.
    rewrite !big_cons; case: (P x)=> // m /msuppD_le.
    by rewrite !mem_cat => /orP [->//|] /ih ->; rewrite orbT.
  Qed.

  Lemma msizeD_le p q: msize (p + q) <= maxn (msize p) (msize q).
  Proof.
    rewrite {1}/msize big_tnth; apply/bigmax_leqP=> /= i _.
    set m := tnth _ _; have: m \in msupp (p + q) by apply/mem_tnth.
    move/msuppD_le; rewrite leq_max mem_cat.
    by case/orP=> /msize_mdeg_lt->; rewrite !simpm.
  Qed.

  Lemma msize_poly_eq0 p: (msize p == 0%N) = (p == 0).
  Proof.
    apply/idP/eqP=> [z_p|->]; last by rewrite msize0.
    apply/mpoly_eqP; move: z_p; rewrite /msize.
    rewrite {2}[p]freeg_mpoly; case: (msupp p).
      by rewrite !big_nil /= freegU0.
    by move=> m q; rewrite !big_cons -leqn0 geq_max.
  Qed.

  Lemma mpolySpred p : p != 0 -> msize p = (msize p).-1.+1.
  Proof. by rewrite -msize_poly_eq0 -lt0n => /prednK. Qed.
End MSize.

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

  Lemma inject_inj n m: injective (@inject n m).
  Proof. by elim: m=> [|m ih] p q //= /polyC_inj /ih. Qed.

  Lemma inject_is_rmorphism n m: rmorphism (@inject n m).
  Proof.
    elim: m => [|m ih] //=; rewrite -/(_ \o _).
    have ->: inject m = RMorphism ih by [].
    by apply/rmorphismP.
  Qed.

  Canonical inject_rmorphism n m := RMorphism (inject_is_rmorphism n m).
  Canonical inject_additive  n m := Additive (inject_is_rmorphism n m).

  Definition inject_cast n m k E: {ipoly R[n]} -> {ipoly R[k]} :=
    ecast k (_ -> {ipoly R[k]}) E (@inject n m).

  Lemma inject_cast_inj n m k E:
    injective (@inject_cast n m k E).
  Proof. by case: k / E; apply/inject_inj. Qed.

  Lemma inject_cast_is_rmorphism n m k E:
    rmorphism (@inject_cast n m k E).
  Proof. by case: k / E; apply/rmorphismP. Qed.

  Canonical inject_cast_rmorphism n m k e := RMorphism (@inject_cast_is_rmorphism n m k e).
  Canonical inject_cast_additive  n m k e := Additive  (@inject_cast_is_rmorphism n m k e).

  Lemma inject1_proof n (i : 'I_n.+1): (n - i + i = n)%N.
  Proof. by rewrite subnK // -ltnS. Qed.

  Definition inject1 n (i : 'I_n.+1) (p : {ipoly R[i]}) : {ipoly R[n]} :=
    inject_cast (inject1_proof i) p.

  Local Notation "c %:IP" := (inject_cast (inject1_proof ord0) c).

  Section IScale.
    Variable n : nat.

    Lemma iscaleA (c1 c2 : R) (p : {ipoly R[n]}):
      c1%:IP * (c2%:IP * p) = (c1 * c2)%:IP * p.
    Proof. by rewrite mulrA rmorphM /=. Qed.

    Lemma iscale1r (p : {ipoly R[n]}): 1%:IP * p = p.
    Proof. by rewrite rmorph1 mul1r. Qed.

    Lemma iscaleDr (c : R) (p q : {ipoly R[n]}):
      c%:IP * (p + q) = c%:IP * p + c%:IP * q.
    Proof. by rewrite mulrDr. Qed.

    Lemma iscaleDl (p : {ipoly R[n]}) (c1 c2 : R):
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

  Lemma mul_poly1_eq0L p q (m : 'X_{1..n} * 'X_{1..n}):
    m.1 \notin msupp p -> p *M_[m] q = 0.
  Proof. by move/memN_msupp_eq0=> ->; rewrite mul0r freegU0. Qed.

  Lemma mul_poly1_eq0R p q (m : 'X_{1..n} * 'X_{1..n}):
    m.2 \notin msupp q -> p *M_[m] q = 0.
  Proof. by move/memN_msupp_eq0=> ->; rewrite mulr0 freegU0. Qed.

  Lemma mpoly_mulwE p q kp kq: msize p <= kp -> msize q <= kq ->
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

  Lemma mpoly_mul_revwE p q kp kq: msize p <= kp -> msize q <= kq ->
    p *M q = [mpoly \sum_(m : 'X_{1..n < kq, kp}) (p *M_[(m.2, m.1)] q)].
  Proof.
    move=> lep leq;  rewrite -pair_bigA_curry exchange_big /=.
    by rewrite pair_bigA /= -mpoly_mulwE //.
  Qed.  

  Implicit Arguments mpoly_mul_revwE [p q].

  Lemma mcoeff_poly_mul p q m k: !|m| < k ->
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

  Lemma mcoeff_poly_mul_rev p q m k: !|m| < k ->
    (p *M q)@_m =
      \sum_(k : 'X_{1..n < k, k} | m == (k.1 + k.2)%MM)
        (p@_k.2 * q@_k.1).
  Proof.
    move=> /mcoeff_poly_mul=> ->; rewrite big_cond_mulrn.
    rewrite -pair_bigA_curry /= exchange_big pair_bigA /=.
    rewrite /= -big_cond_mulrn; apply/eq_big=> //.
    by move=> i /=; rewrite Monoid.mulmC.
  Qed.

  Local Notation "m1 <= m2" := [forall i, m1%MM i <= m2%MM i] : multi_scope.

  Lemma mcoeff_poly_mul_lin p q m k: !|m| < k ->
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
      * by rewrite mnm_addC addmK.
      * by rewrite mnm_addC submK //; apply/mnm_lepP.
    + rewrite negb_forall => /existsP /= [i Nle].
      rewrite big_pred0 //= => h2; apply/negbTE/eqP.
      move/mnmP/(_ i); rewrite mnmDE=> eq; move: Nle.
      by rewrite eq leq_addr.
  Qed.
  Implicit Arguments mcoeff_poly_mul_lin [p q m].

  Local Notation mcoeff_pml  := mcoeff_poly_mul_lin.

  Lemma mcoeff_poly_mul_lin_rev p q m k: !|m| < k ->
    (p *M q)@_m = \sum_(k : 'X_{1..n < k} | (k <= m)%MM) p@_(m-k) * q@_k.
  Proof.
    move=> lt; have/mcoeff_pml := lt => ->.
    have pr (h : 'X_{1..n}) : !|m - h| < k.
      by apply/(leq_ltn_trans (mdegB _ _)).
    pose F (k : 'X_{1..n < k}) := BMultinom (pr k).
    have inv_F (h : 'X_{1..n}): (h <= m)%MM -> (m - (m - h) = h)%MM.
      by move=> le_hm; rewrite submBA // mnm_addC addmK.
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

  Lemma poly_mulA: associative mpoly_mul.
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
    by apply/eq_bigr=> mj le_mj_miBk; rewrite !mulrA !submDA mnm_addC.
  Qed.

  Lemma poly_mul1m: left_id 1%:MP mpoly_mul.
  Proof.
    move=> p; apply/mpoly_eqP/esym; rewrite /mpoly_mul /=.
    rewrite msupp1 -pair_bigA_seq_curry /=.
    rewrite big_seq1 {1}[p]freeg_mpoly /=; apply: eq_bigr.
    by move=> i _; rewrite mpolyCK !simpm.
  Qed.

  Lemma poly_mulm1: right_id 1%:MP mpoly_mul.
  Proof.
    move=> p; apply/mpoly_eqP/esym; rewrite /mpoly_mul /=.
    rewrite msupp1 -pair_bigA_seq_curry /=.
    rewrite exchange_big big_seq1 {1}[p]freeg_mpoly /=.
    by apply: eq_bigr=> i _; rewrite mpolyCK !simpm.
  Qed.

  Lemma poly_mulDl: left_distributive mpoly_mul +%R.
  Proof.
    move=> p q r; pose_big_enough i.
      rewrite !(mpoly_mulwE i (msize r)) //=.
      apply/mpoly_eqP=> /=; rewrite -big_split /=; apply: eq_bigr.
      by case=> [[i1 /= _] [i2 /= _]] _; rewrite freegUD -mulrDl -mcoeffD.
    by close.
  Qed.

  Lemma poly_mulDr: right_distributive mpoly_mul +%R.
  Proof.
    move=> p q r; pose_big_enough i.
      rewrite !(mpoly_mulwE (msize p) i) //=.
      apply/mpoly_eqP=> /=; rewrite -big_split /=; apply: eq_bigr.
      by case=> [[i1 /= _] [i2 /= _]] _; rewrite freegUD -mulrDr -mcoeffD.
    by close.
  Qed.

  Lemma poly_oner_neq0: 1%:MP != 0 :> {mpoly R[n]}.
  Proof. by rewrite mpolyC_eq oner_eq0. Qed.

  Definition mpoly_ringMixin :=
    RingMixin poly_mulA poly_mul1m poly_mulm1
              poly_mulDl poly_mulDr poly_oner_neq0.
  Canonical mpoly_ringType :=
    Eval hnf in RingType {mpoly R[n]} mpoly_ringMixin.
  Canonical mpolynomial_ringType :=
    Eval hnf in RingType (mpoly n R) mpoly_ringMixin.

  Lemma mcoeffM p q m:
    (p * q)@_m =
      \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 + k.2)%MM)
        (p@_k.1 * q@_k.2).
  Proof. by apply: mcoeff_poly_mul. Qed.

  Lemma mcoeffMr p q m:
    (p * q)@_m =
      \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 + k.2)%MM)
        (p@_k.2 * q@_k.1).
  Proof.
    rewrite mcoeffM big_cond_mulrn -pair_bigA_curry /=.
    rewrite exchange_big pair_bigA /= -big_cond_mulrn.
    by apply: eq_bigl=> k /=; rewrite Monoid.mulmC.
  Qed.

  Lemma msuppM_le p q:
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

  Lemma mul_mpolyC c p: c%:MP * p = c *: p.
  Proof.
    have [->|nz_c] := eqVneq c 0; first by rewrite scale0r mul0r.
    apply/mpoly_eqP=> /=; rewrite -pair_bigA_seq_curry /=.
    rewrite msuppC (negbTE nz_c) big_seq1; apply/eq_bigr.
    by move=> i _; rewrite mpolyCK !simpm.
  Qed.

  Lemma mcoeffCM c p m: (c%:MP * p)@_m = c * p@_m.
  Proof. by rewrite mul_mpolyC mcoeffZ. Qed.

  Lemma msuppZ_le (c : R) p:
    {subset msupp (c *: p) <= msupp p}.
  Proof.
    move=> /= m; rewrite !mcoeff_msupp -mul_mpolyC.
    rewrite mcoeffCM; have [->|//] := eqVneq p@_m 0.
    by rewrite mulr0 eqxx.
  Qed.

  Lemma mpolyC_is_multiplicative: multiplicative (mpolyC n (R := R)).
  Proof.
    split=> // p q; apply/mpolyP=> m.
    by rewrite mcoeffCM !mcoeffC mulrA.
  Qed.

  Canonical mpolyC_rmorphism: {rmorphism R -> {mpoly R[n]}} :=
    AddRMorphism mpolyC_is_multiplicative.

  Lemma mpolyC1: mpolyC n 1 = 1.
  Proof. exact: rmorph1. Qed.

  Lemma mpolyC_nat (k : nat): (k%:R)%:MP = k%:R :> {mpoly R[n]}.
  Proof.
    apply/mpolyP=> i; rewrite mcoeffC mcoeffMn mcoeffC.
    by rewrite mul1r commr_nat mulr_natr.
  Qed.

  Lemma mpolyCM: {morph mpolyC n (R := _): p q / p * q}.
  Proof. exact: rmorphM. Qed.

  Lemma msize1: msize 1 = 1%N.
  Proof. by rewrite msizeC oner_eq0. Qed.

  Lemma mpoly_scaleAl c p q: c *: (p * q) = (c *: p) * q.
  Proof. by rewrite -!mul_mpolyC mulrA. Qed.

  Canonical mpoly_lalgType :=
    Eval hnf in LalgType R {mpoly R[n]} mpoly_scaleAl.
  Canonical mpolynomial_lalgType :=
    Eval hnf in LalgType R (mpoly n R) mpoly_scaleAl.

  Lemma alg_mpolyC c: c%:A = c%:MP :> {mpoly R[n]}.
  Proof. by rewrite -mul_mpolyC mulr1. Qed.

  Lemma mcoeff0_is_multiplicative:
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

  Fact mpolyX_key: unit. Proof. by []. Qed.

  Definition mpolyX m: {mpoly R[n]} :=
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

  Lemma msuppX m: msupp 'X_[m] = [:: m].
  Proof. by rewrite unlock /msupp domU1. Qed.

  Lemma mem_msuppXP m m': reflect (m = m') (m' \in msupp 'X_[m]).
  Proof. by rewrite msuppX mem_seq1; apply: (iffP eqP). Qed.

  Lemma mcoeffX m k: 'X_[m]@_k = (m == k)%:R.
  Proof. by rewrite unlock /mpolyX_def mcoeff_MPoly coeffU mul1r. Qed.

  Lemma mpolyX0: 'X_[0] = 1.
  Proof. by apply/mpolyP=> m; rewrite mcoeffX mcoeffC mul1r eq_sym. Qed.

  Lemma mpolyXD m1 m2: 'X_[m1 + m2] = 'X_[m1] * 'X_[m2] :> {mpoly R[n]}.
  Proof.
    apply/mpoly_eqP; rewrite /GRing.mul /= !msuppX big_seq1 /=.
    by rewrite !mcoeffX !eqxx !simpm unlock /=.
  Qed.

  Lemma mpolyX_prod s P:
    \prod_(i <- s | P i) 'X_[i] = 'X_[\sum_(i <- s | P i) i].
  Proof.
    elim: s => [|i s ih]; first by rewrite !big_nil mpolyX0.
    by rewrite !big_cons; case: (P i); rewrite ?mpolyXD ih.
  Qed.

  Lemma mpolyXn m i: 'X_[m] ^+ i = 'X_[m *+ i].
  Proof.
    elim: i=> [|i ih]; first by rewrite expr0 mnm_mulm0 mpolyX0.
    by rewrite mnm_mulmS mpolyXD -ih exprS.
  Qed.

  Lemma mprodXnE (F : 'I_n -> 'X_{1..n}) P m (r : seq _):
      \prod_(i <- r | P i) 'X_[R, F i] ^+ m i
    = 'X_[\sum_(i <- r | P i) (F i *+ m i)].
  Proof.
    elim: r => [|x r ih]; first by rewrite !big_nil mpolyX0.
    by rewrite !big_cons; case: (P x); rewrite ?(mpolyXD, mpolyXn) ih.
  Qed.

  Lemma mprodXE (F : 'I_n -> 'X_{1..n}) P (r : seq _):
      \prod_(i <- r | P i) 'X_[R, F i] = 'X_[\sum_(i <- r | P i) F i].
  Proof.
    pose m   := [multinom 1%N | i < n].
    pose G i := 'X_[R, F i] ^+ m i.
    rewrite (eq_bigr G) => [|i _]; last first.
      by rewrite /G /m mnmE expr1.
    rewrite mprodXnE; congr 'X_[_]; apply/eq_bigr=> i _.
    by rewrite /m mnmE.
  Qed.

  Lemma mpolyXE (s : 'S_n) m:
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
    apply/mnmP=> i; rewrite mnm_sum (bigD1 i) ?big1 //=; last first.
      by move=> j ne_ij; rewrite mnmMn mnm1E (negbTE ne_ij) muln0.
    by rewrite addn0 mnmMn mnm1E eqxx muln1.
  Qed.

  Lemma mpolyXE_id m:
    'X_[m] = \prod_(i < n) 'X_i ^+ m i.
  Proof.
    by rewrite (mpolyXE 1); apply/eq_bigr=> /= i _; rewrite perm1.
  Qed.    

  Lemma mcoeffXn m i k: ('X_[m] ^+ i)@_k = ((m *+ i)%MM == k)%:R.
  Proof. by rewrite mpolyXn mcoeffX. Qed.

  Lemma mpolyE p: p = \sum_(m <- msupp p) (p@_m *: 'X_[m]).
  Proof.
    apply/mpolyP=> m; rewrite {1}[p]freeg_mpoly /= mcoeff_MPoly.
    rewrite !raddf_sum /=; apply/eq_bigr=> i _.
    by rewrite -mul_mpolyC mcoeffCM mcoeffX coeffU.
  Qed.

  Lemma mpolywE k p: msize p <= k ->
    p = \sum_(m : 'X_{1..n < k}) (p@_m *: 'X_[m]).
  Proof.
    move=> lt_pk; pose I := [subFinType of 'X_{1..n < k}].
    rewrite {1}[p]mpolyE (big_mksub I) //=; first last.
      by move=> x /msize_mdeg_lt /leq_trans; apply.
      by rewrite msupp_uniq.
    rewrite big_uncond //= => i.
    by move/memN_msupp_eq0 ->; rewrite scale0r.
  Qed.

  Lemma mpolyME p q:
    p * q = \sum_(m <- msupp p @@ msupp q) (p@_m.1 * q@_m.2) *: 'X_[m.1 + m.2].
  Proof.
    apply/mpolyP=> m; rewrite {1}/GRing.mul /= mcoeff_MPoly.
    rewrite !raddf_sum; apply/eq_bigr=> i _ /=.
    by rewrite coeffU -mul_mpolyC mcoeffCM mcoeffX.
  Qed.

  Lemma mpolywME p q k: msize p <= k -> msize q <= k ->
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

  Lemma commr_mpolyX m p: GRing.comm p 'X_[m].
  Proof.
    apply/mpolyP=> k; rewrite mcoeffM mcoeffMr.
    by apply/eq_bigr=> /= i _; rewrite !mcoeffX GRing.commr_nat.
  Qed.

  Lemma mcoeffMX p m k: (p * 'X_[m])@_(m + k) = p@_k.
  Proof.
    rewrite commr_mpolyX mpolyME msuppX -pair_bigA_seq_curry /=.
    rewrite big_seq1 [X in _=X@__]mpolyE !raddf_sum /=.
    apply/eq_bigr=> i _; rewrite !mcoeffZ !mcoeffX eqxx mul1r.
    by rewrite eqm_add2l.
  Qed.

  Lemma mcoeff_mpoly (E : 'X_{1..n} -> R) m k: mdeg m < k ->
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

  Lemma MPolyU c m: MPoly << c *g m >> = c *: 'X_[m].
  Proof.
    apply/mpolyP=> k; rewrite mcoeff_MPoly.
    by rewrite mcoeffZ mcoeffX coeffU.
  Qed.

  Lemma mpolyrect (P : {mpoly R[n]} -> Type):
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

  Lemma mpolyind (P : {mpoly R[n]} -> Prop):
       P 0
    -> (forall c m p,
          m \notin msupp p -> c != 0 ->
            P p -> P (c *: 'X_[m] + p))
    -> forall p, P p.
  Proof. apply/(@mpolyrect P). Qed.

  Lemma mpolyrect_r (P : {mpoly R[n]} -> Type):
       P 0
    -> (forall c m p,
             m \notin msupp p -> c != 0
          -> (forall q, {subset msupp q <= msupp p} -> P q)
          -> P (c *: 'X_[m] + p))
    -> forall p, P p.
  Proof.
    move=> h0 hS p; have: {subset msupp p <= msupp p} by [].
    elim/mpolyrect: p {-2}p => [p|c m p m_notin_p nz_c ih q le].
      rewrite msupp0 => /(uniq_leq_size (msupp_uniq _)) /=.
      by rewrite leqn0 size_eq0 msupp_eq0 => /eqP->.
    case: (boolP (m \in msupp q)); last first.
      move=> m_notin_q; apply/ih=> /= h h_in_q.
      have ne_hm: h != m.
        by apply/eqP=> eq; rewrite -eq h_in_q in m_notin_q.
      have := h_in_q => /le /msuppD_le; rewrite mem_cat.
      case/orP=> // /msuppZ_le /mem_msuppXP.
      by move/esym/eqP; rewrite (negbTE ne_hm).
    move=> m_in_q; rewrite [q]mpolyE (bigD1_seq m) //=.
    pose r : {mpoly R[n]} := \sum_(h <- msupp q | h != m) q@_h *: 'X_[h].
    have msuppr: {subset msupp r <= [seq h <- msupp q | h != m]}.
      move=> /= h /msupp_sum_le /flattenP /= [s] /mapP /=.
      case=> x; rewrite mem_filter => /andP [ne_xm x_notin_q] ->.
      by move/msuppZ_le/mem_msuppXP=> <-; rewrite mem_filter ne_xm.
    apply/hS; first (apply/contraT; rewrite negbK).
    - by move/msuppr; rewrite mem_filter eqxx.
    - by rewrite -mcoeff_msupp.
    - move=> s les; apply/ih=> /= h /les /msuppr.
      rewrite mem_filter=> /andP [nz_hm] /le /msuppD_le.
      rewrite mem_cat; case/orP=> // /msuppZ_le /mem_msuppXP.
      by move/esym/eqP; rewrite (negbTE nz_hm).
  Qed.
End MPolyVarTheory.

(* -------------------------------------------------------------------- *)
Section MPolyLead.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.

  Definition mlead p : 'X_{1..n} :=
    (\max_(m <- msupp p) m)%O.

  Definition mleadC (c : R): mlead c%:MP = 0%MM.
  Proof.
    rewrite /mlead msuppC; case: eqP=> _.
      by rewrite big_nil.
      by rewrite unlock /= maxo0.
  Qed.

  Definition mlead0: mlead 0 = 0%MM.
  Proof. by rewrite mleadC. Qed.

  Definition mlead1: mlead 1 = 0%MM.
  Proof. by rewrite mleadC. Qed.

  Lemma mlead_supp p: p != 0 -> mlead p \in msupp p.
  Proof.
    move=> nz_p; case: (eq_bigmaxo id (r := msupp p)) => /=.
      by rewrite msupp_eq0.
    by rewrite /mlead=> m /andP [m_in_p /eqP ->].
  Qed.

  Lemma mlead_deg p: p != 0 -> (mdeg (mlead p)).+1 = msize p.
  Proof.
    move=> /mlead_supp lc_in_p; rewrite /mlead /msize mdeg_bigmax.
    have: msupp p != [::] by case: (msupp p) lc_in_p.
    elim: (msupp p)=> [|m [|m' r] ih] // _; first by rewrite !big_seq1.
    by rewrite big_cons -maxnSS {}ih // !big_cons.
  Qed.

  Lemma msupp_le_mlead p m: m \in msupp p -> (m <= mlead p)%O.
  Proof. by move=> m_in_p; apply/(leo_bigmax id)=> //; apply/lem_total. Qed.

  Lemma mleadc_eq0 p: (p@_(mlead p) == 0) = (p == 0).
  Proof.
    apply/idP/idP => [|/eqP->]; last by rewrite mcoeff0.
    by case: (p =P 0) => // /eqP /mlead_supp; rewrite mcoeff_eq0 => ->.
  Qed.

  Lemma mleadM p q: (mlead (p * q) <= (mlead p + mlead q)%MM)%O.
  Proof.
    have [->|] := eqVneq (p * q) 0; first by rewrite mlead0 le0o.
    move/mlead_supp/msuppM_le/allpairsP => [[m1 m2] /=] [m1_in_p m2_in_q ->].
    by apply/lem_add; apply/msupp_le_mlead.
  Qed.

  Notation mleadc p := (p@_(mlead p)).

  Lemma mleadcC (c : R): mleadc c%:MP_[n] = c.
  Proof. by rewrite mleadC mcoeffC eqxx mulr1. Qed.

  Lemma mleadc0: mleadc (0 : {mpoly R[n]}) = 0.
  Proof. by rewrite mleadcC. Qed.

  Lemma mleadc1: mleadc (1 : {mpoly R[n]}) = 1.
  Proof. by rewrite mleadcC. Qed.

  Lemma mleadcM p q:
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

  Lemma mleadM_proper p q: mleadc p * mleadc q != 0 ->
    mlead (p * q) = (mlead p + mlead q)%MM.
  Proof.
    move: (mleadM p q); rewrite leo_eqVlt; case/orP=> [/eqP->//|].
    rewrite -mleadcM mcoeff_eq0 negbK => ltm /msupp_le_mlead lem.
    by move: (lto_leo_trans ltm lem); rewrite ltoo.
  Qed.    
End MPolyLead.

Notation mleadc p := (p@_(mlead p)).

(* -------------------------------------------------------------------- *)
Section MPoly0.
  Variable R : ringType.

  Lemma mpolyKC: cancel (@mcoeff 0 R 0%MM) (@mpolyC 0 R).
  Proof.
    move=> p; apply/mpolyP=> m; rewrite mcoeffC.
    case: (m =P 0%MM)=> [->|//]; first by rewrite mulr1.
    by case: m=> m; rewrite tuple0 //= => /eqP; rewrite eqE.
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

  Lemma mderivE p (i : 'I_n) k: msize p <= k ->
    p^`M(i) = \sum_(m : 'X_{1..n < k}) ((m i)%:R * p@_m) *: 'X_[m - U_(i)].
  Proof.
    pose I := [subFinType of 'X_{1..n < k}].
    move=> le_pk; rewrite /mderiv (big_mksub I) /=; first last.
      by move=> x /msize_mdeg_lt/leq_trans/(_ le_pk).
      by rewrite msupp_uniq.
    rewrite big_uncond //= => j /memN_msupp_eq0 ->.
    by rewrite mulr0 scale0r.
  Qed.
  Implicit Arguments mderivE [p i].

  Lemma mcoeff_deriv i m p: p^`M(i)@_m = p@_(m + U_(i)) *+ (m i).+1.
  Proof.
    pose_big_enough j; first rewrite {2}[p](mpolywE (k := j)) //.
      rewrite !(mderivE j) // !raddf_sum -sumrMnl; apply/eq_bigr.
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

  Lemma mderiv_is_linear i: linear (mderiv i).
  Proof.
    move=> c p q; pose_big_enough j; first rewrite !(mderivE j) //.
      rewrite scaler_sumr -big_split /=; apply/eq_bigr=> k _.
      rewrite !scalerA -scalerDl; congr (_ *: _).
      by rewrite mcoeffD mcoeffZ mulrDr !mulrA commr_nat.
    by close.
  Qed.

  Canonical mderiv_additive i := Additive (mderiv_is_linear i).
  Canonical mderiv_linear   i := Linear   (mderiv_is_linear i).

  Lemma mderiv0 i: mderiv i 0 = 0.
  Proof. exact: raddf0. Qed.

  Lemma mderivC i c: mderiv i c%:MP = 0.
  Proof.
    apply/mpolyP=> m; rewrite mcoeff0 mcoeff_deriv mcoeffC.
    by rewrite mnmD_eq0 mnm1_eq0 andbF mulr0 mul0rn.
  Qed.

  Lemma mderivX i m: mderiv i 'X_[m] = (m i)%:R *: 'X_[m - U_(i)].
  Proof. by rewrite /mderiv msuppX big_seq1 mcoeffX eqxx mulr1. Qed.

  Lemma commr_mderivX i m p: GRing.comm p ('X_[m])^`M(i).
  Proof.
    rewrite /GRing.comm mderivX -mul_mpolyC mpolyC_nat.
    by rewrite -{1}commr_nat mulrA commr_nat commr_mpolyX mulrA.
  Qed.

  Lemma mderivN i: {morph mderiv i: x / - x}.
  Proof. exact: raddfN. Qed.

  Lemma mderivD i: {morph mderiv i: x y / x + y}.
  Proof. exact: raddfD. Qed.

  Lemma mderivB i: {morph mderiv i: x y / x - y}.
  Proof. exact: raddfB. Qed.

  Lemma mderivMn i k: {morph mderiv i: x / x *+ k}.
  Proof. exact: raddfMn. Qed.

  Lemma mderivMNn i k: {morph mderiv i: x / x *- k}.
  Proof. exact: raddfMNn. Qed.

  Lemma mderivZ i c p: (c *: p)^`M(i) = c *: p^`M(i).
  Proof. by rewrite linearZ. Qed.

  Lemma mderiv_mulC i c p : (c%:MP * p)^`M(i) = c%:MP * p^`M(i).
  Proof. by rewrite !mul_mpolyC mderivZ. Qed.

  Lemma mderivCM i c p: (c *: p)^`M(i) = c *: p^`M(i).
  Proof.
    apply/mpolyP=> k; rewrite mcoeff_deriv !mcoeffZ.
    by rewrite -mulrnAr -mcoeff_deriv.
  Qed.

  Lemma mderivM i p q: (p * q)^`M(i) = (p^`M(i) * q) + (p * q^`M(i)).
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
    apply/esym; rewrite mnm_addC addmBA; last by rewrite lep1mP.
    have [z_hi|ne_hi] := eqVneq (h i) 0%N.
      by rewrite z_hi add0n scale0r addr0.
    rewrite addrC mnm_addC addmBA; last by rewrite lep1mP.
    by rewrite mnm_addC -scalerDl natrD.
  Qed.

  Lemma mderiv_comm i j p: p^`M(i)^`M(j) = p^`M(j)^`M(i).
  Proof.
    pose_big_enough k; first pose mderivE := (mderivE k).
      rewrite ![p^`M(_)]mderivE // !raddf_sum /=; apply/eq_bigr.
      move=> l _; rewrite !mderivCM !mderivX !scalerA.
      rewrite !submDA mnm_addC -!commr_nat -!mulrA -!natrM.
      congr (_ * _%:R *: _); rewrite !mnmBE !mnm1E eq_sym.
      by case: eqP=> [->//|_] /=; rewrite !subn0 mulnC.
    by close.
  Qed.

  Definition mderivn i k p : {mpoly R[n]} :=
    iter k (mderiv i) p.

  Notation "p ^`M ( i , k )" := (mderivn i k p).

  Lemma mderivn0 i p: p^`M(i, 0) = p.
  Proof. by []. Qed.

  Lemma nderivn1 i p: p^`M(i, 1) = p^`M(i).
  Proof. by []. Qed.

  Lemma mderivnS i k p: p^`M(i, k.+1) = p^`M(i, k)^`M(i).
  Proof. by []. Qed.

  Lemma mderivSn i k p: p^`M(i, k.+1) = p^`M(i)^`M(i, k).
  Proof. by rewrite /mderivn iterSr. Qed.

  Lemma mderivn_is_linear i k: linear (mderivn i k).
  Proof. by elim: k=> //= k ih c p q /=; rewrite ih mderivD mderivZ. Qed.

  Canonical mderivn_additive i k := Additive (mderivn_is_linear i k).
  Canonical mderivn_linear   i k := Linear   (mderivn_is_linear i k).

  Definition mderivm m p : {mpoly R[n]} :=
    foldr (fun i p => mderivn i (m i) p) p (enum 'I_n).
End MPolyDeriv.

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

  Lemma mmap11 h: mmap1 h 0%MM = 1.
  Proof. by rewrite /mmap1 big1 // => /= i _; rewrite mnm0E expr0. Qed.

  Lemma mmap1U h i: mmap1 h U_(i) = h i.
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

  Lemma commr_mmap1_M h m1 m2:
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

    Lemma mmapE p i: msize p <= i ->
      p^[f,h] = \sum_(m : 'X_{1..n < i}) (f p@_m) * m^[h].
    Proof.
      move=> le_pi; set I := [subFinType of 'X_{1..n < i}].
      rewrite /mmap (big_mksub I) ?msupp_uniq //=; first last.
        by move=> x /msize_mdeg_lt /leq_trans; apply.
      rewrite big_uncond //= => j /memN_msupp_eq0 ->.
      by rewrite raddf0 mul0r.
    Qed.
    Implicit Arguments mmapE [p].

    Lemma mmap_is_additive: additive (mmap f h).
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

    Lemma mmapC c: mmap c%:MP = f c.
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

    Lemma mmapX m: ('X_[m])^[f,h] = m^[h].
    Proof. by rewrite /mmap msuppX big_seq1 mcoeffX eqxx rmorph1 mul1r. Qed.

    Lemma mmapZ c p: (c *: p)^[f,h] = (f c) * p^[f,h].
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
Lemma mmap1_eq n (R : ringType) (f1 f2 : 'I_n -> R) m:
  f1 =1 f2 -> mmap1 f1 m = mmap1 f2 m.
Proof.
  move=> eq_f; rewrite /mmap1; apply/eq_bigr.
  by move=> /= i _; rewrite eq_f.
Qed.

Lemma mmap1_id n (R : ringType) m:
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

  Lemma mmap_is_multiplicative: multiplicative (mmap f h).
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

  Lemma mpoly_mulC p q: p * q = q * p.
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

  Implicit Types p q : {mpoly R[n]}.
  Implicit Types lp : n.-tuple {mpoly R[n]}.

  Definition comp_mpoly lq p: {mpoly R[n]}:=
    mmap (@mpolyC n R) (tnth lq) p.

  Local Notation "p \mPo lq" := (comp_mpoly lq p).

  Lemma comp_mpolyE p lq:
    p \mPo lq = \sum_(m <- msupp p) (p@_m *: \prod_(i < n) (tnth lq i)^+(m i)).
  Proof. by apply/eq_bigr=> i _; rewrite mul_mpolyC. Qed.

  Lemma comp_mpoly_is_additive lq : additive (comp_mpoly lq).
  Proof. by move=> p q; rewrite /comp_mpoly -mmapB. Qed.

  Canonical comp_mpoly_additive lq := Additive (comp_mpoly_is_additive lq).

  Lemma comp_mpoly0   lq   : 0 \mPo lq = 0                     . Proof. exact: raddf0. Qed.
  Lemma comp_mpolyN   lq   : {morph comp_mpoly lq: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma comp_mpolyD   lq   : {morph comp_mpoly lq: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma comp_mpolyB   lq   : {morph comp_mpoly lq: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma comp_mpolyMn  lq k : {morph comp_mpoly lq: x / x *+ k} . Proof. exact: raddfMn. Qed.
  Lemma comp_mpolyMNn lq k : {morph comp_mpoly lq: x / x *- k} . Proof. exact: raddfMNn. Qed.

  Lemma comp_mpoly_is_linear lq: linear (comp_mpoly lq).
  Proof.
    move=> c p q; rewrite comp_mpolyD /comp_mpoly.
    by rewrite mmapZ mul_mpolyC.
  Qed.

  Canonical comp_mpoly_linear lq := Linear (comp_mpoly_is_linear lq).

  Lemma comp_mpoly1 lq: 1 \mPo lq = 1.
  Proof. by rewrite /comp_mpoly -mpolyC1 mmapC. Qed.

  Lemma comp_mpolyC c lq: c%:MP \mPo lq = c%:MP.
  Proof. by rewrite /comp_mpoly mmapC. Qed.

  Lemma comp_mpolyZ c p lq: (c *: p) \mPo lq = c *: (p \mPo lq).
  Proof. by apply/linearZ. Qed.

  Lemma comp_mpolyX i lq: 'X_i \mPo lq = lq`_i.
  Proof. by rewrite /comp_mpoly mmapX mmap1U -tnth_nth. Qed.

  Lemma comp_mpoly_id p: p \mPo [tuple 'X_i | i < n] = p.
  Proof.
    rewrite [p]mpolyE raddf_sum /=; apply/eq_bigr.
    move=> m _; rewrite comp_mpolyZ; congr (_ *: _).
    rewrite /comp_mpoly mmapX -mmap1_id; apply/mmap1_eq.
    by move=> /= i; rewrite tnth_map tnth_ord_tuple.
  Qed.
End MPolyComp.

(* -------------------------------------------------------------------- *)
Section MEval.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.
  Implicit Types v : n.-tuple R.

  Definition meval v p := mmap idfun (tnth v) p.

  Lemma mevalE v p: meval v p =
    \sum_(m <- msupp p) p@_m * (\prod_i (tnth v i)^+(m i)).
  Proof. by []. Qed.

  Lemma meval_is_additive v: additive (meval v).
  Proof. by apply/mmap_is_additive. Qed.

  Canonical meval_additive v := Additive (meval_is_additive v).

  Lemma meval0   v   : meval v 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma mevalN   v   : {morph meval v: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma mevalD   v   : {morph meval v: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma mevalB   v   : {morph meval v: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma mevalMn  v k : {morph meval v: x / x *+ k} . Proof. exact: raddfMn. Qed.
  Lemma mevalMNn v k : {morph meval v: x / x *- k} . Proof. exact: raddfMNn. Qed.

  Lemma mevalC v c: meval v c%:MP = c.
  Proof. by rewrite /meval mmapC. Qed.

  Lemma meval1 v: meval v 1 = 1.
  Proof. by apply/mevalC. Qed.

  Lemma mevalX v i: meval v 'X_i = tnth v i.
  Proof. by rewrite /meval mmapX mmap1U. Qed.

  Lemma meval_is_scalable v: scalable_for *%R (meval v).
  Proof. by move=> /= c p; rewrite /meval mmapZ. Qed.

  Lemma mevalZ v c p: meval v (c *: p) = c * (meval v p).
  Proof. exact: meval_is_scalable. Qed.
End MEval.

Notation "p .@[ v ]" := (@meval _ _ v p).

(* -------------------------------------------------------------------- *)
Section MEvalCom.
  Variable n : nat.
  Variable R : comRingType.

  Implicit Types p q r : {mpoly R[n]}.
  Implicit Types v : n.-tuple R.

  Lemma meval_is_lrmorphism v: lrmorphism_for *%R (meval v).
  Proof.
    split; first split.
    + by apply/mmap_is_additive.
    + by apply/mmap_is_multiplicative.
    by move=> /= c p; rewrite /meval mmapZ /=.
  Qed.

  Canonical meval_rmorphism  v := RMorphism (meval_is_lrmorphism v).
  Canonical meval_linear     v := AddLinear (meval_is_lrmorphism v).
  Canonical meval_lrmorphism v := [lrmorphism of meval v].

  Lemma mevalM v: {morph meval v: x y / x * y}.
  Proof. exact: rmorphM. Qed.
End MEvalCom.

(* -------------------------------------------------------------------- *)
Section MPolyMap.
  Variable n   : nat.
  Variable R S : ringType.

  Implicit Types p q r : {mpoly R[n]}.

  Section Defs.
    Variable f : R -> S.

    Definition map_mpoly p: {mpoly S[n]} :=
      mmap ((@mpolyC n _) \o f) (fun i => 'X_i) p.
  End Defs.

  Section Additive.
    Variable f : {additive R -> S}.

    Local Notation "p ^f" := (map_mpoly f p).

    Lemma map_mpoly_is_additive: additive (map_mpoly f).
    Proof. by apply/mmap_is_additive. Qed.

    Canonical map_mpoly_additive := Additive map_mpoly_is_additive.

    Lemma map_mpolyE p k: msize p <= k ->
      p^f = \sum_(m : 'X_{1..n < k}) (f p@_m) *: 'X_[m].
    Proof.
      rewrite /map_mpoly; move/mmapE=> -> /=; apply/eq_bigr.
      by move=> i _; rewrite mmap1_id mul_mpolyC.
    Qed.
    Implicit Arguments map_mpolyE [p].

    Lemma mcoeff_map_mpoly m p: p^f@_m = f p@_m.
    Proof.
      pose_big_enough i; first rewrite (map_mpolyE i) //.
        by rewrite (mcoeff_mpoly (fun m => (f p@_m))).
      by close.
    Qed.
  End Additive.

  Section Multiplicative.
    Variable f : {rmorphism R -> S}.

    Local Notation "p ^f" := (map_mpoly f p).

    Lemma map_mpoly_is_multiplicative: multiplicative (map_mpoly f).
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

  Lemma mpolyOver_mpoly (S : pred_class) E:
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

    Lemma mpolyOverP {p}: reflect (forall m, p@_m \in kS) (p \in mpolyOver kS).
    Proof.
      case: p=> E; rewrite qualifE /=; apply: (iffP allP); last first.
        by move=> h x /mapP /= [m m_in_E] ->; apply/h.
      move=> h m; case: (boolP (m \in msupp (MPoly E))).
        by move=> m_in_E; apply/h/map_f.
        by rewrite -mcoeff_eq0 => /eqP->; rewrite rpred0.
    Qed.

    Lemma mpolyOverC c: (c%:MP \in mpolyOver kS) = (c \in kS).
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

    Lemma mpolyOver_mulr_closed: mulr_closed (mpolyOver kS).
    Proof.
      split=> [|p q /mpolyOverP Sp /mpolyOverP Sq].
        by rewrite mpolyOverC rpred1.
      apply/mpolyOverP=> i; rewrite mcoeffM rpred_sum //.
      by move=> j _; apply: rpredM.
    Qed.

    Canonical mpolyOver_mulrPred := MulrPred mpolyOver_mulr_closed.
    Canonical pmolyOver_semiringPred := SemiringPred mpolyOver_mulr_closed.

    Lemma mpolyOverZ: {in kS & mpolyOver kS, forall c p, c *: p \is a mpolyOver kS}.
    Proof.
      move=> c p Sc /mpolyOverP Sp; apply/mpolyOverP=> i.
      by rewrite mcoeffZ rpredM ?Sp. 
    Qed.

    Lemma mpolyOverX m: 'X_[m] \in mpolyOver kS.
    Proof. by rewrite qualifE msuppX /= mcoeffX eqxx rpred1. Qed.

    Lemma rpred_mhorner:
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

    Lemma mpolyOverXaddC m c: ('X_[m] + c%:MP \in mpolyOver kS) = (c \in kS).
    Proof. by rewrite rpredDl ?mpolyOverX ?mpolyOverC. Qed.
  End MPolyOverRing.
End MPolyOver.

(* -------------------------------------------------------------------- *)
Section MPolyIdomain.
  Variable n : nat.
  Variable R : idomainType.

  Implicit Types p q r : {mpoly R[n]}.

  Lemma msizeM p q: p != 0 -> q != 0 ->
    msize (p * q) = (msize p + msize q).-1.
  Proof.
    move=> nz_p nz_q; have lm_pq: mlead (p * q) = (mlead p + mlead q)%MM.
      by rewrite mleadM_proper // mulf_neq0 ?mleadc_eq0.
    rewrite -!mlead_deg //; last first.
      by rewrite -mleadc_eq0 lm_pq mleadcM ?mulf_neq0 ?mleadc_eq0.
    rewrite !(addnS, addSn) /= mleadM_proper ?mdegD //.
    by rewrite mulf_neq0 ?mleadc_eq0.
  Qed.

  Lemma mpoly_idomainAxiom p q:
    p * q = 0 -> (p == 0) || (q == 0).
  Proof.
    move=> z_pq; apply/norP; case=> [nz_p nz_q].
    move/eqP: (msizeM nz_p nz_q); rewrite eq_sym z_pq.
    by rewrite msize0 (mpolySpred nz_p) (mpolySpred nz_q) addnS.
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

  Lemma msize1_polyC p: msize p <= 1 -> p = (p@_0)%:MP.
  Proof.
    move=> le_p_1; apply/mpolyP=> m; rewrite mcoeffC.
    case: (m =P 0%MM)=> [->|/eqP]; first by rewrite mulr1.
    rewrite mulr0 -mdeg_eq0 => nz_m; rewrite memN_msupp_eq0 //.
    by apply/msize_mdeg_ge; rewrite 1?(@leq_trans 1) // lt0n.
  Qed.

  Lemma msize_poly1P p: reflect (exists2 c, c != 0 & p = c%:MP) (msize p == 1%N).
  Proof.
    apply: (iffP eqP)=> [pC|[c nz_c ->]]; last by rewrite msizeC nz_c.
    have def_p: p = (p@_0)%:MP by rewrite -msize1_polyC ?pC.
    by exists p@_0; rewrite // -(mpolyC_eq0 n) -def_p -msize_poly_eq0 pC.
  Qed.

  Lemma mpoly_intro_unit p q: q * p = 1 -> p \in mpoly_unit.
  Proof.
    move=> qp1; apply/andP; split; last first.
      apply/unitrP; exists q@_0.
      by rewrite 2!mulrC -rmorphM qp1 rmorph1.
    apply/eqP/msize1_polyC; have: msize (q * p) == 1%N.
      by rewrite qp1 msize1.
    have [-> | nz_p] := eqVneq p 0; first by rewrite mulr0 msize0.
    have [-> | nz_q] := eqVneq q 0; first by rewrite mul0r msize0.
    rewrite msizeM // (mpolySpred nz_p) (mpolySpred nz_q).
    by rewrite addnS addSn !eqSS addn_eq0 => /andP[] _ /eqP->.
  Qed.

  Lemma mpoly_inv_out: {in [predC mpoly_unit], mpoly_inv =1 id}.
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

  Lemma msuppZ (c : R) p:
    perm_eq (msupp (c *: p)) (if c == 0 then [::] else msupp p).
  Proof.
    case: eqP=> [->|/eqP nz_c]; first by rewrite scale0r msupp0.
    apply/uniq_perm_eq=> // m; rewrite !mcoeff_msupp.
    by rewrite mcoeffZ mulf_eq0 (negbTE nz_c).
  Qed.
End MPolyIdomain.

(* -------------------------------------------------------------------- *)
Section MPolySym.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.

  Definition msym (s : 'S_n) p : {mpoly R[n]} :=
    mmap (@mpolyC n R) (fun i => 'X_(s i)) p.

  Local Notation "m # s" := [multinom m (s i) | i < n]
    (at level 40, left associativity, format "m # s").

  Lemma msymE p (s : 'S_n) k: msize p <= k ->
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

  Lemma mcoeff_sym p (s : 'S_n) m: (msym s p)@_m = p@_(m#s).
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

  Lemma msymX m s: msym s 'X_[m] = 'X_[m#(s^-1)%g].
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

  Lemma msym_is_multiplicative s: multiplicative (msym s).
  Proof.
    apply/commr_mmap_is_multiplicative=> /=.
    + by move=> i  x; apply/commr_mpolyX.
    + move=> p m1 m2 /=; rewrite /mmap1; elim/big_rec: _.
        by apply/commr1.
        by move=> /= i q _; apply/commrM/commrX/commr_mpolyX.
  Qed.

  Canonical msym_multiplicative s := AddRMorphism (msym_is_multiplicative s).

  Lemma msym1 s: msym s 1 = 1.
  Proof. exact: rmorph1. Qed.

  Lemma msymM s: {morph msym s: x y / x * y}.
  Proof. exact: rmorphM. Qed.

  Lemma msymZ c p s: msym s (c *: p) = c *: (msym s p).
  Proof.
    pose_big_enough i; first rewrite !(msymE s i) //.
      rewrite scaler_sumr; apply/eq_bigr => j _.
      by rewrite mcoeffZ scalerA.
    by close.
  Qed.

  Canonical msym_linear (s : 'S_n) : {linear {mpoly R[n]} -> {mpoly R[n]}} :=
    AddLinear ((fun c => (msymZ c)^~ s) : scalable_for *:%R (msym s)).

  Canonical msym_lrmorphism s := [lrmorphism of msym s].

  Definition symmetric: qualifier 0 {mpoly R[n]} :=
    [qualify p | [forall s, msym s p == p]].

  Fact symmetric_key: pred_key symmetric. Proof. by []. Qed.
  Canonical symmetric_keyed := KeyedQualifier symmetric_key.

  Lemma issymP p: reflect (forall s, msym s p = p) (p \is symmetric).
  Proof.
    apply: (iffP forallP)=> /= h s; last by rewrite h.
    by rewrite (eqP (h s)).
  Qed.

  Lemma sym_zmod: zmod_closed symmetric.
  Proof.
    split=> [|p q /issymP sp /issymP sq]; apply/issymP=> s.
      by rewrite msym0.
    by rewrite msymB sp sq.
  Qed.

  Canonical sym_opprPred := OpprPred sym_zmod.
  Canonical sym_addrPred := AddrPred sym_zmod.
  Canonical sym_zmodPred := ZmodPred sym_zmod.

  Lemma sym_mulr_closed: mulr_closed symmetric.
  Proof.
    split=> [|p q /issymP sp /issymP sq]; apply/issymP=> s.
      by rewrite msym1.
    by rewrite msymM sp sq.
  Qed.

  Canonical sym_mulrPred     := MulrPred     sym_mulr_closed.
  Canonical sym_smulrPred    := SmulrPred    sym_mulr_closed.
  Canonical sym_semiringPred := SemiringPred sym_mulr_closed.
  Canonical sym_subringPred  := SubringPred  sym_mulr_closed.

  Lemma sym_submod_closed: submod_closed symmetric.
  Proof.
    split=> [|c p q /issymP sp /issymP sq]; apply/issymP=> s.
      by rewrite msym0.
    by rewrite msymD msymZ sp sq.
  Qed.

  Canonical sym_submodPred := SubmodPred sym_submod_closed.
  Canonical sym_subalgPred := SubalgPred sym_submod_closed.

  Lemma issym_msupp p (s : 'S_n) (m : 'X_{1..n}): p \is symmetric ->
    (m#s \in msupp p) = (m \in msupp p).
  Proof. by rewrite !mcoeff_msupp -mcoeff_sym => /issymP ->. Qed.

  Local Notation "m # s" := [multinom m (s i) | i < n]
    (at level 40, left associativity, format "m # s").

  Lemma msym_coeff (p : {mpoly R[n]}) (m : 'X_{1..n}) (s : 'S_n):
    p \is symmetric -> p@_(m#s) = p@_m.
  Proof.
    move/issymP=> /(_ s^-1)%g {1}<-; rewrite mcoeff_sym.
    by congr (_@__); apply/mnmP=> i /=; rewrite !mnmE permKV.     
  Qed.
End MPolySym.

Implicit Arguments symmetric [n R].

(* -------------------------------------------------------------------- *)
Section MElemPolySym.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.

  Definition mesym (k : nat): {mpoly R[n]} :=
    \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i.

  Local Notation "''s_' k" := (@mesym k).

  Definition tmono (n : nat) (h : seq 'I_n) :=
    sorted ltn (map val h).

  Lemma uniq_tmono (h : seq 'I_n): tmono h -> uniq h.
  Proof.
    rewrite /tmono => /sorted_uniq; rewrite (map_inj_uniq val_inj).
    by apply; [apply/ltn_trans | move=> ?; rewrite /ltn /= ltnn].
  Qed.

  Lemma eq_tmono (h1 h2 : seq 'I_n):
    tmono h1 -> tmono h2 -> h1 =i h2 -> h1 = h2.
  Proof.
    move=> tm1 tm2 h; apply/(inj_map val_inj).
    apply/(eq_sorted_irr (leT := ltn))=> //.
      by apply/ltn_trans.
      by move=> ?; rewrite /ltn /= ltnn.
    move=> m; apply/mapP/mapP; case=> /= x;
      by rewrite (h, =^~ h)=> {h} h ->; exists x.
  Qed.

  Lemma mesym_tupleE (k : nat): 's_k =
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

  Definition mechar k (m : 'X_{1..n}) :=
    (mdeg m == k) && [forall i, m i <= 1%N].

  Lemma mcoeff_mesym (k : nat) m: ('s_k)@_m = (mechar k m)%:R.
  Proof.
    pose P (h : {set 'I_n}) := (\sum_(i in h) U_(i))%MM.
    have PE h i: P h i = (i \in h).
      rewrite mnm_sum (eq_bigr (fun x => (x == i : nat))); last first.
        by move=> /= j _; rewrite mnm1E.
      case mem_ih: (i \in h).
        by rewrite (bigD1 i) //= eqxx big1 // => j /andP [_ /negbTE ->].
      rewrite big1 // => j mem_jh; case: eqP=> //= eq_ji.
      by move: mem_ih mem_jh; rewrite eq_ji => ->.
    have mdeg_P h: mdeg (P h) = #|h|.
      rewrite /P mdeg_sum (eq_bigr (fun _ => 1%N)) ?sum1_card //.
      by move=> /= i _; rewrite mdeg1.
    have inj_P: injective P.
      move=> h1 h2 /mnmP eq; apply/setP=> /= i.
      by move/(_ i): eq; rewrite !PE; do! case: (_ \in _).
    rewrite /mesym raddf_sum (eq_bigr (fun h => (P h == m)%:R)); last first.
      by move=> h _ /=; rewrite mprodXE mcoeffX.
    rewrite /mechar; case: (mdeg m =P k) => /=; last first.
      move/eqP=> ne_m_k; rewrite big1 // => i eq_i_k.
      case: eqP=> //= /(congr1 mdeg); rewrite mdeg_P (eqP eq_i_k).
      by move/eqP; rewrite eq_sym (negbTE ne_m_k).
    move=> eq_m_k; case: forallP => [/= mx_le1|/forallP]; last first.
      rewrite negb_forall => /existsP /= [i Nle_mi_1].
      rewrite big1 // => j _; case: eqP=> //= /mnmP.
      move/(_ i); rewrite PE => /esym miE; move: Nle_mi_1.
      by rewrite miE; case: (_ \in _).
    pose h := [set i | m i != 0%N]; have cardh: #|h| = k.
      pose Pm := [pred i | m i == 0%N].
      rewrite -sum1dep_card -eq_m_k mdegE; apply/esym.
      rewrite (bigID Pm) /= big1 ?add0n; last by move=> i /eqP ->.
      by apply/eq_bigr=> i; move/(_ i): mx_le1; case: (m i)=> [|[]].
    have PhE: P h = m; first apply/mnmP=> i.
      by rewrite PE inE; move/(_ i): mx_le1; case: (m i)=> [|[]].
    rewrite (bigD1 h) ?cardh //= PhE eqxx big1 ?addr0 //.
    move=> i /andP [_ ne_i_h]; rewrite -PhE; case: eqP=> //=.
    by move/inj_P/eqP; rewrite (negbTE ne_i_h).
  Qed.      

  Lemma mesym_sym k: 's_k \is symmetric.
  Proof.
    apply/issymP=> s; apply/mpolyP=> m; rewrite mcoeff_sym.
    rewrite !mcoeff_mesym /mechar; rewrite {1}mdegE.
    rewrite (reindex [eta s^-1]%g) /=; last first.
      by exists s=> i _; rewrite (permK, permKV).
    rewrite (eq_bigr (fun i => m i))=> [|i _]; last first.
      by rewrite mnmE permKV.
    rewrite -mdegE; case: eqP=> //= _; congr (_%:R).
    case: (boolP [forall i, m i <= 1]).
    + move/forallP=> h /=; apply/eqP; rewrite eqb1.
      by apply/forallP=> /= i; rewrite mnmE (h (s i)).
    + rewrite negb_forall => /existsP [/= i h].
      apply/eqP; rewrite eqb0; rewrite negb_forall.
      by apply/existsP; exists (s^-1 i)%g; rewrite mnmE permKV.
  Qed.

  Lemma mesym0: 's_0 = 1.
  Proof.
    rewrite /mesym (bigD1 set0) ?cards0 //= big_set0 big1 ?addr0 //.
    by move=> i /andP [] /eqP /cards0_eq => ->; rewrite eqxx.
  Qed.

  Lemma mesymnn: 's_n = \prod_(i < n) 'X_i.
  Proof.
    rewrite /mesym (bigD1 setT) ?cardsT ?card_ord //=.
    rewrite [X in _+X]big1 ?addr0; last first.
      move=> i /andP []; rewrite eqEcard => /eqP ->.
      by rewrite subsetT cardsT card_ord leqnn.
    by apply/eq_big=> //= x; rewrite in_setT.
  Qed.
End MElemPolySym.

Local Notation "''s_' ( n , k )" := (@mesym n _ k).

(* -------------------------------------------------------------------- *)
Local Notation widen := (widen_ord (leqnSn _)).

Section MWiden.
  Variable n : nat.
  Variable R : ringType.

  Definition mwiden (p : {mpoly R[n]}) : {mpoly R[n.+1]} :=
    mmap (@mpolyC _ _) (fun i => 'X_(widen i)) p.

  Definition mnmwiden (m : 'X_{1..n}) : 'X_{1..n.+1} :=
    [multinom of rcons m 0%N].

  Lemma mnmwiden_ordmax m: (mnmwiden m) ord_max = 0%N.
  Proof.
    rewrite multinomE (tnth_nth 0%N) nth_rcons /=.
    by rewrite size_tuple ltnn eqxx.
  Qed.

  Lemma mnmwiden_widen m (i : 'I_n): (mnmwiden m) (widen i) = m i.
  Proof.
    case: m=> m; rewrite !multinomE !(tnth_nth 0%N).
    by rewrite nth_rcons size_tuple /=; case: i => i /= ->.
  Qed.    

  Lemma mnmwiden0: mnmwiden 0 = 0%MM.
  Proof.
    apply/mnmP=> i; rewrite mnm0E multinomE (tnth_nth 0%N).
    by rewrite /= nth_rcons size_nseq nth_nseq !if_same.
  Qed.

  Lemma mnmwidenD m1 m2: mnmwiden (m1 + m2) = (mnmwiden m1 + mnmwiden m2)%MM.
  Proof.
    apply/mnmP=> i; rewrite mnmDE !multinomE !(tnth_nth 0%N) /=.
    rewrite !nth_rcons size_map size_enum_ord !size_tuple !if_same.
    case h: (i < n); last by rewrite addn0.
    rewrite (nth_map (Ordinal h)) ?size_enum_ord //.
    by rewrite /fun_of_multinom !(tnth_nth 0%N) /= !nth_enum_ord.
  Qed.

  Lemma mnmwiden_sum (I : Type) (r : seq I) P F:
      mnmwiden (\sum_(x <- r | P x) (F x))
    = (\sum_(x <- r | P x) (mnmwiden (F x)))%MM.
  Proof. by apply/big_morph; [apply/mnmwidenD | apply/mnmwiden0]. Qed.  

  Lemma mnmwiden1 i: (mnmwiden U_(i) = U_(widen i))%MM.
  Proof.
    apply/mnmP; case=> j /= lt; rewrite /mnmwiden !mnmE; apply/esym.
    rewrite eqE multinomE /tnth /=; move: (tnth_default _ _) => x.
    rewrite nth_rcons size_map size_enum_ord; move: lt.
    rewrite ltnS leq_eqVlt; case/orP => [/eqP->|lt].
      by apply/eqP; rewrite ltnn eqxx eqb0 ltn_eqF.
    rewrite lt (nth_map i) ?size_enum_ord //.
    by apply/esym; rewrite eqE /= nth_enum_ord.
  Qed.

  Lemma inj_mnmwiden: injective mnmwiden.
  Proof.
    move=> m1 m2 /mnmP h; apply/mnmP=> i; move: (h (widen i)).
    by rewrite !mnmwiden_widen.
  Qed.

  Lemma mwiden_is_additive: additive mwiden.
  Proof. by apply/mmap_is_additive. Qed.

  Lemma mwiden0     : mwiden 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma mwidenN     : {morph mwiden: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma mwidenD     : {morph mwiden: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma mwidenB     : {morph mwiden: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma mwidenMn  k : {morph mwiden: x / x *+ k} . Proof. exact: raddfMn. Qed.
  Lemma mwidenMNn k : {morph mwiden: x / x *- k} . Proof. exact: raddfMNn. Qed.

  Canonical mwiden_additive := Additive mwiden_is_additive.

  Lemma mwiden_is_multiplicative: multiplicative mwiden.
  Proof.
    apply/commr_mmap_is_multiplicative=> /=.
    + by move=> i p; apply/commr_mpolyX.
    + move=> p m m'; rewrite /mmap1; elim/big_rec: _ => /=.
        by apply/commr1.
      by move=> i q _; apply/commrM/commrX/commr_mpolyX.
  Qed.

  Canonical mwiden_rmorphism := AddRMorphism mwiden_is_multiplicative.

  Lemma mwiden1: mwiden 1 = 1.
  Proof. exact: rmorph1. Qed.

  Lemma mwidenM: {morph mwiden: x y / x * y}.
  Proof. exact: rmorphM. Qed.

  Lemma mwidenC c: mwiden c%:MP = c%:MP.  
  Proof. by rewrite /mwiden mmapC. Qed.

  Lemma mwidenN1: mwiden (-1) = -1.
  Proof. by rewrite raddfN /= mwidenC. Qed.

  Lemma mwidenX m: mwiden 'X_[m] = 'X_[mnmwiden m].
  Proof.
    rewrite /mwiden mmapX /mmap1 /= (mpolyXE _ 1); apply/esym.
    rewrite (eq_bigr (fun i => 'X_i ^+ (mnmwiden m i))); last first.
      by move=> i _; rewrite perm1.
    rewrite big_ord_recr /= mnmwiden_ordmax expr0 mulr1.
    by apply/eq_bigr=> i _; rewrite mnmwiden_widen.
  Qed.

  Lemma mwidenZ c p: mwiden (c *: p) = c *: mwiden p.
  Proof. by rewrite /mwiden mmapZ /= mul_mpolyC. Qed.

  Lemma mwidenE (p : {mpoly R[n]}) (k : nat): msize p <= k ->
    mwiden p = \sum_(m : 'X_{1..n < k}) (p@_m *: 'X_[mnmwiden m]).
  Proof.
    move=> h; rewrite {1}[p](mpolywE (k := k)) //.
    rewrite raddf_sum /=; apply/eq_bigr=> m _.
    by rewrite mwidenZ mwidenX.
  Qed.    

  Lemma mwiden_mnmwiden p m: (mwiden p)@_(mnmwiden m) = p@_m.
  Proof.
    rewrite (mwidenE (k := msize p)) // raddf_sum /=.
    rewrite [X in _=X@__](mpolywE (k := msize p)) //.
    rewrite raddf_sum /=; apply/eq_bigr=> i _.
    by rewrite !mcoeffZ !mcoeffX inj_eq //; apply/inj_mnmwiden.
  Qed.

  Lemma inj_mwiden: injective mwiden.
  Proof.
    move=> m1 m2 /mpolyP h; apply/mpolyP=> m.
    by move: (h (mnmwiden m)); rewrite !mwiden_mnmwiden.
  Qed.

  Definition mpwiden (p : {poly {mpoly R[n]}}) : {poly {mpoly R[n.+1]}} :=
    map_poly mwiden p.

  Lemma mpwiden_is_additive: additive mpwiden.
  Proof. exact: map_poly_is_additive. Qed.

  Canonical mpwiden_additive := Additive mpwiden_is_additive.

  Lemma mpwiden_is_rmorphism: rmorphism mpwiden.
  Proof. exact: map_poly_is_rmorphism. Qed.

  Canonical mpwiden_rmorphism := RMorphism mpwiden_is_rmorphism.

  Lemma mpwidenX: mpwiden 'X = 'X.
  Proof. by rewrite /mpwiden map_polyX. Qed.

  Lemma mpwidenC c: mpwiden c%:P = (mwiden c)%:P.
  Proof. by rewrite /mpwiden map_polyC. Qed.

  Lemma mpwidenZ c p: mpwiden (c *: p) = mwiden c *: (mpwiden p).
  Proof. by rewrite /mpwiden map_polyZ. Qed.
End MWiden.

(* -------------------------------------------------------------------- *)
Section MESymViete.
  Definition twiden n k (t : k.-tuple 'I_n) := [tuple of map widen t].

  Lemma inj_widen n: injective (widen : 'I_n -> _).
  Proof. by move=> x y /eqP; rewrite eqE /= val_eqE => /eqP. Qed.

  Local Notation mw  := mwiden.
  Local Notation mpw := mpwiden.

  Local Hint Resolve inj_widen.

  Lemma mesymSS (R : ringType) n k:
    's_(n.+1, k.+1) = mw 's_(n, k.+1) + mw 's_(n, k) * 'X_(ord_max)
    :> {mpoly R[n.+1]}.
  Proof.
    pose T k n := k.-tuple 'I_n; rewrite {1}mesym_tupleE.
    pose F1 (t : T k.+1 n) := twiden t.
    pose F2 (t : T k n) := [tuple of rcons [seq widen i | i <- t] (inord n)].
    pose E1 := [set F1 t | t : T k.+1 n & tmono t].
    pose E2 := [set F2 t | t : T k n & tmono t].
    have inj_F1: injective F1.
      by move=> x y /= [] /(inj_map (@inj_widen _)) /val_inj.
    have inj_F2: injective F2.
      move=> x y /= [] /(congr1 rev); rewrite !rev_rcons.
      case=> /(congr1 rev); rewrite !revK => [].
      by move/(inj_map (@inj_widen _)) /val_inj.
    have sorted_E1: forall t, t \in E1 -> tmono t.
      move=> /= t /imsetP [/= u]; rewrite inE /tmono => st_u ->.
      by rewrite -map_comp (eq_map (f2 := val)).
    have sorted_E2: forall t, t \in E2 -> tmono t.
      move=> /= t /imsetP [/= u]; rewrite inE /tmono => st_u ->.
      case: u st_u; case=> //= x u _ st_u.
      rewrite map_rcons -map_comp (eq_map (f2 := val)) //.
      by rewrite rcons_path st_u /= last_map inordK.
    have disj_E: [disjoint E1 & E2].
      apply/pred0P=> x /=; apply/negP=> /andP [].
      case/imsetP=> /= t1 _ -> /imsetP /= [t2 /= _].
      move/(congr1 ((@tnth _ _)^~ ord_max))/esym.
      rewrite {1}/tnth nth_rcons size_map size_tuple /= ltnn eqxx.
      by apply/eqP; rewrite eqE /= inordK // tnth_map gtn_eqF /=.
    have split_E: [set t : T k.+1 n.+1 | tmono t] = E1 :|: E2.
      apply/esym/eqP; rewrite eqEcard; apply/andP; split.
        apply/subsetP=> /= t; rewrite in_setU; case/orP.
        * by move/sorted_E1; rewrite inE.
        * by move/sorted_E2; rewrite inE.
      rewrite cardsU disjoint_setI0 // cards0 subn0.
      rewrite !card_imset /= ?(cardsT, card_tuple, card_ord) //.
      by rewrite !card_ltn_sorted_tuples binS addnC.
    rewrite -big_set /= split_E big_set /= bigU //=; congr (_ + _).
    + rewrite /E1 big_imset /=; last by move=> t1 t2 _ _; apply/inj_F1.
      rewrite big_set mesym_tupleE /= raddf_sum /=; apply/eq_bigr=> i _.
      rewrite !mprodXE mwidenX; congr 'X_[_]; apply/mnmP=> j.
      rewrite big_map mnmwiden_sum !mnm_sum; apply/eq_bigr.
      by move=> l _; rewrite mnmwiden1.
    + rewrite /E2 big_imset /=; last by move=> t1 t2 _ _; apply/inj_F2.
      rewrite big_set mesym_tupleE raddf_sum mulr_suml /=.
      apply/eq_bigr=> i _; set s := [seq _ | _ <- i].
      rewrite !mprodXE mwidenX -mpolyXD; congr 'X_[_].
      rewrite mnmwiden_sum; move/perm_eqlP: (perm_rcons (inord n) s).
      move=> h; rewrite {h}(eq_big_perm _ h) /= big_cons mnm_addC.
      congr (_ + U_(_))%MM; last by apply/eqP; rewrite eqE /= inordK.
      by rewrite big_map; apply/eq_bigr; move=> l _; rewrite mnmwiden1.
  Qed.

  Lemma Viete:
    forall n,
         \prod_(i < n   ) ('X - ('X_i)%:P)
      =  \sum_ (k < n.+1) (-1)^+k *: ('s_(n, k) *: 'X^(n-k))
      :> {poly {mpoly int[n]}}.
  Proof.
    elim => [|n ih].
      by rewrite !big_ord0 big_ord1 mesym0 expr0 !scale1r.
    pose F n k : {poly {mpoly int[n]}} :=
      (-1)^+k *: ('s_(n, k) *: 'X^(n-k)).
    have Fn0 l: F l 0%N = 'X^l.
      by rewrite /F expr0 mesym0 !scale1r subn0.
    have Fnn l: F l l = (-1)^+l *: \prod_(i < l) ('X_i)%:P.
      by rewrite /F mesymnn subnn expr0 alg_polyC rmorph_prod.
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

  Lemma mroots_coeff (R : idomainType) n (cs : n.-tuple R) (k : 'I_n.+1):
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
End MESymViete.

(* -------------------------------------------------------------------- *)
Section MESymFundamental.
  Variable n : nat.
  Variable R : idomainType.

  Implicit Types p q : {mpoly R[n]}.
  Implicit Types m : 'X_{1..n}.

  Local Notation "m # s" := [multinom m (s i) | i < n]
    (at level 40, left associativity, format "m # s").

  Definition S (m : 'X_{1..n}) : {mpoly R[n]} := \sum_(s : 'S_n) 'X_[R, m#s].

  Lemma mperm_inj (s : 'S_n): injective (fun m => m#s).
  Proof.
    move=> m1 m2 /= /mnmP h; apply/mnmP=> i.
    by move: (h (s^-1 i)%g); rewrite !mnmE permKV.
  Qed.

  Lemma mperm1 (m : 'X_{1..n}): m#(1 : 'S_n)%g = m.
  Proof. by apply/mnmP=> i; rewrite mnmE perm1. Qed.

  Lemma mpermM (m : 'X_{1..n}) (s1 s2 : 'S_n): m#(s1 * s2)%g = m#s2#s1.
  Proof. by apply/mnmP=> i; rewrite !mnmE permM. Qed.

  Lemma mpermKV (s : 'S_n):
    cancel (fun m => m#s) (fun m => m#(s^-1))%g.
  Proof. by move=> m /=; apply/mnmP=> i; rewrite !mnmE permKV. Qed.

  Lemma mpermK (s : 'S_n):
    cancel (fun m => m#(s^-1))%g (fun m => m#s).
  Proof. by move=> m /=; apply/mnmP=> i; rewrite !mnmE permK. Qed.

  Lemma mdeg_mperm m (s : 'S_n): mdeg (m#s) = mdeg m.
  Proof.
    rewrite !mdegE (reindex_inj (h := s^-1))%g /=; last first.
      by apply/perm_inj.
    by apply/eq_bigr=> j _; rewrite !mnmE permKV.
  Qed.

  Definition msum_perm p := \sum_(s : 'S_n) (msym s p).

  Definition msym_perm_issym p: msum_perm p \is symmetric.
  Proof.
    rewrite /msum_perm; apply/issymP=> s; apply/mpolyP=> k; apply/esym.
    rewrite mcoeff_sym !raddf_sum /= (reindex (mulg^~ s)) /=; last first.
      by exists (mulg^~ s^-1)%g=> s' _; rewrite -mulgA (mulgV, mulVg) mulg1.
    apply/eq_bigr=> s' _; rewrite !mcoeff_sym; congr (p@__).
    by apply/mnmP=> i; rewrite !mnmE permM.
  Qed.

  Lemma S_sym m: S m \is symmetric.
  Proof.
    apply/issymP=> s; apply/mpolyP=> h; rewrite mcoeff_sym.
    rewrite /S !raddf_sum (reindex_inj (mulgI s)%g) /=.
    apply/eq_bigr=> s' _; rewrite !mcoeffX mpermM.
    by rewrite (inj_eq (@mperm_inj s)).
  Qed.

  Lemma msupp_S m: {subset msupp (S m) <= [seq m#s | s : 'S_n]}.
  Proof.
    move=> h /msupp_sum_le /flattenP /= [xs] /mapP /=.
    case=> s _ {xs}-> /mem_msuppXP <-; apply/mapP.
    by exists s=>//; rewrite mem_enum.
  Qed.

  Lemma L p: p \is symmetric ->
    {cms | p = \sum_(cm <- cms) cm.1 *: (S cm.2)}.
  Proof.
    elim/mpolyrect_r: p; first by exists [::]; rewrite big_nil.
    move=> c m p m_notin_p nz_c ih sym_cXDp.
    pose q : {mpoly R[n]} := c *: 'X_[m] + p.
    pose r : {mpoly R[n]} := q - c *: (S m).
    have L (s : 'S_n): q@_(m#s) = c.
      rewrite /q -mcoeff_sym (issymP _ sym_cXDp) mcoeffD.
      rewrite [X in _+X]memN_msupp_eq0 // addr0 mcoeffZ.
      by rewrite mcoeffX eqxx mulr1.
    have msupp_r: {subset msupp r <= msupp p}.
      admit.
    have sym_r: r \is symmetric.
      by rewrite /r rpredB // rpredZ // S_sym.
    case: (ih _ msupp_r sym_r)=> cms rE; exists ((c, m) :: cms).
    by rewrite big_cons /= -rE /r addrCA subrr addr0.
  Qed.

  Lemma mpolyind_order (P : {mpoly R[n]} -> Prop):
       P 0
    -> (forall c m p,
             m \notin msupp p -> c != 0
          -> (forall m', m' \in msupp p -> (m' < m)%O)
          -> P p -> P (c *: 'X_[m] + p))
    -> forall p, P p.
  Proof.
    move=> h0 hS p; rewrite [p]mpolyE.
    pose leT (m m' : 'X_{1..n}) := (m >= m')%O.
    have trans_leT: transitive leT.
      move=> m2 m3 m1; rewrite /leT /= => h.
      by move/leo_trans/(_ h).
    rewrite (eq_big_perm (sort leT (msupp p))) /=; last first.
      by rewrite perm_eq_sym; apply/perm_eqlP/perm_sort.
    set s := sort _ _; have: sorted leT s .
      apply/sort_sorted=> m m'; rewrite lex_total //=.
      by apply/leq_total.
    have: uniq s; first by rewrite sort_uniq.
    have: {subset s <= msupp p}; first by move=> ?; rewrite mem_sort.
    elim: s=> /= [|m s ih mem_s /andP [m_notin_s uniq_s] m_le_s].
      by move=> _ _ _; rewrite big_nil; apply/h0.
    rewrite big_cons; apply/hS.
    + rewrite mcoeff_msupp negbK raddf_sum /= big_seq big1 //.
      move=> /= m' h; move/memPn/(_ _ h): m_notin_s.
      by rewrite mcoeffZ mcoeffX => /negbTE ->; rewrite mulr0.
    + by rewrite -mcoeff_msupp; apply/mem_s; rewrite in_cons eqxx.
    + move=> m' /msupp_sum_le; rewrite filter_predT => /flatten_mapP.
      case=> /= m'e m'e_in_s; rewrite (perm_eq_mem (msuppZ _ _)).
      rewrite -[_ == 0]negbK -mcoeff_msupp; move: (mem_s m'e).
      rewrite in_cons m'e_in_s orbT => -> //=; rewrite msuppX mem_seq1.
      move/eqP=> eq_m'; move/order_path_min: m_le_s.
      move/(_ trans_leT) /allP /(_ _ m'e_in_s); rewrite -eq_m' /leT.
      rewrite leo_eqVlt; case/orP=> // /eqP eq_mm'.
      move/memPn/(_ _ m'e_in_s): m_notin_s.
      by rewrite -eq_m' eq_mm' eqxx.
    apply/ih=> //; last by move/path_sorted: m_le_s.
    by move=> m' m'_in_s; rewrite (mem_s m') // in_cons m'_in_s orbT.
  Qed.
End MESymFundamental.

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" "ssreflect-extra" ".") ***
*** End: ***
 *)
