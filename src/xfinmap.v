(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
From mathcomp Require Import choice seq path finset finfun fintype bigop.
From mathcomp Require Export finmap.
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.

(* some bigop lemmas with relaxed commutativity condition *)
Lemma perm_big' R (op : SemiGroup.law R) (x : R)
  (I : eqType) (r1 r2 : seq I) (P : pred I) (F : I -> R) :
  perm_eq r1 r2 ->
  (forall i j, i \in r1 -> P i -> j \in r1 -> P j ->
               op (F i) (F j) = op (F j) (F i)) ->
  \big[op/x]_(i <- r1 | P i) F i = \big[op/x]_(i <- r2 | P i) F i.
Proof.
move=> perm_r12 comm; rewrite -big_filter -[RHS]big_filter.
have {comm}: {in filter P r1 &, forall i j, op (F i) (F j) = op (F j) (F i)}.
  by move=> i j; rewrite !mem_filter => /andP[? ?] /andP[? ?]; rewrite comm.
have {perm_r12}: perm_eq (filter P r1) (filter P r2) by exact: perm_filter.
rewrite perm_sym; elim: {r1 r2} (filter P r1) (filter P r2) => [|i r1 IHr1] r2.
  by move=> /perm_nilP -> ?; rewrite ?big_nil.
move=> perm_r12 comm.
have ir2 : i \in r2 by rewrite (perm_mem perm_r12) inE eqxx.
case: {ir2}(path.splitP ir2) perm_r12 => r2l r2r.
rewrite cat_rcons perm_catC/= perm_cons perm_catC => perm_r12.
rewrite big_cons (IHr1 _ perm_r12).
  by move=> j k Hj Hk; rewrite comm// inE (Hj, Hk) ?orbT.
have {}comm: {in r2l, forall j, op (F i) (F j) = op (F j) (F i)}.
  move=> j Hj.
  by rewrite comm// inE ?eqxx// -(perm_mem perm_r12) mem_cat Hj !orbT.
elim: {r1 IHr1 perm_r12}r2l comm => [|j r IHr] comm.
  by rewrite /= big_cons.
rewrite /= 2!big_cons SemiGroup.opA comm ?inE ?eqxx// -SemiGroup.opA IHr//.
by move=> k Hk; rewrite comm// inE Hk orbT.
Qed.

Local Abbreviation eq_big_imfset := (perm_big' _ (enum_imfset _ _)).

Section BigComFSet.
Variable (R : Type) (idx : R) (op : Monoid.law idx).
Variable (I J : choiceType).

Lemma big_fset' (X : finmempred _) (P : pred I) (F : I -> R) :
  (forall i j, X i -> P i -> X j -> P j -> op (F i) (F j) = op (F j) (F i)) ->
  \big[op/idx]_(i <- [fset i in X | P i]) F i =
    \big[op/idx]_(i <- enum_finmem X | P i) F i.
Proof.
move=> comm; rewrite eq_big_imfset//; last by rewrite big_map -[RHS]big_filter.
by move=> i j /[!inE] /andP[? ?] _ /andP[? ?] _; apply/comm.
Qed.

Lemma big_fset_condE' (X : {fset I}) (P : pred I) (F : I -> R) :
  (forall i j, i \in X -> P i -> j \in X -> P j ->
               op (F i) (F j) = op (F j) (F i)) ->
  \big[op/idx]_(i <- X | P i) F i = \big[op/idx]_(i <- [fset i in X | P i]) F i.
Proof. by move=> comm; apply/esym/big_fset'/comm. Qed.

Lemma eq_fbig_cond' (A B : {fset I}) (P Q : pred I) (F G : I -> R) :
  [fset x in A | P x] =i [fset x in B | Q x] ->
  (forall x, x \in A -> P x -> F x = G x) ->
  (forall i j, i \in A -> P i -> j \in A -> P j ->
               op (F i) (F j) = op (F j) (F i)) ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- B | Q i) G i.
Proof.
move=> /fsetP eqABPQ FG comm; rewrite big_fset_condE'// [RHS]big_fset_condE'//.
  move=> i j Hi1 Hi2 Hj1 Hj2.
  have/fsetP/(_ i) := eqABPQ; rewrite !inE/= Hi1 Hi2 => /andP[{}Hi1 {}Hi2].
  have/fsetP/(_ j) := eqABPQ; rewrite !inE/= Hj1 Hj2 => /andP[{}Hj1 {}Hj2].
  by rewrite -!FG// comm.
rewrite -eqABPQ big_seq_cond [RHS]big_seq_cond; apply: eq_bigr.
by move=> i; rewrite !inE andbT/= => /andP[]; apply: FG.
Qed.

Lemma eq_fbig (A B : {fset I}) (F G : I -> R) :
  A =i B -> (forall x, x \in A -> F x = G x) ->
  \big[op/idx]_(i <- A) F i = \big[op/idx]_(i <- B) G i.
Proof. by move=> /fsetP<- FG; rewrite big_seq [RHS]big_seq; apply: eq_bigr. Qed.

Lemma eq_fbigl_cond' (A B : {fset I}) (P Q : pred I) (F : I -> R) :
  [fset x in A | P x] =i [fset x in B | Q x] ->
  (forall i j, i \in A -> P i -> j \in A -> P j ->
               op (F i) (F j) = op (F j) (F i)) ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- B | Q i) F i.
Proof. by move=> AB; apply: eq_fbig_cond'. Qed.

Lemma eq_fbigl (A B : {fset I}) (F : I -> R) :
  A =i B -> \big[op/idx]_(i <- A) F i = \big[op/idx]_(i <- B) F i.
Proof. by move=> AB; apply: eq_fbig. Qed.

Lemma eq_fbigr (A : {fset I}) (P : pred I) (F G : I -> R) :
  (forall x, x \in A -> P x -> F x = G x) ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- A | P i) G i.
Proof.
move=> FG; rewrite big_seq_cond [RHS]big_seq_cond.
by apply: eq_bigr => ? /andP[]; apply: FG.
Qed.

Lemma big_fsetID' (B : pred I) (A : {fset I}) (F : I -> R) :
  (forall i j, i \in A -> j \in A -> op (F i) (F j) = op (F j) (F i)) ->
   \big[op/idx]_(i <- A) F i =
   op (\big[op/idx]_(i <- [fset x in A | B x]) F i)
      (\big[op/idx]_(i <- [fset x in A | ~~ B x]) F i).
Proof.
move=> comm; rewrite -big_cat; apply/perm_big'; last first.
  by move=> + + + _ + _; apply: comm.
apply/uniq_perm => //.
  rewrite uniq_pairwise pairwise_cat -!uniq_pairwise.
  apply/and3P; split => //; apply/allrelP => i j; rewrite !inE/=.
  by case: eqP => // <- /andP[_ ->]; rewrite andbF.
by move=> i; rewrite mem_cat !inE; case: (B i); rewrite /= andbT andbF// orbF.
Qed.

Lemma big_fsetIDcond' (B : pred I) (A : {fset I}) (P : pred I) (F : I -> R) :
  (forall i j, i \in A -> P i -> j \in A -> P j ->
               op (F i) (F j) = op (F j) (F i)) ->
   \big[op/idx]_(i <- A | P i) F i =
   op (\big[op/idx]_(i <- [fset x in A | B x] | P i) F i)
      (\big[op/idx]_(i <- [fset x in A | ~~ B x] | P i) F i).
Proof.
move=> comm; rewrite big_fset_condE'// (big_fsetID' B).
  by move=> i j /[!inE]/= /andP[+ +] /andP[+ +]; apply: comm.
congr (op _ _); rewrite [RHS]big_fset_condE'.
- by move=> i j /[!inE]/= /andP[+ _] + /andP[+ _] +; apply: comm.
- by apply: eq_fbigl => i; rewrite !inE/= andbAC.
- by move=> i j /[!inE]/= /andP[+ _] + /andP[+ _] +; apply: comm.
by apply: eq_fbigl => i; rewrite !inE/= andbAC.
Qed.

Lemma big_fsetD1' (a : I) (A : {fset I}) (F : I -> R) : a \in A ->
  (forall i j, i \in A -> j \in A -> op (F i) (F j) = op (F j) (F i)) ->
  \big[op/idx]_(i <- A) F i = op (F a) (\big[op/idx]_(i <- A `\ a) F i).
Proof.
move=> aA comm; rewrite (big_fsetID' (eq_op^~ a)) //.
congr (op _ _); last first.
  by apply: eq_fbigl => i; rewrite !inE/= andbC.
rewrite (_ : [fset _ | _ in _ & _] = [fset a]) ?big_seq_fset1//=.
by apply/fsetP=> i; rewrite !inE /= andbC; case: eqP => //->.
Qed.

Lemma big_fsetU1' (a : I) (A : {fset I}) (F : I -> R) : a \notin A ->
  (forall i j, i \in a |` A -> j \in a |` A ->
               op (F i) (F j) = op (F j) (F i)) ->
  \big[op/idx]_(i <- (a |` A)) F i = op (F a) (\big[op/idx]_(i <- A) F i).
Proof.
move=> aNA comm; have/big_fsetD1'->//: a \in a |` A by rewrite !inE/= eqxx.
congr (op _ _); apply: eq_fbigl => i /[!inE].
by case: eqP => //= ->; apply/esym/negbTE.
Qed.

Lemma big_fset_incl' (A : {fset I}) B F : A `<=` B ->
  (forall x, x \in B -> x \notin A -> F x = idx) ->
  (forall i j, i \in A -> j \in A -> op (F i) (F j) = op (F j) (F i)) ->
  \big[op/idx]_(x <- A) F x = \big[op/idx]_(x <- B) F x.
Proof.
move=> subAB Fid comm; rewrite [in RHS](big_fsetID' (mem A)) /=.
  move=> i j Hi Hj.
  case: (boolP (_ \in _)) (Fid i Hi) => [{}Hi _|_ ->//]; last first.
    by rewrite Monoid.mul1m Monoid.mulm1.
  case: (boolP (_ \in _)) (Fid j Hj) => [{}Hj _|_ ->//]; first exact: comm.
  by rewrite Monoid.mul1m Monoid.mulm1.
rewrite [X in op _ X]big1_fset ?Monoid.mulm1.
  by move=> i; rewrite !inE /= => /andP[iB iNA _]; apply: Fid.
by apply: eq_fbigl => i; rewrite !inE /= -(@in_fsetI _ B A) (fsetIidPr _).
Qed.

Lemma big_imfset' key (h : I -> J) (A : finmempred _) (G : J -> R) :
  {in A &, injective h} ->
  (forall i j, i \in A -> j \in A ->
               op (G (h i)) (G (h j)) = op (G (h j)) (G (h i))) ->
  \big[op/idx]_(j <- imfset key h A) G j =
    \big[op/idx]_(i <- enum_finmem A) G (h i).
Proof.
move=> H_inj comm; rewrite eq_big_imfset// ?big_map//.
by move=> i j /imfsetP[{}i + ->] _ /imfsetP[{}j + ->] _; apply: comm.
Qed.

End BigComFSet.
Arguments big_fsetD1 {R idx op I} a [A F].
