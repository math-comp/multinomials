(* --------------------------------------------------------------------
 * (c) Copyright 2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop tuple finfun ssralg perm poly bigenough freeg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory BigEnough.

Local Open Scope ring_scope.

Delimit Scope mpoly_scope with MP.
Delimit Scope multi_scope with MM.

Local Notation simpm := Monoid.simpm.

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

  Lemma pair_bigA_curry (F : T1 * T2 -> R):
      \big[op/idx]_i \big[op/idx]_j F (i, j)
    = \big[op/idx]_x F x.
  Proof. by rewrite pair_bigA; apply/eq_bigr; case. Qed.
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
Reserved Notation "c %:MP"
  (at level 2, format "c %:MP").
Reserved Notation "c %:MP_[ n ]"
  (at level 2, n at level 50, format "c %:MP_[ n ]").
Reserved Notation "c %:IP"
  (at level 2, format "c %:IP").
Reserved Notation "s @_ i"
   (at level 3, i at level 2, left associativity, format "s @_ i").
Reserved Notation "x ^[ f ]"
   (at level 2, left associativity, format "x ^[ f ]").
Reserved Notation "x ^[ f , g ]"
   (at level 2, left associativity, format "x ^[ f , g ]").
Reserved Notation "p ^`M ( m )"
   (at level 8, format "p ^`M ( m )").

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

  Notation "1" := [multinom of nseq n 0%N] : multi_scope.

  Lemma mpow1 i: 1%MM i = 0%N.
  Proof. by rewrite multinomE (tnth_nth 0%N) nth_nseq if_same. Qed.

  Definition mnm_mul m1 m2 :=
    [multinom (m1 i + m2 i)%N | i < n].

  Local Notation "m1 * m2" := (mnm_mul m1 m2) : multi_scope.

  Lemma mpowD i m1 m2: (m1 * m2)%MM i = (m1 i + m2 i)%N.
  Proof. by rewrite multinomE tnth_map tnth_ord_tuple. Qed.

  Lemma mnm_mulC: commutative mnm_mul.
  Proof. by move=> m1 m2; apply/mnmP=> i; rewrite !mnmE addnC. Qed.

  Lemma mnm_mulA: associative mnm_mul.
  Proof. by move=> m1 m2 m3; apply/mnmP=> i; rewrite !mnmE addnA. Qed.

  Lemma mnm_mul0m: left_id 1%MM mnm_mul.
  Proof.
    move=> m; apply/mnmP=> i; rewrite !mnmE multinomE.
    by rewrite (tnth_nth 0%N) /= nth_nseq if_same add0n.
  Qed.

  Lemma mnm_mulm0: right_id 1%MM mnm_mul.
  Proof. by move=> m; rewrite mnm_mulC mnm_mul0m. Qed.

  Canonical mnm_monoid := Monoid.Law mnm_mulA mnm_mul0m mnm_mulm0.
  Canonical mnm_comoid := Monoid.ComLaw mnm_mulC.

  Lemma eqm_mul2l m n1 n2:
    ((m * n1)%MM == (m * n2)%MM) = (n1 == n2).
  Proof.
    apply/eqP/eqP=> [|->//] /mnmP h; apply/mnmP.
    by move=> i; move: (h i); rewrite !mpowD => /addnI.
  Qed.

  Definition mdeg m := (\sum_(i <- m) i)%N.

  Lemma mdegE m: mdeg m = (\sum_i (m i))%N.
  Proof. by rewrite /mdeg big_tuple. Qed.

  Lemma mdeg1: mdeg 1%MM = 0%N.
  Proof.
    rewrite /mdeg big_seq big1 // => i /tnthP.
    by case=> j ->; rewrite -multinomE mpow1.
  Qed.

  Lemma mdegM m1 m2: mdeg (m1 * m2) = (mdeg m1 + mdeg m2)%N.
  Proof.
    case: m1 m2 => [m1] [m2]; rewrite !mdegE -big_split /=.
    by apply: eq_bigr=> i _; rewrite [(_*_)%MM _]multinomE tnth_mktuple.
  Qed.

  Lemma mdeg_eq0 m: (mdeg m == 0%N) = (m == 1%MM).
  Proof.
    apply/idP/eqP=> [|->]; last by rewrite mdeg1.
    move=> h; apply/mnmP=> i; move: h; rewrite mdegE mpow1.
    by rewrite (bigD1 i) //= addn_eq0 => /andP [/eqP-> _].
  Qed.
End MultinomTheory.

Local Notation "1" := [multinom of nseq _ 0%N] : multi_scope.
Local Notation "m1 * m2" := (mnm_mul m1 m2) : multi_scope.

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

  Lemma bm0_proof: mdeg (1%MM : 'X_{1..n}) < bound.+1.
  Proof. by rewrite mdeg1. Qed.
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
    [mpoly << c *g 1%MM >>].

  Local Notation "c %:MP" := (mpolyC c) : ring_scope.

  Lemma mpolyC_eq (c1 c2 : R): (c1%:MP == c2%:MP) = (c1 == c2).
  Proof.
    apply/eqP/eqP=> [|->//] /eqP/freeg_eqP.
    by move/(_ 1%MM); rewrite !coeffU eqxx !simpm.
  Qed.

  Definition mcoeff (m : 'X_{1..n}) p : R :=
    coeff m p.

  Lemma mcoeff_MPoly D m: mcoeff m (MPoly D) = coeff m D.
  Proof. by []. Qed.

  Local Notation "p @_ i" := (mcoeff i p) : ring_scope.

  Lemma mcoeffC c m: c%:MP@_m = c * (m == 1%MM)%:R.
  Proof. by rewrite mcoeff_MPoly coeffU eq_sym. Qed.

  Lemma mpolyCK: cancel mpolyC (mcoeff 1%MM).
  Proof. by move=> c; rewrite mcoeffC eqxx mulr1. Qed.

  Definition msupp p : seq 'X_{1..n} :=
    dom p.

  Lemma msuppE p: msupp p = dom p :> seq _.
  Proof. by []. Qed.

  Lemma msupp_uniq p: uniq (msupp p).
  Proof. by rewrite msuppE uniq_dom. Qed.

  Lemma mcoeff_eq0 p m: m \notin msupp p -> p@_m = 0.
  Proof. by rewrite !msuppE /mcoeff => /coeff_outdom. Qed.

  Lemma msupp0: msupp 0%:MP = [::].
  Proof. by rewrite msuppE /= freegU0 dom0. Qed.

  Lemma msupp1: msupp 1%:MP = [:: 1%MM].
  Proof. by rewrite msuppE /= domU1. Qed.

  Lemma msuppC (c : R):
    msupp c%:MP = if c == 0 then [::] else [:: 1%MM].
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
    by move/freeg_eqP/(_ 1%MM); rewrite !coeffU eqxx !mulr1.
  Qed.

  Definition msize p := \max_(m <- msupp p) (mdeg m).+1.

  Lemma msize0: msize 0 = 0%N.
  Proof. by rewrite /msize msupp0 big_nil. Qed.

  Lemma msizeC c: msize c%:MP = (c != 0%R) :> nat.
  Proof.
    rewrite /msize msuppC; case: (_ == 0).
    by rewrite big_nil. by rewrite big_seq1 mdeg1.
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

  Lemma msizeD_le p q: msize (p + q) <= maxn (msize p) (msize q).
  Proof.
    rewrite {1}/msize big_tnth; apply/bigmax_leqP=> /= i _.
    set m := tnth _ _; have: m \in msupp (p + q) by apply/mem_tnth.
    move/msuppD_le; rewrite leq_max mem_cat.
    by case/orP=> /msize_mdeg_lt->; rewrite !simpm.
  Qed.
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
    << (p@_m.1)%MM * (q@_m.2)%MM *g (m.1 * m.2)%MM >>
    (at level 40, no associativity, format "p  *M_[ m ]  q").

  Definition mpoly_mul p q : {mpoly R[n]} := [mpoly
    \sum_(m <- msupp p @@ msupp q) (p *M_[m] q)
  ].

  Local Notation "p *M q" := (mpoly_mul p q)
     (at level 40, left associativity, format "p  *M  q").

  Lemma mul_poly1_eq0L p q (m : 'X_{1..n} * 'X_{1..n}):
    m.1 \notin msupp p -> p *M_[m] q = 0.
  Proof. by move/mcoeff_eq0=> ->; rewrite mul0r freegU0. Qed.

  Lemma mul_poly1_eq0R p q (m : 'X_{1..n} * 'X_{1..n}):
    m.2 \notin msupp q -> p *M_[m] q = 0.
  Proof. by move/mcoeff_eq0=> ->; rewrite mulr0 freegU0. Qed.

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
      move=> i /mcoeff_eq0=> ->; rewrite big1=> //.
      by move=> j _; rewrite mul0r freegU0.
    apply/eq_bigr=> i _; rewrite (big_mksub Iq) /=; first last.
      by move=> x /msize_mdeg_lt /leq_trans; apply.
      by rewrite msupp_uniq.
    rewrite [X in _=X]big_uncond //= => j /mcoeff_eq0.
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
      \sum_(k : 'X_{1..n < k, k} | m == (k.1 * k.2)%MM)
        (p@_k.1 * q@_k.2).
  Proof.
    pose_big_enough i; first rewrite (mpoly_mulwE i i) // => lt_mk.
      rewrite mcoeff_MPoly raddf_sum /=; have lt_mi: k < i by [].
      apply/esym; rewrite big_cond_mulrn -!pair_bigA_curry /=.
      pose Ik := [subFinType of 'X_{1..n < k}].
      pose Ii := [subFinType of 'X_{1..n < i}].
      pose F i j := (p@_i * q@_j) *+ (m == (i * j))%MM.
      pose G i   := \sum_(j : 'X_{1..n < k}) (F i j).
      rewrite (big_sub_widen Ik Ii xpredT G) /=; last first.
        by move=> x /leq_trans; apply.
      rewrite big_uncond /=; last first.
        case=> /= j _; rewrite -leqNgt => /(leq_trans lt_mk).
        move=> h; rewrite {}/G {}/F big1 // => /= l _.
        case: eqP h => [{1}->|]; last by rewrite mulr0n.
        by rewrite mdegM ltnNge leq_addr.
      apply/eq_bigr=> j _; rewrite {}/G.
      rewrite (big_sub_widen Ik Ii xpredT (F _)) /=; last first.
        by move=> x /leq_trans; apply.
      rewrite big_uncond => //=; last first.
        move=> l; rewrite -leqNgt => /(leq_trans lt_mk).
        move=> h; rewrite {}/F; case: eqP h; rewrite ?mulr0n //.
        by move=> ->; rewrite mdegM ltnNge leq_addl.
      by apply/eq_bigr=> l _; rewrite {}/F coeffU eq_sym mulr_natr.
    by close.
  Qed.                                                       

  Lemma mcoeff_poly_mul_rev p q m k: !|m| < k ->
    (p *M q)@_m =
      \sum_(k : 'X_{1..n < k, k} | m == (k.1 * k.2)%MM)
        (p@_k.2 * q@_k.1).
  Proof.
    move=> /mcoeff_poly_mul=> ->; rewrite big_cond_mulrn.
    rewrite -pair_bigA_curry /= exchange_big pair_bigA /=.
    rewrite /= -big_cond_mulrn; apply/eq_big=> //.
    by move=> i /=; rewrite Monoid.mulmC.
  Qed.

  Lemma poly_mulA: associative mpoly_mul.
  Proof. Admitted.

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
      \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 * k.2)%MM)
        (p@_k.1 * q@_k.2).
  Proof. by apply: mcoeff_poly_mul. Qed.

  Lemma mcoeffMr p q m:
    (p * q)@_m =
      \sum_(k : 'X_{1..n < !|m|.+1, !|m|.+1} | m == (k.1 * k.2)%MM)
        (p@_k.2 * q@_k.1).
  Proof.
    rewrite mcoeffM big_cond_mulrn -pair_bigA_curry /=.
    rewrite exchange_big pair_bigA /= -big_cond_mulrn.
    by apply: eq_bigl=> k /=; rewrite Monoid.mulmC.
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

  Lemma mpolyC_is_multiplicative: multiplicative (mpolyC n (R := R)).
  Proof.
    split=> // p q; apply/mpolyP=> m.
    by rewrite mcoeffCM !mcoeffC mulrA.
  Qed.

  Canonical mpolyC_rmorphism: {rmorphism R -> {mpoly R[n]}} :=
    AddRMorphism mpolyC_is_multiplicative.

  Lemma mpolyC1: mpolyC n 1 = 1.
  Proof. exact: rmorph1. Qed.

  Lemma mpolyCM: {morph mpolyC n (R := _): p q / p * q}.
  Proof. exact: rmorphM. Qed.

  Lemma mpoly_scaleAl c p q: c *: (p * q) = (c *: p) * q.
  Proof. by rewrite -!mul_mpolyC mulrA. Qed.

  Canonical mpoly_lalgType :=
    Eval hnf in LalgType R {mpoly R[n]} mpoly_scaleAl.
  Canonical mpolynomial_lalgType :=
    Eval hnf in LalgType R (mpoly n R) mpoly_scaleAl.

  Lemma alg_mpolyC c: c%:A = c%:MP :> {mpoly R[n]}.
  Proof. by rewrite -mul_mpolyC mulr1. Qed.

  Lemma mcoeff1_is_multiplicative:
    multiplicative (mcoeff 1%MM : {mpoly R[n]} -> R).
  Proof.
    split=> [p q|]; rewrite ?mpolyCK //.
    rewrite (mcoeff_poly_mul _ _ (k := 1)) ?mdeg1 //.
    rewrite (bigD1 (bm0, bm0)) ?simpm //=; last first.
    rewrite [X in _+X]big1 ?addr0 // => i /andP [] h.
    rewrite eqE /= !bmeqP /=; move/eqP/esym/(congr1 mdeg): h.
    rewrite mdegM [X in _=X]mdeg1 => /eqP; rewrite addn_eq0.
    by rewrite !mdeg_eq0=> /andP [/eqP->/eqP->]; rewrite !eqxx.
  Qed.

  Canonical mcoeff1_rmorphism  := AddRMorphism mcoeff1_is_multiplicative.
  Canonical mcoeff1_lrmorphism := [lrmorphism of mcoeff 1%MM].
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

Notation "'X_[ m ]" := (@mpolyX _ _ m).
Notation "'X_ i" := (@mpolyX _ _ (@mX _ i)).

(* -------------------------------------------------------------------- *)
Section MPolyVarTheory.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.
  Implicit Types m : 'X_{1..n}.

  Local Notation "'X_[ m ]" := (@mpolyX n R m).

  Lemma msuppX m: msupp 'X_[m] = [:: m].
  Proof. by rewrite unlock /msupp domU1. Qed.

  Lemma mcoeffX m k: 'X_[m]@_k = (m == k)%:R.
  Proof. by rewrite unlock /mpolyX_def mcoeff_MPoly coeffU mul1r. Qed.

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
    by move/mcoeff_eq0 ->; rewrite scale0r.
  Qed.

  Lemma mpolyME p q:
    p * q = \sum_(m <- msupp p @@ msupp q) (p@_m.1 * q@_m.2) *: 'X_[m.1 * m.2].
  Proof.
    apply/mpolyP=> m; rewrite {1}/GRing.mul /= mcoeff_MPoly.
    rewrite !raddf_sum; apply/eq_bigr=> i _ /=.
    by rewrite coeffU -mul_mpolyC mcoeffCM mcoeffX.
  Qed.

  Lemma mpolywME p q k: msize p <= k -> msize q <= k ->
    p * q = \sum_(m : 'X_{1..n < k, k}) (p@_m.1 * q@_m.2) *: 'X_[m.1 * m.2].
  Proof.  
    move=> ltpk ltqk; rewrite mpolyME; pose I := [subFinType of 'X_{1..n < k}].
    rewrite -pair_bigA_seq_curry (big_mksub I) /=; last first.
      by move=> m /msize_mdeg_lt /leq_trans; apply. by rewrite msupp_uniq. 
    rewrite big_uncond /= => [|i]; last first.
      by move/mcoeff_eq0=> ->; rewrite big1 // => j _; rewrite mul0r scale0r.
    rewrite -pair_bigA_curry /=; apply/eq_bigr=> i _.
    rewrite (big_mksub I) /=; last first.
      by move=> m /msize_mdeg_lt /leq_trans; apply. by rewrite msupp_uniq. 
    rewrite big_uncond /= => [//|j].
    by move/mcoeff_eq0=> ->; rewrite mulr0 scale0r.
  Qed.    

  Lemma mpolyXM m1 m2: 'X_[m1 * m2] = 'X_[m1] * 'X_[m2] :> {mpoly R[n]}.
  Proof.
    apply/mpoly_eqP; rewrite /GRing.mul /= !msuppX big_seq1 /=.
    by rewrite !mcoeffX !eqxx !simpm unlock /=.
  Qed.

  Lemma commr_mpolyX m p: GRing.comm p 'X_[m].
  Proof.
    apply/mpolyP=> k; rewrite mcoeffM mcoeffMr.
    by apply/eq_bigr=> /= i _; rewrite !mcoeffX GRing.commr_nat.
  Qed.

  Lemma mcoeffMX p m k: (p * 'X_[m])@_(m * k) = p@_k.
  Proof.
    rewrite commr_mpolyX mpolyME msuppX -pair_bigA_seq_curry /=.
    rewrite big_seq1 [X in _=X@__]mpolyE !raddf_sum /=.
    apply/eq_bigr=> i _; rewrite !mcoeffZ !mcoeffX eqxx mul1r.
    by rewrite eqm_mul2l.
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

  Lemma mpoly_ind' (P : {mpoly R[n]} -> Prop):
       P 0
    -> (forall c m p, P p -> P (c *: 'X_[m] + p))
    -> forall p, P p.
  Proof.
    move=> h0 hS [p] /=; elim/freeg_ind_dom0: p => /=.
      by rewrite raddf0.
    by move=> c q m _ _ /hS h; rewrite raddfD /= MPolyU.
  Qed.
End MPolyVarTheory.

(* -------------------------------------------------------------------- *)
Section MPolyDeriv.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.
  Implicit Types m : 'X_{1..n}.

  Definition md1 i m :=
    [multinom (m j - (i == j))%N | j < n].

  Definition mbump (i : 'I_n) m :=
    [multinom (m j + (i == j))%N | j < n].

  Lemma md1E  (i : 'I_n) m j:
    (md1 i m) j = (m j - (i == j))%N.
  Proof. by rewrite !multinomE tnth_map tnth_ord_tuple. Qed.

  Lemma mbumpE (i : 'I_n) m j:
    (mbump i m) j = (m j + (i == j))%N.
  Proof. by rewrite !multinomE tnth_map tnth_ord_tuple. Qed.

  Lemma mbump_eq (i : 'I_n) m1 m2:
    (mbump i m1 == mbump i m2) = (m1 == m2).
  Proof.
    apply/eqP/eqP=> [|->] // /mnmP h; apply/mnmP.
    by move=> j; have/eqP := h j; rewrite !mbumpE eqn_add2r => /eqP.
  Qed.

  Lemma mbump_eq1 i m: (mbump i m == 1%MM) = false.
  Proof.
    apply/negP; move/eqP/mnmP/(_ i); rewrite mpow1.
    by rewrite mbumpE eqxx addn1.
  Qed.

  Lemma md1K (i : 'I_n) m: md1 i (mbump i m) = m.
  Proof. by apply/mnmP=> j; rewrite md1E mbumpE addnK. Qed.

  Lemma mbumpK (i : 'I_n) m: m i != 0%N -> (mbump i (md1 i m)) = m.
  Proof.
    move=> nz_mi; apply/mnmP=> j; rewrite mbumpE md1E.
    rewrite subnK //; move: nz_mi; case: (i =P j) => //= ->.
    by rewrite lt0n.
  Qed.

  Definition mderiv (i : 'I_n) p :=
    \sum_(m <- msupp p) ((m i)%:R * p@_m) *: 'X_[md1 i m].

  Local Notation "p ^`M ( i )" := (mderiv i p).

  Lemma mderivE p (i : 'I_n) k: msize p <= k ->
    p^`M(i) = \sum_(m : 'X_{1..n < k}) ((m i)%:R * p@_m) *: 'X_[md1 i m].
  Proof.
    pose I := [subFinType of 'X_{1..n < k}].
    move=> le_pk; rewrite /mderiv (big_mksub I) /=; first last.
      by move=> x /msize_mdeg_lt/leq_trans/(_ le_pk).
      by rewrite msupp_uniq.
    rewrite big_uncond //= => j /mcoeff_eq0 ->.
    by rewrite mulr0 scale0r.
  Qed.
  Implicit Arguments mderivE [p i].

  Lemma mcoeff_deriv i m p: p^`M(i)@_m = p@_(mbump i m) *+ (m i).+1.
  Proof.
    pose_big_enough j; first rewrite {2}[p](mpolywE (k := j)) //.
      rewrite !(mderivE j) // !raddf_sum -sumrMnl; apply/eq_bigr.
      move=> /= [k /= _] _; rewrite !mcoeffZ !mcoeffX.
      case: (k =P mbump i m)=> [{1 3}->|].
        by rewrite mbumpE eqxx addn1 md1K eqxx !simpm mulr_natl.
      rewrite !simpm mul0rn; have [->|nz_mi] := (eqVneq (k i) 0%N).
        by rewrite !simpm.
      by case: eqP=> [{1}<-|]; rewrite ?simpm // mbumpK.
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
    by rewrite mbump_eq1 mulr0 mul0rn.
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
  Proof. Admitted.
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

  Lemma mmap1_1 h: mmap1 h 1%MM = 1.
  Proof. by rewrite /mmap1 big1 // => /= i _; rewrite mpow1 expr0. Qed.

  Lemma commr_mmap1_M h m1 m2:
       (forall i x, GRing.comm x (h i))
    -> mmap1 h (m1 * m2) = (mmap1 h m1) * (mmap1 h m2).
  Proof.
    move=> comm; pose F (i : 'I_n) := (h i ^+ m1 i) * (h i ^+ m2 i).
    rewrite /mmap1 (eq_bigr F) => [|i _]; last first.
      by rewrite mpowD exprD.
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
      rewrite big_uncond //= => j /mcoeff_eq0 ->.
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
      rewrite /mmap msuppC (negbTE nz_c) big_seq1 mmap1_1 mulr1.
      by rewrite mcoeffC eqxx mulr1.
    Qed.
  End Additive.

  Implicit Arguments mmapE [f h p].

  Section Multiplicative.
    Variable h : 'I_n -> S.
    Variable f : {rmorphism R -> S}.

    Hypothesis commr_h: forall i x, GRing.comm x (h i).
    Hypothesis commr_f: forall p m m', GRing.comm (f p@_m) (m'^[h]).

    Lemma mmapX m: ('X_[m])^[f,h] = m^[h].
    Proof. by rewrite /mmap msuppX big_seq1 mcoeffX eqxx rmorph1 mul1r. Qed.

    Lemma mmapZ c p: (c *: p)^[f,h] = (f c) * p^[f,h].
    Proof.
      pose_big_enough i.
        rewrite !(mmapE i) // mulr_sumr; apply/eq_bigr.
        by move=> j _; rewrite mcoeffZ mulrA -rmorphM.
      by close.
    Qed.

    Lemma commr_mmap_is_multiplicative: multiplicative (mmap f h).
    Proof.
      split=> //= [p q|]; last first.
        by rewrite /mmap msupp1 big_seq1 mpolyCK rmorph1 mul1r mmap1_1.
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
Section MEval.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.
  Implicit Types v : n.-tuple R.

  Definition meval v p := mmap idfun (tnth v) p.

  Lemma meval_is_additive v: additive (meval v).
  Proof. by apply/mmap_is_additive. Qed.

  Canonical meval_additive v := Additive (meval_is_additive v).

  Lemma meval0   v   : meval v 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma mevalN   v   : {morph meval v: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma mevalD   v   : {morph meval v: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma mevalB   v   : {morph meval v: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma mevalMn  v k : {morph meval v: x / x *+ k} . Proof. exact: raddfMn. Qed.
  Lemma mevalMNn v k : {morph meval v: x / x *- k} . Proof. exact: raddfMNn. Qed.
End MEval.

(* -------------------------------------------------------------------- *)
Section MEvalCom.
  Variable n : nat.
  Variable R : comRingType.

  Implicit Types p q r : {mpoly R[n]}.
  Implicit Types v : n.-tuple R.

  Lemma meval_is_multiplicative v: multiplicative (meval v).
  Proof. by apply/mmap_is_multiplicative. Qed.

  Canonical meval_multiplicative v := AddRMorphism (meval_is_multiplicative v).

  Lemma mevalM v: {morph meval v: x y / x * y}.
  Proof. exact: rmorphM. Qed.
End MEvalCom.

(* -------------------------------------------------------------------- *)
Section MPolyIdomain.
  Variable n : nat.
  Variable R : idomainType.

  Implicit Types p q r : {mpoly R[n]}.

  Lemma sizeM p q: p != 0 -> q != 0 ->
    msize (p * q) = (msize p * msize q).-1.
  Proof. Admitted.

  Lemma mpoly_idomainAxiom p q:
    p * q = 0 -> (p == 0) || (q == 0).
  Proof. Admitted.

  Definition mpoly_unit : pred {mpoly R[n]} :=
    fun p => (p == (p@_1)%:MP) && (p@_1 \in GRing.unit).

  Definition mpoly_inv p :=
    if p \in mpoly_unit then (p@_1)^-1%:MP else p.

  Lemma mpoly_mulVp : {in mpoly_unit, left_inverse 1 mpoly_inv *%R}.
  Proof. Admitted.

  Lemma mpoly_intro_unit p q: q * p = 1 -> p \in mpoly_unit.
  Proof. Admitted.

  Lemma mpoly_inv_out: {in [predC mpoly_unit], mpoly_inv =1 id}.
  Proof. Admitted.

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
Section MPolySym.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.

  Definition msym (s : 'S_n) p : {mpoly R[n]} :=
    mmap (@mpolyC n R) (fun i => 'X_(s i)) p.

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

  Lemma msymM s: {morph msym s: x y / x * y}.
  Proof. exact: rmorphM. Qed.

  Definition issym p := [forall s, msym s p == p].

  Lemma issymP p: reflect (forall s, p = msym s p) (issym p).
  Proof.
    apply: (iffP forallP)=> /= h s; last by rewrite -h.
    by rewrite (eqP (h s)).
  Qed.
End MPolySym.

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" ".") ***
*** End: ***
 *)
