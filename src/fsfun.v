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

Coercion finMap_of_fsfun : fsfun >-> finMap.
Coercion map_of_fsfun    : fsfun >-> finmap_of.
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
Definition fsfun_eqMixin := Eval hnf in [eqMixin of @fsfun K T x by <:].
Canonical  fsfun_eqType := Eval hnf in EqType (@fsfun K T x) (fsfun_eqMixin).

Definition fsfunof_eqMixin := Eval hnf in [eqMixin of {fsfun K -> T / x} by <:].
Canonical  fsfunof_eqType := Eval hnf in EqType {fsfun K -> T / x} (fsfunof_eqMixin).
End FsfunCanonicals.

(* -------------------------------------------------------------------- *)
Section FsfunChoice.
Variable (K : choiceType) (T : choiceType) (x : T).

Definition fsfunof_choiceMixin :=
  Eval hnf in [choiceMixin of {fsfun K -> T / x} by <:].
Canonical  fsfunof_choiceType :=
  Eval hnf in ChoiceType {fsfun K -> T / x } fsfunof_choiceMixin.
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

Lemma canonical_fsfunK (g : {fmap K -> T}) :
  canonical_fsfun x g -> fsfun_reduce g = g.
Proof.
move=> h; apply/fmapP=> k; rewrite fnd_rem; case: (boolP (_ \in _))=> //.
by case/imfsetP=> y /eqP eq; move/forallP/(_ y)/eqP: h.
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

(* -------------------------------------------------------------------- *)
Section FsfunTheory.
Variable (K : choiceType) (T : eqType) (x : T).

Lemma mkfsfunK (g : {fmap K -> T}) :
  [fsfun g / x] = fsfun_reduce x g :> {fmap K -> T}.
Proof. by []. Qed.

Lemma fsfun_reduceE (g : {fmap K -> T}) (y : K) :
  odflt x (fsfun_reduce x g).[?y] = odflt x g.[?y].
Proof.
rewrite fnd_rem; case: (boolP (y \in _))=> //=.
by case/imfsetP=> y' /eqP <- ->; rewrite -Some_fnd.
Qed.

Lemma fsfun_fnd (g : {fmap K -> T}) (y : K) :
  [fsfun g / x] y = odflt x g.[? y].
Proof. by apply/fsfun_reduceE. Qed.

Lemma fsfunE (domf : {fset K}) (E : K -> T) (y : K) :
    [fsfun [fmap x : domf => E (val x)] / x] y
  = if y \in domf then E y else x.
Proof. by rewrite fsfun_fnd; case: fndP=> //= kf; rewrite ffunE. Qed.

Lemma fsfunW (P : {fsfun K -> T / x} -> Prop) :
  (forall g, P [fsfun g / x]) -> forall g, P g.
Proof.
move=> ih; case=> g h; have ->//: mkFsfun h = [fsfun g].
by apply/eqP; rewrite -val_eqE /= canonical_fsfunK.
Qed.

Lemma canonical_fsfun_codom
  (g : {fmap K -> T}) (k : K) (kf : k \in domf g) :
  canonical_fsfun x g -> g.[kf] != x.
Proof.
move=> c_g; apply/eqP=> eq_gk_x; move/forallP: c_g.
by move/(_ (FSetSub kf)); rewrite eq_gk_x eqxx.
Qed.

Lemma canonical_getfI (g1 g2 : {fmap K -> T}) (y : K)
    (c_g1 : canonical_fsfun x g1)
    (c_g2 : canonical_fsfun x g2)
  : odflt x g1.[? y] = odflt x g2.[? y] -> g1.[? y] = g2.[? y].
Proof.
case: (fndP g1); case: (fndP g2)=> //=; first by move=> k1 k2 /= ->.
+ by move=> _ kf ?; have /eqP := canonical_fsfun_codom kf c_g1.
+ by move=> kf _ /esym ?; have /eqP := canonical_fsfun_codom kf c_g2.
Qed.

Lemma fsfunP (g1 g2 : {fsfun K -> T / x}) :
  reflect (forall k, g1 k = g2 k) (g1 == g2).
Proof.
apply: (iffP idP)=> [/eqP->//|]; move: g1 g2.
elim/fsfunW=> g1; elim/fsfunW => g2 h; rewrite -val_eqE /=.
apply/eqP/fmapP=> k; move/(_ k): h; rewrite !fsfun_fnd.
rewrite -[LHS]fsfun_reduceE -[RHS]fsfun_reduceE.
by apply/canonical_getfI; apply/canonical_fsfun_reduce.
Qed.

Lemma domf_fsfunE (g : {fmap K -> T}) :
  domf [fsfun g / x] = [fset k : domf g | g k != x].
Proof.
rewrite /finMap_of_fsfun mkfsfunK domf_rem; apply/fsetP.
move=> k; rewrite in_fsetD andbC; case: (boolP (_ \in _))=> /=.
  move=> k_in_g; have ->: k = val (FSetSub k_in_g) by [].
  by rewrite !val_in_FSet /= -!topredE /=.
move=> k_notin_g; apply/esym/imfsetP=> h; move: h k_notin_g.
by case=> [[y]] y_in_g /= _ -> /negP.
Qed.

Lemma fsfun_eqdfl (f : {fsfun K -> T / x}) y :
  (f y == x) = (y \notin domf f).
Proof.
elim/fsfunW: f => g; rewrite fsfun_fnd domf_fsfunE.
case: fndP=> yf /=; first have: y = val (FSetSub yf) by [].
  by move=> {2}->; rewrite val_in_FSet -topredE /= negbK.
rewrite eqxx; apply/esym/imfsetP=> h; case: h yf.
by case=> /= z ? _ -> /negP.
Qed.

Lemma fsfun_outdom (f : {fsfun K -> T / x}) y :
  y \notin domf f -> f y = x.
Proof. by rewrite -fsfun_eqdfl=> /eqP. Qed.

CoInductive fsfun_spec (f : {fsfun K -> T / x}) y : bool -> T -> Type :=
| FsfunIn  (_ : y \in    domf f) : fsfun_spec f y true  (f y)
| FsfunOut (_ : y \notin domf f) : fsfun_spec f y false x.

Lemma fsfunEP (f : {fsfun K -> T / x}) y : fsfun_spec f y (y \in domf f) (f y).
Proof.
case: (boolP (y \in domf f)); first by apply/FsfunIn.
by move=> y_notin_f; rewrite (fsfun_outdom y_notin_f); apply/FsfunOut.
Qed.
End FsfunTheory.
