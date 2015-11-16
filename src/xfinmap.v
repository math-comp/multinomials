(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import choice  path finset finfun fintype bigop bigenough.
Require Export finmap.

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
Local Open Scope fmap.

(* -------------------------------------------------------------------- *)
Lemma fnd_fmap0 (T : choiceType) (U : Type) x :
  ([fmap] : {fmap T -> U}).[?x] = None.
Proof. by rewrite not_fnd // in_fset0. Qed.

(* -------------------------------------------------------------------- *)
Lemma enum_fset0 (T : choiceType) :
  enum [finType of fset0] = [::] :> seq (@fset0 T).
Proof. by rewrite enumT unlock. Qed.

Lemma enum_fset1 (T : choiceType) (x : T) :
  enum [finType of [fset x]] = [:: (FSetSub (fset11 x))].
Proof.
rewrite enumT unlock /=; have ->//=: sort_keys [:: x] = [:: x].
  by apply/perm_eq_small/uniq_perm_eq=> // y; rewrite sort_keysE.
apply/eqP; rewrite insubT ?in_fset1 //= => h.
by rewrite eqE /= andbT -val_eqE.
Qed.

(* -------------------------------------------------------------------- *)
Section BigFSet.
Variable (R : Type) (idx : R) (op : Monoid.law idx).
Variable (I : choiceType).

Lemma big_fset0 (F : @fset0 I -> R) :
  \big[op/idx]_(i : fset0) F i = idx.
Proof. by rewrite /index_enum -enumT /= enum_fset0 big_nil. Qed.

Lemma big_fset1 (a : I) (F : [fset a] -> R) :
  \big[op/idx]_(i : [fset a]) F i = F (FSetSub (fset11 a)).
Proof. by rewrite /index_enum -enumT enum_fset1 big_seq1. Qed.
End BigFSet.

Section BigFSetIncl.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Variables (T : choiceType) (A B : {fset T}) (F : T -> R).

Lemma big_fset_incl :
    A `<=` B
  -> (forall x, x \in B -> x \notin A -> F x = idx)
  -> \big[op/idx]_(x : A) F (val x) = \big[op/idx]_(x : B) F (val x).
Proof. admit. Qed.
End BigFSetIncl.

Implicit Arguments big_fset_incl [R idx op T A B].

(* -------------------------------------------------------------------- *)
Module BigEnoughFSet.
Export BigEnough.

Definition big_rel_fsubset_class K : big_rel_class_of (@fsubset K).
Proof.
exists fsubset (fun G => \big[fsetU/fset0]_(g <- G) g)=> [|g s|g1 g2 j] //.
  by rewrite big_cons fsubsetUl.
by rewrite big_cons => h; rewrite fsubsetU // h orbT.
Qed.
Canonical big_enough_fset K := BigRelOf (big_rel_fsubset_class K).

Ltac fset_big_enough_trans :=
  match goal with
  | [leq : is_true (?A `<=` ?B) |- is_true (?X `<=` ?B)] =>
       apply: fsubset_trans leq; big_enough; olddone
  end.

Ltac done := do [fset_big_enough_trans|BigEnough.done].

Ltac pose_big_fset K i :=
  evar (i : {fset K}); suff : closed i; first do
    [move=> _; instantiate (1 := bigger_than (@fsubset K) _) in (Value of i)].
End BigEnoughFSet.
