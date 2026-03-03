(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
From mathcomp Require Import choice seq path finset finfun fintype bigop.
From mathcomp Require Import bigenough.
From mathcomp Require Export finmap.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.

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
    [move=> _; instantiate (1 := bigger_than (@fsubset K) _) in (value of i)].
End BigEnoughFSet.
