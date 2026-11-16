(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
From mathcomp Require Import choice seq path finset finfun fintype bigop.
From mathcomp Require Import bigenough.
From mathcomp Require Export finmap.
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
