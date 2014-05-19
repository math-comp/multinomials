(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop tuple finfun ssralg poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Reserved Notation "''X_{1..' n '}'" (at level 3, n at level 2).

(* -------------------------------------------------------------------- *)
Section MultinomDef.
  Context (n : nat).

  Inductive multinom : predArgType :=
    Multinom of n.-tuple nat.

  Definition multinom_val M := let: Multinom m := M in m.

  Canonical multinom_subType := Eval hnf in [newType for multinom_val].

  Definition fun_of_multinom M (i : 'I_n) := tnth (multinom_val M) i.

  Coercion fun_of_multinom : multinom >-> Funclass.
End MultinomDef.

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

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" ".") ***
*** End: ***
 *)
