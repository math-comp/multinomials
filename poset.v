(* --------------------------------------------------------------------
 * (c) Copyright 2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool eqtype ssrfun ssrnat choice seq.
Require Import fintype tuple bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Delimit Scope cpo_scope with O.

Local Open Scope cpo_scope.

(* -------------------------------------------------------------------- *)
Module POSet.
  Section ClassDef.
    Structure mixin_of T := Mixin {
      le : rel T;
      _  : reflexive     le;
      _  : antisymmetric le;
      _  : transitive    le
    }.

    Record class_of T := Class {
      base  : Equality.class_of T;
      mixin : mixin_of T
    }.

    Local Coercion base : class_of >-> Equality.class_of.

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).
  
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).
  
    Definition pack m :=
      fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.
  
    Definition eqType := @Equality.Pack cT xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base   : class_of >-> Equality.class_of.
    Coercion mixin  : class_of >-> mixin_of.
    Coercion sort   : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.

    Canonical eqType.

    Notation posetType := type.
    Notation posetMixin := mixin_of.
    Notation POSetMixin := Mixin.
    Notation POSetType T m := (@pack T m _ _ id).
  End Exports.
End POSet.

Export POSet.Exports.

Bind Scope cpo_sort with POSet.sort.

Definition le (R : posetType) : rel R :=
  POSet.le (POSet.class R).

Definition lt (R : posetType) : rel R :=
  fun (x y : R) => (x != y) && (le x y).

Notation "[ 'posetType' 'of' T ]" := (@POSet.clone T _ _ id)
  (at level 0, format "[ 'posetType'  'of'  T ]") : form_scope.

Notation "<=%O" := (@le _).
Notation  "<%O" := (@lt _).

Notation "x <= y" := (le x y) : cpo_scope.
Notation "x < y"  := (lt x y) : cpo_scope.
Notation "x >= y" := (le y x) (only parsing) : cpo_scope.
Notation "x > y"  := (lt y x) (only parsing) : cpo_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : cpo_scope.
Notation "x < y <= z"  := ((x <  y) && (y <= z)) : cpo_scope.
Notation "x <= y < z"  := ((x <= y) && (y <  z)) : cpo_scope.
Notation "x < y < z"   := ((x <  y) && (y <  z)) : cpo_scope.

(* -------------------------------------------------------------------- *)
Section POSetTheory.
  Context {R : posetType}.

  Implicit Types x y : R.

  Lemma leo_refl x: x <= x.
  Proof. by case: R x=> ? [? []]. Qed.

  Hint Resolve leo_refl.

  Definition leoo := leo_refl.

  Lemma leo_asym: antisymmetric (<=%O : rel R).
  Proof. by case: R => ? [? []]. Qed.
    
  Lemma leo_trans: transitive (<=%O : rel R).
  Proof. by case: R => ? [? []]. Qed.

  Lemma ltoo x: x < x = false.
  Proof. by rewrite /lt eqxx. Qed.

  Lemma lto_neqAle x y: (x < y) = (x != y) && (x <= y).
  Proof. by []. Qed.    

  Lemma leo_eqVlt x y: (x <= y) = (x == y) || (x < y).
  Proof.
    rewrite lto_neqAle orb_andr orbN; case ->: (x =P y) => //.
    by move=> ->; rewrite leoo.
  Qed.

  Lemma lto_eqF x y: x < y -> x == y = false.
  Proof. by case/andP=> [/negbTE->]. Qed.

  Lemma eqo_leq x y: (x == y) = (x <= y <= x).
  Proof. by apply/eqP/idP=> [->|/leo_asym]; rewrite ?leoo. Qed.

  Lemma ltoW x y: x < y -> x <= y.
  Proof. by rewrite leo_eqVlt orbC => ->. Qed.

  Lemma lto_leo_trans y x z: x < y -> y <= z -> x < z.
  Proof.
    rewrite !lto_neqAle => /andP [ne_xy le1 le2].
    rewrite (leo_trans le1 le2) andbT; apply/eqP=> eq_xz.
    by move: ne_xy; rewrite eqo_leq {2}eq_xz le1 le2.
  Qed.

  Lemma lto_trans: transitive (<%O : rel R).
  Proof. by move=> y x z le1 /ltoW le2; apply/(@lto_leo_trans y). Qed.

  Lemma leoNgt x y: (x <= y) -> ~~ (y < x).
  Proof.
    move=> le_xy; apply/negP=> /andP [ne_yx le_yx].
    by move: ne_yx; rewrite eqo_leq le_xy le_yx.
  Qed.

  Lemma ltoNge x y : (x < y) -> ~~ (y <= x).
  Proof.
    move=> lt_xy; rewrite leo_eqVlt eq_sym lto_eqF //=.
    by rewrite leoNgt // ltoW.
  Qed.

  Section Total.
    Hypothesis Rtotal: total (<=%O : rel R).

    Lemma letNgt x y: (x <= y) = ~~ (y < x).
    Proof.
      apply/idP/idP=> [/leoNgt|] //; rewrite lto_neqAle.
      by case/orP: (Rtotal x y)=> -> //; rewrite andbT negbK=> /eqP->.
   Qed.

   Lemma lttNge x y: (x < y) = ~~ (y <= x).
   Proof. by rewrite letNgt negbK. Qed.
  End Total.
End POSetTheory.

Hint Resolve leo_refl.

(* -------------------------------------------------------------------- *)
Definition natPOSetMixin := POSetMixin leqnn anti_leq leq_trans.
Canonical  natPOSetType  := POSetType nat natPOSetMixin.

Lemma lenP (n m : nat): (n <= m) = (n <= m)%N.
Proof. by []. Qed.

Lemma ltnP (n m : nat): (n < m) = (n < m)%N.
Proof. by rewrite lto_neqAle ltn_neqAle lenP. Qed.

(* -------------------------------------------------------------------- *)
Section LexOrder.
  Variable T : posetType.

  Implicit Types s : seq T.

  Fixpoint lex s1 s2 :=
    if s1 is x1 :: s1' then
      if s2 is x2 :: s2' then
        (x1 < x2) || ((x1 == x2) && lex s1' s2')
      else
        false
    else
      true.

  Lemma lex_le_head x sx y sy:
    lex (x :: sx) (y :: sy) -> x <= y.
  Proof. by case/orP => [/ltoW|/andP [/eqP-> _]]. Qed.

  Lemma lex_refl: reflexive lex.
  Proof. by elim => [|x s ih] //=; rewrite eqxx ih orbT. Qed.

  Lemma lex_antisym: antisymmetric lex.
  Proof.
    elim=> [|x sx ih] [|y sy] //= /andP []; case/orP=> [h|].
      rewrite [y<x]lto_neqAle andbC {2}eq_sym (lto_eqF h).
      by move/ltoNge/negbTE: h=> ->.
    case/andP=> /eqP->; rewrite eqxx ltoo /= => h1 h2.
    by rewrite (ih sy) // h1 h2.
  Qed.      

  Lemma lex_trans: transitive lex.
  Proof.
    elim=> [|y sy ih] [|x sx] [|z sz] // h1 h2.
    have le := leo_trans (lex_le_head h1) (lex_le_head h2).
    have := h2 => /= /orP []; have := h1 => /= /orP [].
      by move=> lt1 lt2; rewrite (lto_trans lt1 lt2).
      by case/andP=> /eqP-> _ ->.
      by move=> lt /andP [/eqP<- _]; rewrite lt.
   move=> /andP [_ l1] /andP [_ l2]; rewrite ih // andbT.
   by rewrite orbC -leo_eqVlt.
  Qed.

  Hypothesis le_total: total (<=%O : rel T).

  Lemma lex_total: total lex.
  Proof.
    elim=> [|x sx ih] [|y sy] //=; case: (boolP (x < y))=> //=.
    rewrite -letNgt // leo_eqVlt; case/orP=> [/eqP->|].
      by rewrite !eqxx ltoo /= ih.
    by move=> lt; rewrite [x==y]eq_sym (lto_eqF lt) /= orbF.
  Qed.
End LexOrder.

(* -------------------------------------------------------------------- *)
Module CPO.
  Section ClassDef.
    Structure mixin_of (T : posetType) := Mixin {
      bot : T; _ : forall x, bot <= x
    }.

    Record class_of (T : Type) := Class {
      base  : POSet.class_of T;
      mixin : mixin_of (POSet.Pack base T)
    }.

    Local Coercion base : class_of >-> POSet.class_of.

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).
  
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@POSet.Pack T b0 T)) :=
      fun bT b & phant_id (POSet.class bT) b =>
        fun    m & phant_id m0 m => Pack (@Class T b m) T.
  
    Definition eqType := @Equality.Pack cT xclass xT.
    Definition posetType := @POSet.Pack cT xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base      : class_of >-> POSet.class_of.
    Coercion mixin     : class_of >-> mixin_of.
    Coercion sort      : type >-> Sortclass.
    Coercion eqType    : type >-> Equality.type.
    Coercion posetType : type >-> POSet.type.

    Canonical eqType.
    Canonical posetType.

    Notation cpoType  := type.
    Notation cpoMixin := mixin_of.
    Notation CPOMixin := Mixin.
    Notation CPOType T m := (@pack T _ m _ _ id _ id).
  End Exports.
End CPO.

Export CPO.Exports.

Definition bot (R : cpoType) : R :=
  CPO.bot (CPO.class R).

Notation "0" := (@bot _) : cpo_scope.

(* -------------------------------------------------------------------- *)
Section Max.
  Variable T : posetType.

  Implicit Types x y z : T.

  Definition maxo x y := if x < y then y else x.
End Max.

(* -------------------------------------------------------------------- *)
Notation "\max_ ( i <- r | P ) F" :=
  (\big[@maxo _/0%O]_(i <- r | P%B) F%N) : cpo_scope.
Notation "\max_ ( i <- r ) F" :=
  (\big[@maxo _/0%O]_(i <- r) F%N) : cpo_scope.
Notation "\max_ ( i | P ) F" :=
  (\big[@maxo _/0%O]_(i | P%B) F%N) : cpo_scope.
Notation "\max_ i F" :=
  (\big[@maxo _/0%O]_i F%N) : cpo_scope.
Notation "\max_ ( i : I | P ) F" :=
  (\big[@maxo _/0%O]_(i : I | P%B) F%N) (only parsing) : cpo_scope.
Notation "\max_ ( i : I ) F" :=
  (\big[@maxo _/0%O]_(i : I) F%N) (only parsing) : cpo_scope.
Notation "\max_ ( m <= i < n | P ) F" :=
 (\big[@maxo _/0%O]_(m <= i < n | P%B) F%N) : cpo_scope.
Notation "\max_ ( m <= i < n ) F" :=
 (\big[@maxo _/0%O]_(m <= i < n) F%N) : cpo_scope.
Notation "\max_ ( i < n | P ) F" :=
 (\big[@maxo _/0%O]_(i < n | P%B) F%N) : cpo_scope.
Notation "\max_ ( i < n ) F" :=
 (\big[@maxo _/0%O]_(i < n) F%N) : cpo_scope.
Notation "\max_ ( i 'in' A | P ) F" :=
 (\big[@maxo _/0%O]_(i in A | P%B) F%N) : cpo_scope.
Notation "\max_ ( i 'in' A ) F" :=
 (\big[@maxo _/0%O]_(i in A) F%N) : cpo_scope.

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" ".") ***
*** End: ***
 *)
