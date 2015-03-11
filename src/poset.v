(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
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

  Lemma leo_lto_trans y x z: x <= y -> y < z -> x < z.
  Proof.
    rewrite leo_eqVlt; case/orP=> [/eqP->//|].
    by move/lto_trans; apply.
  Qed.

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

  Lemma ltxP_seq (x : T) (s1 s2 : seq T): size s1 = size s2 ->
    reflect
      (exists2 i : nat, i < size s1 &
         [/\ forall j, (j < i)%N -> nth x s1 j = nth x s2 j
          &  nth x s1 i < nth x s2 i])
      ((s1 != s2) && lex s1 s2).
  Proof.
    elim: s1 s2=> [|x1 s1 ih] [|x2 s2] //=.
      by move=> _; constructor; do 2! case.
    case=> eq_sz; rewrite eqseq_cons; case: eqP.
      move=> -> /=; rewrite ltoo /=; apply: (iffP idP).
        move/ih=> /(_ eq_sz) [i lt_i_sz1 [h1 h2]].
        by exists i.+1 => //; split=> //; case.
      case; case=> /= [_ []|n]; first by rewrite ltoo.
      rewrite ltnP ltnS => lt_n_sz1 [h1 h2]; apply/ih=> //.
      exists n; [by rewrite ltnP | split=> // j lt_jn].
      by apply/(h1 j.+1).
    move/eqP=> ne_x1x2; rewrite /= orbF; case h: (x1 < x2).
      by constructor; exists 0.
    constructor; case; case=> [|n] _; case=> /=.
      by rewrite h.
    by move/(_ 0 (erefl true))=> /= /eqP; rewrite (negbTE ne_x1x2).
  Qed.
    
  Lemma ltxP n (s1 s2 : n.-tuple T):
    reflect
      (exists2 i : 'I_n,
            forall (j : 'I_n), (j < i)%N -> tnth s1 j = tnth s2 j
          & tnth s1 i < tnth s2 i)
      ((s1 != s2) && lex s1 s2).
  Proof.
    case: n s1 s2 => [|n] s1 s2.
      by rewrite [s1]tuple0 [s2]tuple0; constructor; do 2! case.
    have x: T by case: {s2} s1; case.
    move: (@ltxP_seq x s1 s2); rewrite !size_tuple.
    case=> // h; constructor.
    + case: h=> i; rewrite ltnP => p [h1 h2].
      exists (Ordinal p) => [j|] /=; rewrite !(tnth_nth x) //.
      by apply/h1.
    + move=> ho; apply/h => {h}; case: ho; case=> i /= p.
      rewrite !(tnth_nth x) /= => h1 h2; exists i; rewrite ?ltnP //.
      split=> // j lt_ji; move: (h1 (Ordinal (ltn_trans lt_ji p)) lt_ji).
      by rewrite !(tnth_nth x).
  Qed.
End LexOrder.

Definition ltx (T : posetType) (x y : seq T) := (x != y) && (lex x y).

Lemma lex_eqVlt (T : posetType) (x y : seq T):
  lex x y = (x == y) || (ltx x y).
Proof.
  rewrite /ltx orb_andr orbN /= orb_idl //.
  by move/eqP=> ->; rewrite lex_refl.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ltx_lex_nat_sum (k : nat) (s1 s2 r1 r2: k.-tuple nat):
       ltx s1 r1 -> lex s2 r2
    -> ltx [seq (x.1 + x.2)%N | x <- zip s1 s2]
           [seq (x.1 + x.2)%N | x <- zip r1 r2].
Proof.
  move=> lt1; rewrite lex_eqVlt; case/orP.
    move/eqP=> ->; apply/ltxP=> /=; case/ltxP: lt1.
    move=> i eq le; exists i.
    + move=> j lt_ij; rewrite !(tnth_nth 0%N) /=.
      rewrite !(nth_map (0, 0)) ?(size_zip, size_tuple, minnn) //=.
      apply/eqP; rewrite !nth_zip ?size_tuple //= eqn_add2r.
      by move: (eq _ lt_ij); rewrite !(tnth_nth 0%N)=> ->.
    + rewrite !(tnth_nth 0%N) /= !(nth_map (0, 0)); last first.
        by rewrite size_zip !size_tuple minnn.
        by rewrite size_zip !size_tuple minnn.
      rewrite !nth_zip ?size_tuple //= ltnP ltn_add2r.
      by move: le; rewrite !(tnth_nth 0%N) !ltnP.
  move=> lt2; case/ltxP: lt1=> i eqi lti; case/ltxP: lt2=> j eqj ltj.
  have lt_ij_k: (minn i j < k)%N by rewrite gtn_min ltn_ord.
  pose a := Ordinal lt_ij_k; apply/ltxP; exists a.
  + move=> l lt_la; rewrite !(tnth_nth 0%N) /=.
    rewrite !(nth_map (0, 0)) ?(size_zip, size_tuple, minnn) //.
    move: lt_la; rewrite leq_min => /andP [lt_li lt_lj].
    by rewrite !nth_zip ?size_tuple //= -!tnth_nth ?(eqi, eqj).
  + rewrite !(tnth_nth 0%N) /= !(nth_map (0, 0)); first last.
      by rewrite size_zip !size_tuple minnn.
      by rewrite size_zip !size_tuple minnn.
    rewrite !nth_zip ?size_tuple //= ltnP.
    rewrite /minn; case: (ssrnat.ltnP i j) => [lt_ij|].
      by rewrite -!tnth_nth eqj // ltn_add2r -ltnP.
    rewrite leq_eqVlt => /orP [/eqP|lt_ji]; last first.
      by rewrite -!tnth_nth eqi // ltn_add2l -ltnP.
    move=> eq_ij; rewrite -addnS leq_add // -?ltnP ?ltj.
      by apply/ltnW; rewrite -ltnP eq_ij -!tnth_nth.
      by rewrite -!tnth_nth.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ltx_nat_sum (k : nat) (s1 s2 r1 r2: k.-tuple nat):
       ltx s1 r1 -> ltx s2 r2
    -> ltx [seq (x.1 + x.2)%N | x <- zip s1 s2]
           [seq (x.1 + x.2)%N | x <- zip r1 r2].
Proof.
  move=> lt1; rewrite /ltx; case/andP=> _.
  by apply/ltx_lex_nat_sum: lt1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lex_ltx_nat_sum (k : nat) (s1 s2 r1 r2: k.-tuple nat):
       lex s1 r1 -> ltx s2 r2
    -> ltx [seq (x.1 + x.2)%N | x <- zip s1 s2]
           [seq (x.1 + x.2)%N | x <- zip r1 r2].
Proof.
  have eqC (s r : k.-tuple nat):
      [seq x.1+x.2 | x <- zip s r]
    = [seq x.1+x.2 | x <- zip r s].
  + apply/(@eq_from_nth _ 0%N); rewrite ?(size_map, size_zip) minnC //.
    move=> i lt_is; rewrite !(nth_map (0, 0)) ?size_zip // 1?minnC //.
    by rewrite !nth_zip ?size_tuple //= addnC.
  move=> le lt; move/ltx_lex_nat_sum/(_ le): lt.
  by rewrite [X in ltx X _] eqC [X in ltx _ X]eqC.
Qed.

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
Section CPOTheory.
  Variable T : cpoType.

  Lemma le0o (x : T): 0 <= x.
  Proof. by case: T x=> U [? []]. Qed.

  Lemma leqo0 (x : T): (x <= 0) = (x == 0).
  Proof.
    apply/idP/eqP=> [le_x0|->//]; apply/eqP.
    by rewrite eqo_leq le_x0 le0o.
  Qed.

  Lemma lto0 (x : T): (x < 0) = false.
  Proof. by apply/negP=> /ltoNge; rewrite le0o. Qed.
End CPOTheory.

(* -------------------------------------------------------------------- *)
Section Max.
  Context {T : posetType}.

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

(* -------------------------------------------------------------------- *)
Section MaxTheory.
  Variable T : cpoType.

  Hypothesis total: total (@le T).

  Local Notation max := (@maxo T) (only parsing).

  Lemma maxo0: right_id 0%O max.
  Proof. by move=> x; rewrite /maxo lto0. Qed.

  Lemma maxoC: commutative max.
  Proof.
    move=> x y; rewrite /maxo lttNge // leo_eqVlt.
    by case: eqP=> [->|_] /=; [rewrite ltoo | case: (_ < _)].
  Qed.

  Lemma max0o: left_id 0%O max.
  Proof. by move=> x; rewrite maxoC maxo0. Qed.

  Lemma maxoA: associative max.
  Proof.
    move=> x y z; rewrite /maxo; case: (boolP (y < z))=> c_yz.
      case: (boolP (x < y))=> c_xy //.
      by rewrite c_yz (lto_trans c_xy c_yz).
    case: (boolP (x < y))=> c_xy; rewrite ?(negbTE c_yz) //.
    rewrite lttNge //; move: c_xy c_yz; rewrite -!letNgt //.
    by move=> h /leo_trans=> ->.
  Qed.

  Canonical maxo_monoid := Monoid.Law maxoA max0o maxo0.
  Canonical maxo_comoid := Monoid.ComLaw maxoC.

  Lemma maxoAC: right_commutative max.
  Proof. by apply/Monoid.mulmAC. Qed.

  Lemma maxoCA: left_commutative max.
  Proof. by apply/Monoid.mulmCA. Qed.

  Lemma maxoACA : interchange max max.
  Proof. by apply/Monoid.mulmACA. Qed.

  Lemma maxo_idPl {x y} : reflect (max x y = x) (x >= y).
  Proof.
    apply: (iffP idP)=> [le_yx|].
      by rewrite /maxo lttNge // le_yx.
    move=> eq_max; rewrite letNgt //; apply/negP.
    rewrite lto_neqAle; case/andP=> ne_yx le_yx.
    move: eq_max; rewrite /maxo lto_neqAle ne_yx le_yx /=.
    by move/eqP; rewrite eq_sym (negbTE ne_yx).
  Qed.

  Lemma maxo_idPr {x y} : reflect (max x y = y) (x <= y).
  Proof. by rewrite maxoC; apply/maxo_idPl. Qed.

  Lemma maxoo: idempotent max.
  Proof. by move=> x; apply/maxo_idPl. Qed.

  Lemma leo_max x y1 y2: (x <= max y1 y2) = (x <= y1) || (x <= y2).
  Proof.
    without loss le_y21: y1 y2 / y2 <= y1.
      by case/orP: (total y2 y1) => le_y12; last rewrite maxoC orbC; apply.
    by rewrite (maxo_idPl le_y21) orb_idr // => /leo_trans->.
  Qed.

  Lemma lto_max x y1 y2: (x < max y1 y2) = (x < y1) || (x < y2).
  Proof.
    without loss le_y21: y1 y2 / y2 <= y1.
      by case/orP: (total y2 y1) => le_y12; last rewrite maxoC orbC; apply.
    by rewrite (maxo_idPl le_y21) orb_idr // => /lto_leo_trans->.
  Qed.

  Lemma leo_maxl x y: x <= max x y. Proof. by rewrite leo_max leoo. Qed.
  Lemma leo_maxr x y: y <= max x y. Proof. by rewrite maxoC leo_maxl. Qed.

  Lemma gto_max x y1 y2: (x > max y1 y2) = (x > y1) && (x > y2).
  Proof. by rewrite !lttNge // leo_max negb_or. Qed.

  Lemma geo_max x y1 y2: (x >= max y1 y2) = (x >= y1) && (x >= y2).
  Proof. by rewrite letNgt // lto_max negb_or -!letNgt. Qed.
End MaxTheory.  

(* -------------------------------------------------------------------- *)
Section BigMaxTheory.
  Variable T : eqType.
  Variable U : cpoType.
  Variable F : T -> U.

  Lemma eq_bigmaxo (r : seq T): r != [::] ->
    {x : T | (x \in r) && \max_(i <- r) F i == F x}.
  Proof.
    elim: r => [//|z r ih] _; case: r ih => [_|z' r ih].
      exists z; rewrite mem_seq1 eqxx /=.
      by rewrite unlock /= maxo0.
    rewrite big_cons; set M := \max_(_ <- _) _; rewrite /maxo.
    case: (F z < M); last by exists z; rewrite in_cons !eqxx.
    case: ih=> // x /andP [x_in eq_Fx]; exists x.
    by rewrite in_cons x_in orbT eq_Fx.
  Qed.

  Lemma leo_bigmax_cond (P : pred T) (r : seq T) i0: total (@le U) ->
    P i0 -> i0 \in r -> F i0 <= \max_(i <- r | P i) F i.
  Proof.
    move=> tot Pi0; elim: r=> // x r ih; rewrite in_cons.
    case/orP=> [/eqP<-|]; rewrite big_cons ?Pi0.
      by rewrite leo_max // leoo.
    by move/ih; case: (P x)=> //; rewrite leo_max 1?orbC // => ->.
  Qed.

  Lemma leo_bigmax (r : seq T) i0: total (@le U) ->
    i0 \in r -> F i0 <= \max_(i <- r) F i.
  Proof. move=> tot i0_in_r; exact/leo_bigmax_cond. Qed.
End BigMaxTheory.
