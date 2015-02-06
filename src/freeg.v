(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2015 IMDEA Software Institute.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg ssrnum ssrint generic_quotient.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Defensive Implicit.

(* -------------------------------------------------------------------- *)
Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'freeg' K / G }" (at level 0, K, G at level 2, format "{ 'freeg'  K  /  G }").
Reserved Notation "{ 'freeg' K }" (at level 0, K at level 2, format "{ 'freeg'  K }").
Reserved Notation "[ 'freeg' S ]" (at level 0, S at level 2, format "[ 'freeg'  S ]").

Reserved Notation "[ 'regular' 'of' R ]" (format "[ 'regular' 'of'  R ]").

(* -------------------------------------------------------------------- *)
Local Notation "[ 'regular' 'of' R ]" := (GRing.regular_lmodType R).

(* -------------------------------------------------------------------- *)
Let perm_eq_map (T U : eqType) (f : T -> U) (xs ys : seq T):
  perm_eq xs ys -> (perm_eq (map f xs) (map f ys)).
Proof. by move/perm_eqP=> h; apply/perm_eqP=> p; rewrite !count_map. Qed.

Lemma perm_eq_filter (T : eqType) (p : pred T) (xs ys : seq T):
  perm_eq xs ys -> perm_eq (filter p xs) (filter p ys).
Proof.
  move=> /perm_eqP peq; apply/perm_eqP=> pc.
  by rewrite !count_filter; apply/peq.
Qed.

(* -------------------------------------------------------------------- *)
Module FreegDefs.
  Section Defs.
    Variable G : zmodType.
    Variable K : choiceType.

    Definition reduced (D : seq (G * K)) :=
         (uniq [seq zx.2 | zx <- D])
      && (all  [pred zx | zx.1 != 0] D).

    Lemma reduced_uniq: forall D, reduced D -> uniq [seq zx.2 | zx <- D].
    Proof. by move=> D /andP []. Qed.

    Record prefreeg : Type := mkPrefreeg {
      seq_of_prefreeg : seq (G * K);
      _ : reduced seq_of_prefreeg
    }.

    Implicit Arguments mkPrefreeg [].

    Local Coercion seq_of_prefreeg : prefreeg >-> seq.

    Lemma prefreeg_reduced: forall (D : prefreeg), reduced D.
    Proof. by case. Qed.

    Lemma prefreeg_uniq: forall (D : prefreeg), uniq [seq zx.2 | zx <- D].
    Proof. by move=> D; apply reduced_uniq; apply prefreeg_reduced. Qed.

    Canonical prefreeg_subType :=
      [subType for seq_of_prefreeg by prefreeg_rect].

    Definition prefreeg_eqMixin := Eval hnf in [eqMixin of prefreeg by <:].
    Canonical  prefreeg_eqType  := Eval hnf in EqType _ prefreeg_eqMixin.

    Definition prefreeg_choiceMixin := Eval hnf in [choiceMixin of prefreeg by <:].
    Canonical  prefreeg_choiceType  := Eval hnf in ChoiceType prefreeg prefreeg_choiceMixin.
  End Defs.

  Implicit Arguments mkPrefreeg [G K].

  Section Quotient.
    Variable G : zmodType.
    Variable K : choiceType.

    Local Coercion seq_of_prefreeg : prefreeg >-> seq.

    Definition equiv (D1 D2 : prefreeg G K) := perm_eq D1 D2.

    Lemma equiv_refl: reflexive equiv.
    Proof. by move=> D; apply: perm_eq_refl. Qed.

    Lemma equiv_sym: symmetric equiv.
    Proof. by move=> D1 D2; apply: perm_eq_sym. Qed.

    Lemma equiv_trans: transitive equiv.
    Proof. by move=> D1 D2 D3 H12 H23; apply (perm_eq_trans H12 H23). Qed.

    Canonical prefreeg_equiv := EquivRel equiv equiv_refl equiv_sym equiv_trans.
    Canonical prefreeg_equiv_direct := defaultEncModRel equiv.

    Definition type := {eq_quot equiv}.
    Definition type_of of phant G & phant K := type.

    Notation "{ 'freeg' K / G }" := (type_of (Phant G) (Phant K)).

    Canonical freeg_quotType   := [quotType of type].
    Canonical freeg_eqType     := [eqType of type].
    Canonical freeg_choiceType := [choiceType of type].
    Canonical freeg_eqQuotType := [eqQuotType equiv of type].

    Canonical freeg_of_quotType   := [quotType of {freeg K / G}].
    Canonical freeg_of_eqType     := [eqType of {freeg K / G}].
    Canonical freeg_of_choiceType := [choiceType of {freeg K / G}].
    Canonical freeg_of_eqQuotType := [eqQuotType equiv of {freeg K / G}].
  End Quotient.

  Module Exports.
    Coercion seq_of_prefreeg : prefreeg >-> seq.

    Canonical prefreeg_equiv.
    Canonical prefreeg_equiv_direct.

    Canonical prefreeg_subType.
    Canonical prefreeg_eqType.
    Canonical prefreeg_choiceType.
    Canonical prefreeg_equiv.
    Canonical freeg_quotType.
    Canonical freeg_eqType.
    Canonical freeg_choiceType.
    Canonical freeg_eqQuotType.
    Canonical freeg_of_quotType.
    Canonical freeg_of_eqType.
    Canonical freeg_of_choiceType.
    Canonical freeg_of_eqQuotType.

    Notation prefreeg   := prefreeg.
    Notation fgequiv    := equiv.
    Notation mkPrefreeg := mkPrefreeg.

    Notation reduced := reduced.

    Notation "{ 'freeg' T / G }" := (type_of (Phant G) (Phant T)).
    Notation "{ 'freeg' T  }" := (type_of (Phant int) (Phant T)).

    Identity Coercion type_freeg_of : type_of >-> type.
  End Exports.
End FreegDefs.

Export FreegDefs.Exports.

(* -------------------------------------------------------------------- *)
Section FreegTheory.
  Section MkFreeg.

  Variable G : zmodType.
  Variable K : choiceType.

  Implicit Types rD  : prefreeg G K.
  Implicit Types D   : {freeg K / G}.
  Implicit Types s   : seq (G * K).
  Implicit Types z k : G.
  Implicit Types x y : K.

  Local Notation freeg := {freeg K / G}.

  Lemma perm_eq_fgrepr rD: perm_eq (repr (\pi_freeg rD)) rD.
  Proof. by rewrite -/(fgequiv _ _); apply/eqmodP; rewrite reprK. Qed.

  Lemma reduced_uniq s: reduced s -> uniq [seq zx.2 | zx <- s].
  Proof. by case/andP. Qed.

  Lemma prefreeg_reduced rD: reduced rD.
  Proof. by case: rD. Qed.

  Lemma prefreeg_uniq rD: uniq [seq zx.2 | zx <- rD].
  Proof. by apply reduced_uniq; apply prefreeg_reduced. Qed.

  Fixpoint augment s z x :=
    if   s is ((z', x') as d) :: s
    then if x == x' then (z + z', x) :: s else d :: (augment s z x)
    else [:: (z, x)].

  Definition reduce s :=
    filter
      [pred zx | zx.1 != 0]
      (foldr (fun zx s => augment s zx.1 zx.2) [::] s).

  Definition predom s: seq K := [seq x.2 | x <- s].

  Definition dom D := [seq zx.2 | zx <- (repr D)].

  Lemma uniq_dom D: uniq (dom D).
  Proof. by rewrite /dom; case: (repr D)=> /= {D} D; case/andP. Qed.

  Lemma reduced_cons zx s:
    reduced (zx :: s) = [&& zx.1 != 0, zx.2 \notin predom s & reduced s].
  Proof.
    rewrite /reduced map_cons cons_uniq /= !andbA; congr (_ && _).
    by rewrite andbAC; congr (_ && _); rewrite andbC.
  Qed.

  Lemma mem_augment: forall s z x y,
    x != y -> y \notin (predom s) -> y \notin (predom (augment s z x)).
  Proof.
    move=> s z x y neq_xy; elim: s => [|[z' x'] s IH] /=.
    + by move=> _; rewrite mem_seq1 eq_sym.
    + rewrite in_cons negb_or => /andP [neq_yx' Hys].
      have [->|neq_xx'] := eqVneq x x'; rewrite ?eqxx /=.
      * by rewrite in_cons negb_or neq_yx' Hys.
      * by rewrite (negbTE neq_xx') /= in_cons (negbTE neq_yx') IH.
  Qed.

  Lemma uniq_predom_augment s z x:
    uniq (predom s) -> uniq (predom (augment s z x)).
  Proof.
    elim: s => [|[z' x'] s ih] //=.
    have [->|neq_xx'] := eqVneq x x'; rewrite ?eqxx //.
    rewrite (negbTE neq_xx') /=; case/andP=> Hx's /ih ->.
    by rewrite andbT; apply mem_augment.
  Qed.

  Lemma uniq_predom_reduce s: uniq (predom (reduce s)).
  Proof.
    rewrite /reduce; set s' := (foldr _ _ _).
    apply (subseq_uniq (s2 := predom s')).
    + by apply map_subseq; apply filter_subseq.
    rewrite /s' => {s'}; elim: s=> [|[z x] s IH] //=.
    by apply uniq_predom_augment.
  Qed.

  Lemma reduced_reduce s: reduced (reduce s).
  Proof.
    rewrite /reduced uniq_predom_reduce /=.
    by apply/allP=> zx; rewrite mem_filter=> /andP [].
  Qed.

  Lemma outdom_augmentE s k x:
    x \notin predom s -> augment s k x = rcons s (k, x).
  Proof.
    elim: s=> [//|[k' x'] s ih] /=; rewrite in_cons.
    by case/norP=> /negbTE -> /ih ->.
  Qed.

  Lemma reduce_reduced s: reduced s -> reduce s = rev s.
  Proof.
    move=> rs; rewrite /reduce; set S := foldr _ _ _.
    have ->: S = rev s; rewrite {}/S.
      elim: s rs => [//|[k x] s ih]; rewrite reduced_cons /=.
      case/and3P=> nz_k x_notin_s rs; rewrite ih //.
      rewrite rev_cons outdom_augmentE //; move: x_notin_s.
      by rewrite /predom map_rev mem_rev.
    rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
    move=> kx; rewrite mem_rev /=; case/andP: rs.
    by move=> _ /allP /(_ kx).
  Qed.

  Lemma reduceK s: reduced s -> perm_eq (reduce s) s.
  Proof.
    move/reduce_reduced=> ->; apply/perm_eqP=> p.
    rewrite /rev -[X in _ = X]addn0; have ->: (0 = count p [::])%N by [].
    elim: s [::] => [|xk s ih] S.
      by rewrite catrevE /= add0n.
      by rewrite /= ih /= addnCA addnA.
  Qed.

  Definition Prefreeg s :=
    mkPrefreeg (reduce s) (reduced_reduce s).

  Lemma PrefreegK rD: Prefreeg rD = rD %[mod_eq (@fgequiv G K)].
  Proof.
    case: rD => [s hs]; rewrite /Prefreeg; apply/eqmodP=> /=.
    by rewrite /fgequiv /=; apply: reduceK.
  Qed.

  Definition Freeg := lift_embed {freeg K / G} Prefreeg.
  Canonical to_freeg_pi_morph := PiEmbed Freeg.

  End MkFreeg.

  Local Notation "[ 'freeg' S ]" := (Freeg S).

  Local Notation "<< z *g p >>" := [freeg [:: (z, p)]].
  Local Notation "<< p >>"      := [freeg [:: (1, p)]].

  (* ------------------------------------------------------------------ *)
  Section ZLift.
  Variable R : ringType.
  Variable M : lmodType R.
  Variable K : choiceType.

  Implicit Types rD  : prefreeg R K.
  Implicit Types D   : {freeg K / R}.
  Implicit Types s   : seq (R * K).
  Implicit Types z k : R.
  Implicit Types x y : K.

  Variable f : K -> M.

  Definition prelift s : M :=
    \sum_(x <- s) x.1 *: (f x.2).

  Definition prefreeg_opp s :=
    [seq (-xz.1, xz.2) | xz <- s].

  Lemma prelift_nil: prelift [::] = 0.
  Proof. by rewrite /prelift big_nil. Qed.

  Lemma prelift_cons s k x:
    prelift ((k, x) :: s) = k *: (f x) + (prelift s).
  Proof. by rewrite /prelift big_cons. Qed.

  Lemma prelift_cat s1 s2: prelift (s1 ++ s2) = prelift s1 + prelift s2.
  Proof. by rewrite /prelift big_cat. Qed.

  Lemma prelift_opp s: prelift (prefreeg_opp s) = -(prelift s).
  Proof.
    rewrite /prelift big_map big_endo ?oppr0 //=; last exact: opprD.
    by apply: eq_bigr => i _; rewrite scaleNr.
  Qed.

  Lemma prelift_seq1 k x: prelift [:: (k, x)] = k *: (f x).
  Proof. by rewrite /prelift big_seq1. Qed.

  Lemma prelift_perm_eq s1 s2: perm_eq s1 s2 -> prelift s1 = prelift s2.
  Proof. by move=> peq; apply: eq_big_perm. Qed.

  Lemma prelift_augment s k x:
    prelift (augment s k x) = k *: (f x) + (prelift s).
  Proof.
    elim: s => [|[k' x'] s ih] //=.
      by rewrite prelift_seq1 prelift_nil !simpm.
    have [->|ne_xx'] := eqVneq x x'.
      by rewrite eqxx !prelift_cons scalerDl addrA.
      by rewrite (negbTE ne_xx') !prelift_cons ih addrCA.
  Qed.

  Lemma prelift_reduce s: prelift (reduce s) = prelift s.
  Proof.
    rewrite /reduce; set S := foldr _ _ _; set rD := filter _ _.
    have ->: prelift rD = prelift S; rewrite ?/rD => {rD}.
      elim: S => [//|[k x] S IH] /=; have [->|nz_k] := eqVneq k 0.
        by rewrite eqxx /= prelift_cons scale0r !simpm.
      by rewrite nz_k !prelift_cons IH.
    rewrite /S; elim: {S} s => [//|[k x] s ih].
    by rewrite prelift_cons /= prelift_augment ih.
  Qed.

  Lemma prelift_repr rD: prelift(repr (\pi_{freeg K / R} rD)) = prelift rD.
  Proof. by rewrite (prelift_perm_eq (perm_eq_fgrepr _)). Qed.

  Definition lift   := fun (rD : prefreeg _ _) => prelift rD.
  Definition fglift := lift_fun1 {freeg K / R} lift.

  Lemma pi_fglift: {mono \pi_{freeg K / R} : D / lift D >-> fglift D}.
  Proof.
    case=> [s reds]; unlock fglift; rewrite !piE.
    by apply/prelift_perm_eq; apply: perm_eq_fgrepr.
  Qed.

  Canonical pi_fglift_morph := PiMono1 pi_fglift.

  Lemma fglift_Freeg s: fglift [freeg s] = prelift s.
  Proof.
    unlock Freeg; unlock fglift; rewrite !piE /lift.
    rewrite (prelift_perm_eq (perm_eq_fgrepr _)) /=.
    exact: prelift_reduce.
  Qed.

  Lemma liftU k x: fglift << k *g x >> = k *: (f x).
  Proof. by rewrite fglift_Freeg prelift_seq1. Qed.

  End ZLift.

  (* -------------------------------------------------------------------- *)
  Variable R : ringType.
  Variable K : choiceType.

  Implicit Types rD  : prefreeg R K.
  Implicit Types D   : {freeg K / R}.
  Implicit Types s   : seq (R * K).
  Implicit Types z k : R.
  Implicit Types x y : K.

  Definition coeff x D : R := fglift (fun y => (y == x)%:R : R^o) D.

  Lemma coeffU k x y: coeff y << k *g x >> = k * (x == y)%:R.
  Proof. by rewrite /coeff liftU. Qed.

  Definition precoeff x s : R :=
    \sum_(kx <- s | kx.2 == x) kx.1.

  Lemma precoeffE x:
    precoeff x =1 prelift (fun y => (y == x)%:R : R^o).
  Proof.
    move=> s; rewrite /precoeff /prelift; apply/esym.
    rewrite (bigID [pred kx | kx.2 == x]) /= addrC big1; last first.
      by move=> i /negbTE ->; rewrite scaler0.
    rewrite add0r; apply: eq_bigr=> i /eqP ->.
    by rewrite eqxx /GRing.scale /= mulr1.
  Qed.

  Lemma precoeff_nil x: precoeff x [::] = 0.
  Proof. by rewrite /precoeff big_nil. Qed.

  Lemma precoeff_cons x s y k:
    precoeff x ((k, y) :: s) = (y == x)%:R * k + (precoeff x s).
  Proof. by rewrite /precoeff big_cons /=; case: eqP; rewrite !simpm. Qed.

  Lemma precoeff_cat x s1 s2:
    precoeff x (s1 ++ s2) = (precoeff x s1) + (precoeff x s2).
  Proof. by rewrite !precoeffE prelift_cat. Qed.

  Lemma precoeff_opp x s: precoeff x (prefreeg_opp s) = -(precoeff x s).
  Proof. by rewrite !precoeffE prelift_opp. Qed.

  Lemma precoeff_perm_eq x s1 s2:
    perm_eq s1 s2 -> precoeff x s1 = precoeff x s2.
  Proof. by rewrite !precoeffE; move/prelift_perm_eq=> ->. Qed.

  Lemma precoeff_repr x rD:
    precoeff x (repr (\pi_{freeg K / R} rD)) = precoeff x rD.
  Proof. by rewrite !precoeffE prelift_repr. Qed.

  Lemma precoeff_reduce x s: precoeff x (reduce s) = precoeff x s.
  Proof. by rewrite !precoeffE prelift_reduce. Qed.

  Lemma precoeff_outdom x s: x \notin predom s -> precoeff x s = 0.
  Proof.
    move=> x_notin_s; rewrite /precoeff big_seq_cond big_pred0 //.
    case=> k z /=; have [->|/negbTE ->] := eqVneq z x; last first.
      by rewrite andbF.
    rewrite eqxx andbT; apply/negP=> /(map_f (@snd _ _)).
    by rewrite (negbTE x_notin_s).
  Qed.

  Lemma reduced_mem s k x: reduced s ->
    ((k, x) \in s) = (precoeff x s == k) && (k != 0).
  Proof.
    elim: s => [|[k' x'] s ih] /=.
      by rewrite in_nil precoeff_nil eq_sym andbN.
    rewrite reduced_cons => /and3P [/= nz_k' x'Ns rs].
    rewrite in_cons precoeff_cons ih //.
    move: x'Ns; have [->|nz_x'x] := eqVneq x' x.
      move=> xNs; rewrite eqE /= eqxx andbT mul1r.
      rewrite precoeff_outdom // addr0 [0 == _]eq_sym.
      by rewrite andbN orbF [k == _]eq_sym andb_idr // => /eqP <-.
    rewrite eqE /= [x == _]eq_sym (negbTE nz_x'x) andbF.
    by rewrite mul0r add0r.
  Qed.

  Lemma coeff_Freeg x s: coeff x [freeg s] = precoeff x s.
  Proof. by rewrite /coeff fglift_Freeg precoeffE. Qed.

  Lemma freegequivP s1 s2 (hs1 : reduced s1) (hs2 : reduced s2):
    reflect
      (precoeff^~ s1 =1 precoeff^~ s2)
      (fgequiv (mkPrefreeg s1 hs1) (mkPrefreeg s2 hs2)).
  Proof.
    apply: (iffP idP); rewrite /fgequiv /=.
    + by move=> H k; apply: precoeff_perm_eq.
    move=> H; apply uniq_perm_eq.
    + by move/reduced_uniq: hs1=> /map_uniq.
    + by move/reduced_uniq: hs2=> /map_uniq.
    move=> [z k]; have [->|nz_z] := eqVneq z 0.
      by rewrite !reduced_mem // eqxx !andbF.
    by rewrite !reduced_mem // nz_z !andbT H.
  Qed.

  Lemma fgequivP rD1 rD2:
    reflect
      (precoeff^~ rD1 =1 precoeff^~ rD2)
      (fgequiv rD1 rD2).
  Proof. by case: rD1 rD2 => [s1 HD1] [s2 HD2]; apply/freegequivP. Qed.

  Lemma freeg_eqP D1 D2:
    reflect (coeff^~ D1 =1 coeff^~ D2) (D1 == D2).
  Proof.
    apply: (iffP idP); first by move/eqP=> ->.
    elim/quotW: D1 => D1; elim/quotW: D2 => D2.
    move=> eqc; rewrite eqmodE; apply/fgequivP=> k.
    by move: (eqc k); rewrite /coeff !piE /lift !precoeffE.
  Qed.

  Lemma perm_eq_Freeg s1 s2:
    perm_eq s1 s2 -> [freeg s1] = [freeg s2].
  Proof.
    move=> peq; apply/eqP/freeg_eqP=> k.
    by rewrite !coeff_Freeg; apply precoeff_perm_eq.
  Qed.

  Lemma freeg_repr D: [freeg (repr D)] = D.
  Proof.
    apply/eqP/freeg_eqP=> k.
    by rewrite coeff_Freeg precoeffE /coeff; unlock fglift.
  Qed.

  Lemma Freeg_dom D:
    [freeg [seq (coeff z D, z) | z <- dom D]] = D.
  Proof.
    apply/esym/eqP/freeg_eqP=> k.
    rewrite -{1 2}[D]freeg_repr !coeff_Freeg /dom.
    case: (repr D)=> {D} D rD /=; rewrite -map_comp map_id_in //.
    move=> [z x]; rewrite reduced_mem // => /andP [/eqP <- _].
    by rewrite /= coeff_Freeg.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma precoeff_uniqE s x:
      uniq (predom s) ->
        precoeff x s = [seq x.1 | x <- s]`_(index x (predom s)).
  Proof.
    elim: s => [|[z y s ih]].
      by rewrite precoeff_nil nth_nil.
    rewrite precoeff_cons /= => /andP [x_notin_s /ih ->].
    have [eq_yx|ne_yx] := altP (y =P x); last by rewrite mul0r add0r.
    rewrite mul1r /= nth_default ?addr0 //.
    move: (index_size x (predom s)); rewrite leq_eqVlt.
    rewrite index_mem -eq_yx (negbTE x_notin_s) orbF.
    by move=> /eqP ->; rewrite !size_map.
  Qed.

  Lemma precoeff_mem_uniqE s kz:
     uniq (predom s) -> kz \in s -> precoeff kz.2 s = kz.1.
  Proof.
    move=> uniq_dom_s kz_in_s; have uniq_s: (uniq s).
      by move/map_uniq: uniq_dom_s.
    rewrite precoeff_uniqE // (nth_map kz); last first.
      by rewrite -(size_map (@snd _ _)) index_mem map_f.
    rewrite nth_index_map // => {kz kz_in_s} kz1 kz2.
    move=> kz1_in_s kz2_in_s eq; apply/eqP; case: eqP=> //.
    move/eqP;
      rewrite -[kz1](nth_index kz1 (s := s)) //;
      rewrite -[kz2](nth_index kz1 (s := s)) //.
    rewrite nth_uniq ?index_mem //.
    set i1 := index _ _; set i2 := index _ _ => ne_i.
    have := ne_i; rewrite -(nth_uniq kz1.2 (s := predom s)) //;
      try by rewrite size_map index_mem.
    by rewrite !(nth_map kz1) ?index_mem // !nth_index // eq eqxx.
  Qed.

  Lemma mem_dom D : dom D =i [pred x | coeff x D != 0].
  Proof.
    elim/quotW: D; case=> D rD; rewrite /dom => z; rewrite !inE.
    rewrite (perm_eq_mem (perm_eq_map _ (perm_eq_fgrepr _))) /=.
    unlock coeff; rewrite !piE /lift /= -precoeffE.
    rewrite precoeff_uniqE -/(predom _); last by case/andP: rD.
    case/andP: rD=> _ /allP rD; apply/esym.
    case z_in_D: (_ \in _); last first.
      rewrite nth_default ?eqxx // size_map -(size_map (@snd _ _)).
      by rewrite leqNgt index_mem z_in_D.
    rewrite (nth_map (0, z)); last first.
      by rewrite -(size_map (@snd _ _)) index_mem z_in_D.
    set x := nth _ _ _; rewrite (negbTE (rD x _)) //.
    by rewrite /x mem_nth // -(size_map (@snd _ _)) index_mem z_in_D.
  Qed.

  Lemma coeff_outdom D x:
    x \notin dom D -> coeff x D = 0.
  Proof. by rewrite mem_dom inE negbK => /eqP ->. Qed.
End FreegTheory.

Notation "[ 'freeg' S ]" := (Freeg S).

Notation "<< z *g p >>" := [freeg [:: (z, p)]].
Notation "<< p >>"      := [freeg [:: (1, p)]].

(* -------------------------------------------------------------------- *)
Module FreegZmodType.
  Section Defs.
    Variable R : ringType.
    Variable K : choiceType.

    Implicit Types rD  : prefreeg R K.
    Implicit Types D   : {freeg K / R}.
    Implicit Types s   : seq (R * K).
    Implicit Types z k : R.
    Implicit Types x y : K.

    Local Notation zero := [freeg [::]].

    Lemma reprfg0: repr zero = Prefreeg [::] :> (prefreeg R K).
    Proof.
      rewrite !piE; apply/eqP; rewrite eqE /=; apply/eqP.
      by apply: perm_eq_small => //=; apply: perm_eq_fgrepr.
    Qed.

    Definition fgadd_r rD1 rD2 := Prefreeg (rD1 ++ rD2).

    Definition fgadd := lift_op2 {freeg K / R} fgadd_r.

    Lemma pi_fgadd: {morph \pi : D1 D2 / fgadd_r D1 D2 >-> fgadd D1 D2}.
    Proof.
      case=> [D1 redD1] [D2 redD2]; unlock fgadd; rewrite !piE.
      apply/eqmodP=> /=; apply/freegequivP=> k /=.
      by rewrite !precoeff_reduce !precoeff_cat !precoeff_repr.
    Qed.

    Canonical pi_fgadd_morph := PiMorph2 pi_fgadd.

    Definition fgopp_r rD := Prefreeg (prefreeg_opp rD).

    Definition fgopp := lift_op1 {freeg K / R} fgopp_r.

    Lemma pi_fgopp: {morph \pi : D / fgopp_r D >-> fgopp D}.
    Proof.
      case=> [D redD]; unlock fgopp; rewrite !piE.
      apply/eqmodP=> /=; apply/freegequivP=> k /=.
      by rewrite !precoeff_reduce !precoeff_opp !precoeff_repr.
    Qed.

    Canonical pi_fgopp_morph := PiMorph1 pi_fgopp.

    Lemma addmA: associative fgadd.
    Proof.
      elim/quotW=> [D1]; elim/quotW=> [D2]; elim/quotW=> [D3].
      unlock fgadd; rewrite !piE /fgadd_r /=.
      apply/eqmodP; apply/freegequivP=> k /=.
      by rewrite !(precoeff_reduce, precoeff_cat, precoeff_repr) addrA.
    Qed.

    Lemma addmC: commutative fgadd.
    Proof.
      elim/quotW=> [D1]; elim/quotW=> [D2].
      unlock fgadd; rewrite !piE /fgadd_r /=.
      apply/eqmodP; apply/freegequivP=> k /=.
      by rewrite !(precoeff_reduce, precoeff_cat, precoeff_repr) addrC.
    Qed.

    Lemma addm0: left_id zero fgadd.
    Proof.
      elim/quotW=> [[D redD]]; unlock fgadd; rewrite !(reprfg0, piE).
      rewrite /fgadd_r /=; apply/eqmodP=> /=; apply/freegequivP=> /= k.
      by rewrite precoeff_reduce precoeff_repr.
    Qed.

    Lemma addmN: left_inverse zero fgopp fgadd.
    Proof.
      elim/quotW=> [[D redD]]; unlock fgadd fgopp; rewrite !(reprfg0, piE).
      rewrite /fgadd_r /fgopp_r; apply/eqmodP=> /=; apply/freegequivP=> /= k.
      set rw := (precoeff_reduce, precoeff_repr,
                 precoeff_cat   , precoeff_opp ,
                 precoeff_repr  , precoeff_nil ).
      by rewrite !rw /= addrC subrr.
    Qed.

    Definition freeg_zmodMixin := ZmodMixin addmA addmC addm0 addmN.
    Canonical  freeg_zmodType  := ZmodType {freeg K / R} freeg_zmodMixin.
  End Defs.

  Module Exports.
    Canonical pi_fgadd_morph.
    Canonical pi_fgopp_morph.
    Canonical freeg_zmodType.
  End Exports.
End FreegZmodType.

Import FreegZmodType.
Export FreegZmodType.Exports.

(* -------------------------------------------------------------------- *)
Section FreegZmodTypeTheory.
  Variable R : ringType.
  Variable K : choiceType.

  Implicit Types x y z : K.
  Implicit Types k : R.

  Implicit Types D: {freeg K / R}.

  Local Notation coeff := (@coeff R K).

  (* -------------------------------------------------------------------- *)
  Section Lift.
    Variable M : lmodType R.
    Variable f : K -> M.

    Lemma lift_is_additive: additive (fglift f).
    Proof.
      elim/quotW=> [[D1 /= H1]]; elim/quotW=> [[D2 /= H2]].
      unlock fglift; rewrite !piE [_ + _]piE /lift /=.
      rewrite !prelift_repr /fgadd_r /fgopp_r /=.
      by rewrite !(prelift_reduce, prelift_cat, prelift_opp).
    Qed.
  End Lift.

  (* -------------------------------------------------------------------- *)
  Lemma coeff_is_additive x: additive (coeff x).
  Proof. by apply (@lift_is_additive [regular of R]). Qed.

  Canonical coeff_additive x := Additive (coeff_is_additive x).

  Lemma coeff0   z   : coeff z 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma coeffN   z   : {morph coeff z: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma coeffD   z   : {morph coeff z: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma coeffB   z   : {morph coeff z: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma coeffMn  z n : {morph coeff z: x / x *+ n} . Proof. exact: raddfMn. Qed.
  Lemma coeffMNn z n : {morph coeff z: x / x *- n} . Proof. exact: raddfMNn. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma dom0: dom (0 : {freeg K / R}) = [::] :> seq K.
  Proof.
    apply: perm_eq_small=> //; apply: uniq_perm_eq=> //.
      by apply: uniq_dom.
    by move=> z; rewrite mem_dom !(inE, in_nil) coeff0 eqxx.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma dom_eq0 (D : {freeg K / R}): (dom D == [::]) = (D == 0).
  Proof.
    apply/eqP/eqP; last by move=> ->; rewrite dom0.
    move=> z_domD; apply/eqP/freeg_eqP=> z; rewrite coeff0 coeff_outdom //.
    by rewrite z_domD in_nil.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domU (c : R) (x : K): c != 0 -> dom << c *g x >> = [:: x].
  Proof.
    move=> nz_c; apply: perm_eq_small=> //; apply: uniq_perm_eq=> //.
      by apply: uniq_dom.
    move=> y; rewrite mem_dom !(inE, in_nil) coeffU [x == _]eq_sym.
    by case: (y =P x) => _ /=; rewrite ?(mulr0, mulr1, eqxx).
  Qed.

  (* -------------------------------------------------------------------*)
  Lemma domU1 z: dom (<< z >> : {freeg K / R}) = [:: z].
  Proof. by rewrite domU ?oner_eq0. Qed.

  (* -------------------------------------------------------------------*)
  Lemma domN D: dom (-D) =i dom D.
  Proof. by move=> z; rewrite !mem_dom !inE coeffN oppr_eq0. Qed.

  Lemma domN_perm_eq D: perm_eq (dom (-D)) (dom D).
  Proof. by apply: uniq_perm_eq; rewrite ?uniq_dom //; apply: domN. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domD_perm_eq D1 D2:
       [predI (dom D1) & (dom D2)] =1 pred0
    -> perm_eq (dom (D1 + D2)) (dom D1 ++ dom D2).
  Proof.
    move=> D12_nI; have inD1E p: p \in dom D1 -> p \notin dom D2.
      move=> p_in_D1; move/(_ p): D12_nI; rewrite !inE p_in_D1.
      by rewrite andTb => /= ->.
    have inD2E p: p \in dom D2 -> p \notin dom D1.
      move=> p_in_D2; move/(_ p): D12_nI; rewrite !inE p_in_D2.
      by rewrite andbT => /= ->.
    apply: uniq_perm_eq; rewrite ?uniq_dom //.
      rewrite cat_uniq ?uniq_dom //= andbT; apply/hasP.
      case=> p p_in_D2; move/(_ p): D12_nI => /=.
      by rewrite p_in_D2 andbT=> ->.
    move=> p; rewrite mem_cat !mem_dom !inE coeffD.
    move/(_ p): D12_nI; rewrite /= !mem_dom !inE.
    case nz_D1p: (_ != 0) => /=.
      by move/negbT; rewrite negbK=> /eqP->; rewrite addr0.
    move=> _; move/negbT: nz_D1p; rewrite negbK.
    by move/eqP->; rewrite add0r.
  Qed.

  Lemma domD D1 D2 x:
       [predI (dom D1) & (dom D2)] =1 pred0
    -> (x \in dom (D1 + D2)) = (x \in dom D1) || (x \in dom D2).
  Proof. by move/domD_perm_eq/perm_eq_mem/(_ x); rewrite mem_cat. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domD_subset D1 D2:
    {subset dom (D1 + D2) <= (dom D1) ++ (dom D2)}.
  Proof.
    move=> z; rewrite mem_cat !mem_dom !inE coeffD.
    have nz_sum (x1 x2 : R): x1 + x2 != 0 -> (x1 != 0) || (x2 != 0).
      by have [->|->] := eqVneq x1 0; first by rewrite add0r eqxx.
    by move/nz_sum; case/orP=> ->; rewrite ?orbT.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma dom_sum_subset (I : Type) (r : seq I) (F : I -> {freeg K / R}) (P : pred I):
    {subset dom (\sum_(i <- r | P i) F i) <= flatten [seq dom (F i) | i <- r & P i]}.
  Proof.
    move=> p; elim: r => [|r rs IH]; first by rewrite big_nil dom0.
    rewrite big_cons; case Pr: (P r); last by move/IH=> /=; rewrite Pr.
    move/domD_subset; rewrite mem_cat; case/orP=> /=; rewrite Pr.
    + by rewrite map_cons /= mem_cat=> ->.
    + by move/IH; rewrite map_cons /= mem_cat=> ->; rewrite orbT.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domB D1 D2:
    {subset dom (D1 - D2) <= (dom D1) ++ (dom D2)}.
  Proof. by move=> z; move/domD_subset; rewrite !mem_cat domN. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma freegUD k1 k2 x:
    << k1 *g x >> + << k2 *g x >> = << (k1 + k2) *g x >>.
  Proof. by apply/eqP/freeg_eqP=> z; rewrite coeffD !coeffU -mulrDl. Qed.

  Lemma freegUN k x: - << k *g x >> = << -k *g x >>.
  Proof.
    by apply/eqP/freeg_eqP=> z; rewrite coeffN !coeffU mulNr.
  Qed.

  Lemma freegUB k1 k2 x:
    << k1 *g x >> - << k2 *g x >> = << (k1-k2) *g x >>.
  Proof. by rewrite freegUN freegUD. Qed.

  Lemma freegU0 x: << 0 *g x >> = 0 :> {freeg K / R}.
  Proof. by apply/eqP/freeg_eqP=> y; rewrite coeffU coeff0 mul0r. Qed.

  Lemma freegU_eq0 k x: (<< k *g x >> == 0) = (k == 0).
  Proof.
    apply/eqP/eqP; last by move=> ->; rewrite freegU0.
    by move/(congr1 (coeff x)); rewrite coeff0 coeffU eqxx mulr1.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma freeg_muln k n (S : K):
    << k *g S >> *+ n = << (k *+ n) *g S >>.
  Proof.
    elim: n => [|n ih].
    + by rewrite !mulr0n freegU0.
    + by rewrite !mulrS ih freegUD.
  Qed.

  Lemma freegU_muln n (S : K):
    << S >> *+ n = << n%:R *g S >> :> {freeg K / R}.
  Proof. by rewrite freeg_muln. Qed.

  Lemma freeg_mulz k (m : int) (S : K):
    << k *g S >> *~ m = << k *~ m *g S >>.
  Proof.
    case: m=> [n|n].
    + by rewrite -pmulrn freeg_muln.
    + by rewrite NegzE -nmulrn freeg_muln mulrNz freegUN.
  Qed.

  Lemma freegU_mulz (m : int) (S : K):
    << S >> *~ m = << m%:~R *g S >> :> {freeg K / R}.
  Proof. by rewrite freeg_mulz. Qed.

  (* -------------------------------------------------------------------- *)
  Lemma freeg_nil: [freeg [::]] = 0 :> {freeg K / R}.
  Proof. by apply/eqP/freeg_eqP. Qed.

  Lemma freeg_cat (s1 s2 : seq (R * K)):
    [freeg s1 ++ s2] = [freeg s1] + [freeg s2].
  Proof.
    apply/eqP/freeg_eqP => k; rewrite coeffD.
    by rewrite !coeff_Freeg precoeff_cat.
  Qed.

  (* -------------------------------------------------------------------- *)
  Definition fgenum D : seq (R * K) := repr D.

  Lemma Freeg_enum D: Freeg (fgenum D) = D.
  Proof.
    elim/quotW: D; case=> D rD /=; unlock Freeg; rewrite /Prefreeg.
    apply/eqmodP=> /=; rewrite /fgequiv /fgenum /=.
    apply: (perm_eq_trans (reduceK _)); last by apply: perm_eq_fgrepr.
    by apply: prefreeg_reduced.
  Qed.

  Lemma perm_eq_fgenum (s : seq (R * K)) (rD : reduced s):
    perm_eq (fgenum (\pi_{freeg K / R} (mkPrefreeg s rD))) s.
  Proof. by rewrite /fgenum; apply: perm_eq_fgrepr. Qed.

  (* -------------------------------------------------------------------- *)
  Lemma freeg_sumE D:
    \sum_(z <- dom D) << (coeff z D) *g z >> = D.
  Proof.
    apply/eqP/freeg_eqP=> x /=; rewrite raddf_sum /=.
    case x_in_dom: (x \in dom D); last rewrite coeff_outdom ?x_in_dom //.
    + rewrite (bigD1_seq x) ?uniq_dom //= big1 ?addr0.
      * by rewrite coeffU eqxx mulr1.
      * by move=> z ne_z_x; rewrite coeffU (negbTE ne_z_x) mulr0.
    + rewrite big_seq big1 // => z z_notin_dom; rewrite coeffU.
      have ->: (z == x)%:R = 0 :> R; last by rewrite mulr0.
      by case: (z =P x)=> //= eq_zx; rewrite eq_zx x_in_dom in z_notin_dom.
  Qed.
End FreegZmodTypeTheory.

(* -------------------------------------------------------------------- *)
Section FreeglModType.
  Variable R : ringType.
  Variable K : choiceType.

  Implicit Types x y z : K.
  Implicit Types c k : R.

  Implicit Types D: {freeg K / R}.

  Local Notation coeff := (@coeff R K).

  Definition fgscale c D :=
    \sum_(x <- dom D) << c * (coeff x D) *g x >>.

  Local Notation "c *:F D" := (fgscale c D)
    (at level 40, left associativity).

  Lemma coeff_fgscale c D x:
    coeff x (c *:F D) = c * (coeff x D).
  Proof.
    rewrite -{2}[D]freeg_sumE /fgscale !raddf_sum /=.
    by rewrite mulr_sumr; apply/eq_bigr=> i _; rewrite !coeffU mulrA.
  Qed.

  Lemma fgscaleA c1 c2 D:
    c1 *:F (c2 *:F D) = (c1 * c2) *:F D.
  Proof. by apply/eqP/freeg_eqP=> x; rewrite !coeff_fgscale mulrA. Qed.

  Lemma fgscale1r D: 1 *:F D = D.
  Proof. by apply/eqP/freeg_eqP=> x; rewrite !coeff_fgscale mul1r. Qed.

  Lemma fgscaleDr c D1 D2:
    c *:F (D1 + D2) = c *:F D1 + c *:F D2.
  Proof.
    by apply/eqP/freeg_eqP=> x; rewrite !(coeffD, coeff_fgscale) mulrDr.
  Qed.

  Lemma fgscaleDl D c1 c2:
    (c1 + c2) *:F D = c1 *:F D + c2 *:F D.
  Proof.
    by apply/eqP/freeg_eqP=> x; rewrite !(coeffD, coeff_fgscale) mulrDl.
  Qed.

  Definition freeg_lmodMixin :=
    LmodMixin fgscaleA fgscale1r fgscaleDr fgscaleDl.
  Canonical freeg_lmodType :=
    Eval hnf in LmodType R {freeg K / R} freeg_lmodMixin.
End FreeglModType.
  
(* -------------------------------------------------------------------- *)
Section FreeglModTheory.
  Variable R : ringType.
  Variable K : choiceType.

  Implicit Types x y z : K.
  Implicit Types c k : R.

  Implicit Types D: {freeg K / R}.

  Local Notation coeff := (@coeff R K).

  Lemma coeffZ c D x: coeff x (c *: D) = c * (coeff x D).
  Proof. by rewrite coeff_fgscale. Qed.

  Lemma domZ_subset c D: {subset dom (c *: D) <= dom D}.
  Proof.
    move=> x; rewrite !mem_dom !inE coeffZ.
    by case: (coeff _ _ =P 0)=> // ->; rewrite mulr0 eqxx.
  Qed.
End FreeglModTheory.

(* -------------------------------------------------------------------- *)
Section FreeglModTheoryId.
  Variable R : idomainType.
  Variable K : choiceType.

  Implicit Types x y z : K.
  Implicit Types c k : R.

  Implicit Types D: {freeg K / R}.

  Local Notation coeff := (@coeff R K).

  Lemma domZ c D: c != 0 -> dom (c *: D) =i dom D.
  Proof.
    move=> nz_c x; rewrite !mem_dom !inE coeffZ.
    by rewrite mulf_eq0 negb_or nz_c.
  Qed.
End FreeglModTheoryId.

(* -------------------------------------------------------------------- *)
Section Deg.
  Variable K : choiceType.

  (* -------------------------------------------------------------------- *)
  Definition deg (D : {freeg K / int}) : int :=
    fglift (fun _ => (1%:Z : int^o)) D.

  Lemma degU k z: deg << k *g z >> = k.
  Proof. by rewrite /deg liftU /GRing.scale /= mulr1. Qed.

  Definition predeg (D : seq (int * K)) :=
    \sum_(kx <- D) kx.1.

  Lemma deg_is_additive: additive deg.
  Proof. by apply: (@lift_is_additive _ K [regular of int_Ring]). Qed.

  Canonical deg_additive := Additive deg_is_additive.

  Lemma deg0     : deg 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma degN     : {morph deg: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma degD     : {morph deg: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma degB     : {morph deg: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma degMn  n : {morph deg: x / x *+ n} . Proof. exact: raddfMn. Qed.
  Lemma degMNn n : {morph deg: x / x *- n} . Proof. exact: raddfMNn. Qed.

  Lemma predegE: predeg =1 prelift (fun _ => (1%:Z : int^o)).
  Proof.
    move=> D; rewrite /predeg /prelift; apply: eq_bigr.
    by move=> i _; rewrite /GRing.scale /= mulr1.
  Qed.

  Lemma predeg_nil: predeg [::] = 0.
  Proof. by rewrite /predeg big_nil. Qed.

  Lemma predeg_cons D k x:
    predeg ((k, x) :: D) = k + (predeg D).
  Proof. by rewrite /predeg big_cons. Qed.

  Lemma predeg_cat D1 D2:
    predeg (D1 ++ D2) = (predeg D1) + (predeg D2).
  Proof. by rewrite !predegE prelift_cat. Qed.

  Lemma predeg_opp D: predeg (prefreeg_opp D) = -(predeg D).
  Proof. by rewrite !predegE prelift_opp. Qed.

  Lemma predeg_perm_eq D1 D2: perm_eq D1 D2 -> predeg D1 = predeg D2.
  Proof. by rewrite !predegE => /prelift_perm_eq ->. Qed.

  Lemma predeg_repr D: predeg (repr (\pi_{freeg K / int} D)) = predeg D.
  Proof. by rewrite !predegE prelift_repr. Qed.

  Lemma predeg_reduce D: predeg (reduce D) = predeg D.
  Proof. by rewrite !predegE prelift_reduce. Qed.
End Deg.

(* -------------------------------------------------------------------- *)
Reserved Notation "D1 <=g D2" (at level 50, no associativity).

Section FreegCmp.
  Variable G : numDomainType.
  Variable K : choiceType.

  Definition fgle (D1 D2 : {freeg K / G}) :=
    all [pred z | coeff z D1 <= coeff z D2] (dom D1 ++ dom D2).

  Local Notation "D1 <=g D2" := (fgle D1 D2).

  Lemma fgleP D1 D2:
    reflect (forall z, coeff z D1 <= coeff z D2) (D1 <=g D2).
  Proof.
    apply: (iffP allP); last by move=> H z _; apply: H.
    move=> lec z; case z_in_dom: (z \in (dom D1 ++ dom D2)).
      by apply: lec.
    move: z_in_dom; rewrite mem_cat; case/norP=> zD1 zD2.
    by rewrite !coeff_outdom // lerr.
  Qed.

  Lemma fgposP D:
    reflect (forall z, 0 <= coeff z D) (0 <=g D).
  Proof.
    apply: (iffP idP).
    + by move=> posD z; move/fgleP/(_ z): posD; rewrite coeff0.
    + by move=> posD; apply/fgleP=> z; rewrite coeff0.
  Qed.

  Lemma fgledd D: D <=g D.
  Proof. by apply/fgleP=> z; rewrite lerr. Qed.

  Lemma fgle_trans: transitive fgle.
  Proof.
    move=> D2 D1 D3 le12 le23; apply/fgleP=> z.
    by rewrite (ler_trans (y := coeff z D2)) //; apply/fgleP.
  Qed.
End FreegCmp.

Local Notation "D1 <=g D2" := (fgle D1 D2).

(* -------------------------------------------------------------------- *)
Section FreegCmpDom.
  Variable K : choiceType.

  Lemma dompDl (D1 D2 : {freeg K}):
    0 <=g D1 -> 0 <=g D2 -> dom (D1 + D2) =i (dom D1) ++ (dom D2).
  Proof.
    move=> pos_D1 pos_D2 z; rewrite mem_cat !mem_dom !inE coeffD.
    by rewrite paddr_eq0; first 1 [rewrite negb_and] || apply/fgposP.
  Qed.
End FreegCmpDom.

(* -------------------------------------------------------------------- *)
Section FreegMap.
  Variable G : ringType.
  Variable K : choiceType.
  Variable P : pred K.
  Variable f : G -> G.

  Implicit Types D : {freeg K / G}.

  Definition fgmap D :=
    \sum_(z <- dom D | P z) << f (coeff z D) *g z >>.

  Lemma fgmap_coeffE (D : {freeg K / G}) z:
    z \in dom D -> coeff z (fgmap D) = (f (coeff z D)) *+ (P z).
  Proof.
    move=> zD; rewrite /fgmap raddf_sum /= -big_filter; case Pz: (P z).
    + rewrite (bigD1_seq z) ?(filter_uniq, uniq_dom) //=; last first.
        by rewrite mem_filter Pz.
      rewrite coeffU eqxx mulr1 big1 ?addr0 //.
      by move=> z' ne_z'z; rewrite coeffU (negbTE ne_z'z) mulr0.
    + rewrite big_seq big1 ?mulr0 //.
      move=> z' z'PD; rewrite coeffU; have/negbTE->: z' != z.
        apply/eqP=> /(congr1 (fun x => x \in filter P (dom D))).
        by rewrite z'PD mem_filter Pz.
      by rewrite mulr0.
  Qed.

  Lemma fgmap_dom D: {subset dom (fgmap D) <= filter P (dom D)}.
  Proof.
    move=> z; rewrite mem_dom inE mem_filter andbC.
    case zD: (z \in (dom D)) => /=.
    + rewrite fgmap_coeffE //; case: (P _)=> //=.
      by rewrite mulr0n eqxx.
    + rewrite /fgmap raddf_sum /= big_seq_cond big1 ?eqxx //.
      move=> z' /andP [z'D _]; rewrite coeffU.
      have/negbTE->: z' != z; last by rewrite mulr0.
      apply/eqP=> /(congr1 (fun x => x \in dom D)).
      by rewrite  zD z'D.
  Qed.

  Lemma fgmap_f0_coeffE (D : {freeg K / G}) z:
    f 0 = 0 -> coeff z (fgmap D) = (f (coeff z D)) *+ (P z).
  Proof.
    move=> z_f0; case zD: (z \in dom D).
      by rewrite fgmap_coeffE.
    rewrite !coeff_outdom ?z_f0 ?zD ?mul0rn //.
    by apply/negP=> /fgmap_dom; rewrite mem_filter zD andbF.
  Qed.
End FreegMap.

(* -------------------------------------------------------------------- *)
Section FreegNorm.
  Variable G : numDomainType.
  Variable K : choiceType.

  Implicit Types D : {freeg K / G}.

  Definition fgnorm D: {freeg K / G} :=
    fgmap xpredT Num.norm D.

  Lemma fgnormE D: fgnorm D = \sum_(z <- dom D) << `|coeff z D| *g z >>.
  Proof. by []. Qed.

  Lemma coeff_fgnormE D z: coeff z (fgnorm D) = `|coeff z D|.
  Proof. by rewrite fgmap_f0_coeffE ?mulr1n // normr0. Qed.
End FreegNorm.

(* -------------------------------------------------------------------- *)
Section FreegPosDecomp.
  Variable G : realDomainType.
  Variable K : choiceType.

  Implicit Types D : {freeg K / G}.

  Definition fgpos D: {freeg K / G} :=
    fgmap [pred z | coeff z D >= 0] Num.norm D.

  Definition fgneg D: {freeg K / G} :=
    fgmap [pred z | coeff z D <= 0] Num.norm D.

  Lemma fgposE D:
    fgpos D = \sum_(z <- dom D | coeff z D >= 0) << `|coeff z D| *g z >>.
  Proof. by []. Qed.

  Lemma fgnegE D:
    fgneg D = \sum_(z <- dom D | coeff z D <= 0) << `|coeff z D| *g z >>.
  Proof. by []. Qed.

  Lemma fgposN D: fgpos (-D) = fgneg D.
  Proof.
    apply/eqP/freeg_eqP=> z; rewrite !fgmap_f0_coeffE ?normr0 //.
    by rewrite inE /= !coeffN oppr_ge0 normrN.
  Qed.

  Lemma fgpos_le0 D: 0 <=g fgpos D.
  Proof.
    apply/fgleP=> z; rewrite coeff0 fgmap_f0_coeffE ?normr0 //.
    by rewrite mulrn_wge0.
  Qed.

  Lemma fgneg_le0 D: 0 <=g fgneg D.
  Proof. by rewrite -fgposN fgpos_le0. Qed.

  Lemma coeff_fgposE D k: coeff k (fgpos D) = Num.max 0 (coeff k D).
  Proof.
    rewrite fgmap_f0_coeffE ?normr0 //inE; rewrite /Num.max.
    rewrite lerNgt ler_eqVlt; case: eqP=> [->//|_] /=.
      by rewrite normr0 mul0rn.
    case: ltrP; rewrite ?(mulr0, mulr1) // => pos_zD.
    by rewrite ger0_norm.
  Qed.

  Lemma coeff_fgnegE D k: coeff k (fgneg D) = - (Num.min 0 (coeff k D)).
  Proof.
    by rewrite -fgposN coeff_fgposE coeffN -{1}[0]oppr0 -oppr_min.
  Qed.

  Lemma fgpos_dom D: {subset dom (fgpos D) <= dom D}.
  Proof.
    by move=> x /fgmap_dom; rewrite mem_filter => /andP [_].
  Qed.

  Lemma fgneg_dom D: {subset dom (fgneg D) <= dom D}.
  Proof.
    by move=> k; rewrite -fgposN => /fgpos_dom; rewrite domN.
  Qed.

  Lemma fg_decomp D: D = (fgpos D) - (fgneg D).
  Proof.
    apply/eqP/freeg_eqP=> k; rewrite coeffB.
    by rewrite coeff_fgposE coeff_fgnegE opprK addr_max_min add0r.
  Qed.

  Lemma fgnorm_decomp D: fgnorm D = (fgpos D) + (fgneg D).
  Proof.
    apply/eqP/freeg_eqP=> k; rewrite coeffD coeff_fgnormE.
    rewrite coeff_fgposE coeff_fgnegE /Num.max /Num.min.
    rewrite lerNgt ler_eqVlt; case: (0 =P _)=> [<-//|_] /=.
      by rewrite ltrr subr0 normr0.
    case: ltrP=> /=; rewrite ?(subr0, sub0r) => lt.
    + by rewrite gtr0_norm.
    + by rewrite ler0_norm.
  Qed.
End FreegPosDecomp.

(* -------------------------------------------------------------------- *)
Section PosFreegDeg.
  Variable K : choiceType.

  Lemma fgpos_eq0P (D : {freeg K}): 0 <=g D -> deg D = 0 -> D = 0.
  Proof.
    move=> posD; rewrite -{1}[D]freeg_sumE raddf_sum /=.
    rewrite (eq_bigr (fun z => coeff z D)); last first.
      by move=> i _; rewrite degU.
    move/eqP; rewrite psumr_eq0; last by move=> i _; apply/fgposP.
    move/allP=> zD; apply/eqP; apply/freeg_eqP=> z; rewrite coeff0.
    case z_in_D: (z \in dom D); last first.
      by rewrite coeff_outdom // z_in_D.
    by apply/eqP/zD.
  Qed.

  Lemma fgneg_eq0P (D : {freeg K}): D <=g 0 -> deg D = 0 -> D = 0.
  Proof.
    move=> negD deg_eq0; apply/eqP; rewrite -oppr_eq0; apply/eqP.
    apply/fgpos_eq0P; last by apply/eqP; rewrite degN oppr_eq0 deg_eq0.
    apply/fgposP=> z; rewrite coeffN oppr_ge0.
    by move/fgleP: negD => /(_ z); rewrite coeff0.
  Qed.

  Lemma deg1pos (D : {freeg K}):
    0 <=g D -> deg D = 1 -> exists x, D = << x >>.
  Proof.
    move=> D_ge0 degD_eq1; have: D != 0.
      by case: (D =P 0) degD_eq1 => [->|//]; rewrite deg0.
    rewrite -dom_eq0; case DE: (dom D) => [//|p ps] _.
    rewrite -[D]addr0 -(subrr <<p>>) addrA addrAC.
    have: coeff p D != 0.
      by move: (mem_dom D p); rewrite DE in_cons eqxx inE /=.
    rewrite neqr_lt ltrNge; have/fgposP/(_ p) := D_ge0 => ->/=.
    move=> coeffpD_gt0; have: 0 <=g (D - <<p>>).
      apply/fgposP=> q; rewrite coeffB coeffU mul1r.
      case: (p =P q) =>[<-/=|]; last first.
        by move=> _; rewrite subr0; apply/fgposP.
      by rewrite subr_ge0.
    move/fgpos_eq0P=> ->; first by rewrite add0r; exists p.
    by rewrite degB degU degD_eq1 subrr.
  Qed.

  Lemma deg1neg (D : {freeg K}):
    D <=g 0 -> deg D = -1 -> exists x, D = - << x >>.
  Proof.
    move=> D_le0 degD_eqN1; case: (@deg1pos (-D)).
    + apply/fgleP=> p; rewrite coeffN coeff0 oppr_ge0.
      by move/fgleP/(_ p): D_le0; rewrite coeff0.
    + by rewrite degN degD_eqN1 opprK.
    + by move=> p /eqP; rewrite eqr_oppLR => /eqP->; exists p.
  Qed.
End PosFreegDeg.

(* -------------------------------------------------------------------- *)
Section FreegIndDom.
  Variable R : ringType.
  Variable K : choiceType.

  Variable F : pred K.
  Variable P : {freeg K / R} -> Type.

  Implicit Types D : {freeg K / R}.

  Hypothesis H0:
    forall D, [predI dom D & [predC F]] =1 pred0 -> P D.

  Hypothesis HS:
    forall k x D, x \notin dom D -> k != 0 -> ~~ (F x) ->
      P D -> P (<< k *g x >> + D).

  Lemma freeg_rect_dom D: P D.
  Proof.
    rewrite -[D]freeg_sumE (bigID F) /=; set DR := \sum_(_ <- _ | _) _.
    have: [predI dom DR & [predC F]] =1 pred0.
      move=> p /=; rewrite !inE; apply/negP=> /andP [].
      rewrite /DR => /dom_sum_subset /flattenP.
      case=> [ps /mapP [q]]; rewrite mem_filter => /andP [].
      move=> Rq q_in_D ->; rewrite domU ?mem_seq1; last first.
        by move: (mem_dom D q); rewrite inE => <-.
      by move/eqP=> ->; move: Rq; rewrite /in_mem /= => ->.
    move: DR => DR domDR; rewrite addrC -big_filter.
    set ps := [seq _ <- _ | _]; move: (perm_eq_refl ps).
    rewrite {1}/ps; move: ps (D) => {D}; elim => [|p ps IH] D.
    + by move=> _; rewrite big_nil add0r; apply: H0.
    + move=> DE; move/(_ p): (perm_eq_mem DE); rewrite !inE eqxx /=.
      have /=: uniq (p :: ps).
        by move/perm_eq_uniq: DE; rewrite filter_uniq // uniq_dom.
      case/andP=> p_notin_ps uniq_ps; rewrite mem_filter=> /andP [NRp p_in_D].
      rewrite big_cons -addrA; apply HS => //; first 1 last.
      * by move: p_in_D; rewrite mem_dom.
      * pose D' := D - << coeff p D *g p >>.
        have coeffD' q: coeff q D' = coeff q D * (p != q)%:R.
          rewrite {}/D' coeffB coeffU; case: (p =P q).
          - by move=> ->; rewrite !(mulr1, mulr0) subrr.
          - by move/eqP=> ne_pq; rewrite !(mulr1, mulr0) subr0.
        have: perm_eq (dom D) (p :: dom D').
          apply: uniq_perm_eq; rewrite /= ?uniq_dom ?andbT //.
          - by rewrite mem_dom inE coeffD' eqxx mulr0 eqxx.
          move=> q; rewrite in_cons !mem_dom !inE coeffD' [q == _]eq_sym.
          case: (p =P q); rewrite !(mulr0, mulr1) //=.
          by move=> <-; move: p_in_D; rewrite mem_dom.
        move/perm_eq_filter=> /(_ [pred q | ~~ (F q)]) /=.
        rewrite NRp; rewrite perm_eq_sym; move/(perm_eq_trans)=> /(_ _ DE).
        rewrite perm_cons => domD'; rewrite big_seq.
        rewrite (eq_bigr (fun q => << coeff q D' *g q >>)); last first.
          move=> q q_in_ps; rewrite /D' coeffB coeffU; case: (p =P q).
          - by move=> eq_pq; move: p_notin_ps; rewrite eq_pq q_in_ps.
          - by move=> _; rewrite mulr0 subr0.
        by rewrite -big_seq; apply IH.
      * apply/negP=> /domD_subset; rewrite mem_cat; case/orP; last first.
          by move=> p_in_DR; move/(_ p): domDR; rewrite !inE NRp p_in_DR.
        move/dom_sum_subset; rewrite filter_predT => /flattenP [qs].
        move/mapP => [q q_in_ps ->]; rewrite domU; last first.
          move/perm_eq_mem/(_ q): DE; rewrite !inE q_in_ps orbT.
          by rewrite mem_filter => /andP [_]; rewrite mem_dom.
        rewrite mem_seq1 => /eqP pq_eq; move: p_notin_ps.
        by rewrite pq_eq q_in_ps.
  Qed.
End FreegIndDom.

Lemma freeg_ind_dom  (R : ringType) (K : choiceType) (F : pred K):
     forall (P : {freeg K / R} -> Prop),
     (forall D : {freeg K / R},
       [predI dom (G:=R) (K:=K) D & [predC F]] =1 pred0 -> P D)
  -> (forall (k : R) (x : K) (D : {freeg K / R}),
        x \notin dom (G:=R) (K:=K) D -> k != 0 -> ~~ F x ->
          P D -> P (<< k *g x >> + D))
  -> forall D : {freeg K / R}, P D.
Proof. by move=> P; apply/(@freeg_rect_dom R K F P). Qed.

(* -------------------------------------------------------------------- *)
Section FreegIndDom0.
  Variable R : ringType.
  Variable K : choiceType.
  Variable P : {freeg K / R} -> Type.

  Hypothesis H0: P 0.
  Hypothesis HS:
    forall k x D, x \notin dom D -> k != 0 ->
      P D -> P (<< k *g x >> + D).

  Lemma freeg_rect_dom0 D: P D.
  Proof.
    apply: (@freeg_rect_dom _ _ xpred0) => {D} [D|k x D].
    + move=> domD; have ->: D = 0; last exact: H0.
      case: (D =P 0) => [//|/eqP]; rewrite -dom_eq0.
      case: (dom D) domD => [//|p ps] /(_ p).
      by rewrite !inE eqxx andbT /= /in_mem.
    + by move=> ?? _ ?; apply: HS.
  Qed.
End FreegIndDom0.

Lemma freeg_ind_dom0 (R : ringType) (K : choiceType):
  forall (P : {freeg K / R} -> Prop),
       P 0
    -> (forall (k : R) (x : K) (D : {freeg K / R}),
          x \notin dom (G:=R) (K:=K) D -> k != 0 -> P D ->
            P (<< k *g x >> + D))
    -> forall D : {freeg K / R}, P D.
Proof. by move=> P; apply/(@freeg_rect_dom0 R K P). Qed.

(*
*** Local Variables: ***
*** coq-load-path: ("../ssreflect" ("../3rdparty" "SsrMultinomials") ("." "SsrMultinomials")) ***
*** End: ***
 *)
