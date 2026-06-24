From Corelib Require Import PosDef IntDef RatDef.
From Corelib Require Import micromega_witness micromega_checker.
From elpi Require Import derive param2.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype.
From mathcomp Require Import ssralg ssrint mpoly positive_nat Zint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.

Section Pol_mpoly.
Context {C : comNzRingType}.
Local Notation mpol n := {mpoly C[n]}.
Implicit Type P Q : Pol C.
Implicit Type c : C.
Implicit Type n : nat.

Fixpoint Pol_to_mpoly n P : option (mpol n) :=
  match P with
  | Pc c => Some c%:MP
  | Pinj j Q =>
      let j := Pos.to_nat j in
      if leqP j n isn't LeqNotGtn jlen then None
      else if Pol_to_mpoly (n - j) Q isn't Some q then None
      else Some (mpcast (subnKC jlen) (mrshift j q))
  | PX P i Q =>
      let i := Pos.to_nat i in
      if n isn't n'.+1 then None
      else if Pol_to_mpoly n'.+1 P isn't Some p then None
      else if Pol_to_mpoly n' Q isn't Some q then None
      else Some (p * 'X_ord0 ^+ i + mrshift 1 q)
  end.

Definition Pol_mpoly {n} P (p : mpol n) := Pol_to_mpoly n P == Some p.

Variant Pol_mpoly_spec {n} P (p : mpol n) : Pol C -> mpol n -> bool -> Type :=
  | Pol_mpoly_spec_false : Pol_mpoly_spec P p false
  | Pol_mpoly_spec_Pc :
      forall c, P = Pc c -> p = c%:MP -> Pol_mpoly_spec (Pc c) c%:MP true
  | Pol_mpoly_spec_Pinj :
      forall j nj mj Q q (eq_n : (nj + mj = n)%N),
        P = Pinj j Q -> p = mpcast eq_n (mrshift nj q) ->
        pos_nat j nj -> Pol_mpoly Q q ->
        Pol_mpoly_spec (Pinj j Q) (mpcast eq_n (mrshift nj q)) true
  | Pol_mpoly_spec_PX :
      forall P' p' i ni pn Q q (eq_n : (1 + pn = n)%N),
        P = PX P' i Q ->
        p = p' * mpcast eq_n 'X_ord0 ^+ ni + mpcast eq_n (mrshift 1 q) ->
        Pol_mpoly P' p' -> pos_nat i ni -> Pol_mpoly Q q ->
        Pol_mpoly_spec (PX P' i Q)
          (p' * mpcast eq_n 'X_ord0 ^+ ni + mpcast eq_n (mrshift 1 q)) true.

Lemma Pol_mpolyP n P (p : mpol n) : Pol_mpoly_spec P p P p (Pol_mpoly P p).
Proof.
case: (boolP (Pol_mpoly P p)) => [|/eqP Pp]; last exact: Pol_mpoly_spec_false.
elim: P n p => [c n p /eqP[<-]| j Q _ n p | P' _ i Q _]; rewrite /Pol_mpoly/=.
- exact: Pol_mpoly_spec_Pc.
- set nj := Pos.to_nat j.
  case: leqP => [njn |//].
  case Eq: Pol_to_mpoly => [|//] => /eqP[<-].
  by apply: Pol_mpoly_spec_Pinj => //; apply/eqP.
- case=> [//| n] p.
  case Ep': Pol_to_mpoly => [|//].
  case Eq: Pol_to_mpoly => [|//] => /eqP[<-].
  rewrite -['X_ord0](mpcast_id erefl) -[mrshift _ _](mpcast_id erefl).
  by apply: Pol_mpoly_spec_PX => //; apply/eqP.
Qed.

Lemma Pol_mpoly_ind (Pr : forall n, Pol C -> mpol n -> Prop) :
    (forall n c, Pr n (Pc c) c%:MP) ->
    (forall n j nj mj Q (q : mpol mj) (eq_n : (nj + mj = n)%N),
       pos_nat j nj -> Pol_mpoly Q q -> Pr mj Q q ->
       Pr n (Pinj j Q) (mpcast eq_n (mrshift nj q))) ->
    (forall n P p i ni pn Q q (eq_n : (1 + pn = n)%N),
       Pol_mpoly P p -> pos_nat i ni -> Pol_mpoly Q q ->
       Pr n P p -> Pr pn Q q ->
       Pr n (PX P i Q)
         (p * mpcast eq_n 'X_ord0 ^+ ni + mpcast eq_n (mrshift 1 q))) ->
  forall n P p, Pol_mpoly P p -> Pr n P p.
Proof.
move=> PC PI PX n P.
elim: P n => [c n p /eqP[<-]| j Q IH n q | P' IHP' i Q IHQ n p].
- exact: PC.
- case: Pol_mpolyP => // _ nj mj _ {}q eq_n [<- <-] _ jnj Qq _.
  by apply: PI => //; apply: IH.
- case: Pol_mpolyP => // _ p' _ ni pn _ q eq_n [<- <- <-] _ P'p' ini Qq _.
  by apply: PX => //; [apply: IHP'|apply: IHQ].
Qed.

Lemma Pol_mpoly0 n : @Pol_mpoly n (P0 0) 0.
Proof. by rewrite /Pol_mpoly. Qed.
Hint Resolve Pol_mpoly0 : core.

Lemma Pol_mpoly1 n : @Pol_mpoly n (P1 1) 1.
Proof. by rewrite /Pol_mpoly. Qed.
Hint Resolve Pol_mpoly1 : core.

Lemma Pol_mpolyC n c : Pol_mpoly (Pc c) c%:MP_[n].
Proof. by rewrite /Pol_mpoly. Qed.

Lemma Pol_mpolyI n j nj mj Q q (eq_n : (nj + mj = n)%N) :
    pos_nat j nj -> Pol_mpoly Q q ->
  Pol_mpoly (Pinj j Q) (mpcast eq_n (mrshift nj q)).
Proof.
rewrite /Pol_mpoly/= => /eqP-> {j}.
have: (nj <= n)%N by rewrite -eq_n leq_addr.
have mjnnj : mj = (n - nj)%N by rewrite -eq_n addKn.
case: leqP mjnnj q eq_n => [njn -> q eq_n _|//].
case: Pol_to_mpoly => // _ /eqP[->].
by rewrite (nat_irrelevance (subnKC njn) eq_n).
Qed.

Lemma Pol_mpolyX n P (p : mpol n) i ni pn Q q (eq_n : (1 + pn = n)%N) :
    Pol_mpoly P p -> pos_nat i ni -> Pol_mpoly Q q ->
  Pol_mpoly (PX P i Q)
    (p * mpcast eq_n 'X_ord0 ^+ ni + mpcast eq_n (mrshift 1 q)).
Proof.
case: n eq_n p => [//| n]; move=> /[dup][[/[!add0n]<-{n}]] eq_n p.
by rewrite /Pol_mpoly/= => /eqP-> /eqP-> /eqP->; rewrite !mpcast_id.
Qed.

Lemma Pol_mpolyX0 n P (p : mpol n) i ni pn (eq_n : (1 + pn = n)%N) :
    Pol_mpoly P p -> pos_nat i ni ->
  Pol_mpoly (PX P i (P0 0)) (p * mpcast eq_n 'X_ord0 ^+ ni).
Proof.
move=> Pp ini.
by rewrite -[p * _]addr0 -mpolyC0 -(mpcastC eq_n) -mrshiftC Pol_mpolyX.
Qed.

Definition Pol_mpolyE := (Pol_mpolyC, Pol_mpolyI, Pol_mpolyX, Pol_mpolyX0).

Lemma Pol_mpoly_mkPinj n mj j nj P (p : mpol mj) (eq_n : (nj + mj = n)%N) :
    pos_nat j nj -> Pol_mpoly P p ->
  Pol_mpoly (mkPinj j P) (mpcast eq_n (mrshift nj p)).
Proof.
move=> jnj; case: Pol_mpolyP => [//| c _ _ _ ||] /=.
- by rewrite mrshiftC mpcastC Pol_mpolyC.
- move=> j' nj' mj' Q q eq_n' _ _ j'nj' Qq _.
  move: eq_n' eq_n p => /[dup]<- eq_n' eq_n p.
  rewrite mpcast_id -(mpcast_mrshiftDn _ (etrans (esym (addnA _ _ _)) eq_n)).
  by rewrite Pol_mpolyI ?pos_natD.
- move=> P' p' i ni pn Q q eq_pn _ _ P'p' ini Qq _.
  by rewrite Pol_mpolyI ?Pol_mpolyX.
Qed.

Lemma Pol_mpoly_mkPX n P (p : mpol n) i ni pn Q q (eq_n : (1 + pn = n)%N) :
    Pol_mpoly P p -> pos_nat i ni -> Pol_mpoly Q q ->
  Pol_mpoly (mkPX 0 eq_op P i Q)
    (p * mpcast eq_n 'X_ord0 ^+ ni + mpcast eq_n (mrshift 1 q)).
Proof.
case: Pol_mpolyP => [//| c _ _ _ ini Qq /= ||].
- case: eqP => [->|_]; first by rewrite mpolyC0 mul0r add0r Pol_mpoly_mkPinj.
  by rewrite Pol_mpolyX ?Pol_mpolyC.
- move=> j nj mj Q' q' eq_n' _ _ jnj Q'q' _ ini Qq.
  by rewrite Pol_mpolyX ?Pol_mpolyI.
- move=> P' p' i' ni' pn' Q' q' eq_n' _ _ P'p' i'ni' Q'q' _ ini Qq.
  rewrite /mkPX; case: ifP => EQ'0; last by rewrite !Pol_mpolyX.
  have Q'0 : Q' = Pc 0 by case: Q' EQ'0 {Q'q'} => [c /eqP->|//|//].
  move: Q'0 Q'q' {EQ'0} => ->/eqP[<-].
  have epn' : pn' = pn by apply: (@addnI 1); rewrite eq_n eq_n'.
  move: epn' q' eq_n' => -> q' eq_n'; rewrite (nat_irrelevance eq_n' eq_n).
  by rewrite mrshiftC mpcastC addr0 -mulrA -exprD Pol_mpolyX ?pos_natD.
Qed.

Lemma Pol_mpoly_mkPX0 n P (p : mpol n) i ni pn (eq_n : (1 + pn = n)%N) :
    Pol_mpoly P p -> pos_nat i ni ->
  Pol_mpoly (mkPX 0 eq_op P i (P0 0)) (p * mpcast eq_n 'X_ord0 ^+ ni).
Proof.
move=> Pp ini.
by rewrite -[p * _]addr0 -mpolyC0 -(mpcastC eq_n) -mrshiftC Pol_mpoly_mkPX.
Qed.

Lemma Pol_mpolyN n P (p : mpol n) :
  Pol_mpoly P p -> Pol_mpoly (Popp -%R P) (- p).
Proof.
elim/Pol_mpoly_ind => [{P p}n c ||] /=.
- by rewrite -mpolyCN Pol_mpolyC.
- move=> {P p}n j nj mj Q q eq_n jnj Qq IH.
  by rewrite -!rmorphN/= Pol_mpolyI.
- move=> {P p}n P p i ni pn Q q eq_n Pp ini Qq IHP IHQ.
  by rewrite opprD -mulNr -!rmorphN/= Pol_mpolyX.
Qed.

Lemma Pol_mpolyDC n P (p : mpol n) c :
  Pol_mpoly P p -> Pol_mpoly (PaddC +%R P c) (p + c%:MP).
Proof.
elim/Pol_mpoly_ind => {P p}n /= => [c'||].
- by rewrite -mpolyCD Pol_mpolyC.
- move=> j nj mj Q q eq_n jnj Qq IH.
  by rewrite -(mpcastC eq_n) -mrshiftC -!rmorphD/= Pol_mpolyI.
- move=> P p i ni pn Q q eq_n Pp ini Qq IHP IHQ.
  by rewrite -addrA -(mpcastC eq_n) -mrshiftC -!rmorphD/= Pol_mpolyX.
Qed.

Lemma Pol_mpolyBC n P (p : mpol n) c :
  Pol_mpoly P p -> Pol_mpoly (PsubC (fun x y => x - y) P c) (p - c%:MP).
Proof.
elim/Pol_mpoly_ind => {P p}n /= => [c'||].
- by rewrite -mpolyCB Pol_mpolyC.
- move=> j nj mj Q q eq_n jnj Qq IH.
  by rewrite -(mpcastC eq_n) -mrshiftC -!rmorphB/= Pol_mpolyI.
- move=> P p i ni pn Q q eq_n Pp ini Qq IHP IHQ.
  by rewrite -addrA -(mpcastC eq_n) -mrshiftC -!rmorphB/= Pol_mpolyX.
Qed.

Lemma Pol_mpoly_addI n
    (Pop : Pol C -> Pol C -> Pol C)
    (mj : nat) (Q : Pol C) (q : mpol mj) (j : positive) (nj : nat)
    (P : Pol C) (p : mpol n) :
  (forall P (p : mpol mj), Pol_mpoly P p -> Pol_mpoly (Pop P Q) (p + q)) ->
  forall eq_n : (nj + mj = n)%N,
  Pol_mpoly Q q -> pos_nat j nj -> Pol_mpoly P p ->
  Pol_mpoly (PaddI +%R Pop Q j P) (p + mpcast eq_n (mrshift nj q)).
Proof.
move=> PopD eq_n Qq jnj Pp.
elim/Pol_mpoly_ind: Pp mj Q q Qq PopD j nj jnj eq_n => {P p}n /=.
- move=> c mj Q q Qq PopD j nj jnj eq_n.
  rewrite -(mpcastC eq_n) -mrshiftC -!rmorphD/= Pol_mpoly_mkPinj//.
  by rewrite addrC Pol_mpolyDC.
- move=> j nj mj Q q eq_n jnj Qq IH mj' Q' q' Q'q' PopD j' nj' j'nj' eq_n'.
  case: ZintP (Zint_pos_sub jnj j'nj') => [//|| k nk | k nk] jj'.
  + move=> /subr0_eq[njnj'] _.
    have mjmj' : mj = mj' by apply: (@addnI nj); rewrite [in RHS]njnj' eq_n'.
    move: eq_n eq_n' q Qq IH; rewrite njnj' mjmj' => eq_n eq_n' q Qq IH.
    by rewrite (nat_irrelevance eq_n eq_n') -!rmorphD/= Pol_mpoly_mkPinj// PopD.
  + move=> njnj' knk _.
    have enj : (nj = nj' + nk)%N.
      by move/eqP: njnj'; rewrite subr_eq addrC -PoszD => /eqP[->].
    have emj' : (mj' = nk + mj)%N.
      by apply: (@addnI nj'); rewrite eq_n' -eq_n enj addnA.
    move: q' PopD eq_n eq_n' {Q'q' jnj}; rewrite enj emj' => q' PopD eq_n eq_n'.
    rewrite (mpcast_mrshiftDn eq_n') -!rmorphD/= Pol_mpoly_mkPinj//.
    by rewrite PopD// -[mrshift nk q]mpcast_id Pol_mpolyI.
  + move=> njnj' knk _.
    have enj' : (nj' = nj + nk.+1)%N.
      move/eqP: njnj'; rewrite NegzE -opprB eqr_opp subr_eq -PoszD => /eqP[->].
      by rewrite addnC.
    have emj : (mj = nk.+1 + mj')%N.
      by apply: (@addnI nj); rewrite eq_n -eq_n' enj' addnA.
    move: q Qq IH j'nj' eq_n eq_n'; rewrite enj' emj => q Qq IH j'nj eq_n eq_n'.
    rewrite (mpcast_mrshiftDn eq_n) -!rmorphD/= Pol_mpoly_mkPinj//.
    by rewrite -[mrshift _ _]mpcast_id IH.
- move=> P p i ni pn Q' q' eq_pn Pp ini Qq' IHP IHQ' mj Q q Qq PopD j nj.
  move=> /pos_nat_exS[{}nj-> jnj] eq_n.
  have epn : (pn = nj + mj)%N.
    by apply: (@addnI 1); rewrite eq_pn -eq_n -add1n addnA.
  move: q' Qq' IHQ' eq_pn; rewrite epn => q' Qq' IHQ' eq_pn.
  rewrite (mpcast_mrshiftDn eq_pn) -addrA -!rmorphD/= -[mrshift nj q]mpcast_id.
  case: j jnj => [j | j |] jnj; rewrite Pol_mpolyX ?IHQ'//.
  + case: pos_natP jnj => // _ [//|n'] [<-] /[!doubleS][[->]].
    by move=> + _; apply: pos_nat_pred_double.
  + case: pos_natP jnj => // _ nj1 _.
    have enj : nj = 0%N by case: nj nj1 {eq_n epn q' Qq' IHQ' eq_pn}.
    move: q' Qq' {IHQ' epn eq_n eq_pn nj1}; rewrite enj => q' Qq'.
    by rewrite mpcast_id mrshift0n PopD.
Qed.

Lemma Pol_mpoly_subI n
    (Pop : Pol C -> Pol C -> Pol C)
    (mj : nat) (Q : Pol C) (q : mpol mj) (j : positive) (nj : nat)
    (P : Pol C) (p : mpol n) :
  (forall P (p : mpol mj), Pol_mpoly P p -> Pol_mpoly (Pop P Q) (p - q)) ->
  forall eq_n : (nj + mj = n)%N,
  Pol_mpoly Q q -> pos_nat j nj -> Pol_mpoly P p ->
  Pol_mpoly (PsubI +%R -%R Pop Q j P) (p - mpcast eq_n (mrshift nj q)).
Proof.
move=> PopB eq_n Qq jnj Pp.
elim/Pol_mpoly_ind: Pp mj Q q Qq PopB j nj jnj eq_n => {P p}n /=.
- move=> c mj Q q Qq PopB j nj jnj eq_n.
  rewrite -(mpcastC eq_n) -mrshiftC -!rmorphB/= Pol_mpoly_mkPinj//.
  by rewrite addrC Pol_mpolyDC ?Pol_mpolyN.
- move=> j nj mj Q q eq_n jnj Qq IH mj' Q' q' Q'q' PopB j' nj' j'nj' eq_n'.
  case: ZintP (Zint_pos_sub jnj j'nj') => [//|| k nk | k nk] jj'.
  + move=> /subr0_eq[njnj'] _.
    have mjmj' : mj = mj' by apply: (@addnI nj); rewrite [in RHS]njnj' eq_n'.
    move: eq_n eq_n' q Qq IH; rewrite njnj' mjmj' => eq_n eq_n' q Qq IH.
    by rewrite (nat_irrelevance eq_n eq_n') -!rmorphB/= Pol_mpoly_mkPinj// PopB.
  + move=> njnj' knk _.
    have enj : (nj = nj' + nk)%N.
      by move/eqP: njnj'; rewrite subr_eq addrC -PoszD => /eqP[->].
    have emj' : (mj' = nk + mj)%N.
      by apply: (@addnI nj'); rewrite eq_n' -eq_n enj addnA.
    move: q' PopB eq_n eq_n' {Q'q' jnj}; rewrite enj emj' => q' PopB eq_n eq_n'.
    rewrite (mpcast_mrshiftDn eq_n') -!rmorphB/= Pol_mpoly_mkPinj//.
    by rewrite PopB// -[mrshift nk q]mpcast_id Pol_mpolyI.
  + move=> njnj' knk _.
    have enj' : (nj' = nj + nk.+1)%N.
      move/eqP: njnj'; rewrite NegzE -opprB eqr_opp subr_eq -PoszD => /eqP[->].
      by rewrite addnC.
    have emj : (mj = nk.+1 + mj')%N.
      by apply: (@addnI nj); rewrite eq_n -eq_n' enj' addnA.
    move: q Qq IH j'nj' eq_n eq_n'; rewrite enj' emj => q Qq IH j'nj eq_n eq_n'.
    rewrite (mpcast_mrshiftDn eq_n) -!rmorphB/= Pol_mpoly_mkPinj//.
    by rewrite -[mrshift _ _]mpcast_id IH.
- move=> P p i ni pn Q' q' eq_pn Pp ini Qq' IHP IHQ' mj Q q Qq PopB j nj.
  move=> /pos_nat_exS[{}nj-> jnj] eq_n.
  have epn : (pn = nj + mj)%N.
    by apply: (@addnI 1); rewrite eq_pn -eq_n -add1n addnA.
  move: q' Qq' IHQ' eq_pn; rewrite epn => q' Qq' IHQ' eq_pn.
  rewrite (mpcast_mrshiftDn eq_pn) -addrA -!rmorphB/= -[mrshift nj q]mpcast_id.
  case: j jnj => [j | j |] jnj; rewrite Pol_mpolyX ?IHQ'//.
  + case: pos_natP jnj => // _ [//|n'] [<-] /[!doubleS][[->]].
    by move=> + _; apply: pos_nat_pred_double.
  + case: pos_natP jnj => // _ nj1 _.
    have enj : nj = 0%N by case: nj nj1 {eq_n epn q' Qq' IHQ' eq_pn}.
    move: q' Qq' {IHQ' epn eq_n eq_pn nj1}; rewrite enj => q' Qq'.
    by rewrite mpcast_id mrshift0n PopB.
Qed.

Lemma Pol_mpoly_addX n
    (Pop : Pol C -> Pol C -> Pol C)
    (P' : Pol C) (p' : mpol n) (i' : positive) (ni' : nat)
    (P : Pol C) (p : mpol n) :
  (forall P p, Pol_mpoly P p -> Pol_mpoly (Pop P P') (p + p')) ->
  forall pn (eq_n : (1 + pn = n)%N),
  Pol_mpoly P p -> Pol_mpoly P' p' -> pos_nat i' ni' ->
  Pol_mpoly (PaddX 0 eq_op Pop P' i' P)
    (p + p' * mpcast eq_n 'X_ord0 ^+ ni').
Proof.
move=> PopD pn eq_n Pp P'p' i'ni'; move: Pp P' p' P'p' PopD i' ni' i'ni' pn eq_n.
elim/Pol_mpoly_ind => {P p}n /= => [c P' p' P'p' PopD i' ni' i'ni' pn eq_n ||].
- by rewrite addrC -(mpcastC eq_n) -mrshiftC Pol_mpolyX// Pol_mpolyC.
- move=> j nj mj Q' q' eq_n jnj Q'q' IH P' p' P'p' PopD i' ni' i'ni' pn eq_pn.
  move: jnj eq_n => /pos_nat_exS[{}nj-> jnj] eq_n; rewrite addrC.
  have epn : (pn = nj + mj)%N.
    by apply: (@addnI 1); rewrite eq_pn -eq_n -add1n addnA.
  move: eq_pn; rewrite epn => eq_pn; rewrite (mpcast_mrshiftDn eq_pn).
  case: j jnj => [j | j |] jnj; rewrite Pol_mpolyX// -[mrshift nj q']mpcast_id.
  + exact: Pol_mpolyI.
  + rewrite Pol_mpolyI//.
    case: pos_natP jnj => // _ [//|n'] [<-] /[!doubleS][[->]].
    by move=> + _; apply: pos_nat_pred_double.
  + case: pos_natP jnj => // _ nj1 _.
    have enj : nj = 0%N by case: nj nj1 {eq_n epn eq_pn}.
    by rewrite enj mpcast_id mrshift0n.
- move=> P p i ni pn Q q eq_n Pp ini Qq IHP IHQ P' p' P'p' PopD i' ni' i'ni'.
  move=> pn' eq_pn'.
  have epn' : pn' = pn by apply: (@addnI 1); rewrite eq_pn' eq_n.
  move: eq_pn'; rewrite epn' => eq_pn'; rewrite (nat_irrelevance eq_pn' eq_n).
  case: ZintP (Zint_pos_sub ini i'ni') => [//|| k nk | k nk] ii'.
  + move: i'ni' => /[swap] /subr0_eq[<-] i'ni _ {ni'}.
    by rewrite addrAC -mulrDl Pol_mpoly_mkPX// PopD.
  + move=> nini' knk _.
    have -> : (ni = nk + ni')%N.
      by move/eqP: nini'; rewrite subr_eq -PoszD => /eqP[->].
    by rewrite exprD mulrA addrAC -mulrDl Pol_mpoly_mkPX ?PopD ?Pol_mpolyX0.
  + move=> nini' knk _.
    have -> : (ni' = nk.+1 + ni)%N.
      by move/eqP: nini'; rewrite NegzE -opprB eqr_opp subr_eq -PoszD => /eqP[].
    by rewrite exprD mulrA addrAC -mulrDl Pol_mpoly_mkPX ?IHP.
Qed.

Lemma Pol_mpoly_subX n
    (Pop : Pol C -> Pol C -> Pol C)
    (P' : Pol C) (p' : mpol n) (i' : positive) (ni' : nat)
    (P : Pol C) (p : mpol n) :
  (forall P p, Pol_mpoly P p -> Pol_mpoly (Pop P P') (p - p')) ->
  forall pn (eq_n : (1 + pn = n)%N),
  Pol_mpoly P p -> Pol_mpoly P' p' -> pos_nat i' ni' ->
  Pol_mpoly (PsubX 0 -%R eq_op Pop P' i' P)
    (p - p' * mpcast eq_n 'X_ord0 ^+ ni').
Proof.
move=> PopB pn eq_n Pp P'p' i'ni'; move: Pp P' p' P'p' PopB i' ni' i'ni' pn eq_n.
elim/Pol_mpoly_ind => {P p}n /= => [c P' p' P'p' PopB i' ni' i'ni' pn eq_n ||].
- rewrite addrC -mulNr -(mpcastC eq_n) -mrshiftC Pol_mpolyX ?Pol_mpolyC//.
  exact: Pol_mpolyN.
- move=> j nj mj Q' q' eq_n jnj Q'q' IH P' p' P'p' PopB i' ni' i'ni' pn eq_pn.
  move: jnj eq_n => /pos_nat_exS[{}nj-> jnj] eq_n; rewrite addrC -mulNr.
  have epn : (pn = nj + mj)%N.
    by apply: (@addnI 1); rewrite eq_pn -eq_n -add1n addnA.
  move: eq_pn; rewrite epn => eq_pn; rewrite (mpcast_mrshiftDn eq_pn).
  rewrite  -[mrshift nj q']mpcast_id.
  case: j jnj => [j | j |] jnj; rewrite Pol_mpolyX ?Pol_mpolyN//.
  + exact: Pol_mpolyI.
  + rewrite Pol_mpolyI//.
    case: pos_natP jnj => // _ [//|n'] [<-] /[!doubleS][[->]].
    by move=> + _; apply: pos_nat_pred_double.
  + case: pos_natP jnj => // _ nj1 _.
    have enj : nj = 0%N by case: nj nj1 {eq_n epn eq_pn}.
    by rewrite enj mpcast_id mrshift0n.
- move=> P p i ni pn Q q eq_n Pp ini Qq IHP IHQ P' p' P'p' PopB i' ni' i'ni'.
  move=> pn' eq_pn'.
  have epn' : pn' = pn by apply: (@addnI 1); rewrite eq_pn' eq_n.
  move: eq_pn'; rewrite epn' => eq_pn'; rewrite (nat_irrelevance eq_pn' eq_n).
  case: ZintP (Zint_pos_sub ini i'ni') => [//|| k nk | k nk] ii'.
  + move: i'ni' => /[swap] /subr0_eq[<-] i'ni _ {ni'}.
    by rewrite addrAC -mulrBl Pol_mpoly_mkPX// PopB.
  + move=> nini' knk _.
    have -> : (ni = nk + ni')%N.
      by move/eqP: nini'; rewrite subr_eq -PoszD => /eqP[->].
    by rewrite exprD mulrA addrAC -mulrBl Pol_mpoly_mkPX ?PopB ?Pol_mpolyX0.
  + move=> nini' knk _.
    have -> : (ni' = nk.+1 + ni)%N.
      by move/eqP: nini'; rewrite NegzE -opprB eqr_opp subr_eq -PoszD => /eqP[].
    by rewrite exprD mulrA addrAC -mulrBl Pol_mpoly_mkPX ?IHP.
Qed.

Lemma Pol_mpolyD n P (p : mpol n) P' p' : Pol_mpoly P p -> Pol_mpoly P' p' ->
  Pol_mpoly (Padd 0 +%R eq_op P P') (p + p').
Proof.
move=> Pp P'p'; elim/Pol_mpoly_ind: P'p' P p Pp => {P' p'}n /= => [c P p Pp ||].
- exact: Pol_mpolyDC.
- by move=> j nj mn Q q eq_pn jnj Qq IH P p Pp; apply: Pol_mpoly_addI.
move=> P' p' i' ni' pn Q' q' eq_pn P'p' i'ni' Q'q' IHP IHQ P p; rewrite addrCA.
case: Pol_mpolyP => [//| c _ _ _ ||].
- rewrite -(mpcastC eq_pn) -mrshiftC -!rmorphD/= Pol_mpolyX//.
  by rewrite addrC Pol_mpolyDC.
- move=> j nj mj Q q eq_n _ _ jnj Qq _.
  case: pos_natP jnj eq_n => [//|_ _| k nk _ _ knk | k nk _ _ knk] _ eq_n.
  + have emj : mj = pn by apply: (@addnI 1); rewrite eq_n eq_pn.
    move: emj q Qq eq_n => -> q Qq eq_n; rewrite (nat_irrelevance eq_n eq_pn).
    by rewrite -!rmorphD/= Pol_mpolyX ?IHQ.
  + move: knk eq_n => /pos_nat_exS[{}nk-> knk] eq_n.
    have epn : (pn = nk.*2.+1 + mj)%N.
      by apply: (@addnI 1); rewrite eq_pn -eq_n addnA doubleS add1n.
    move: epn q' Q'q' IHQ eq_pn => -> q' Q'q' IHQ eq_pn.
    rewrite (mpcast_mrshiftDn eq_pn) -!rmorphD/= Pol_mpolyX ?IHQ//.
    rewrite -[mrshift _ q](mpcast_id erefl) Pol_mpolyI//.
    by rewrite -pred_doubleS pos_nat_pred_double.
  + have epn : (pn = nk.*2 + mj)%N.
      by apply: (@addnI 1); rewrite eq_pn -eq_n addnA add1n.
    move: epn q' Q'q' IHQ eq_pn => -> q' Q'q' IHQ eq_pn.
    rewrite (mpcast_mrshiftDn eq_pn) -!rmorphD/= Pol_mpolyX ?IHQ//.
    by rewrite -[mrshift _ q](mpcast_id erefl) Pol_mpolyI ?pos_natE.
- move=> {}P {}p i ni pn' Q q eq_n _ _ Pp ini Qq _.
  have epn' : pn' = pn by apply: (@addnI 1); rewrite eq_pn eq_n.
  move: epn' q Qq eq_n => -> q Qq eq_n; rewrite (nat_irrelevance eq_pn eq_n).
  rewrite -addrA -!rmorphD/= addrA [p' * _ + _]addrC.
  case: ZintP (Zint_pos_sub ini i'ni') => [//|| k nk | k nk] ii'.
  + move: i'ni' => /[swap] /subr0_eq[<-] i'ni _ {ni'}.
    by rewrite -mulrDl Pol_mpoly_mkPX ?IHP ?IHQ.
  + move=> nini' knk _.
    have -> : (ni = nk + ni')%N.
      by move/eqP: nini'; rewrite subr_eq -PoszD => /eqP[->].
    by rewrite exprD mulrA -mulrDl Pol_mpoly_mkPX ?IHP ?IHQ ?Pol_mpolyX0.
  + move=> nini' knk _.
    have -> : (ni' = nk.+1 + ni)%N.
      by move/eqP: nini'; rewrite NegzE -opprB eqr_opp subr_eq -PoszD => /eqP[].
    by rewrite exprD mulrA -mulrDl Pol_mpoly_mkPX ?IHQ ?Pol_mpoly_addX.
Qed.

Lemma Pol_mpolyB n P (p : mpol n) P' p' : Pol_mpoly P p -> Pol_mpoly P' p' ->
  Pol_mpoly (Psub 0 +%R (fun x y => x - y) -%R eq_op P P') (p - p').
Proof.
move=> Pp P'p'; elim/Pol_mpoly_ind: P'p' P p Pp => {P' p'}n /= => [c P p Pp ||].
- exact: Pol_mpolyBC.
- by move=> j nj mn Q q eq_pn jnj Qq IH P p Pp; apply: Pol_mpoly_subI.
move=> P' p' i' ni' pn Q' q' eq_pn P'p' i'ni' Q'q' IHP IHQ P p.
rewrite opprD -mulNr addrCA; case: Pol_mpolyP => [//| c _ _ _ ||].
- rewrite -(mpcastC eq_pn) -mrshiftC -!rmorphB/= Pol_mpolyX ?Pol_mpolyN//.
  by rewrite addrC Pol_mpolyDC ?Pol_mpolyN.
- move=> j nj mj Q q eq_n _ _ jnj Qq _.
  case: pos_natP jnj eq_n => [//|_ _| k nk _ _ knk | k nk _ _ knk] _ eq_n.
  + have emj : mj = pn by apply: (@addnI 1); rewrite eq_n eq_pn.
    move: emj q Qq eq_n => -> q Qq eq_n; rewrite (nat_irrelevance eq_n eq_pn).
    by rewrite -!rmorphB/= Pol_mpolyX ?Pol_mpolyN ?IHQ.
  + move: knk eq_n => /pos_nat_exS[{}nk-> knk] eq_n.
    have epn : (pn = nk.*2.+1 + mj)%N.
      by apply: (@addnI 1); rewrite eq_pn -eq_n addnA doubleS add1n.
    move: epn q' Q'q' IHQ eq_pn => -> q' Q'q' IHQ eq_pn.
    rewrite (mpcast_mrshiftDn eq_pn) -!rmorphB/= Pol_mpolyX ?Pol_mpolyN ?IHQ//.
    rewrite -[mrshift _ q](mpcast_id erefl) Pol_mpolyI//.
    by rewrite -pred_doubleS pos_nat_pred_double.
  + have epn : (pn = nk.*2 + mj)%N.
      by apply: (@addnI 1); rewrite eq_pn -eq_n addnA add1n.
    move: epn q' Q'q' IHQ eq_pn => -> q' Q'q' IHQ eq_pn.
    rewrite (mpcast_mrshiftDn eq_pn) -!rmorphB/= Pol_mpolyX ?Pol_mpolyN ?IHQ//.
    by rewrite -[mrshift _ q](mpcast_id erefl) Pol_mpolyI ?pos_natE.
- move=> {}P {}p i ni pn' Q q eq_n _ _ Pp ini Qq _.
  have epn' : pn' = pn by apply: (@addnI 1); rewrite eq_pn eq_n.
  move: epn' q Qq eq_n => -> q Qq eq_n; rewrite (nat_irrelevance eq_pn eq_n).
  rewrite -addrA -!rmorphB/= addrA [- p' * _ + _]addrC.
  case: ZintP (Zint_pos_sub ini i'ni') => [//|| k nk | k nk] ii'.
  + move: i'ni' => /[swap] /subr0_eq[<-] i'ni _ {ni'}.
    by rewrite -mulrDl Pol_mpoly_mkPX ?IHP ?IHQ.
  + move=> nini' knk _.
    have -> : (ni = nk + ni')%N.
      by move/eqP: nini'; rewrite subr_eq -PoszD => /eqP[->].
    by rewrite exprD mulrA -mulrDl Pol_mpoly_mkPX ?IHP ?IHQ ?Pol_mpolyX0.
  + move=> nini' knk _.
    have -> : (ni' = nk.+1 + ni)%N.
      by move/eqP: nini'; rewrite NegzE -opprB eqr_opp subr_eq -PoszD => /eqP[].
    by rewrite exprD mulrA -mulrDl Pol_mpoly_mkPX ?IHQ// mulNr Pol_mpoly_subX.
Qed.

Lemma Pol_mpoly_mulC_aux n P (p : mpol n) c : Pol_mpoly P p ->
  Pol_mpoly (PmulC_aux 0 *%R eq_op P c) (p * c%:MP).
Proof.
elim/Pol_mpoly_ind => {P p}n /= => [c' ||].
- by rewrite -mpolyCM Pol_mpolyC.
- move=> j nj mj Q q eq_n jnj Qq IHQ.
  by rewrite -(mpcastC eq_n) -mrshiftC -!rmorphM/= Pol_mpoly_mkPinj.
- move=> P p i ni pn Q q eq_n Pp ini Qq IHP IHQ.
  rewrite mulrDl mulrAC -(mpcastC eq_n) -mrshiftC -!rmorphM/=.
  by rewrite Pol_mpoly_mkPX ?mrshiftC ?mpcastC.
Qed.

Lemma Pol_mpolyMC n P (p : mpol n) c : Pol_mpoly P p ->
  Pol_mpoly (PmulC 0 1 *%R eq_op P c) (p * c%:MP).
Proof.
rewrite /PmulC/=; case: eqP => [->|_]; first by rewrite mpolyC0 mulr0.
by case: eqP => [->|_?]; rewrite ?mpolyC1?mulr1 ?Pol_mpoly1 ?Pol_mpoly_mulC_aux.
Qed.

Lemma Pol_mpoly_mulI n
    (Pmul : Pol C -> Pol C -> Pol C)
    (mj : nat) (Q : Pol C) (q : mpol mj) (j : positive) (nj : nat)
    (P : Pol C) (p : mpol n) :
  (forall P (p : mpol mj), Pol_mpoly P p -> Pol_mpoly (Pmul P Q) (p * q)) ->
  forall eq_n : (nj + mj = n)%N,
  Pol_mpoly Q q -> pos_nat j nj -> Pol_mpoly P p ->
  Pol_mpoly (PmulI 0 1 *%R eq_op Pmul Q j P) (p * mpcast eq_n (mrshift nj q)).
Proof.
move=> PmulM eq_n Qq jnj Pp.
elim/Pol_mpoly_ind: Pp Q q j nj PmulM eq_n Qq jnj => {P p}n /=.
- move=> c Q q j nj PmulM eq_n Qq jnj.
  rewrite -(mpcastC eq_n) -mrshiftC -!rmorphM/= Pol_mpoly_mkPinj//.
  by rewrite mulrC Pol_mpolyMC.
- move=> j nj mj' Q q eq_n jnj Qq IH Q' q' j' nj' MulM eq_n' Q'q' j'nj'.
  case: ZintP (Zint_pos_sub jnj j'nj') => [//|| k nk | k nk] jj' njnj'.
  + move: njnj' j'nj' jj' eq_n' => /subr0_eq[<-] j'nj _ eq_n' _.
    have emj' : mj' = mj by apply: (@addnI nj); rewrite eq_n eq_n'.
    move: emj' q Qq IH eq_n => -> q Qq IH eq_n.
    by rewrite (nat_irrelevance eq_n' eq_n) -!rmorphM/= Pol_mpoly_mkPinj ?MulM.
  + move=> knk _; have enj : (nj = nj' + nk)%N.
      by move/eqP: njnj'; rewrite subr_eq addrC -PoszD => /eqP[->].
    move: enj eq_n jnj njnj' => -> eq_n jnj njnj'.
    have emj : (mj = nk + mj')%N.
      by apply: (@addnI nj'); rewrite addnA eq_n' eq_n.
    move: emj IH q' MulM Q'q' eq_n' => -> IH q' MulM Q'q' eq_n'.
    rewrite (mpcast_mrshiftDn eq_n') -!rmorphM/= Pol_mpoly_mkPinj ?MulM//.
    by rewrite -[mrshift nk q]mpcast_id Pol_mpolyI.
  + move=> knk _; have enj : (nj' = nj + nk.+1)%N.
      move/eqP: njnj'.
      by rewrite NegzE -opprB eqr_opp subr_eq addrC -PoszD => /eqP[].
    move: enj eq_n' j'nj' njnj' => -> eq_n' j'nj' njnj'.
    have emj' : (mj' = nk.+1 + mj)%N.
      by apply: (@addnI nj); rewrite eq_n -eq_n' addnA.
    move: emj' q Qq IH eq_n => -> q Qq IH eq_n.
    rewrite (mpcast_mrshiftDn eq_n) -!rmorphM/= Pol_mpoly_mkPinj//.
    by rewrite -[mrshift _ q']mpcast_id IH.
- move=> P' p' i' ni pn' Q' q' eq_n' P'p' i'ni' Q'q' IHP' IHQ'.
  move=> Q q j nj MulM eq_n Qq jnj; rewrite mulrDl mulrAC.
  case: pos_natP jnj eq_n => [//|_ _| k nk _ _ knk | k nk _ _ knk] _ eq_n.
  + have epn' : pn' = mj by apply: (@addnI 1); rewrite eq_n eq_n'.
    move: epn' q' Q'q' IHQ' eq_n' => -> q' Qq' IHQ' eq_n'.
    rewrite (nat_irrelevance eq_n' eq_n) -!rmorphM/= Pol_mpoly_mkPX ?MulM//.
    by rewrite IHP'.
  + move: knk eq_n => /pos_nat_exS[{}nk-> knk] eq_n.
    have epn' : (pn' = nk.*2.+1 + mj)%N.
      by apply: (@addnI 1); rewrite eq_n' add1n -addSn eq_n.
    move: epn' q' Q'q' IHQ' eq_n' => -> q' Q'q' IHQ' eq_n'.
    rewrite [in X in _ + X](mpcast_mrshiftDn eq_n') -!rmorphM/=.
    rewrite Pol_mpoly_mkPX ?IHP' ?pos_natE//.
    by rewrite -[mrshift _ q]mpcast_id IHQ' -?pred_doubleS ?pos_nat_pred_double.
  + have epn' : (pn' = nk.*2 + mj)%N.
      by apply: (@addnI 1); rewrite eq_n' add1n -addSn eq_n.
    move: epn' q' Q'q' IHQ' eq_n' => -> q' Q'q' IHQ' eq_n'.
    rewrite [in X in _ + X](mpcast_mrshiftDn eq_n') -!rmorphM/=.
    rewrite Pol_mpoly_mkPX ?IHP' ?pos_natE//.
    by rewrite -[mrshift _ q]mpcast_id IHQ' ?pos_natE.
Qed.

Lemma Pol_mpolyM n P (p : mpol n) P'' p'' :
    Pol_mpoly P p -> Pol_mpoly P'' p'' ->
  Pol_mpoly (Pmul 0 1 +%R *%R eq_op P P'') (p * p'').
Proof.
move=> Pp P''p''; elim/Pol_mpoly_ind: P''p'' P p Pp => {P'' p''}n /=.
- by move=> c P p Pp; apply: Pol_mpolyMC.
- by move=> j' nj' mj' Q' q' eq_n j'nj' Q'q' IH P p Pp; apply: Pol_mpoly_mulI.
move=> P' p' i' ni' pn' Q' q' eq_pn' P'p' i'ni' Q'q' IHP' IHQ' P p.
case: Pol_mpolyP => [//| c _ _ _||].
- by rewrite mulrC Pol_mpolyMC ?Pol_mpolyX.
- move=> j nj mj Q q eq_n _ _ jnj Qq _ {P p}; rewrite mulrDr mulrA.
  case: pos_natP jnj eq_n => [//|_ _| k nk _ _ knk | k nk _ _ knk ] _ eq_n.
  + have emj : mj = pn' by apply: (@addnI 1); rewrite eq_pn' eq_n.
    move: emj q Qq eq_n => -> q Qq eq_n; rewrite (nat_irrelevance eq_pn' eq_n).
    rewrite -!rmorphM/= Pol_mpoly_mkPX ?IHQ'//.
    by rewrite IHP' ?Pol_mpolyI.
  + move: knk eq_n => /pos_nat_exS[{}nk-> knk] eq_n.
    have epn' : (pn' = nk.*2.+1 + mj)%N.
      by apply: (@addnI 1); rewrite eq_pn' -eq_n.
    move: epn' q' Q'q' IHQ' eq_pn' => -> q' Q'q' IHQ' eq_pn'.
    rewrite [in X in _ + X](mpcast_mrshiftDn eq_pn') -!rmorphM/=.
    rewrite Pol_mpoly_mkPX ?IHP' ?Pol_mpolyI ?pos_natE ?IHQ'//.
    rewrite -[mrshift _ q]mpcast_id Pol_mpolyI//.
    by rewrite-?pred_doubleS ?pos_nat_pred_double.
  + have epn' : (pn' = nk.*2 + mj)%N by apply: (@addnI 1); rewrite eq_pn' -eq_n.
    move: epn' q' Q'q' IHQ' eq_pn' => -> q' Q'q' IHQ' eq_pn'.
    rewrite [in X in _ + X](mpcast_mrshiftDn eq_pn') -!rmorphM/=.
    rewrite Pol_mpoly_mkPX ?IHP' ?Pol_mpolyI ?pos_natE ?IHQ'//.
    by rewrite -[mrshift _ q]mpcast_id Pol_mpolyI ?pos_natE.
- move=> {}P {}p i ni pn Q q eq_n _ _ Pp ini Qq _.
  have epn' : pn' = pn by apply: (@addnI 1); rewrite eq_pn' eq_n.
  move: epn' q' Q'q' IHQ' eq_pn' => -> q' Q'q' IHQ' eq_pn'.
  rewrite (nat_irrelevance eq_pn' eq_n) => {eq_pn'}.
  rewrite mulrDl !mulrDr addrACA Pol_mpolyD//; last first.
    by rewrite mulrAC -!rmorphM/= Pol_mpoly_mkPX ?Pol_mpoly_mulI ?IHQ'.
  rewrite -mulrDl mulrA Pol_mpoly_mkPX0// mulrDl Pol_mpolyD ?IHP'//.
    by rewrite mulrAC Pol_mpoly_mkPX0 ?IHP'//.
  by rewrite Pol_mpoly_mkPinj.
Qed.

Lemma Pol_mpoly_square n P (p : mpol n) :
  Pol_mpoly P p -> Pol_mpoly (Psquare 0 1 +%R *%R eq_op P) (p * p).
Proof.
elim/Pol_mpoly_ind => {P p}n /= => [c ||].
- by rewrite -mpolyCM Pol_mpolyC.
- by move=> j nj mj Q q eq_n jnj Qq IH; rewrite -!rmorphM/= Pol_mpolyI.
move=> P p i ni pn Q q eq_n Pp ini Qq IHP IHQ.
rewrite -expr2 sqrrD exprMn [_ ^+ ni ^+ 2]expr2 mulrA mulrAC -mulrnAl -mulrDl.
rewrite -!(rmorphXn _ 2)/= Pol_mpoly_mkPX ?Pol_mpolyD ?Pol_mpoly_mkPX0//.
rewrite -mulrnAr Pol_mpolyM -?rmorphMn/= ?Pol_mpoly_mkPinj//.
by rewrite -mulr_natr -[2]/(1 + 1) -mpolyC1 -mpolyCD Pol_mpolyMC.
Qed.

Lemma Pol_mpoly_pow_pos n Res (res : mpol n) P p p' n' :
    Pol_mpoly Res res -> Pol_mpoly P p -> pos_nat p' n' ->
  Pol_mpoly (Ppow_pos 0 1 +%R *%R eq_op Res P p') (res * p ^+ n').
Proof.
move=> Resres Pp p'n'; move: p'n' Res res Resres P p Pp.
elim/pos_nat_ind => {p' n'} => [| p' n' p'n' IH | p' n' p'n' IH];
    move=> Res res Resres P p Pp /=.
- by rewrite expr1 Pol_mpolyM.
- by rewrite -addnn exprD mulrA !IH.
- by rewrite -addn1 exprD expr1 mulrA Pol_mpolyM// -addnn exprD mulrA !IH.
Qed.

End Pol_mpoly.

Elpi derive.param2 bool.
Elpi derive.param2 positive.
Elpi derive.param2 Z.
Elpi derive.param2 comparison.
Elpi derive.param2 Pol.

Elpi derive.param2 Pos.succ.
(* Use derive.param2 when elpi supports mutual fixpoints *)
Definition add_R :=
  (let fix_add_1 :=
    fix add (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | p~0 => match y with
               | q~1 => (add p q)~1
               | q~0 => (add p q)~0
               | 1 => p~1
               end
      | 1 => match y with
             | q~1 => (Pos.succ q)~0
             | q~0 => q~1
             | 1 => 2
             end
      end
    with add_carry (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~1
          | q~0 => (add_carry p q)~0
          | 1 => (Pos.succ p)~1
          end
      | p~0 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | 1 => match y with
             | q~1 => (Pos.succ q)~1
             | q~0 => (Pos.succ q)~0
             | 1 => 3
             end
      end
    for
    add in
  let fix_add_2 :=
    fix add (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | p~0 => match y with
               | q~1 => (add p q)~1
               | q~0 => (add p q)~0
               | 1 => p~1
               end
      | 1 => match y with
             | q~1 => (Pos.succ q)~0
             | q~0 => q~1
             | 1 => 2
             end
      end
    with add_carry (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~1
          | q~0 => (add_carry p q)~0
          | 1 => (Pos.succ p)~1
          end
      | p~0 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | 1 => match y with
             | q~1 => (Pos.succ q)~1
             | q~0 => (Pos.succ q)~0
             | 1 => 3
             end
      end
    for
    add in
  let fix_add_carry_1 :=
    fix add (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | p~0 => match y with
               | q~1 => (add p q)~1
               | q~0 => (add p q)~0
               | 1 => p~1
               end
      | 1 => match y with
             | q~1 => (Pos.succ q)~0
             | q~0 => q~1
             | 1 => 2
             end
      end
    with add_carry (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~1
          | q~0 => (add_carry p q)~0
          | 1 => (Pos.succ p)~1
          end
      | p~0 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | 1 => match y with
             | q~1 => (Pos.succ q)~1
             | q~0 => (Pos.succ q)~0
             | 1 => 3
             end
      end
    for
    add_carry in
  let fix_add_carry_2 :=
    fix add (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | p~0 => match y with
               | q~1 => (add p q)~1
               | q~0 => (add p q)~0
               | 1 => p~1
               end
      | 1 => match y with
             | q~1 => (Pos.succ q)~0
             | q~0 => q~1
             | 1 => 2
             end
      end
    with add_carry (x y : positive) {struct x} : positive :=
      match x with
      | p~1 =>
          match y with
          | q~1 => (add_carry p q)~1
          | q~0 => (add_carry p q)~0
          | 1 => (Pos.succ p)~1
          end
      | p~0 =>
          match y with
          | q~1 => (add_carry p q)~0
          | q~0 => (add p q)~1
          | 1 => (Pos.succ p)~0
          end
      | 1 => match y with
             | q~1 => (Pos.succ q)~1
             | q~0 => (Pos.succ q)~0
             | 1 => 3
             end
      end
    for
    add_carry in
  fix add_R (x_1 x_2 : positive) (x_R : positive_R x_1 x_2)
        (y_1 y_2 : positive) (y_R : positive_R y_1 y_2) {struct x_R} :
      positive_R (fix_add_1 x_1 y_1) (fix_add_2 x_2 y_2) :=
    match
      x_R in (positive_R x_10 x_20)
      return (positive_R (fix_add_1 x_10 y_1) (fix_add_2 x_20 y_2))
    with
    | @xI_R p_1 p_2 p_R =>
        match
          y_R in (positive_R y_10 y_20)
          return
            (positive_R
               match y_10 with
               | q~1 => (fix_add_carry_1 p_1 q)~0
               | q~0 => (fix_add_1 p_1 q)~1
               | 1 => (Pos.succ p_1)~0
               end
               match y_20 with
               | q~1 => (fix_add_carry_2 p_2 q)~0
               | q~0 => (fix_add_2 p_2 q)~1
               | 1 => (Pos.succ p_2)~0
               end)
        with
        | @xI_R q_1 q_2 q_R => xO_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
        | @xO_R q_1 q_2 q_R => xI_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
        | xH_R => xO_R (succ_R p_R)
        end
    | @xO_R p_1 p_2 p_R =>
        match
          y_R in (positive_R y_10 y_20)
          return
            (positive_R
               match y_10 with
               | q~1 => (fix_add_1 p_1 q)~1
               | q~0 => (fix_add_1 p_1 q)~0
               | 1 => p_1~1
               end
               match y_20 with
               | q~1 => (fix_add_2 p_2 q)~1
               | q~0 => (fix_add_2 p_2 q)~0
               | 1 => p_2~1
               end)
        with
        | @xI_R q_1 q_2 q_R => xI_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
        | @xO_R q_1 q_2 q_R => xO_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
        | xH_R => xI_R p_R
        end
    | xH_R =>
        match
          y_R in (positive_R y_10 y_20)
          return
            (positive_R match y_10 with
                        | q~1 => (Pos.succ q)~0
                        | q~0 => q~1
                        | 1 => 2
                        end
               match y_20 with
               | q~1 => (Pos.succ q)~0
               | q~0 => q~1
               | 1 => 2
               end)
        with
        | @xI_R q_1 q_2 q_R => xO_R (succ_R q_R)
        | @xO_R q_1 q_2 q_R => xI_R q_R
        | xH_R => xO_R xH_R
        end
    end
    with add_carry_R (x_1 x_2 : positive) (x_R : positive_R x_1 x_2)
        (y_1 y_2 : positive) (y_R : positive_R y_1 y_2) {struct x_R} :
      positive_R (fix_add_carry_1 x_1 y_1) (fix_add_carry_2 x_2 y_2) :=
    match
      x_R in (positive_R x_10 x_20)
      return (positive_R (fix_add_carry_1 x_10 y_1) (fix_add_carry_2 x_20 y_2))
    with
    | @xI_R p_1 p_2 p_R =>
        match
          y_R in (positive_R y_10 y_20)
          return
            (positive_R
               match y_10 with
               | q~1 => (fix_add_carry_1 p_1 q)~1
               | q~0 => (fix_add_carry_1 p_1 q)~0
               | 1 => (Pos.succ p_1)~1
               end
               match y_20 with
               | q~1 => (fix_add_carry_2 p_2 q)~1
               | q~0 => (fix_add_carry_2 p_2 q)~0
               | 1 => (Pos.succ p_2)~1
               end)
        with
        | @xI_R q_1 q_2 q_R => xI_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
        | @xO_R q_1 q_2 q_R => xO_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
        | xH_R => xI_R (succ_R p_R)
        end
    | @xO_R p_1 p_2 p_R =>
        match
          y_R in (positive_R y_10 y_20)
          return
            (positive_R
               match y_10 with
               | q~1 => (fix_add_carry_1 p_1 q)~0
               | q~0 => (fix_add_1 p_1 q)~1
               | 1 => (Pos.succ p_1)~0
               end
               match y_20 with
               | q~1 => (fix_add_carry_2 p_2 q)~0
               | q~0 => (fix_add_2 p_2 q)~1
               | 1 => (Pos.succ p_2)~0
               end)
        with
        | @xI_R q_1 q_2 q_R => xO_R (add_carry_R p_1 p_2 p_R q_1 q_2 q_R)
        | @xO_R q_1 q_2 q_R => xI_R (add_R p_1 p_2 p_R q_1 q_2 q_R)
        | xH_R => xO_R (succ_R p_R)
        end
    | xH_R =>
        match
          y_R in (positive_R y_10 y_20)
          return
            (positive_R
               match y_10 with
               | q~1 => (Pos.succ q)~1
               | q~0 => (Pos.succ q)~0
               | 1 => 3
               end
               match y_20 with
               | q~1 => (Pos.succ q)~1
               | q~0 => (Pos.succ q)~0
               | 1 => 3
               end)
        with
        | @xI_R q_1 q_2 q_R => xI_R (succ_R q_R)
        | @xO_R q_1 q_2 q_R => xO_R (succ_R q_R)
        | xH_R => xI_R xH_R
        end
    end
  for
  add_R)%positive.
Elpi derive.param2.register Pos.add add_R.
Elpi derive.param2 Pos.pred_double.
Elpi derive.param2 Pos.compare_cont.
Elpi derive.param2 Pos.compare.

Elpi derive.param2 Z.double.
Elpi derive.param2 Z.succ_double.
Elpi derive.param2 Z.pred_double.
Elpi derive.param2 Z.pos_sub.

Elpi derive.param2 Peq.
Elpi derive.param2 P0.
Elpi derive.param2 mkPinj.
Elpi derive.param2 mkPX.

Elpi derive.param2 Popp.
Elpi derive.param2 PaddC.
Elpi derive.param2 PaddI.
Elpi derive.param2 PaddX.
Elpi derive.param2 Padd.
Elpi derive.param2 PsubC.
Elpi derive.param2 PsubI.
Elpi derive.param2 PsubX.
Elpi derive.param2 Psub.
Elpi derive.param2 PmulC_aux.
Elpi derive.param2 PmulC.
Elpi derive.param2 PmulI.
Elpi derive.param2 Pmul.
Elpi derive.param2 Psquare.
Elpi derive.param2 Ppow_pos.

Section Pol_mpolyCA.

Context {C : Type} {A : comNzRingType} (rCA : C -> A -> Type).

Variable c0 : C.
Hypothesis r0 : rCA c0 0.
Variable c1 : C.
Hypothesis r1 : rCA c1 1.
Variable cadd : C -> C -> C.
Hypothesis radd :
  forall c a, rCA c a -> forall c' a', rCA c' a' -> rCA (cadd c c') (a + a').
Variable csub : C -> C -> C.
Hypothesis rsub :
  forall c a, rCA c a -> forall c' a', rCA c' a' -> rCA (csub c c') (a - a').
Variable copp : C -> C.
Hypothesis ropp : forall c a, rCA c a -> rCA (copp c) (- a).
Variable cmul : C -> C -> C.
Hypothesis rmul :
  forall c a, rCA c a -> forall c' a', rCA c' a' -> rCA (cmul c c') (a * a').
Variable ceqb : C -> C -> bool.
Hypothesis reqb :
  forall c a, rCA c a -> forall c' a', rCA c' a' -> ceqb c c' = (a == a').

Variant Pol_mpolyCA {n} (CP : Pol C) (p : {mpoly A[n]}) : Type :=
  mkPol_mpolyCA AP of Pol_R rCA CP AP & Pol_mpoly AP p.

Lemma Pol_mpolyCAN n CP (p : {mpoly A[n]}) : Pol_mpolyCA CP p ->
  Pol_mpolyCA (Popp copp CP) (- p).
Proof. by case=> AP /(Popp_R ropp)+ /Pol_mpolyN; apply: mkPol_mpolyCA. Qed.

Lemma reqb' c a (ca : rCA c a) c' a' (c'a' : rCA c' a') :
  bool_R (ceqb c c') (a == a').
Proof. by case: eqP (reqb ca c'a') => _ ->; [apply: true_R|apply: false_R]. Qed.

Lemma Pol_mpolyCAD n CP (p : {mpoly A[n]}) CP' p' :
    Pol_mpolyCA CP p -> Pol_mpolyCA CP' p' ->
  Pol_mpolyCA (Padd c0 cadd ceqb CP CP') (p + p').
Proof.
case=> [AP CPAP APp] [AP' CP'AP' AP'p'].
move: (Padd_R r0 radd reqb' CPAP CP'AP') (Pol_mpolyD APp AP'p').
exact: mkPol_mpolyCA.
Qed.

Lemma Pol_mpolyCAB n CP (p : {mpoly A[n]}) CP' p' :
    Pol_mpolyCA CP p -> Pol_mpolyCA CP' p' ->
  Pol_mpolyCA (Psub c0 cadd csub copp ceqb CP CP') (p - p').
Proof.
case=> [AP CPAP APp] [AP' CP'AP' AP'p'].
move: (Psub_R r0 radd rsub ropp reqb' CPAP CP'AP') (Pol_mpolyB APp AP'p').
exact: mkPol_mpolyCA.
Qed.

Lemma Pol_mpolyCAM n CP (p : {mpoly A[n]}) CP' p' :
    Pol_mpolyCA CP p -> Pol_mpolyCA CP' p' ->
  Pol_mpolyCA (Pmul c0 c1 cadd cmul ceqb CP CP') (p * p').
Proof.
case=> [AP CPAP APp] [AP' CP'AP' AP'p'].
move: (Pmul_R r0 r1 radd rmul reqb' CPAP CP'AP') (Pol_mpolyM APp AP'p').
exact: mkPol_mpolyCA.
Qed.

Lemma Pol_mpolyCA_square n CP (p : {mpoly A[n]}) : Pol_mpolyCA CP p ->
  Pol_mpolyCA (Psquare c0 c1 cadd cmul ceqb CP) (p * p).
Proof.
case=> AP /(Psquare_R r0 r1 radd rmul reqb')+ /Pol_mpoly_square.
exact: mkPol_mpolyCA.
Qed.

End Pol_mpolyCA.
