From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq path choice finset fintype finfun.
From mathcomp Require Import tuple bigop ssralg ssrint ssrnum.
From Corelib Require Import PosDef IntDef.
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section Computable.

(* Coefficients *)
Context (C : Type).

Inductive Pol : Type :=
  | Pc : C -> Pol
  | Pinj : positive -> Pol -> Pol
  | PX : Pol -> positive -> Pol -> Pol.

Context (zeroC oneC : C) (addC mulC : C -> C -> C) (oppC : C -> C).
Context (eqC : C -> C -> bool).

Definition P0 := Pc zeroC.
Definition P1 := Pc oneC.

Fixpoint eqPol (P P' : Pol) {struct P'} : bool :=
  match P, P' with
  | Pc c, Pc c' => eqC c c'
  | Pinj j Q, Pinj j' Q' => Pos.eqb j j' && eqPol Q Q'
  | PX P i Q, PX P' i' Q' => Pos.eqb i i' && eqPol Q Q'
  | _, _ => false
  end.

Definition mkPinj j P :=
  match P with
  | Pc _ => P
  | Pinj j' Q => Pinj (Pos.add j j') Q
  | _ => Pinj j P
  end.

Definition mkPinj_pred j P :=
  match j with
  | xH => P
  | xO j => Pinj (Pos.pred_double j) P
  | xI j => Pinj (xO j) P
  end.

Definition mkPX P i Q :=
  match P with
  | Pc c => if eqC c zeroC then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if eqPol Q' P0 then PX P' (Pos.add i' i) Q else PX P i Q
  end.

Definition mkXi i := PX P1 i P0.

Definition mkX := mkXi 1.

(** Polynomial operations *)

Fixpoint oppPol (P : Pol) : Pol :=
  match P with
  | Pc c => Pc (oppC c)
  | Pinj j Q => Pinj j (oppPol Q)
  | PX P i Q => PX (oppPol P) i (oppPol Q)
  end.

Fixpoint addPolC (P : Pol) (c : C) : Pol :=
  match P with
  | Pc c1 => Pc (addC c1 c)
  | Pinj j Q => Pinj j (addPolC Q c)
  | PX P i Q => PX P i (addPolC Q c)
  end.

Section PopI.
Variable Pop : Pol -> Pol -> Pol.
Variable Q : Pol.

(** [P + Pinj j Q], assuming [Pop . Q] is [. + Q] *)
Fixpoint addPolI (j : positive) P : Pol :=
  match P with
  | Pc c => mkPinj j (addPolC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
      | Z0 => mkPinj j (Pop Q' Q)
      | Zneg k => mkPinj j' (addPolI k Q')
      end
  | PX P i Q' =>
      match j with
      | xH => PX P i (Pop Q' Q)
      | xO j => PX P i (addPolI (Pos.pred_double j) Q')
      | xI j => PX P i (addPolI (xO j) Q')
      end
  end.

Variable P' : Pol.

(** [P + PX P' i' P0], assuming [Pop . P'] is [. + P'] *)
Fixpoint addPolX (i' : positive) P : Pol :=
  match P with
  | Pc c => PX P' i' P
  | Pinj j Q' =>
      match j with
      | xH =>  PX P' i' Q'
      | xO j => PX P' i' (Pinj (Pos.pred_double j) Q')
      | xI j => PX P' i' (Pinj (xO j) Q')
      end
  | PX P i Q' =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
      | Z0 => mkPX (Pop P P') i Q'
      | Zneg k => mkPX (addPolX k P) i Q'
      end
  end.

End PopI.

Fixpoint addPol P P' {struct P'} : Pol :=
  match P' with
  | Pc c' => addPolC P c'
  | Pinj j' Q' => addPolI addPol Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PX P' i' (addPolC Q' c)
      | Pinj j Q =>
          match j with
          | xH => PX P' i' (addPol Q Q')
          | xO j => PX P' i' (addPol (Pinj (Pos.pred_double j) Q) Q')
          | xI j => PX P' i' (addPol (Pinj (xO j) Q) Q')
          end
      | PX P i Q =>
          match Z.pos_sub i i' with
          | Zpos k => mkPX (addPol (PX P k P0) P') i' (addPol Q Q')
          | Z0 => mkPX (addPol P P') i (addPol Q Q')
          | Zneg k => mkPX (addPolX addPol P' k P) i (addPol Q Q')
          end
      end
  end.

(** Multiplication *)

Fixpoint mulPolC_aux P c : Pol :=
  match P with
  | Pc c' => Pc (mulC c' c)
  | Pinj j Q => mkPinj j (mulPolC_aux Q c)
  | PX P i Q => mkPX (mulPolC_aux P c) i (mulPolC_aux Q c)
  end.

Definition mulPolC P c :=
  if eqC c zeroC then P0 else
  if eqC c oneC then P else mulPolC_aux P c.

(** [P * Pinj j Q], assuming [mulPol . Q] is [. * Q] *)
Section mulPolI.
Context (mulPol : Pol -> Pol -> Pol) (Q : Pol).

Fixpoint mulPolI (j : positive) P : Pol :=
  match P with
  | Pc c => mkPinj j (mulPolC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinj j (mulPol (Pinj k Q') Q)
      | Z0 => mkPinj j (mulPol Q' Q)
      | Zneg k => mkPinj j' (mulPolI k Q')
      end
  | PX P' i' Q' =>
      match j with
      | xH => mkPX (mulPolI xH P') i' (mulPol Q' Q)
      | xO j' => mkPX (mulPolI j P') i' (mulPolI (Pos.pred_double j') Q')
      | xI j' => mkPX (mulPolI j P') i' (mulPolI (xO j') Q')
      end
   end.
End mulPolI.

Fixpoint mulPol P P'' {struct P''} : Pol :=
  match P'' with
  | Pc c => mulPolC P c
  | Pinj j' Q' => mulPolI mulPol Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => mulPolC P'' c
      | Pinj j Q =>
          let QQ' :=
            match j with
            | xH => mulPol Q Q'
            | xO j => mulPol (Pinj (Pos.pred_double j) Q) Q'
            | xI j => mulPol (Pinj (xO j) Q) Q'
            end in
          mkPX (mulPol P P') i' QQ'
      | PX P i Q =>
          let QQ' := mulPol Q Q' in
          let PQ' := mulPolI mulPol Q' xH P in
          let QP' := mulPol (mkPinj xH Q) P' in
          let PP' := mulPol P P' in
          addPol (mkPX (addPol (mkPX PP' i P0) QP') i' P0) (mkPX PQ' i QQ')
      end
  end.

Fixpoint Psquare P : Pol :=
  match P with
  | Pc c => Pc (mulC c c)
  | Pinj j Q => Pinj j (Psquare Q)
  | PX P i Q =>
      let twoPQ := mulPol P (mkPinj xH (mulPolC Q (addC oneC oneC))) in
      let Q2 := Psquare Q in
      let P2 := Psquare P in
      mkPX (addPol (mkPX P2 i P0) twoPQ) i Q2
  end.

Fixpoint Ppow_pos (res P : Pol) (p : positive) : Pol :=
  match p with
  | xH => mulPol res P
  | xO p => Ppow_pos (Ppow_pos res P p) P p
  | xI p => mulPol (Ppow_pos (Ppow_pos res P p) P p) P
  end.

Definition Ppow_N P n := match n with N0 => P1 | Npos p => Ppow_pos P1 P p end.

(* Pol to a ring *)

Section phiPolSemiring.

Local Open Scope ring_scope.

Context (R : pzSemiRingType) (phiC : C -> R).
Context (phi_zeroC : phiC zeroC = 0%R).
Context (phi_oneC : phiC oneC = 1%R).
Context (phi_addC : forall x y, phiC (addC x y) = phiC x + phiC y).
Context (phi_mulC : forall x y, phiC (mulC x y) = phiC x * phiC y).

Fixpoint phiPol (l : positive -> R) (P : Pol) : R :=
  match P with
  | Pc c => phiC c
  | Pinj j Q => phiPol (fun i => l (Pos.add i j)) Q
  | PX P i Q =>
    phiPol l P * (l xH ^+ Pos.to_nat i) + phiPol (fun i => l (Pos.succ i)) Q
  end.

(* https://github.com/rocq-prover/stdlib/blob/0543892eea4b4eba4b809dea353b89a08910d222/theories/setoid_ring/Ring_polynom.v#L124 *)
Lemma PaddC_ok c P l : phiPol l (addPolC P c) = phiPol l P + phiC c.
Proof.
Abort.

Lemma PmulC_aux_ok c P l : phiPol l (mulPolC_aux P c) = phiPol l P * phiC c.
Proof.
Abort.

Lemma PmulC_ok c P l : phiPol l (mulPolC P c) = phiPol l P * phiC c.
Proof.
Abort.

Lemma PaddX_ok P' P k l :
  (forall P l, phiPol l (addPol P P') = phiPol l P + phiPol l P') ->
  phiPol l (addPolX addPol P' k P) =
    phiPol l P + phiPol l P' * (l xH) ^+ Pos.to_nat k.
Proof.
Abort.

Lemma Padd_ok P' P l : phiPol l (addPol P P') = phiPol l P + phiPol l P'.
Proof.
Abort.

Lemma PmulI_ok P' :
  (forall P l, phiPol l (mulPol P P') = phiPol l P * phiPol l P') ->
  forall P p l, phiPol l (mulPolI mulPol P' p P) =
                  phiPol l P * phiPol (fun i => l (Pos.succ i)) P'.
Proof.
Abort.

Lemma Pmul_ok P P' l : phiPol l (mulPol P P') = phiPol l P * phiPol l P'.
Proof.
Abort.

End phiPolSemiring.

Section phiPolRing.

Local Open Scope ring_scope.

Context (R : pzRingType) (phiC : C -> R).
Context (phi_oppC : forall x, phiC (oppC x) = - phiC x).

Lemma Popp_ok P l : phiPol phiC l (oppPol P) = - phiPol phiC l P.
Proof.
elim: P l => [c|i p IHp|p IHp i q IHq] l /=.
- by rewrite phi_oppC.
- by rewrite IHp.
- by rewrite IHp IHq opprD mulNr.
Qed.

End phiPolRing.

End Computable.
