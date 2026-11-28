/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedStep
public meta import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedStep

/-!
# Tests for the packed operations and steps of the `4n - 9d` refuter

`deleteGate` and `moveAffine` are run on two small circuits at the first step the refuter takes
there, and `restrictAvoid` on fixing a parameter of `xor3Circuit`; the
touched masks, gate rows, equation words and output are compared with the encodings of the
state operations, and the rows of the parameter map by evaluation. The packed steps
(`pDeleteConstraint`, `pFreshEqn`) are checked on masks, the output and the alive flags.
-/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.Refuter4nPackedOps

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.AffineDisperser4n Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Algorithms.WordRAM.Refuter4n

/-- One XOR gate on `3` bits (gate name `3`). -/
def xor3Circuit : Circuit (fullSignature 2 Bool) 3 1 :=
  ⟨Program.gate Program.empty
    ⟨FullOp.fn fun xs => xs 0 ^^ xs 1,
      fun i => if _ : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

/-- Two gates on `2` bits: `g₀ = x₀ ∧ x₁` (name `2`) and the degenerate `g₁ = g₀ ∨ g₀`
(name `3`). -/
def degCircuit : Circuit (fullSignature 2 Bool) 2 1 :=
  let p1 := (Program.empty : Program (fullSignature 2 Bool) 2 0).gate ⟨FullOp.fn fun xs =>
    xs 0 && xs 1,
    fun i => if _ : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩
  let p2 := p1.gate ⟨FullOp.fn fun xs => xs 0 || xs 1, fun _ => Wire.gate ⟨0, by decide⟩⟩
  ⟨p2, fun _ => Wire.gate ⟨1, by decide⟩⟩

/-! Masks and truth tables: clearing bit `2` of `0b101`, setting bit `1`, and absorbing a negated
left input into `∧` (`(¬a) ∧ b` has table `0010₂ = 2`). -/

#guard clearBit 5 2 == 1
#guard clearBit 5 1 == 5
#guard setBit 5 1 == 7
#guard permTT (ttOf (· && ·)) (idx true false) == 2
#guard permTT (ttOf (· && ·)) (idx true false) == ttOf fun a b => (a ^^ true) && b

/-! `(D1)` on `degCircuit`: the refuter deletes the degenerate gate `3 = g₀ ∨ g₀`, rerouting it to
its literal `g₀`. The packed `deleteGate` leaves the gate mask, the row of the remaining gate `2`
and the output equal to the encodings of `applyStep`. -/

/-- The packed initial state of `degCircuit`. -/
def degP : PackedState := initialPacked degCircuit

/-- The literal of the degenerate gate `3`. -/
def degLit : Lit := ((initialState degCircuit).gate 3).lit

/-- The state after the first refuter step on `degCircuit`. -/
def degS₁ : State 2 := applyStep (initialState degCircuit) (.deleteConstantGate 3)

/-- The packed state after the first step. -/
def degP₁ : PackedState := degP.deleteGate 4 3 (argCode degLit.arg) degLit.neg.toNat

#guard match chooseStep? (initialState degCircuit) with
  | some (.deleteConstantGate 3) => true
  | _ => false
#guard degP₁.gates == maskOf degS₁.gates
#guard degP₁.gates == 4
#guard degP₁.out == litCode degS₁.out
#guard degP₁.gateRows.getD 2 ⟨0, 0, 0⟩ == rowOf (degS₁.gate 2)

/-! Moving the XOR gate of `xor3Circuit`: the refuter moves gate `3` into the affine system with
the fresh equation name `0`. The packed `moveAffine` writes the alive equation word
`x₀ + x₁ + x₃ = 0` (`0b10_1011 = 43` at `N = 4`) and moves `3` from the gate mask to the auxiliary
mask. -/

/-- The packed initial state of `xor3Circuit`. -/
def xorP : PackedState := initialPacked xor3Circuit

/-- The state after the first refuter step on `xor3Circuit`. -/
def xorS₁ : State 3 := applyStep (initialState xor3Circuit) (.moveAffine 3)

/-- The packed state after the first step. -/
def xorP₁ : PackedState := xorP.moveAffine 4 3 0

#guard match chooseStep? (initialState xor3Circuit) with
  | some (.moveAffine 3) => true
  | _ => false
#guard (initialState xor3Circuit).freshEqn == 0
#guard xorP₁.gates == maskOf xorS₁.gates
#guard xorP₁.aux == maskOf xorS₁.aux
#guard xorP₁.aux == 8
#guard xorP₁.eqnRows.getD 0 0 == eqnWord 4 (xorS₁.eqn 0) true
#guard xorP₁.eqnRows.getD 0 0 == 43
#guard (List.range 22).all fun e => (xorP₁.eqnRows.getD e 0).testBit 5 == decide (e ∈ xorS₁.eqns)

/-! Fixing the parameter `x₀ := true` in `xor3Circuit`: the gate row becomes the row of
`true ⊕ x₁` (left code `1`, table unchanged), the parameter mask loses bit `0`, and the rows of
the parameter map evaluate as `phi`. -/

/-- `x₀ := true` in the initial state of `xor3Circuit`. -/
def xorF : State 3 := (initialState xor3Circuit).fixConst 0 true

/-- The packed restriction. -/
def xorPF : PackedState := xorP.restrictAvoid 4 0 1 0

#guard xorPF.params == maskOf xorF.params
#guard xorPF.gateRows.getD 3 ⟨0, 0, 0⟩ == rowOf (xorF.gate 3)
#guard xorPF.out == litCode xorF.out
#guard (List.range 16).all fun v =>
  let val : ℕ → Bool := fun j => v.testBit j
  (List.finRange 3).all fun i => rowEval 4 (xorPF.phiRows.getD i 0) val == xorF.phi val i

/-! Rerouting in equation words: substituting `x₁ := ¬x₂` in `x₀ + x₁ = 1` gives
`x₀ + x₂ = 0`. -/

#guard substWord 1 (litWordOf 4 (argCode (.node 2)) 1) (eqnWord 4 ⟨{0, 1}, true⟩ true) ==
  eqnWord 4 (Equation.subst ⟨{0, 1}, true⟩ 1 ⟨.node 2, true⟩) true

/-! Packed steps: the `(D1)` step through `pDeleteConstraint` reads the literal of gate `3` from
its row and agrees with the `deleteGate` above; the fresh equation name is `0` before moving the
XOR gate and `1` after; deleting the moved equation `0` through its least auxiliary term `3`
agrees with `State.deleteConstraint`. -/

#guard rowLit (degP.gateRows.getD 3 ⟨0, 0, 0⟩) == (argCode degLit.arg, degLit.neg.toNat)
#guard (pDeleteConstraint 4 degP (.inl 3)).gates == maskOf degS₁.gates
#guard (pDeleteConstraint 4 degP (.inl 3)).out == litCode degS₁.out
#guard pFreshEqn 4 22 xorP == (initialState xor3Circuit).freshEqn
#guard pFreshEqn 4 22 xorP₁ == 1
#guard pFreshEqn 4 22 xorP₁ == xorS₁.freshEqn

/-- `State.deleteConstraint` of the moved equation `0`. -/
def xorS₂ : State 3 := xorS₁.deleteConstraint (.inr 0)

/-- The packed deletion of the moved equation `0`. -/
def xorP₂ : PackedState := pDeleteConstraint 4 xorP₁ (.inr 0)

#guard xorP₂.aux == maskOf xorS₂.aux
#guard xorP₂.out == litCode xorS₂.out
#guard (List.range 22).all fun e => (xorP₂.eqnRows.getD e 0).testBit 5 == decide (e ∈ xorS₂.eqns)

/-- Packed gate deletion represents gate deletion (module client of `Rep.deleteGate`). -/
example {n N E : ℕ} {P : PackedState} {S : State n} (h : Rep N E P S) {f : BooleanFunction n}
    (hS : S.Valid f) {J : ℕ} (hJ : J < N) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) :
    Rep N E (P.deleteGate N J (argCode ℓ.arg) ℓ.neg.toNat) (S.deleteGate J ℓ) :=
  h.deleteGate hS hJ hℓ

/-- Packed moving of an affine gate represents `State.moveAffine` (module client of
`Rep.moveAffine`). -/
example {n N E : ℕ} {P : PackedState} {S : State n} (h : Rep N E P S) {J : ℕ}
    (hJ : J ∈ S.gates) (he : S.freshEqn < E) :
    Rep N E (P.moveAffine N J S.freshEqn) (S.moveAffine J S.freshEqn) :=
  h.moveAffine hJ he

/-- Packed restriction represents fixing a parameter (module client of `Rep.fixConst`). -/
example {n N E : ℕ} {P : PackedState} {S : State n} (h : Rep N E P S) {f : BooleanFunction n}
    (hS : S.Valid f) {w : ℕ} (hw : w < N) (b : Bool) :
    Rep N E (P.restrictAvoid N w b.toNat 0) (S.fixConst w b) :=
  h.fixConst hS hw b

/-- The packed `(D3)` step represents `applyStep` (module client of
`Rep.applyStep_deleteShortEqn`). -/
example {n N E : ℕ} {P : PackedState} {S : State n} (h : Rep N E P S) {f : BooleanFunction n}
    (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns) :
    Rep N E (pDeleteConstraint N P (.inr e)) (applyStep S (.deleteShortEqn e)) :=
  h.applyStep_deleteShortEqn hS he

/-- The packed moving step represents `applyStep` (module client of
`Rep.applyStep_moveAffine`). -/
example {n N E : ℕ} {P : PackedState} {S : State n} (h : Rep N E P S) {J : ℕ}
    (hJ : J ∈ S.gates) (he : S.freshEqn < E) :
    Rep N E (P.moveAffine N J (pFreshEqn N E P)) (applyStep S (.moveAffine J)) :=
  h.applyStep_moveAffine hJ he

end CslibFrontierTests.Refuter4nPackedOps
