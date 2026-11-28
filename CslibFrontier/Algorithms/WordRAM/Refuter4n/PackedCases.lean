/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedAffineRep

/-!
# Packed Cases 3 and 4 of the `4n - 9d` refuter

Cases 3 (partners sharing a child) and 4 (a paired parameter in the affine system) of the refuter
`applyStep` (`Cslib.Circuits.Boolean.AffineDisperser4n`) on the packed state `PackedState`. This
is part of the pure layer of the step programs of issue `#4322` (Milestone 4); no program and no
running time is claimed here.

The operation of a gate as a function of the two members of a pair is read off the truth table of
its row (`rowPhi`, `rowPhi_rowOf`). Case 4 ends with the packed unit deletion `pUnitDelete`,
whose correctness needs a well-formed state; the intermediate state is valid by
`Valid.step_pairInSystem_of`, under the hypotheses of that lemma.

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.rowPhi`: the operation of a gate row as a function of the
  values of `t` and of the other argument.
* `Cslib.Algorithms.WordRAM.Refuter4n.pPartnersShareChildStep`, `pPartnersShareChild`:
  `State.partnersShareChildStep` and the `.partnersShareChild` step on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pPairInSystem`: the `.pairInSystem` step on the packed
  state.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.rowPhi_rowOf`: `rowPhi` is the function `φ` of
  `State.partnersShareChildStep`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.applyStep_partnersShareChild`,
  `Rep.applyStep_pairInSystem`: the packed Cases 3 and 4 represent `applyStep`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Finset
open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.AffineDisperserCore Cslib.Circuits.Boolean.SemiCircuit

variable {n : ℕ}

/-- The operation of the gate row `r` with every argument equal to `node t` replaced by `a` and
every other argument by `b`. -/
@[expose] def rowPhi (r : GateRow) (t : ℕ) (a b : Bool) : Bool :=
  r.tt.testBit (idx (if r.left = t + 2 then a else b) (if r.right = t + 2 then a else b))

/-- `rowPhi` of the row of a gate. -/
theorem rowPhi_rowOf (g : Gate) (t : ℕ) (a b : Bool) :
    rowPhi (rowOf g) t a b =
      g.op (if g.left = .node t then a else b) (if g.right = .node t then a else b) := by
  simp only [rowPhi, rowOf, argCode_eq_node, testBit_ttOf]

/-- `State.partnersShareChildStep` on the packed state, for the pair `pr` and the shared child
`H`. -/
@[expose] def pPartnersShareChildStep (N : ℕ) (pr : ZeroPair) (P : PackedState) :
    ℕ ⊕ ℕ → PackedState
  | .inl G =>
    if rowPhi (P.gateRows.getD G ⟨0, 0, 0⟩) pr.fst pr.fstBias false =
        rowPhi (P.gateRows.getD G ⟨0, 0, 0⟩) pr.fst pr.fstBias true then
      (P.restrictAvoid N pr.fst pr.fstBias.toNat 0).deleteGate N G
        (rowPhi (P.gateRows.getD G ⟨0, 0, 0⟩) pr.fst pr.fstBias pr.sndBias).toNat 0
    else if rowPhi (P.gateRows.getD G ⟨0, 0, 0⟩) pr.fst false pr.sndBias =
        rowPhi (P.gateRows.getD G ⟨0, 0, 0⟩) pr.fst true pr.sndBias then
      (P.restrictAvoid N pr.snd pr.sndBias.toNat 0).deleteGate N G
        (rowPhi (P.gateRows.getD G ⟨0, 0, 0⟩) pr.fst pr.fstBias pr.sndBias).toNat 0
    else
      (P.restrictAvoid N pr.fst (pr.snd + 2) (!(pr.fstBias ^^ pr.sndBias)).toNat).deleteGate N G
        (rowPhi (P.gateRows.getD G ⟨0, 0, 0⟩) pr.fst pr.fstBias (!pr.sndBias)).toNat 0
  | .inr e =>
    pDeleteConstraint N
      (P.restrictAvoid N pr.fst (pr.snd + 2) (!(pr.fstBias ^^ pr.sndBias)).toNat) (.inr e)

/-- Case 3, the first member `p` of a pair whose members share a child (`applyStep` of
`.partnersShareChild p`): the packed `partnersShareChildStep` at the pair of `p` and the first
child of `p`, if both exist. -/
@[expose] def pPartnersShareChild (N E p : ℕ) (P : PackedState) : PackedState :=
  match pFindPair N p P, pGetChildren N E p P with
  | some pr, H :: _ => pPartnersShareChildStep N pr P H
  | _, _ => P

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- **Case 3.** On a valid represented state, for a parameter `p` below `N`, the packed Case 3
represents `applyStep` of `.partnersShareChild p`. -/
theorem applyStep_partnersShareChild (h : Rep N E P S) (hS : S.Valid f) {p : ℕ} (hp : p < N) :
    Rep N E (pPartnersShareChild N E p P) (applyStep S (.partnersShareChild p)) := by
  have hB := h.bounded hS
  unfold pPartnersShareChild
  rw [h.pFindPair_eq, h.pGetChildren_eq hp]
  simp only [applyStep]
  rcases hf : findPair S p with _ | pr <;> rcases hc : getChildren S p with _ | ⟨H, rest⟩
  · exact h
  · exact h
  · exact h
  obtain ⟨hmem, -⟩ := findPair_spec hf
  obtain ⟨h₁, h₂⟩ := h.pairs_lt hS hmem
  have hH : H ∈ S.children p := mem_getChildren.1 (by rw [hc]; simp)
  have hℓ : ∀ y, (⟨.node pr.snd, !(pr.fstBias ^^ pr.sndBias)⟩ : Lit).Reads y → y < N :=
    fun y hy => by
      have : y = pr.snd := by simpa [Lit.Reads] using hy.symm
      exact this ▸ h₂
  have hc0 : ∀ c : Bool, ∀ y, (Lit.const c).Reads y → y < N := fun _ y hy =>
    absurd hy (by simp [Lit.Reads, Lit.const])
  rcases H with G | e
  · have hG : G ∈ S.gates := ((inl_mem_children _).1 hH).1
    have hGN : G < N := Finset.mem_range.1 (h.names (by simp [nameSet, hG]))
    simp only [pPartnersShareChildStep,
      Cslib.Circuits.Boolean.AffineDisperser4n.State.partnersShareChildStep, h.gateRow G hG,
      rowPhi_rowOf]
    -- `split_ifs` also splits the argument tests inside `φ`; each goal is one of the three cases.
    split_ifs <;> first
      | exact (h.fixConst hB h₁ pr.fstBias).deleteGate (hB.restrict _ (hc0 _) _) hGN
          (ℓ := Lit.const _) (hc0 _)
      | exact (h.fixConst hB h₂ pr.sndBias).deleteGate (hB.restrict _ (hc0 _) _) hGN
          (ℓ := Lit.const _) (hc0 _)
      | exact (h.restrictAvoid hB h₁ hℓ).deleteGate (hB.restrict _ hℓ _) hGN
          (ℓ := Lit.const _) (hc0 _)
  · have he : e ∈ S.eqns := ((inr_mem_children _).1 hH).1
    exact (h.restrictAvoid hB h₁ hℓ).pDeleteConstraint (hB.restrict _ hℓ _) (c := .inr e) he

end Rep

/-! ### Case 4 -/

/-- Case 4, a paired parameter `p` whose first child is an equation `e` (`applyStep` of
`.pairInSystem p`): fix the partner of `p` to its bias, delete the first child of the partner, and
unit-delete `p` through `e` if `p` still has a child. -/
@[expose] def pPairInSystem (N E p : ℕ) (P : PackedState) : PackedState :=
  match pFindPair N p P with
  | some pr =>
    match pGetChildren N E (pr.partner p) P, pGetChildren N E p P with
    | Hr :: _, .inr e :: _ =>
      if (pGetChildren N E p (pDeleteConstraint N
          (P.restrictAvoid N (pr.partner p) (pr.partnerBias p).toNat 0) Hr)).length = 0 then
        pDeleteConstraint N (P.restrictAvoid N (pr.partner p) (pr.partnerBias p).toNat 0) Hr
      else
        pUnitDelete N E p e
          (pDeleteConstraint N (P.restrictAvoid N (pr.partner p) (pr.partnerBias p).toNat 0) Hr)
    | _, _ => P
  | none => P

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- **Case 4.** On a valid represented state with no degenerate pair and no partners sharing a
child, for a parameter `p` below `N` not read by the output, the packed Case 4 represents
`applyStep` of `.pairInSystem p`. The intermediate state is valid by
`Valid.step_pairInSystem_of`, which the packed unit deletion needs. -/
theorem applyStep_pairInSystem (h : Rep N E P S) (hS : S.Valid f) (hndeg : ¬ S.DegeneratePair)
    (hnsh : ¬ S.PartnersShareChild) {p : ℕ} (hp : p < N) (hout : ¬ S.out.Reads p) :
    Rep N E (pPairInSystem N E p P) (applyStep S (.pairInSystem p)) := by
  have hB := h.bounded hS
  unfold pPairInSystem
  rw [h.pFindPair_eq]
  simp only [applyStep]
  rcases hf : findPair S p with _ | pr
  · exact h
  obtain ⟨hmem, hcont⟩ := findPair_spec hf
  obtain ⟨h₁, h₂⟩ := h.pairs_lt hS hmem
  have hrN : pr.partner p < N := by unfold ZeroPair.partner; split_ifs <;> assumption
  dsimp only
  rw [h.pGetChildren_eq hrN, h.pGetChildren_eq hp]
  rcases hc₁ : getChildren S (pr.partner p) with _ | ⟨Hr, l₁⟩ <;>
    rcases hc₂ : getChildren S p with _ | ⟨_ | e, l₂⟩
  · exact h
  · exact h
  · exact h
  · exact h
  · exact h
  have hHr : Hr ∈ S.children (pr.partner p) := mem_getChildren.1 (by rw [hc₁]; simp)
  have hep : (.inr e : ℕ ⊕ ℕ) ∈ S.children p := mem_getChildren.1 (by rw [hc₂]; simp)
  obtain ⟨he, hpe⟩ := (inr_mem_children _).1 hep
  have hstep := Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.step_pairInSystem_of hS hndeg
    hnsh hmem hcont he hpe hout hHr
  obtain ⟨hS₂, -⟩ := hstep
  have hB₁ : Bounded N (S.fixConst (pr.partner p) (pr.partnerBias p)) :=
    hB.restrict _ (ℓ := Lit.const (pr.partnerBias p))
      (fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])) _
  have hm : Hr.elim (· ∈ (S.fixConst (pr.partner p) (pr.partnerBias p)).gates)
      (· ∈ (S.fixConst (pr.partner p) (pr.partnerBias p)).eqns) := by
    rcases Hr with J | e'
    · exact ((inl_mem_children _).1 hHr).1
    · exact ((inr_mem_children _).1 hHr).1
  have h₂' := (h.fixConst hB hrN (pr.partnerBias p)).pDeleteConstraint hB₁ hm
  dsimp only
  rw [h₂'.length_pGetChildren hp]
  split_ifs
  · exact h₂'
  · exact h₂'.unitDelete (h₂'.bounded hS₂) hS₂.wf hp e

end Rep

end Cslib.Algorithms.WordRAM.Refuter4n
