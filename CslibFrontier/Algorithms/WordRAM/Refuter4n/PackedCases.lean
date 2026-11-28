/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedAffineRep

/-!
# Packed Cases 3, 4 and 5a of the `4n - 9d` refuter

Cases 3 (partners sharing a child), 4 (a paired parameter in the affine system) and 5a (a
non-affine gate on a paired parameter) of the refuter `applyStep`
(`Cslib.Circuits.Boolean.AffineDisperser4n`) on the packed state `PackedState`. This is part of the
pure layer of the step programs of issue `#4322` (Milestone 4); no program and no running time is
claimed here.

The operation of a gate as a function of the two members of a pair is read off the truth table of
its row (`rowPhi`, `rowPhi_rowOf`). Case 4 ends with the packed unit deletion `pUnitDelete`,
whose correctness needs a well-formed state; the intermediate state is valid by
`Valid.step_pairInSystem_of`, under the hypotheses of that lemma. Case 5a is split into the
packed successor `pAndOnPairStep`, which represents `State.andOnPairStep` whenever the constraints
it deletes are constraints at that point (`Rep.andOnPairStep`), and the packed searches for its
arguments, which compute the arguments of `applyStep` (`Rep.pAndOnPair_eq`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.rowPhi`: the operation of a gate row as a function of the
  values of `t` and of the other argument.
* `Cslib.Algorithms.WordRAM.Refuter4n.pPartnersShareChildStep`, `pPartnersShareChild`:
  `State.partnersShareChildStep` and the `.partnersShareChild` step on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pPairInSystem`: the `.pairInSystem` step on the packed
  state.
* `Cslib.Algorithms.WordRAM.Refuter4n.rowOtherArg`, `rowFixArg`: `otherArg` and `fixArg` on a
  gate row.
* `Cslib.Algorithms.WordRAM.Refuter4n.pAndOnPairStep`, `pAndOnPair`: `State.andOnPairStep` and
  the `.andOnPair` step on the packed state.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.rowPhi_rowOf`: `rowPhi` is the function `φ` of
  `State.partnersShareChildStep`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.applyStep_partnersShareChild`,
  `Rep.applyStep_pairInSystem`: the packed Cases 3 and 4 represent `applyStep`.
* `Cslib.Algorithms.WordRAM.Refuter4n.rowOtherArg_rowOf`, `rowFixArg_rowOf`: the row versions
  are `otherArg` and `fixArg`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.andOnPairStep`, `Rep.pAndOnPair_eq`: the packed Case 5a
  successor and its arguments.
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
  have hrN : pr.partner p < N := h.partner_lt hS hmem p
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
    have hm₀ := elim_mem_of_mem_children hHr
    rcases Hr with J | e' <;> exact hm₀
  have h₂' := (h.fixConst hB hrN (pr.partnerBias p)).pDeleteConstraint hB₁ hm
  dsimp only
  rw [h₂'.length_pGetChildren hp]
  split_ifs
  · exact h₂'
  · exact h₂'.unitDelete (h₂'.bounded hS₂) hS₂.wf hp e

end Rep

/-! ### Case 5a -/

/-- `otherArg` on a gate row: the argument other than `p` when both arguments are names, and `p`
otherwise. -/
@[expose] def rowOtherArg (r : GateRow) (p : ℕ) : ℕ :=
  if 2 ≤ r.left ∧ 2 ≤ r.right then (if r.left = p + 2 then r.right - 2 else r.left - 2) else p

/-- `rowOtherArg` is `otherArg`. -/
theorem rowOtherArg_rowOf (g : Gate) (p : ℕ) : rowOtherArg (rowOf g) p = otherArg g p := by
  obtain ⟨op, l, r⟩ := g
  cases l with
  | const b =>
    have : ¬ 2 ≤ b.toNat := by have := Bool.toNat_le b; omega
    simp [rowOtherArg, otherArg, rowOf, argCode, this]
  | node u =>
    cases r with
    | const b =>
      have : ¬ 2 ≤ b.toNat := by have := Bool.toNat_le b; omega
      simp [rowOtherArg, otherArg, rowOf, argCode, this]
    | node v =>
      by_cases hu : u = p <;> simp [rowOtherArg, otherArg, rowOf, argCode, hu]

/-- `fixArg` on a gate row: a value of the argument `w` making the gate constant, with that
constant, read off the truth table. -/
@[expose] def rowFixArg (r : GateRow) (w : ℕ) : Bool × Bool :=
  if r.right = w + 2 then
    (!decide (r.tt.testBit (idx false false) = r.tt.testBit (idx true false)),
      r.tt.testBit (idx false
        (!decide (r.tt.testBit (idx false false) = r.tt.testBit (idx true false)))))
  else
    (!decide (r.tt.testBit (idx false false) = r.tt.testBit (idx false true)),
      r.tt.testBit (idx
        (!decide (r.tt.testBit (idx false false) = r.tt.testBit (idx false true))) false))

/-- `rowFixArg` is `fixArg`. -/
theorem rowFixArg_rowOf (g : Gate) (w : ℕ) : rowFixArg (rowOf g) w = fixArg g w := by
  simp only [rowFixArg, fixArg, rowOf, argCode_eq_node, testBit_ttOf]

/-- `State.andOnPairStep` on the packed state, with the same arguments. -/
@[expose] def pAndOnPairStep (N G : ℕ) (pr : ZeroPair) (p w : ℕ) (prw : Option ZeroPair)
    (b c : Bool) (Hr : ℕ ⊕ ℕ) (K : ℕ) (Hw' : ℕ ⊕ ℕ) (P : PackedState) : PackedState :=
  match prw with
  | some q =>
    if b = q.bias w then
      pDeleteConstraint N (((P.restrictAvoid N (pr.partner p) (pr.partnerBias p).toNat 0)
        |>.restrictAvoid N w b.toNat 0).deleteGate N G c.toNat 0) Hr
    else
      pDeleteConstraint N (pDeleteConstraint N
        ((((P.restrictAvoid N (pr.partner p) (pr.partnerBias p).toNat 0)
          |>.restrictAvoid N (q.partner w) (q.partnerBias w).toNat 0)
          |>.restrictAvoid N w b.toNat 0).deleteGate N G c.toNat 0) (.inl K))
        (if Hr = .inl K then Hw' else Hr)
  | none =>
    pDeleteConstraint N (((P.restrictAvoid N (pr.partner p) (pr.partnerBias p).toNat 0)
      |>.restrictAvoid N w b.toNat 0).deleteGate N G c.toNat 0) Hr

/-- Case 5a, the non-affine gate `G` reading the paired parameter `p` (`applyStep` of
`.andOnPair G p`): `pAndOnPairStep` with the arguments of `applyStep` computed on the packed
state, if `p` is paired and its partner has a child. -/
@[expose] def pAndOnPair (N E G p : ℕ) (P : PackedState) : PackedState :=
  match pFindPair N p P with
  | some pr =>
    match pGetChildren N E (pr.partner p) P with
    | Hr :: _ =>
      let w := rowOtherArg (P.gateRows.getD G ⟨0, 0, 0⟩) p
      pAndOnPairStep N G pr p w (pFindPair N w P)
        (rowFixArg (P.gateRows.getD G ⟨0, 0, 0⟩) w).1
        (rowFixArg (P.gateRows.getD G ⟨0, 0, 0⟩) w).2 Hr ((pFindReader N G P).getD 0)
        (match pFindPair N w P with
          | some q => (pGetChildren N E (q.partner w) P).headD Hr
          | none => Hr) P
    | [] => P
  | none => P

private theorem bounded_fixConst {N : ℕ} {S : State n} (hB : Bounded N S) (w : ℕ) (b : Bool) :
    Bounded N (S.fixConst w b) :=
  hB.restrict w (ℓ := Lit.const b) (fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])) _

/-- A constraint other than the gate `G` survives deleting `G`. -/
private theorem elim_mem_deleteGate {S : State n} {c : ℕ ⊕ ℕ} {G : ℕ} {ℓ : Lit}
    (hne : c ≠ .inl G) (hc : c.elim (· ∈ S.gates) (· ∈ S.eqns)) :
    c.elim (· ∈ (S.deleteGate G ℓ).gates) (· ∈ (S.deleteGate G ℓ).eqns) := by
  rcases c with J | e
  · exact Finset.mem_erase.2 ⟨fun h => hne (congrArg Sum.inl h), hc⟩
  · exact hc

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- **The Case 5a successor.** On a valid represented state, the packed `andOnPairStep`
represents `State.andOnPairStep`, when every constraint it deletes is a constraint at that point:
`Hr` is a constraint other than `G`, and in the branch that also deletes the reader `K` of `G`,
`K` is a gate other than `G` and the last deleted constraint is neither `G` nor `K`. -/
theorem andOnPairStep (h : Rep N E P S) (hS : S.Valid f) {G : ℕ} (hG : G ∈ S.gates)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p w : ℕ} (hw : w < N) {prw : Option ZeroPair}
    (hprw : ∀ q, prw = some q → q ∈ S.pairs) (b c : Bool) {Hr : ℕ ⊕ ℕ}
    (hHr : Hr.elim (· ∈ S.gates) (· ∈ S.eqns)) (hHrG : Hr ≠ .inl G) {K : ℕ} {Hw' : ℕ ⊕ ℕ}
    (hK : ∀ q, prw = some q → b ≠ q.bias w → K ∈ S.gates ∧ K ≠ G ∧
      (Hr = .inl K → Hw'.elim (· ∈ S.gates) (· ∈ S.eqns) ∧ Hw' ≠ .inl G ∧ Hw' ≠ .inl K)) :
    Rep N E (pAndOnPairStep N G pr p w prw b c Hr K Hw' P)
      (S.andOnPairStep G pr p w prw b c Hr K Hw') := by
  have hB := h.bounded hS
  have hGN : G < N := Finset.mem_range.1 (h.names (by simp [nameSet, hG]))
  have hc0 : ∀ c : Bool, ∀ y, (Lit.const c).Reads y → y < N := fun _ y hy =>
    absurd hy (by simp [Lit.Reads, Lit.const])
  have hpart : ∀ {q : ZeroPair}, q ∈ S.pairs → ∀ x, q.partner x < N := fun hq x =>
    h.partner_lt hS hq x
  have h₁ := h.fixConst hB (hpart hpr p) (pr.partnerBias p)
  have hB₁ := bounded_fixConst hB (pr.partner p) (pr.partnerBias p)
  unfold pAndOnPairStep Cslib.Circuits.Boolean.AffineDisperser4n.State.andOnPairStep
  rcases prw with _ | q
  · dsimp only
    have hB₂ := bounded_fixConst hB₁ w b
    exact ((h₁.fixConst hB₁ hw b).deleteGate hB₂ hGN (ℓ := Lit.const c)
      (hc0 c)).pDeleteConstraint (hB₂.deleteGate G (hc0 c)) (elim_mem_deleteGate hHrG hHr)
  · have hq := hprw q rfl
    dsimp only
    by_cases hb : b = q.bias w
    · rw [ite_eq_left hb, ite_eq_left hb]
      have hB₂ := bounded_fixConst hB₁ w b
      exact ((h₁.fixConst hB₁ hw b).deleteGate hB₂ hGN (ℓ := Lit.const c)
        (hc0 c)).pDeleteConstraint (hB₂.deleteGate G (hc0 c)) (elim_mem_deleteGate hHrG hHr)
    · rw [ite_eq_right hb, ite_eq_right hb]
      obtain ⟨hKm, hKG, hHw⟩ := hK q rfl hb
      have hB₂ := bounded_fixConst hB₁ (q.partner w) (q.partnerBias w)
      have hB₃ := bounded_fixConst hB₂ w b
      have hB₄ := hB₃.deleteGate G (hc0 c)
      have h₄ := ((h₁.fixConst hB₁ (hpart hq w) _).fixConst hB₂ hw b).deleteGate hB₃ hGN
        (ℓ := Lit.const c) (hc0 c)
      set S₄ := (((S.fixConst (pr.partner p) (pr.partnerBias p)).fixConst (q.partner w)
        (q.partnerBias w)).fixConst w b).deleteGate G (Lit.const c) with hS₄
      have hKmem : (Sum.inl K : ℕ ⊕ ℕ).elim (· ∈ S₄.gates) (· ∈ S₄.eqns) :=
        elim_mem_deleteGate (c := .inl K) (fun he => hKG (Sum.inl.inj he)) hKm
      have h₅ := h₄.pDeleteConstraint hB₄ hKmem
      by_cases hHK : Hr = .inl K
      · rw [ite_eq_left hHK]
        obtain ⟨hHw'm, hHw'G, hHw'K⟩ := hHw hHK
        exact h₅.pDeleteConstraint (hB₄.deleteConstraint hKmem)
          (elim_mem_deleteConstraint hHw'K (elim_mem_deleteGate hHw'G hHw'm))
      · rw [ite_eq_right hHK]
        exact h₅.pDeleteConstraint (hB₄.deleteConstraint hKmem)
          (elim_mem_deleteConstraint hHK (elim_mem_deleteGate hHrG hHr))

/-- The packed Case 5a is `pAndOnPairStep` at the arguments that `applyStep` computes. -/
theorem pAndOnPair_eq (h : Rep N E P S) (hS : S.Valid f) {G : ℕ} (hG : G ∈ S.gates) (p : ℕ) :
    pAndOnPair N E G p P =
      match findPair S p with
      | some pr =>
        match getChildren S (pr.partner p) with
        | Hr :: _ =>
          pAndOnPairStep N G pr p (otherArg (S.gate G) p) (findPair S (otherArg (S.gate G) p))
            (fixArg (S.gate G) (otherArg (S.gate G) p)).1
            (fixArg (S.gate G) (otherArg (S.gate G) p)).2 Hr
            (((S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G ∧ (S.gate K).Reads G))).getD 0)
            (match findPair S (otherArg (S.gate G) p) with
              | some q => (getChildren S (q.partner (otherArg (S.gate G) p))).headD Hr
              | none => Hr) P
        | [] => P
      | none => P := by
  have hpart : ∀ {q : ZeroPair}, q ∈ S.pairs → ∀ x, q.partner x < N := fun hq x =>
    h.partner_lt hS hq x
  unfold pAndOnPair
  simp only [h.pFindPair_eq, h.gateRow G hG, rowOtherArg_rowOf, rowFixArg_rowOf,
    h.pFindReader_eq]
  rcases hf : findPair S p with _ | pr
  · rfl
  · obtain ⟨hmem, -⟩ := findPair_spec hf
    dsimp only
    rw [h.pGetChildren_eq (hpart hmem p)]
    rcases getChildren S (pr.partner p) with _ | ⟨Hr, l⟩
    · rfl
    · dsimp only
      rcases hq : findPair S (otherArg (S.gate G) p) with _ | q
      · rfl
      · obtain ⟨hqm, -⟩ := findPair_spec hq
        dsimp only
        rw [h.pGetChildren_eq (hpart hqm _)]

end Rep

end Cslib.Algorithms.WordRAM.Refuter4n
