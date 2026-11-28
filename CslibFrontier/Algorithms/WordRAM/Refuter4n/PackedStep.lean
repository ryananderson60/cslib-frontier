/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedOps
import Mathlib.Data.List.GetD

/-!
# Packed steps of the `4n - 9d` refuter

Steps of the refuter `applyStep` (`Cslib.Circuits.Boolean.AffineDisperser4n`) on the packed state
`PackedState`, built from the packed primitive operations of `PackedOps`, and proved to represent
the state step (`Rep`). This is the pure layer of the step programs of issue `#4322`
(Milestone 4); no program and no running time is claimed here.

The searches of a step read only words. A least name with a property is the ascending scan of
`List.range N` (`find?_range_eq_min'`).

* **Literal of a degenerate gate.** `rowLit` computes the codes of `Gate.lit` from a gate row
  (`rowLit_rowOf`).
* **Deleting a constraint.** `pDeleteConstraint` deletes a gate through its literal, and an
  equation through its least auxiliary term and least other term, read off the equation word and
  the auxiliary mask (`Rep.pDeleteConstraint`).
* **Fresh equation name.** `pFreshEqn` scans the alive flags (`Rep.pFreshEqn_eq`).
* **Steps.** `(D1)`, `(D2)`, `(D3)` and moving an affine gate
  (`Rep.applyStep_deleteConstantGate`, `Rep.applyStep_deleteDeadGate`,
  `Rep.applyStep_deleteShortEqn`, `Rep.applyStep_moveAffine`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.rowLit`: the literal codes of a degenerate gate row.
* `Cslib.Algorithms.WordRAM.Refuter4n.pDeleteEqn`, `pDeleteConstraint`:
  `State.deleteConstraint` of an equation, and of a gate or an equation, on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pFreshEqn`: `State.freshEqn` on the packed state.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.find?_range_eq_min'`: the ascending scan finds the least
  element.
* `Cslib.Algorithms.WordRAM.Refuter4n.rowLit_rowOf`: `rowLit` is `Gate.lit`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pDeleteConstraint`: the packed deletion represents
  `State.deleteConstraint` of a gate or an equation of a valid state.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pFreshEqn_eq`: the packed fresh name is `freshEqn`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.applyStep_deleteConstantGate`,
  `Rep.applyStep_deleteDeadGate`, `Rep.applyStep_deleteShortEqn`, `Rep.applyStep_moveAffine`: the
  packed `(D1)`, `(D2)`, `(D3)` and moving steps represent `applyStep`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Finset
open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.AffineDisperserCore Cslib.Circuits.Boolean.SemiCircuit

variable {n : ℕ}

/-! ### Least names -/

/-- The ascending scan of `List.range N` finds the least element of a nonempty set of names
below `N`. -/
theorem find?_range_eq_min' {s : Finset ℕ} {N : ℕ} (hs : ∀ i ∈ s, i < N) (h : s.Nonempty) :
    (List.range N).find? (fun i => decide (i ∈ s)) = some (s.min' h) :=
  List.find?_range_eq_some.2 ⟨by simpa using s.min'_mem h,
    List.mem_range.2 (hs _ (s.min'_mem h)), fun j hj => by
      simpa using fun hjs => absurd (s.min'_le j hjs) (by omega)⟩

private theorem find?_range_eq_none_of_empty {s : Finset ℕ} {N : ℕ} (h : ¬ s.Nonempty) :
    (List.range N).find? (fun i => decide (i ∈ s)) = none :=
  List.find?_range_eq_none.2 fun i _ => by
    simpa using fun hi => h ⟨i, hi⟩

/-! ### The literal of a degenerate gate row -/

/-- The literal codes `(argCode, neg)` of `Gate.lit` computed from a gate row. -/
@[expose] def rowLit (r : GateRow) : ℕ × ℕ :=
  if r.left < 2 then
    let b := decide (r.left = 1)
    if r.tt.testBit (idx b false) = r.tt.testBit (idx b true) then
      ((r.tt.testBit (idx b false)).toNat, 0)
    else (r.right, (r.tt.testBit (idx b false)).toNat)
  else if r.right < 2 then
    let b := decide (r.right = 1)
    if r.tt.testBit (idx false b) = r.tt.testBit (idx true b) then
      ((r.tt.testBit (idx false b)).toNat, 0)
    else (r.left, (r.tt.testBit (idx false b)).toNat)
  else if r.tt.testBit (idx false false) = r.tt.testBit (idx true true) then
    ((r.tt.testBit (idx false false)).toNat, 0)
  else (r.left, (r.tt.testBit (idx false false)).toNat)

/-- `rowLit` computes the codes of `Gate.lit`. -/
theorem rowLit_rowOf (g : Gate) : rowLit (rowOf g) = (argCode g.lit.arg, g.lit.neg.toNat) := by
  obtain ⟨op, l, r⟩ := g
  have key : ∀ a b, (ttOf op).testBit (idx a b) = op a b := testBit_ttOf op
  cases l with
  | const b =>
    have hb : decide (b.toNat = 1) = b := by cases b <;> rfl
    have hb2 : b.toNat < 2 := by have := Bool.toNat_le b; omega
    simp only [rowLit, rowOf, argCode, hb2, ↓reduceIte, key, Gate.lit]
    split_ifs <;> simp_all [Lit.const]
  | node t =>
    have ht : ¬ t + 2 < 2 := by omega
    cases r with
    | const b =>
      have hb : decide (b.toNat = 1) = b := by cases b <;> rfl
      have hb2 : b.toNat < 2 := by have := Bool.toNat_le b; omega
      simp only [rowLit, rowOf, argCode, ht, hb2, ↓reduceIte, key, Gate.lit]
      split_ifs <;> simp_all [Lit.const]
    | node u =>
      have hu : ¬ u + 2 < 2 := by omega
      simp only [rowLit, rowOf, argCode, ht, hu, ↓reduceIte, key, Gate.lit]
      split_ifs <;> simp_all [Lit.const]

/-! ### Deleting a constraint -/

/-- `State.deleteConstraint` of the equation `e` on the packed state: delete `e` through its least
auxiliary term `v` and its least other term, or drop `e` if it has no auxiliary term. -/
@[expose] def pDeleteEqn (N e : ℕ) (P : PackedState) : PackedState :=
  match (List.range N).find? (fun i => (P.eqnRows.getD e 0).testBit i && P.aux.testBit i) with
  | some v =>
    match (List.range N).find? (fun i => (P.eqnRows.getD e 0).testBit i && i != v) with
    | some u => P.deleteEqn N e v (u + 2) ((P.eqnRows.getD e 0).testBit N).toNat
    | none => P.deleteEqn N e v ((P.eqnRows.getD e 0).testBit N).toNat 0
  | none => P.dropTrivialEqn e

/-- `State.deleteConstraint` on the packed state. -/
@[expose] def pDeleteConstraint (N : ℕ) (P : PackedState) : ℕ ⊕ ℕ → PackedState
  | .inl J => P.deleteGate N J (rowLit (P.gateRows.getD J ⟨0, 0, 0⟩)).1
      (rowLit (P.gateRows.getD J ⟨0, 0, 0⟩)).2
  | .inr e => pDeleteEqn N e P

/-! ### The fresh equation name -/

/-- `State.freshEqn` on the packed state: one more than the largest alive equation name below
`E`, or `0`. -/
@[expose] def pFreshEqn (N E : ℕ) (P : PackedState) : ℕ :=
  (List.range E).foldl (fun a e => if (P.eqnRows.getD e 0).testBit (N + 1) then e + 1 else a) 0

private theorem freshEqn_eq_sup (S : State n) : S.freshEqn = S.eqns.sup (· + 1) := by
  unfold State.freshEqn
  split_ifs with hne
  · apply le_antisymm
    · exact Finset.le_sup (f := (· + 1)) (S.eqns.max'_mem hne)
    · exact Finset.sup_le fun e he => by have := S.eqns.le_max' e he; omega
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sup_empty]
    rfl

private theorem foldl_alive (s : Finset ℕ) (alive : ℕ → Bool)
    (halive : ∀ e, alive e = decide (e ∈ s)) (k : ℕ) :
    (List.range k).foldl (fun a e => if alive e then e + 1 else a) 0 =
      (s.filter (· < k)).sup (· + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, halive]
    by_cases hk : k ∈ s
    · simp only [hk, decide_true, ↓reduceIte]
      apply le_antisymm
      · exact Finset.le_sup (f := (· + 1)) (Finset.mem_filter.2 ⟨hk, by omega⟩)
      · exact Finset.sup_le fun e he => by have := (Finset.mem_filter.1 he).2; omega
    · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte]
      congr 1
      ext e
      simp only [Finset.mem_filter]
      refine ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, ?_⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h.2 with h' | h'
      · exact h'
      · exact absurd (h' ▸ h.1) hk

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- The packed fresh equation name is `State.freshEqn`. -/
theorem pFreshEqn_eq (h : Rep N E P S) : pFreshEqn N E P = S.freshEqn := by
  have halive : ∀ e, (P.eqnRows.getD e 0).testBit (N + 1) = decide (e ∈ S.eqns) := fun e => by
    by_cases he : e < E
    · exact h.eqnRow_alive e he
    · rw [List.getD_eq_default _ _ (by rw [h.eqnRows_length]; omega), Nat.zero_testBit]
      simpa using fun hm => he (Finset.mem_range.1 (h.eqns hm))
  have := foldl_alive S.eqns (fun e => (P.eqnRows.getD e 0).testBit (N + 1)) halive E
  rw [freshEqn_eq_sup]
  refine this.trans (congrArg (Finset.sup · (· + 1)) ?_)
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h' => h'.1, fun he => ⟨he, Finset.mem_range.1 (h.eqns he)⟩⟩

private theorem lt_of_reads (h : Rep N E P S) (hS : S.Valid f) {J : ℕ} (hJ : J ∈ S.gates)
    {i : ℕ} (hi : (S.gate J).Reads i) : i < N :=
  Finset.mem_range.1 (h.names (hS.wf.reads_live J hJ i hi))

/-- **Deleting a constraint.** On a valid represented state, `pDeleteConstraint` represents
`State.deleteConstraint` of a gate or of an equation. -/
theorem pDeleteConstraint (h : Rep N E P S) (hS : S.Valid f) {c : ℕ ⊕ ℕ}
    (hc : c.elim (· ∈ S.gates) (· ∈ S.eqns)) :
    Rep N E (Refuter4n.pDeleteConstraint N P c) (S.deleteConstraint c) := by
  rcases c with J | e
  · change J ∈ S.gates at hc
    have hrow : rowLit (P.gateRows.getD J ⟨0, 0, 0⟩) =
        (argCode (S.gate J).lit.arg, (S.gate J).lit.neg.toNat) := by
      rw [h.gateRow J hc, rowLit_rowOf]
    change Rep N E (P.deleteGate N J (rowLit (P.gateRows.getD J ⟨0, 0, 0⟩)).1
      (rowLit (P.gateRows.getD J ⟨0, 0, 0⟩)).2) (S.deleteGate J (S.gate J).lit)
    rw [hrow]
    exact h.deleteGate hS (Finset.mem_range.1 (h.names (by simp [nameSet, hc])))
      fun y hy => h.lt_of_reads hS hc (Gate.reads_of_lit_reads hy)
  · change e ∈ S.eqns at hc
    have hw : ∀ i, (P.eqnRows.getD e 0).testBit i = (eqnWord N (S.eqn e) true).testBit i :=
      fun i => by rw [h.eqnRow e hc]
    have hT : ∀ j ∈ (S.eqn e).terms, j < N := fun j hj => h.terms_lt hS hc hj
    have hbit : ∀ i < N, (P.eqnRows.getD e 0).testBit i = decide (i ∈ (S.eqn e).terms) :=
      fun i hi => by rw [hw, testBit_eqnWord]; simp [hi, show i ≠ N + 1 by omega]
    have hrhs : (P.eqnRows.getD e 0).testBit N = (S.eqn e).rhs := by
      rw [hw, testBit_eqnWord]; simp
    have haux : ∀ i, P.aux.testBit i = decide (i ∈ S.aux) := fun i => by
      rw [h.aux, testBit_maskOf]
    set A := (S.eqn e).terms.filter (· ∈ S.aux) with hA
    have hfindA : (List.range N).find?
        (fun i => (P.eqnRows.getD e 0).testBit i && P.aux.testBit i) =
        (List.range N).find? (fun i => decide (i ∈ A)) :=
      List.find?_congr fun i hi => by
        rw [hbit i (List.mem_range.1 hi), haux]
        simp [hA]
    have hAN : ∀ i ∈ A, i < N := fun i hi => hT i (Finset.mem_of_mem_filter i hi)
    unfold Refuter4n.pDeleteConstraint pDeleteEqn
    dsimp only
    rw [hfindA]
    change Rep N E _ (if hA : A.Nonempty then
      if hR : ((S.eqn e).terms.erase (A.min' hA)).Nonempty then
        S.deleteEqn e (A.min' hA) ⟨.node (((S.eqn e).terms.erase (A.min' hA)).min' hR),
          (S.eqn e).rhs⟩
      else S.deleteEqn e (A.min' hA) (Lit.const (S.eqn e).rhs)
      else S.dropTrivialEqn e)
    by_cases hne : A.Nonempty
    · rw [dite_eq_left hne, find?_range_eq_min' hAN hne]
      have hv : A.min' hne < N := hAN _ (A.min'_mem hne)
      set R := (S.eqn e).terms.erase (A.min' hne) with hR
      have hRN : ∀ i ∈ R, i < N := fun i hi => hT i (Finset.mem_of_mem_erase hi)
      have hfindR : (List.range N).find?
          (fun i => (P.eqnRows.getD e 0).testBit i && i != A.min' hne) =
          (List.range N).find? (fun i => decide (i ∈ R)) :=
        List.find?_congr fun i hi => by
          rw [hbit i (List.mem_range.1 hi)]
          by_cases him : i = A.min' hne <;> simp [hR, him]
      dsimp only
      rw [hfindR, hrhs]
      by_cases hRne : R.Nonempty
      · rw [dite_eq_left hRne, find?_range_eq_min' hRN hRne]
        dsimp only
        exact h.deleteEqn hS e (ℓ := ⟨.node (R.min' hRne), (S.eqn e).rhs⟩) hv fun y hy => by
          have : y = R.min' hRne := by simpa [Lit.Reads] using hy.symm
          exact this ▸ hRN _ (R.min'_mem hRne)
      · rw [dite_eq_right hRne, find?_range_eq_none_of_empty hRne]
        dsimp only
        exact h.deleteEqn hS e (ℓ := Lit.const (S.eqn e).rhs) hv fun y hy =>
          absurd hy (by simp [Lit.Reads, Lit.const])
    · rw [dite_eq_right hne, find?_range_eq_none_of_empty hne]
      dsimp only
      exact h.dropTrivialEqn e

/-! ### Steps -/

/-- **`(D1)`.** Deleting the degenerate gate `J` of a valid represented state. -/
theorem applyStep_deleteConstantGate (h : Rep N E P S) (hS : S.Valid f) {J : ℕ}
    (hJ : J ∈ S.gates) :
    Rep N E (Refuter4n.pDeleteConstraint N P (.inl J)) (applyStep S (.deleteConstantGate J)) :=
  h.pDeleteConstraint hS (c := .inl J) hJ

/-- **`(D2)`.** Deleting the dead gate `J` of a valid represented state. -/
theorem applyStep_deleteDeadGate (h : Rep N E P S) (hS : S.Valid f) {J : ℕ}
    (hJ : J ∈ S.gates) :
    Rep N E (P.deleteGate N J 0 0) (applyStep S (.deleteDeadGate J)) :=
  h.deleteGate hS (ℓ := Lit.const false) (Finset.mem_range.1 (h.names (by simp [nameSet, hJ])))
    fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])

/-- **Moving an affine gate.** Moving the gate `J` of a represented state into the affine system
under the fresh equation name, when that name is below `E`. -/
theorem applyStep_moveAffine (h : Rep N E P S) {J : ℕ} (hJ : J ∈ S.gates)
    (he : S.freshEqn < E) :
    Rep N E (P.moveAffine N J (pFreshEqn N E P)) (applyStep S (.moveAffine J)) := by
  rw [h.pFreshEqn_eq]
  exact h.moveAffine hJ he

/-- **`(D3)`.** Deleting the equation `e` of a valid represented state. -/
theorem applyStep_deleteShortEqn (h : Rep N E P S) (hS : S.Valid f) {e : ℕ}
    (he : e ∈ S.eqns) :
    Rep N E (Refuter4n.pDeleteConstraint N P (.inr e)) (applyStep S (.deleteShortEqn e)) :=
  h.pDeleteConstraint hS (c := .inr e) he

end Rep

end Cslib.Algorithms.WordRAM.Refuter4n
