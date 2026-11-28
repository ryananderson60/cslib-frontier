/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedOps
import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterSearch
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
* **Readers.** `pFindReader` scans the gate rows for the least other gate reading a gate
  (`Rep.pFindReader_eq`).
* **Pairs and children.** `pFindPair` tests the candidate pairs of `findPair` on the pair
  records (`Rep.pFindPair_eq`); `pGetChildren` scans the gate rows and the equation words
  (`Rep.pGetChildren_eq`, and the degree `Rep.length_pGetChildren`).
* **Case 2.** `pDegeneratePair` (`Rep.applyStep_degeneratePair`); deleting a constraint keeps
  the other constraints and boundedness (`elim_mem_deleteConstraint`,
  `Bounded.deleteConstraint`), so a step can delete two in a row.
* **Pair creation.** `pPairCreation` (`Rep.applyStep_pairCreation`).
* **Steps.** `(D1)`, `(D2)`, `(D3)` and moving an affine gate
  (`Rep.applyStep_deleteConstantGate`, `Rep.applyStep_deleteDeadGate`,
  `Rep.applyStep_deleteShortEqn`, `Rep.applyStep_moveAffine`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.rowLit`: the literal codes of a degenerate gate row.
* `Cslib.Algorithms.WordRAM.Refuter4n.pDeleteEqn`, `pDeleteConstraint`:
  `State.deleteConstraint` of an equation, and of a gate or an equation, on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pFreshEqn`: `State.freshEqn` on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pFindReader`, `pPairCreation`: the reader search and pair
  creation on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pFindPair`, `pGetChildren`: `findPair` and `getChildren` on
  the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pDegeneratePair`: Case 2 on the packed state.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.find?_range_eq_min'`: the ascending scan finds the least
  element.
* `Cslib.Algorithms.WordRAM.Refuter4n.rowLit_rowOf`: `rowLit` is `Gate.lit`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pDeleteConstraint`: the packed deletion represents
  `State.deleteConstraint` of a gate or an equation of a bounded state.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pFreshEqn_eq`: the packed fresh name is `freshEqn`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pFindReader_eq`, `Rep.applyStep_pairCreation`: the
  reader search and pair creation.
* `Cslib.Algorithms.WordRAM.Refuter4n.elim_mem_deleteConstraint`, `Bounded.deleteConstraint`:
  deleting a constraint keeps the others and boundedness.
* `Cslib.Algorithms.WordRAM.Refuter4n.elim_mem_of_mem_children`, `Rep.partner_lt`: children are
  constraints, and partners in a valid represented state are below `N`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.applyStep_degeneratePair`: Case 2.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.mem_pairs_iff`, `Rep.pFindPair_eq`,
  `Rep.pGetChildren_eq`, `Rep.length_pGetChildren`: pair records, `findPair`, `getChildren` and
  degrees.
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

/-! ### Gates reading a gate -/

/-- The least gate other than `G` reading `G`, scanned on the gate mask and the gate rows. -/
@[expose] def pFindReader (N G : ℕ) (P : PackedState) : Option ℕ :=
  (List.range N).find? fun K => P.gates.testBit K && (decide (K ≠ G) &&
    (decide ((P.gateRows.getD K ⟨0, 0, 0⟩).left = G + 2) ||
      decide ((P.gateRows.getD K ⟨0, 0, 0⟩).right = G + 2)))

/-! ### Pair creation -/

/-- Case 5b, pair creation on the gate `G` (`applyStep` of `.pairCreation G`): add the pair of
its two arguments with the biases making the gate constant, delete `G` as that constant, and
delete the least other gate reading `G`. If an argument of `G` is a constant or no other gate
reads `G`, the state is unchanged, as in `applyStep`. -/
@[expose] def pPairCreation (N G : ℕ) (P : PackedState) : PackedState :=
  if 2 ≤ (P.gateRows.getD G ⟨0, 0, 0⟩).left ∧ 2 ≤ (P.gateRows.getD G ⟨0, 0, 0⟩).right then
    let t := (P.gateRows.getD G ⟨0, 0, 0⟩).tt
    let α := decide (t.testBit (idx true false) = t.testBit (idx true true))
    let β := decide (t.testBit (idx false true) = t.testBit (idx true true))
    match pFindReader N G P with
    | some K =>
      pDeleteConstraint N
        ((P.addPair (2 * ((P.gateRows.getD G ⟨0, 0, 0⟩).left - 2) + α.toNat,
          2 * ((P.gateRows.getD G ⟨0, 0, 0⟩).right - 2) + β.toNat)).deleteGate N G
          (t.testBit (idx α β)).toNat 0) (.inl K)
    | none => P
  else P

/-! ### Pairs and children -/

/-- `findPair` on the packed state: the same candidate pairs in the same order, a pair being
present when its record is in the pair list. -/
@[expose] def pFindPair (N p : ℕ) (P : PackedState) : Option ZeroPair :=
  (List.range N).findSome? fun r =>
    if P.params.testBit r then
      ([⟨p, false, r, false⟩, ⟨p, false, r, true⟩, ⟨p, true, r, false⟩, ⟨p, true, r, true⟩,
        ⟨r, false, p, false⟩, ⟨r, false, p, true⟩, ⟨r, true, p, false⟩, ⟨r, true, p, true⟩] :
          List ZeroPair).find? fun pr => decide (pairCode pr ∈ P.pairs)
    else none

/-- `getChildren` on the packed state: the gates whose row reads `p`, then the alive equations
whose word has bit `p`, in increasing order. -/
@[expose] def pGetChildren (N E p : ℕ) (P : PackedState) : List (ℕ ⊕ ℕ) :=
  (List.range N).filterMap (fun J =>
    if P.gates.testBit J && (decide ((P.gateRows.getD J ⟨0, 0, 0⟩).left = p + 2) ||
        decide ((P.gateRows.getD J ⟨0, 0, 0⟩).right = p + 2)) then some (.inl J) else none) ++
  (List.range E).filterMap (fun e =>
    if (P.eqnRows.getD e 0).testBit (N + 1) && (P.eqnRows.getD e 0).testBit p then some (.inr e)
    else none)

private theorem pairCode_injective : Function.Injective pairCode := by
  rintro ⟨a₁, a₂, a₃, a₄⟩ ⟨b₁, b₂, b₃, b₄⟩ hab
  simp only [pairCode, Prod.mk.injEq] at hab
  obtain ⟨h₁, h₂⟩ := hab
  cases a₂ <;> cases b₂ <;> cases a₄ <;> cases b₄ <;>
    simp only [Bool.toNat_true, Bool.toNat_false] at h₁ h₂ <;>
    first
    | (exfalso; omega)
    | (obtain rfl : a₁ = b₁ := by omega
       obtain rfl : a₃ = b₃ := by omega
       rfl)

/-- A copy of the private `sort_eq_filter_range` of `PackedState`; it can go once that lemma is
public. -/
private theorem sort_eq_filter_range' {s : Finset ℕ} {N : ℕ} (hs : ∀ i ∈ s, i < N) :
    s.sort (· ≤ ·) = (List.range N).filter fun i => decide (i ∈ s) :=
  (Finset.sortedLT_sort s).pairwise.eq_of_mem_iff ((List.pairwise_lt_range).filter _) fun i => by
    simp only [Finset.mem_sort, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => ⟨hs i h, h⟩, fun h => h.2⟩

/-! ### Constraints after a deletion -/

/-- A child of a name is a constraint of the state: a gate or an equation. -/
theorem elim_mem_of_mem_children {S : State n} {p : ℕ} {c : ℕ ⊕ ℕ}
    (hc : c ∈ S.children p) : c.elim (· ∈ S.gates) (· ∈ S.eqns) := by
  rcases c with J | e
  · exact ((inl_mem_children _).1 hc).1
  · exact ((inr_mem_children _).1 hc).1

/-- Deleting one constraint keeps every other constraint. -/
theorem elim_mem_deleteConstraint {S : State n} {c c' : ℕ ⊕ ℕ} (hne : c' ≠ c)
    (hc' : c'.elim (· ∈ S.gates) (· ∈ S.eqns)) :
    c'.elim (· ∈ (S.deleteConstraint c).gates) (· ∈ (S.deleteConstraint c).eqns) := by
  rcases c with J | e <;> rcases c' with K | e'
  · exact Finset.mem_erase.2 ⟨fun h => hne (congrArg Sum.inl h), hc'⟩
  · exact hc'
  · unfold Cslib.Circuits.Boolean.AffineDisperserCore.State.deleteConstraint
    dsimp only
    split_ifs <;> exact hc'
  · unfold Cslib.Circuits.Boolean.AffineDisperserCore.State.deleteConstraint
    dsimp only
    split_ifs <;> exact Finset.mem_erase.2 ⟨fun h => hne (congrArg Sum.inr h), hc'⟩

/-- Deleting a constraint preserves boundedness. -/
theorem Bounded.deleteConstraint {N : ℕ} {S : State n} (hB : Bounded N S) {c : ℕ ⊕ ℕ}
    (hc : c.elim (· ∈ S.gates) (· ∈ S.eqns)) : Bounded N (S.deleteConstraint c) := by
  rcases c with J | e
  · exact hB.deleteGate J fun y hy => hB.reads J hc y (Gate.reads_of_lit_reads hy)
  · unfold Cslib.Circuits.Boolean.AffineDisperserCore.State.deleteConstraint
    dsimp only
    split_ifs with hA hR
    · refine hB.deleteEqn e _ fun y hy => ?_
      have hy' : y = ((S.eqn e).terms.erase _).min' hR := by simpa [Lit.Reads] using hy.symm
      exact hy' ▸ hB.terms e hc _ (Finset.mem_of_mem_erase (Finset.min'_mem _ hR))
    · exact hB.deleteEqn e _ fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])
    · exact hB.dropTrivialEqn e

/-! ### Case 2 -/

/-- Case 2, a paired parameter `p` of degree `0` or at least `2` (`applyStep` of
`.degeneratePair p`): fix the partner of `p` if `p` is unused, and otherwise fix `p` to its bias
and delete its first two children. -/
@[expose] def pDegeneratePair (N E p : ℕ) (P : PackedState) : PackedState :=
  match pFindPair N p P with
  | some pr =>
    if (pGetChildren N E p P).length = 0 then
      P.restrictAvoid N (pr.partner p) (pr.partnerBias p).toNat 0
    else
      match pGetChildren N E p P with
      | N₁ :: N₂ :: _ =>
        pDeleteConstraint N (pDeleteConstraint N (P.restrictAvoid N p (pr.bias p).toNat 0) N₁) N₂
      | _ => P
  | none => P

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

/-- A copy of the private `Rep.lt_of_mem_nameSet` of `PackedState`; it can go once that helper is
public. -/
private theorem lt_names (h : Rep N E P S) {i : ℕ} (hi : i ∈ nameSet S) : i < N :=
  Finset.mem_range.1 (h.names hi)

/-- The packed reader search is the reader search of `applyStep`. -/
theorem pFindReader_eq (h : Rep N E P S) (G : ℕ) :
    pFindReader N G P =
      (S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G ∧ (S.gate K).Reads G)) := by
  rw [find?_sort_eq_find?_range (N := N) fun i hi =>
    h.lt_names (by simp [nameSet, hi]), pFindReader, ← h.gates]
  refine List.find?_congr fun K _ => ?_
  by_cases hK : K ∈ S.gates
  · have hbit : P.gates.testBit K = true := by rw [h.gates, testBit_maskOf]; simpa using hK
    rw [hbit, h.gateRow K hK]
    simp only [rowOf, Bool.true_and, Gate.Reads, argCode_eq_node]
    by_cases hKG : K = G <;> simp [hKG]
  · have hbit : P.gates.testBit K = false := by rw [h.gates, testBit_maskOf]; simpa using hK
    simp [hbit]

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

/-- **Deleting a constraint.** On a bounded represented state, `pDeleteConstraint` represents
`State.deleteConstraint` of a gate or of an equation of a bounded state. -/
theorem pDeleteConstraint (h : Rep N E P S) (hB : Bounded N S) {c : ℕ ⊕ ℕ}
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
    exact h.deleteGate hB (h.lt_names (by simp [nameSet, hc]))
      fun y hy => hB.reads J hc y (Gate.reads_of_lit_reads hy)
  · change e ∈ S.eqns at hc
    have hw : ∀ i, (P.eqnRows.getD e 0).testBit i = (eqnWord N (S.eqn e) true).testBit i :=
      fun i => by rw [h.eqnRow e hc]
    have hT : ∀ j ∈ (S.eqn e).terms, j < N := hB.terms e hc
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
        exact h.deleteEqn hB e (ℓ := ⟨.node (R.min' hRne), (S.eqn e).rhs⟩) hv fun y hy => by
          have : y = R.min' hRne := by simpa [Lit.Reads] using hy.symm
          exact this ▸ hRN _ (R.min'_mem hRne)
      · rw [dite_eq_right hRne, find?_range_eq_none_of_empty hRne]
        dsimp only
        exact h.deleteEqn hB e (ℓ := Lit.const (S.eqn e).rhs) hv fun y hy =>
          absurd hy (by simp [Lit.Reads, Lit.const])
    · rw [dite_eq_right hne, find?_range_eq_none_of_empty hne]
      dsimp only
      exact h.dropTrivialEqn e

/-! ### Steps -/

/-- **`(D1)`.** Deleting the degenerate gate `J` of a bounded represented state. -/
theorem applyStep_deleteConstantGate (h : Rep N E P S) (hB : Bounded N S) {J : ℕ}
    (hJ : J ∈ S.gates) :
    Rep N E (Refuter4n.pDeleteConstraint N P (.inl J)) (applyStep S (.deleteConstantGate J)) :=
  h.pDeleteConstraint hB (c := .inl J) hJ

/-- **`(D2)`.** Deleting the dead gate `J` of a bounded represented state. -/
theorem applyStep_deleteDeadGate (h : Rep N E P S) (hB : Bounded N S) {J : ℕ}
    (hJ : J ∈ S.gates) :
    Rep N E (P.deleteGate N J 0 0) (applyStep S (.deleteDeadGate J)) :=
  h.deleteGate hB (ℓ := Lit.const false) (h.lt_names (by simp [nameSet, hJ]))
    fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])

/-- **Moving an affine gate.** Moving the gate `J` of a represented state into the affine system
under the fresh equation name, when that name is below `E`. -/
theorem applyStep_moveAffine (h : Rep N E P S) {J : ℕ} (hJ : J ∈ S.gates)
    (he : S.freshEqn < E) :
    Rep N E (P.moveAffine N J (pFreshEqn N E P)) (applyStep S (.moveAffine J)) := by
  rw [h.pFreshEqn_eq]
  exact h.moveAffine hJ he

/-- **`(D3)`.** Deleting the equation `e` of a bounded represented state. -/
theorem applyStep_deleteShortEqn (h : Rep N E P S) (hB : Bounded N S) {e : ℕ}
    (he : e ∈ S.eqns) :
    Rep N E (Refuter4n.pDeleteConstraint N P (.inr e)) (applyStep S (.deleteShortEqn e)) :=
  h.pDeleteConstraint hB (c := .inr e) he

/-- A pair record is in the pair list iff its pair is a pair of the state. -/
theorem mem_pairs_iff (h : Rep N E P S) (pr : ZeroPair) :
    pairCode pr ∈ P.pairs ↔ pr ∈ S.pairs := by
  obtain ⟨l, -, hS, hP⟩ := h.pairs
  rw [hP, ← hS, List.mem_toFinset, List.mem_map]
  exact ⟨fun ⟨q, hq, he⟩ => pairCode_injective he ▸ hq, fun hm => ⟨pr, hm, rfl⟩⟩

/-- The packed pair search is `findPair`. -/
theorem pFindPair_eq (h : Rep N E P S) (p : ℕ) : pFindPair N p P = findPair S p := by
  rw [findPair, findSome?_sort_eq_findSome?_range (N := N) fun i hi =>
    h.lt_names (by simp [nameSet, hi]), ← h.params, pFindPair]
  simp only [h.mem_pairs_iff]

/-- The packed children of a name below `N` are `getChildren`. -/
theorem pGetChildren_eq (h : Rep N E P S) {p : ℕ} (hp : p < N) :
    pGetChildren N E p P = getChildren S p := by
  unfold pGetChildren getChildren
  rw [sort_eq_filter_range' (N := N) fun i hi =>
      h.lt_names (by simp [nameSet, hi]),
    sort_eq_filter_range' (N := E) fun e he => Finset.mem_range.1 (h.eqns he),
    List.filterMap_filter, List.filterMap_filter]
  congr 1
  · congr 1
    funext J
    by_cases hJ : J ∈ S.gates
    · have hbit : P.gates.testBit J = true := by rw [h.gates, testBit_maskOf]; simpa using hJ
      rw [hbit, h.gateRow J hJ]
      simp [rowOf, argCode_eq_node, hJ, Gate.Reads]
    · have hbit : P.gates.testBit J = false := by rw [h.gates, testBit_maskOf]; simpa using hJ
      simp [hbit, hJ]
  · congr 1
    funext e
    by_cases he : e ∈ S.eqns
    · rw [h.eqnRow e he, testBit_eqnWord, testBit_eqnWord]
      simp [he, hp, show ¬ N + 1 < N by omega, show p ≠ N + 1 by omega]
    · have halive : (P.eqnRows.getD e 0).testBit (N + 1) = false := by
        by_cases heE : e < E
        · rw [h.eqnRow_alive e heE]; simpa using he
        · rw [List.getD_eq_default _ _ (by rw [h.eqnRows_length]; omega)]; simp
      rw [halive]
      simp [he]

/-- The packed degree of a name below `N` is its degree. -/
theorem length_pGetChildren (h : Rep N E P S) {p : ℕ} (hp : p < N) :
    (pGetChildren N E p P).length = S.deg p := by
  rw [h.pGetChildren_eq hp, length_getChildren]

/-- In a valid represented state, the partner of any name in a pair is below `N`. -/
theorem partner_lt (h : Rep N E P S) (hS : S.Valid f) {pr : ZeroPair} (hpr : pr ∈ S.pairs)
    (x : ℕ) : pr.partner x < N := by
  obtain ⟨h₁, h₂⟩ := h.pairs_lt hS hpr
  unfold ZeroPair.partner
  split_ifs <;> assumption

/-- **Case 2.** On a valid represented state, for a parameter `p` below `N`, the packed Case 2
represents `applyStep` of `.degeneratePair p`. -/
theorem applyStep_degeneratePair (h : Rep N E P S) (hS : S.Valid f) {p : ℕ} (hp : p < N) :
    Rep N E (pDegeneratePair N E p P) (applyStep S (.degeneratePair p)) := by
  have hB := h.bounded hS
  unfold pDegeneratePair
  rw [h.pFindPair_eq, h.length_pGetChildren hp, h.pGetChildren_eq hp]
  simp only [applyStep]
  rcases hf : findPair S p with _ | pr
  · exact h
  · obtain ⟨hmem, -⟩ := findPair_spec hf
    dsimp only
    split_ifs with hd
    · exact h.fixConst hB (h.partner_lt hS hmem p) _
    · have hnd := nodup_getChildren S p
      rcases hc : getChildren S p with _ | ⟨N₁, _ | ⟨N₂, rest⟩⟩
      · exact h
      · exact h
      · rw [hc] at hnd
        have hN₁ : N₁ ∈ S.children p := mem_getChildren.1 (by rw [hc]; simp)
        have hN₂ : N₂ ∈ S.children p := mem_getChildren.1 (by rw [hc]; simp)
        have hB₁ : Bounded N (S.fixConst p (pr.bias p)) :=
          hB.restrict p (ℓ := Lit.const (pr.bias p))
            (fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])) _
        have hg : (S.fixConst p (pr.bias p)).gates = S.gates := rfl
        have he : (S.fixConst p (pr.bias p)).eqns = S.eqns := rfl
        have hm₁ : N₁.elim (· ∈ (S.fixConst p (pr.bias p)).gates)
            (· ∈ (S.fixConst p (pr.bias p)).eqns) := by
          rw [hg, he]; exact elim_mem_of_mem_children hN₁
        have hm₂ : N₂.elim (· ∈ (S.fixConst p (pr.bias p)).gates)
            (· ∈ (S.fixConst p (pr.bias p)).eqns) := by
          rw [hg, he]; exact elim_mem_of_mem_children hN₂
        have hne : N₂ ≠ N₁ := fun he => (List.nodup_cons.1 hnd).1 (by rw [← he]; simp)
        exact ((h.fixConst hB hp (pr.bias p)).pDeleteConstraint hB₁ hm₁).pDeleteConstraint
          (hB₁.deleteConstraint hm₁) (elim_mem_deleteConstraint hne hm₂)

/-- **Pair creation.** On a bounded represented state, for a gate `G` whose first argument is
the first member of no pair, the packed pair creation represents `applyStep` of
`.pairCreation G`. -/
theorem applyStep_pairCreation (h : Rep N E P S) (hB : Bounded N S) {G : ℕ}
    (hG : G ∈ S.gates) (hfresh : ∀ t, (S.gate G).left = .node t → ∀ pr ∈ S.pairs, pr.fst ≠ t) :
    Rep N E (pPairCreation N G P) (applyStep S (.pairCreation G)) := by
  have hGN : G < N := h.lt_names (by simp [nameSet, hG])
  have hrow := h.gateRow G hG
  rcases hgate : S.gate G with ⟨op, l, r⟩
  rw [hgate] at hrow hfresh
  have key : ∀ a b, (ttOf op).testBit (idx a b) = op a b := testBit_ttOf op
  cases l with
  | const b =>
    have : ¬ 2 ≤ b.toNat := by have := Bool.toNat_le b; omega
    simp only [pPairCreation, hrow, rowOf, argCode, this, false_and, ↓reduceIte]
    simpa only [applyStep, hgate] using h
  | node t₁ =>
    cases r with
    | const b =>
      have : ¬ 2 ≤ b.toNat := by have := Bool.toNat_le b; omega
      simp only [pPairCreation, hrow, rowOf, argCode, this, and_false, ↓reduceIte]
      simpa only [applyStep, hgate] using h
    | node t₂ =>
      simp only [pPairCreation, hrow, rowOf, argCode, le_add_iff_nonneg_left, zero_le, and_self,
        ↓reduceIte, key, Nat.add_sub_cancel, h.pFindReader_eq]
      simp only [applyStep, hgate]
      rcases hK : (S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G ∧ (S.gate K).Reads G))
        with _ | K
      · exact h
      · obtain ⟨hKmem, hKp⟩ : K ∈ S.gates ∧ K ≠ G := by
          have hm := List.mem_of_find?_eq_some hK
          have hp := List.find?_some hK
          simp only [decide_eq_true_eq] at hp
          exact ⟨(Finset.mem_sort _).1 hm, hp.1⟩
        set α := decide (op true false = op true true)
        set β := decide (op false true = op true true)
        have hpr : (⟨t₁, α, t₂, β⟩ : ZeroPair) ∉ S.pairs := fun hm =>
          hfresh t₁ rfl _ hm rfl
        have h₁ := h.addPair hpr
        have h₂ := h₁.deleteGate (hB.addPair _) hGN (ℓ := Lit.const (op α β))
          fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])
        have hB₂ := (hB.addPair (⟨t₁, α, t₂, β⟩ : ZeroPair)).deleteGate G
          (ℓ := Lit.const (op α β)) fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])
        exact h₂.pDeleteConstraint hB₂ (c := .inl K) (Finset.mem_erase.2 ⟨hKp, hKmem⟩)

end Rep

end Cslib.Algorithms.WordRAM.Refuter4n
