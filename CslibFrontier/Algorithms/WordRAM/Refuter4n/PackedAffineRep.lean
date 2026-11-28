/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedStep
import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterAffineRep

/-!
# Packed affine representations and the steps that use them

The affine-representation oracle `findAffineRep` of the `4n - 9d` refuter
(`Cslib.Circuits.Boolean.AffineDisperser4n`) on the packed state `PackedState`, and the two steps
that call it: `(D4)` (`unitDelete`) and the swap of an auxiliary argument of the minimal gate
(`applyStep` of `.swapAuxIn`). This is part of the pure layer of the step programs of issue
`#4322` (Milestone 4); no program and no running time is claimed here.

`evaluateAux S a val` decides a dense `XORSAT` system of width `varBound S`. The packed
`pEvaluateAux` decides the same equations at width `N` instead, on packed rows only: the alive
equation words below their alive flag (`eqnWord_mod`), the unit rows `unitWord` of the parameters
and of `a`, eliminated by the packed columns `XORSATDense.cols`. Every name of a represented state
is below `N`, so the extra columns are zero and the answer is the same
(`Rep.pEvaluateAux_eq`).

* **Oracle.** `pEvaluateAux`, `pFindAffineRep` (`Rep.pEvaluateAux_eq`, `Rep.pFindAffineRep_eq`);
  the representation set is returned as a mask.
* **Unit deletion.** `pUnitDelete` (`Rep.unitDelete`), hence the `(D4)` step
  (`Rep.applyStep_deleteUnitParam`).
* **Swapping an auxiliary argument.** `pAuxArgs`, `pPaired` and `pSwapAuxIn`
  (`Rep.pAuxArgs_eq`, `Rep.pPaired_eq`, `Rep.applyStep_swapAuxIn`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.unitWord`, `auxWords`: the packed rows queried by
  `evaluateAux`.
* `Cslib.Algorithms.WordRAM.Refuter4n.pEvaluateAux`, `pFindAffineRep`: `evaluateAux` and
  `findAffineRep` on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.swapWord`: the substitution word of the affine
  reparameterisation from a constant and a mask.
* `Cslib.Algorithms.WordRAM.Refuter4n.pUnitDelete`: `unitDelete` on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.pAuxArgs`, `pPaired`, `pSwapAuxIn`: `auxArgs`,
  `State.Paired` and the `.swapAuxIn` step on the packed state.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.unitWord_eq`, `swapWord_eq`: the words are packed dense
  rows.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pEvaluateAux_eq`, `Rep.pFindAffineRep_eq`: on a valid
  represented state, the packed oracle is `evaluateAux` and `findAffineRep` at every auxiliary
  variable.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.unitDelete`, `Rep.applyStep_deleteUnitParam`: the
  packed `(D4)`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pAuxArgs_eq`, `Rep.pPaired_eq`: auxiliary arguments and
  pairing.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.applyStep_swapAuxIn`: the packed `.swapAuxIn` step.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Finset
open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.AffineDisperserCore Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Algorithms.WordRAM.XORSATDense

variable {n : ℕ}

/-! ### Packed rows of the oracle -/

/-- The packed row of `x_p = b` at width `N`: bit `p`, and the right-hand side `b` at bit `N`. -/
@[expose] def unitWord (N p : ℕ) (b : Bool) : ℕ :=
  2 ^ p ||| (if b then 2 ^ N else 0)

/-- `unitWord` is the packed dense row of `x_p = b`. -/
theorem unitWord_eq {N p : ℕ} (hp : p < N) (b : Bool) :
    unitWord N p b = rowWord (toDenseRow N {p} b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [unitWord, Nat.testBit_or, Nat.testBit_two_pow, testBit_rowWord_toDenseRow]
  by_cases hi : i < N
  · have hNi : N ≠ i := by omega
    rw [ite_eq_left hi]
    simp only [Finset.mem_singleton]
    by_cases hpi : p = i
    · subst hpi
      cases b <;> simp
    · have hip : i ≠ p := Ne.symm hpi
      cases b <;> simp [hpi, hip, hNi]
  · have hpi : p ≠ i := by omega
    rw [ite_eq_right hi]
    by_cases hiN : i = N
    · subst hiN
      cases b <;> simp [hpi]
    · have hNi : N ≠ i := Ne.symm hiN
      cases b <;> simp [hpi, hiN, hNi]

/-- The packed rows of the system queried by `evaluateAux S a val`, at width `N`: the alive
equation words below their alive flag, the rows `x_p = val p` of the parameters, and `x_a = 0`. -/
@[expose] def auxWords (N E a : ℕ) (P : PackedState) (val : ℕ → Bool) : List ℕ :=
  (List.range E).filterMap (fun e => if (P.eqnRows.getD e 0).testBit (N + 1) then
      some (P.eqnRows.getD e 0 % 2 ^ (N + 1)) else none) ++
    (List.range N).filterMap (fun p => if P.params.testBit p then some (unitWord N p (val p))
      else none) ++
    [unitWord N a false]

/-- `evaluateAux` on the packed state: `false` exactly when the packed elimination
(`XORSATDense.cols`) of `auxWords` leaves no row `0 = 1`. -/
@[expose] def pEvaluateAux (N E a : ℕ) (P : PackedState) (val : ℕ → Bool) : Bool :=
  !(cols (auxWords N E a P val) N).all (fun x => !x.testBit N)

/-- `findAffineRep` on the packed state: the constant, and the mask of the parameters `y` whose
unit assignment changes the value. -/
@[expose] def pFindAffineRep (N E a : ℕ) (P : PackedState) : Bool × ℕ :=
  let c := pEvaluateAux N E a P (fun _ => false)
  (c, (((List.range N).filter fun y =>
    P.params.testBit y && (pEvaluateAux N E a P (fun j => j == y) != c)).map (2 ^ ·)).sum)

/-! ### Correctness of the oracle -/

/-- A copy of the private `dot_toDenseRow` of `RefuterAffineRep`; it can go once that lemma is
public. -/
private theorem dot_toDenseRow' {N : ℕ} {T : Finset ℕ} (hT : ∀ i ∈ T, i < N) (c : Bool)
    (w : ℕ → Bool) :
    dot (toDenseRow N T c).coeffs ((List.range N).map w) = ∑ i ∈ T, w i := by
  change dot ((List.range N).map fun i => decide (i ∈ T)) ((List.range N).map w) = _
  have key : ∀ l : List ℕ, dot (l.map fun i => decide (i ∈ T)) (l.map w) =
      (l.map fun i => if i ∈ T then w i else 0).sum := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, dot, ih, List.sum_cons]
      by_cases ha : a ∈ T <;>
        simp only [ha, decide_true, decide_false, ite_true, ite_false] <;> cases w a <;> rfl
  rw [key, show ((List.range N).map fun i => if i ∈ T then w i else 0).sum =
    ∑ i ∈ Finset.range N, if i ∈ T then w i else 0 from rfl, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 fun i hi => Finset.mem_range.2 (hT i hi)]

/-- The rows of `auxWords` as dense rows, in the same order. -/
private def auxRows (N E a : ℕ) (S : State n) (val : ℕ → Bool) : System :=
  (List.range E).filterMap (fun e => if e ∈ S.eqns then
      some (toDenseRow N (S.eqn e).terms (S.eqn e).rhs) else none) ++
    (List.range N).filterMap (fun p => if p ∈ S.params then some (toDenseRow N {p} (val p))
      else none) ++
    [toDenseRow N {a} false]

private theorem forall_mem_filterMap_ite {α β : Type*} (l : List α) (q : α → Prop)
    [DecidablePred q] (g : α → β) (R : β → Prop) :
    (∀ r ∈ l.filterMap (fun x => if q x then some (g x) else none), R r) ↔
      ∀ x ∈ l, q x → R (g x) := by
  simp only [List.mem_filterMap]
  refine ⟨fun H x hx hq => H _ ⟨x, hx, by simp [hq]⟩, ?_⟩
  rintro H r ⟨x, hx, hr⟩
  by_cases hq : q x
  · rw [ite_eq_left hq] at hr
    obtain rfl := Option.some.inj hr
    exact H x hx hq
  · rw [ite_eq_right hq] at hr
    cases hr

private theorem width_auxRows (N E a : ℕ) (S : State n) (val : ℕ → Bool) :
    Width N (auxRows N E a S val) := by
  unfold Width auxRows
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton,
    forall_mem_filterMap_ite, forall_mem_filterMap_ite]
  exact ⟨⟨fun _ _ _ => by simp [toDenseRow], fun _ _ _ => by simp [toDenseRow]⟩,
    by simp [toDenseRow]⟩

private theorem holds_auxRows_iff {N E : ℕ} {S : State n} (hB : Bounded N S)
    (hE : ∀ e ∈ S.eqns, e < E) (hp : ∀ p ∈ S.params, p < N) {a : ℕ} (ha : a < N)
    (val v : ℕ → Bool) :
    Holds (auxRows N E a S val) ((List.range N).map v) ↔
      S.EqnsHold v ∧ (∀ p ∈ S.params, v p = val p) ∧ v a = false := by
  unfold Holds auxRows
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton,
    forall_mem_filterMap_ite, forall_mem_filterMap_ite, and_assoc]
  have hsing : ∀ {q : ℕ}, q < N → ∀ i ∈ ({q} : Finset ℕ), i < N := fun hq i hi =>
    (Finset.mem_singleton.1 hi) ▸ hq
  refine and_congr ⟨fun H e he => ?_, fun H e _ he => ?_⟩
    (and_congr ⟨fun H q hq => ?_, fun H q _ hq => ?_⟩ ?_)
  · have := H e (List.mem_range.2 (hE e he)) he
    rw [dot_toDenseRow' (hB.terms e he)] at this
    exact this
  · rw [dot_toDenseRow' (hB.terms e he)]
    exact H e he
  · have := H q (List.mem_range.2 (hp q hq)) hq
    rwa [dot_toDenseRow' (hsing (hp q hq)), Finset.sum_singleton] at this
  · rw [dot_toDenseRow' (hsing (hp q hq)), Finset.sum_singleton]
    exact H q hq
  · rw [dot_toDenseRow' (hsing ha), Finset.sum_singleton]
    rfl

private theorem satisfiable_auxRows_iff {N E : ℕ} {S : State n} (hB : Bounded N S)
    (hE : ∀ e ∈ S.eqns, e < E) (hp : ∀ p ∈ S.params, p < N) {a : ℕ} (ha : a < N)
    (val : ℕ → Bool) :
    Satisfiable N (auxRows N E a S val) ↔
      ∃ v, S.EqnsHold v ∧ (∀ p ∈ S.params, v p = val p) ∧ v a = false := by
  refine ⟨fun ⟨l, hl, hH⟩ => ⟨fun i => l.getD i false, ?_⟩,
    fun ⟨v, hv⟩ => ⟨_, by simp, (holds_auxRows_iff hB hE hp ha val v).2 hv⟩⟩
  have hl' : ((List.range N).map fun i => l.getD i false) = l :=
    List.ext_getElem (by simp [hl]) fun i _ h₂ => by simp [h₂]
  rwa [← holds_auxRows_iff hB hE hp ha, hl']

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- A copy of the private `Rep.lt_of_mem_nameSet` of `PackedState`; it can go once that helper is
public. -/
private theorem lt_names (h : Rep N E P S) {i : ℕ} (hi : i ∈ nameSet S) : i < N :=
  Finset.mem_range.1 (h.names hi)

private theorem auxWords_eq (h : Rep N E P S) {a : ℕ} (ha : a < N)
    (val : ℕ → Bool) : auxWords N E a P val = (auxRows N E a S val).map rowWord := by
  unfold auxWords auxRows
  rw [List.map_append, List.map_append, List.map_filterMap, List.map_filterMap,
    List.map_singleton, unitWord_eq ha]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) rfl
  · refine List.filterMap_congr fun e he => ?_
    rw [h.eqnRow_alive e (List.mem_range.1 he)]
    by_cases hm : e ∈ S.eqns
    · rw [h.eqnRow e hm, eqnWord_mod]
      simp [hm]
    · simp [hm]
  · refine List.filterMap_congr fun p hp => ?_
    rw [h.params, testBit_maskOf]
    by_cases hm : p ∈ S.params
    · simp [hm, unitWord_eq (List.mem_range.1 hp)]
    · simp [hm]

/-- **The packed oracle.** On a bounded well-formed represented state, `pEvaluateAux` is
`evaluateAux` at every auxiliary variable and every parameter assignment. -/
theorem pEvaluateAux_eq (h : Rep N E P S) (hB : Bounded N S) (hwf : S.WellFormed) {a : ℕ}
    (ha : a ∈ S.aux) (val : ℕ → Bool) : pEvaluateAux N E a P val = evaluateAux S a val := by
  have haN : a < N := h.lt_names (by simp [nameSet, ha])
  have hE : ∀ e ∈ S.eqns, e < E := fun e he => Finset.mem_range.1 (h.eqns he)
  have hp : ∀ p ∈ S.params, p < N := fun p hp => h.lt_names (by simp [nameSet, hp])
  obtain ⟨w, hw, hweq⟩ := hwf.solvable val
  have hd := decide_eq_cols ⟨N, auxRows N E a S val⟩ (width_auxRows N E a S val)
  dsimp only at hd
  rw [evaluateAux_eq hwf ha hw hweq, pEvaluateAux, h.auxWords_eq haN, ← hd]
  have key : Cslib.Complexity.XORSAT.Dense.decide ⟨N, auxRows N E a S val⟩ = true ↔
      w a = false := by
    rw [Cslib.Complexity.XORSAT.Dense.decide_eq_true_iff, and_iff_right (width_auxRows N E a S val),
      satisfiable_auxRows_iff hB hE hp haN]
    exact ⟨fun ⟨v, hv, hvp, hva⟩ =>
      hva ▸ hwf.unique w v (fun j hj => (hw j hj).trans (hvp j hj).symm) hweq hv a ha,
      fun hwa => ⟨w, hweq, hw, hwa⟩⟩
  cases hdq : Cslib.Complexity.XORSAT.Dense.decide ⟨N, auxRows N E a S val⟩
  · cases hwa : w a
    · exact absurd (key.2 hwa) (by rw [hdq]; decide)
    · rfl
  · rw [key.1 hdq]
    rfl

/-- **The packed affine representation.** On a bounded well-formed represented state,
`pFindAffineRep` is `findAffineRep` at every auxiliary variable, with the representation set as
its mask. -/
theorem pFindAffineRep_eq (h : Rep N E P S) (hB : Bounded N S) (hwf : S.WellFormed) {a : ℕ}
    (ha : a ∈ S.aux) :
    pFindAffineRep N E a P = ((findAffineRep S a).1, maskOf (findAffineRep S a).2) := by
  have hev := h.pEvaluateAux_eq hB hwf ha
  have hp : ∀ p ∈ S.params, p < N := fun p hp => h.lt_names (by simp [nameSet, hp])
  simp only [pFindAffineRep, findAffineRep, hev]
  refine Prod.ext rfl ?_
  dsimp only
  rw [maskOf, ← List.sum_toFinset (fun i => 2 ^ i) (List.nodup_range.filter _)]
  congr 1
  ext y
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_filter, h.params,
    testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨_, hy, hne⟩ => ⟨hy, hne⟩, fun ⟨hy, hne⟩ => ⟨hp y hy, hy, hne⟩⟩

end Rep

/-! ### Unit deletion -/

/-- The substitution word of the affine reparameterisation of `x` by `Q = c + ∑ T`, from the
constant `c` and the mask of `T`: the packed row of `c + ∑ (T \ {x}) Δ {Q}`. -/
@[expose] def swapWord (N x Q : ℕ) (rep : Bool × ℕ) : ℕ :=
  (clearBit rep.2 x ^^^ 2 ^ Q) ||| (if rep.1 then 2 ^ N else 0)

/-- `swapWord` is the word that `Rep.swap` substitutes. -/
theorem swapWord_eq {N x Q : ℕ} {T : Finset ℕ} (hT : ∀ j ∈ T, j < N) (hQ : Q < N) (c : Bool) :
    swapWord N x Q (c, maskOf T) = rowWord (toDenseRow N (symmDiff (T.erase x) {Q}) c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [swapWord, ← maskOf_erase, Nat.testBit_or, Nat.testBit_xor, testBit_maskOf,
    Nat.testBit_two_pow, testBit_rowWord_toDenseRow]
  dsimp only
  by_cases hi : i < N
  · have hNi : N ≠ i := by omega
    have hif : (if c then 2 ^ N else 0).testBit i = false := by
      split_ifs
      · rw [Nat.testBit_two_pow, decide_eq_false hNi]
      · simp
    rw [hif, ite_eq_left hi, Bool.or_false]
    simp only [Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hQi : Q = i
    · subst hQi
      by_cases h1 : Q ∈ T.erase x <;> simp [h1]
    · have hiQ : i ≠ Q := Ne.symm hQi
      by_cases h1 : i ∈ T.erase x <;> simp [h1, hQi, hiQ]
  · have h1 : i ∉ T.erase x := fun hm => hi (hT i (Finset.mem_of_mem_erase hm))
    have hQi : Q ≠ i := by omega
    rw [ite_eq_right hi]
    by_cases hiN : i = N
    · subst hiN
      cases c <;> simp [h1, hQi]
    · have hNi : N ≠ i := Ne.symm hiN
      cases c <;> simp [h1, hQi, hiN, hNi]

/-- `unitDelete` on the packed state: swap `x` with the least auxiliary variable whose packed
representation mask has bit `x`, then drop the equation `e` and `x`. -/
@[expose] def pUnitDelete (N E x e : ℕ) (P : PackedState) : PackedState :=
  match (List.range N).find? (fun Q => P.aux.testBit Q && (pFindAffineRep N E Q P).2.testBit x)
    with
  | some Q => (P.swap x Q (swapWord N x Q (pFindAffineRep N E Q P))).dropEqn e x
  | none => P

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

private theorem rep_lt (h : Rep N E P S) (hwf : S.WellFormed) {Q : ℕ} (hQ : Q ∈ S.aux) :
    ∀ j ∈ (findAffineRep S Q).2, j < N := fun j hj =>
  h.lt_names (by simp [nameSet, (findAffineRep_spec hwf hQ).1 hj])

/-- **Unit deletion.** On a bounded well-formed represented state, for `x` below `N`, the packed
unit deletion represents `unitDelete`. -/
theorem unitDelete (h : Rep N E P S) (hB : Bounded N S) (hwf : S.WellFormed) {x : ℕ} (hx : x < N)
    (e : ℕ) :
    Rep N E (pUnitDelete N E x e P)
      (Cslib.Circuits.Boolean.AffineDisperser4n.unitDelete S x e) := by
  have hfind : (List.range N).find?
      (fun Q => P.aux.testBit Q && (pFindAffineRep N E Q P).2.testBit x) =
      (S.aux.sort (· ≤ ·)).find? (fun Q => decide (x ∈ (findAffineRep S Q).2)) := by
    rw [find?_sort_eq_find?_range (N := N) fun i hi => h.lt_names (by simp [nameSet, hi]),
      ← h.aux]
    refine List.find?_congr fun Q _ => ?_
    by_cases hQ : Q ∈ S.aux
    · have hbit : P.aux.testBit Q = true := by rw [h.aux, testBit_maskOf]; simpa using hQ
      rw [hbit, h.pFindAffineRep_eq hB hwf hQ, testBit_maskOf]
    · have hbit : P.aux.testBit Q = false := by rw [h.aux, testBit_maskOf]; simpa using hQ
      simp [hbit]
  unfold pUnitDelete Cslib.Circuits.Boolean.AffineDisperser4n.unitDelete
  rw [hfind]
  rcases hQ : (S.aux.sort (· ≤ ·)).find? (fun Q => decide (x ∈ (findAffineRep S Q).2))
    with _ | Q
  · exact h
  · have hQaux : Q ∈ S.aux := (Finset.mem_sort _).1 (List.mem_of_find?_eq_some hQ)
    have hQN : Q < N := h.lt_names (by simp [nameSet, hQaux])
    dsimp only
    rw [h.pFindAffineRep_eq hB hwf hQaux, swapWord_eq (h.rep_lt hwf hQaux) hQN]
    exact (h.swap hx hQN (h.rep_lt hwf hQaux) _).dropEqn e x

/-- **`(D4)`.** The packed unit deletion of `x` below `N` represents `applyStep` of
`.deleteUnitParam x e`. -/
theorem applyStep_deleteUnitParam (h : Rep N E P S) (hS : S.Valid f) {x : ℕ} (hx : x < N)
    (e : ℕ) : Rep N E (pUnitDelete N E x e P) (applyStep S (.deleteUnitParam x e)) :=
  h.unitDelete (h.bounded hS) hS.wf hx e

end Rep

/-! ### Swapping an auxiliary argument of the minimal gate -/

/-- `auxArgs` on a gate row: an auxiliary argument with the other argument, read off the
argument codes and the auxiliary mask. -/
@[expose] def pAuxArgs (P : PackedState) (r : GateRow) : Option (ℕ × ℕ) :=
  if 2 ≤ r.left ∧ 2 ≤ r.right then
    if P.aux.testBit (r.left - 2) then some (r.left - 2, r.right - 2)
    else if P.aux.testBit (r.right - 2) then some (r.right - 2, r.left - 2)
    else none
  else none

/-- `State.Paired` on the packed state: some pair record names `y`. -/
@[expose] def pPaired (P : PackedState) (y : ℕ) : Bool :=
  P.pairs.any fun c => c.1 / 2 == y || c.2 / 2 == y

/-- The `.swapAuxIn G` step on the packed state, with `(c, T)` the packed representation of the
auxiliary argument `a` of `G` and `b` its other argument: if `T ⊆ {b}`, delete `G` as its literal
after substituting the representation of `a`; otherwise swap `a` with the least unpaired parameter
of `T` other than `b`, if there is one. -/
@[expose] def pSwapAuxIn (N E G : ℕ) (P : PackedState) : PackedState :=
  match pAuxArgs P (P.gateRows.getD G ⟨0, 0, 0⟩) with
  | some (a, b) =>
    let rep := pFindAffineRep N E a P
    if clearBit rep.2 b = 0 then
      let la := if rep.2 = 0 then rep.1.toNat else b + 2
      let ln := if rep.2 = 0 then 0 else rep.1.toNat
      P.deleteGate N G (rowLit (substRow a la ln (P.gateRows.getD G ⟨0, 0, 0⟩))).1
        (rowLit (substRow a la ln (P.gateRows.getD G ⟨0, 0, 0⟩))).2
    else
      match (List.range N).find? (fun y => rep.2.testBit y && (y != b) && P.params.testBit y &&
          !pPaired P y) with
      | some y => P.swap y a (swapWord N y a rep)
      | none => P
  | none => P

private theorem maskOf_eq_zero_iff (s : Finset ℕ) : maskOf s = 0 ↔ s = ∅ := by
  rw [maskOf, Finset.sum_eq_zero_iff, ← Finset.not_nonempty_iff_eq_empty]
  exact ⟨fun H ⟨i, hi⟩ => pow_ne_zero i two_ne_zero (H i hi),
    fun H i hi => absurd ⟨i, hi⟩ H⟩

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- The packed auxiliary arguments of a gate are `auxArgs`. -/
theorem pAuxArgs_eq (h : Rep N E P S) (g : Gate) : pAuxArgs P (rowOf g) = auxArgs S g := by
  obtain ⟨op, l, r⟩ := g
  have haux : ∀ i, P.aux.testBit i = decide (i ∈ S.aux) := fun i => by
    rw [h.aux, testBit_maskOf]
  cases l with
  | const b =>
    have : ¬ 2 ≤ b.toNat := by have := Bool.toNat_le b; omega
    simp [pAuxArgs, auxArgs, rowOf, argCode, this]
  | node u =>
    cases r with
    | const b =>
      have : ¬ 2 ≤ b.toNat := by have := Bool.toNat_le b; omega
      simp [pAuxArgs, auxArgs, rowOf, argCode, this]
    | node v =>
      simp only [pAuxArgs, auxArgs, rowOf, argCode, le_add_iff_nonneg_left, zero_le, and_self,
        ↓reduceIte, Nat.add_sub_cancel, haux]
      by_cases hu : u ∈ S.aux <;> by_cases hv : v ∈ S.aux <;> simp [hu, hv]

/-- The packed pairing test is `State.Paired`. -/
theorem pPaired_eq (h : Rep N E P S) (y : ℕ) : pPaired P y = decide (S.Paired y) := by
  obtain ⟨l, -, hS, hP⟩ := h.pairs
  have hdiv : ∀ (a : ℕ) (b : Bool), (2 * a + b.toNat) / 2 = a := fun a b => by
    cases b <;> simp [Nat.mul_add_div two_pos]
  rw [pPaired, hP, List.any_map, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
  simp only [Function.comp_apply, pairCode, hdiv, Bool.or_eq_true, beq_iff_eq]
  refine ⟨fun ⟨pr, hpr, hc⟩ => ⟨pr, hS ▸ List.mem_toFinset.2 hpr, hc⟩,
    fun ⟨pr, hpr, hc⟩ => ⟨pr, List.mem_toFinset.1 (hS ▸ hpr), hc⟩⟩

/-- **Swapping an auxiliary argument.** On a valid represented state, for a gate `G` of the
state, the packed `.swapAuxIn` step represents `applyStep` of `.swapAuxIn G`. -/
theorem applyStep_swapAuxIn (h : Rep N E P S) (hS : S.Valid f) {G : ℕ} (hG : G ∈ S.gates) :
    Rep N E (pSwapAuxIn N E G P) (applyStep S (.swapAuxIn G)) := by
  have hB := h.bounded hS
  have hGN : G < N := h.lt_names (by simp [nameSet, hG])
  have hrow := h.gateRow G hG
  unfold pSwapAuxIn
  simp only [applyStep]
  rw [hrow, h.pAuxArgs_eq]
  rcases hargs : auxArgs S (S.gate G) with _ | ⟨a, b⟩
  · exact h
  · -- `a` is an auxiliary variable and `b` the other argument of `G`
    have hab : a ∈ S.aux ∧ ((S.gate G).Reads a ∧ (S.gate G).Reads b) := by
      rcases hg : S.gate G with ⟨op, l, r⟩
      rw [hg] at hargs
      cases l with
      | const _ => simp [auxArgs] at hargs
      | node u =>
        cases r with
        | const _ => simp [auxArgs] at hargs
        | node v =>
          simp only [auxArgs] at hargs
          split_ifs at hargs with hu hv
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hargs)
            exact ⟨hu, .inl rfl, .inr rfl⟩
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hargs)
            exact ⟨hv, .inr rfl, .inl rfl⟩
    obtain ⟨ha, hra, hrb⟩ := hab
    have haN : a < N := hB.reads G hG a hra
    have hbN : b < N := hB.reads G hG b hrb
    have hT := h.rep_lt hS.wf ha
    dsimp only
    rw [h.pFindAffineRep_eq hB hS.wf ha]
    dsimp only
    set c := (findAffineRep S a).1
    set T := (findAffineRep S a).2
    have hsub : clearBit (maskOf T) b = 0 ↔ T ⊆ {b} := by
      rw [← maskOf_erase, maskOf_eq_zero_iff, Finset.erase_eq_empty_iff,
        Finset.subset_singleton_iff]
    have hzero : maskOf T = 0 ↔ T = ∅ := maskOf_eq_zero_iff T
    by_cases hTb : T ⊆ {b}
    · rw [ite_eq_left (hsub.2 hTb), ite_eq_left hTb]
      set ℓ : Lit := if T = ∅ then Lit.const c else ⟨.node b, c⟩ with hℓdef
      have hla : (if maskOf T = 0 then c.toNat else b + 2) = argCode ℓ.arg := by
        by_cases hT0 : T = ∅
        · rw [ite_eq_left (hzero.2 hT0)]
          simp [hℓdef, hT0, Lit.const, argCode]
        · rw [ite_eq_right (mt hzero.1 hT0)]
          simp [hℓdef, hT0, argCode]
      have hln : (if maskOf T = 0 then 0 else c.toNat) = ℓ.neg.toNat := by
        by_cases hT0 : T = ∅
        · rw [ite_eq_left (hzero.2 hT0)]
          simp [hℓdef, hT0, Lit.const]
        · rw [ite_eq_right (mt hzero.1 hT0)]
          simp [hℓdef, hT0]
      have hℓ : ∀ y, ℓ.Reads y → y < N := fun y hy => by
        by_cases hT0 : T = ∅
        · simp [hℓdef, hT0, Lit.Reads, Lit.const] at hy
        · have : y = b := by simpa [hℓdef, hT0, Lit.Reads] using hy.symm
          exact this ▸ hbN
      rw [hla, hln, substRow_rowOf, rowLit_rowOf]
      exact h.deleteGate hB hGN fun y hy =>
        (Gate.reads_of_reads_subst (Gate.reads_of_lit_reads hy)).elim
          (fun hy' => hB.reads G hG y hy') fun hy' => hℓ y hy'.2
    · rw [ite_eq_right (mt hsub.1 hTb), ite_eq_right hTb]
      have hfind : (List.range N).find? (fun y => (maskOf T).testBit y && (y != b) &&
          P.params.testBit y && !pPaired P y) =
          (T.sort (· ≤ ·)).find? (fun y => decide (y ≠ b ∧ y ∈ S.unpaired)) := by
        rw [find?_sort_eq_find?_range (N := N) hT]
        refine List.find?_congr fun y _ => ?_
        rw [h.params, testBit_maskOf, h.pPaired_eq]
        by_cases hyT : y ∈ T
        · have hyp : y ∈ S.params := (findAffineRep_spec hS.wf ha).1 hyT
          by_cases hyb : y = b <;> simp [hyT, hyb, hyp, State.unpaired]
        · simp [hyT]
      rw [hfind]
      rcases hy : (T.sort (· ≤ ·)).find? (fun y => decide (y ≠ b ∧ y ∈ S.unpaired)) with _ | y
      · exact h
      · have hyT : y ∈ T := (Finset.mem_sort _).1 (List.mem_of_find?_eq_some hy)
        dsimp only
        rw [swapWord_eq hT haN]
        exact h.swap (hT y hyT) haN hT c

end Rep

end Cslib.Algorithms.WordRAM.Refuter4n
