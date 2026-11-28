/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedState
import Mathlib.Data.List.GetD

/-!
# Packed primitive operations of the `4n - 9d` refuter

The refuter step `applyStep` (`Cslib.Circuits.Boolean.AffineDisperser4n`) is built from a few
state operations: rerouting a name to a literal (inside `State.deleteGate`, `State.restrict` and
`State.deleteEqn`), dropping equations, moving an affine gate into the affine system, the affine
reparameterisation `State.swap` and pair creation `State.addPair`. This file gives each of them as
a word-level operation on the packed state `PackedState` and proves that it represents the state
operation (`Rep`). This is the pure layer of the step programs of issue `#4322` (Milestone 4); no
program and no running time is claimed here.

The operations read and write only words: names, argument codes `argCode`, negation bits and
packed rows. A literal `ℓ` enters as its argument code `argCode ℓ.arg` and negation bit
`ℓ.neg.toNat`.

* **Gate rows.** Rerouting `v` rewrites every row by `substRow`: argument codes `v + 2` become the
  code of the literal, and its negation is absorbed into the truth table by `permTT`, which
  permutes the four bits (`substRow_rowOf`).
* **Equation words.** Rerouting `v` in an equation is the row substitution `substWord` of the
  parameter map applied to the equation word, with the literal as the row `litWordOf`
  (`substWord_eqnWord`, `litWordOf_eq`). A deleted equation gets the word `0`.
* **Output.** `substOut` rewrites the output code (`substOut_litCode`).
* **Masks.** Erasing and inserting a name clear and set its bit (`maskOf_erase`, `maskOf_insert`).
* **Moved gates.** The equation of a moved affine gate is computed from its row by `affWord`
  (`affWord_rowOf`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.clearBit`, `setBit`: mask updates.
* `Cslib.Algorithms.WordRAM.Refuter4n.permTT`, `negBit`, `substCode`, `substRow`, `substOut`:
  rerouting in gate rows and in the output.
* `Cslib.Algorithms.WordRAM.Refuter4n.argWord`, `litWordOf`, `affWord`: rows of literals and of
  moved gates.
* `Cslib.Algorithms.WordRAM.Refuter4n.pairAvoids`: the pair records avoiding a name.
* `Cslib.Algorithms.WordRAM.Refuter4n.Bounded`: names read by a state are below `N`.
* `Cslib.Algorithms.WordRAM.Refuter4n.PackedState.subst`, `PackedState.deleteGate`,
  `PackedState.restrictAvoid`, `PackedState.deleteEqn`, `PackedState.dropEqn`,
  `PackedState.dropTrivialEqn`, `PackedState.moveAffine`, `PackedState.swap`,
  `PackedState.addPair`: the packed operations.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.testBit_eqnWord`, `argCode_eq_node`: the bits of an
  equation word, and the codes of nodes.
* `Cslib.Algorithms.WordRAM.Refuter4n.maskOf_erase`, `maskOf_insert`, `permTT_ttOf`,
  `substRow_rowOf`, `substOut_litCode`, `litWordOf_eq`, `substWord_eqnWord`, `affWord_rowOf`: the
  word operations are the operations on gates, literals and equations.
* `Cslib.Algorithms.WordRAM.Refuter4n.permTT_lt`, `rowLt_substRow`: rerouted rows stay within
  range.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.deleteGate`, `Rep.restrictAvoid`, `Rep.fixConst`,
  `Rep.deleteEqn`, `Rep.dropEqn`, `Rep.dropTrivialEqn`, `Rep.moveAffine`, `Rep.swap`,
  `Rep.addPair`: each packed operation represents its state operation. The hypotheses are names
  below `N` (and `E` for a new equation name), the moved gate for `Rep.moveAffine`, for
  `Rep.addPair` a new pair, and, for the operations that reroute a name, a bounded state
  (`Bounded`: the names read by equations, gates and the output are below `N`).
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.bounded`, `Bounded.deleteGate`, `Bounded.restrict`,
  `Bounded.deleteEqn`, `Bounded.dropEqn`, `Bounded.dropTrivialEqn`, `Bounded.swap`,
  `Bounded.addPair`, `Bounded.moveAffine`: valid represented states are bounded, and the state
  operations preserve boundedness, so a step can chain operations.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Finset
open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.AffineDisperserCore Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Algorithms.WordRAM.XORSATDense
open scoped symmDiff

variable {n : ℕ}

/-! ### Masks -/

/-- Clear bit `i` of the mask `m`. -/
@[expose] def clearBit (m i : ℕ) : ℕ :=
  m ^^^ (m &&& 2 ^ i)

/-- Set bit `i` of the mask `m`. -/
@[expose] def setBit (m i : ℕ) : ℕ :=
  m ||| 2 ^ i

/-- Erasing a name clears its bit. -/
theorem maskOf_erase (s : Finset ℕ) (i : ℕ) : maskOf (s.erase i) = clearBit (maskOf s) i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_maskOf, clearBit, Nat.testBit_xor, Nat.testBit_and, testBit_maskOf,
    Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- Inserting a name sets its bit. -/
theorem maskOf_insert (s : Finset ℕ) (i : ℕ) : maskOf (insert i s) = setBit (maskOf s) i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_maskOf, setBit, Nat.testBit_or, testBit_maskOf, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-! ### Rerouting in gate rows and in the output -/

/-- The truth table of `fun a b => op (a ^^ n₁) (b ^^ n₂)` from the table `t` of `op`, where
`m = idx n₁ n₂`: bit `idx a b` of the result is bit `idx a b ^^^ m` of `t`. -/
@[expose] def permTT (t m : ℕ) : ℕ :=
  (t.testBit (idx false false ^^^ m)).toNat + 2 * (t.testBit (idx false true ^^^ m)).toNat +
    4 * (t.testBit (idx true false ^^^ m)).toNat + 8 * (t.testBit (idx true true ^^^ m)).toNat

private theorem idx_xor_idx (a b n₁ n₂ : Bool) :
    idx a b ^^^ idx n₁ n₂ = idx (a ^^ n₁) (b ^^ n₂) := by
  cases a <;> cases b <;> cases n₁ <;> cases n₂ <;> decide

/-- Permuting the table of `op` absorbs negations of the inputs. -/
theorem permTT_ttOf (op : Bool → Bool → Bool) (n₁ n₂ : Bool) :
    permTT (ttOf op) (idx n₁ n₂) = ttOf fun a b => op (a ^^ n₁) (b ^^ n₂) := by
  have key : ∀ a b, (ttOf op).testBit (idx a b ^^^ idx n₁ n₂) = op (a ^^ n₁) (b ^^ n₂) :=
    fun a b => by rw [idx_xor_idx, testBit_ttOf]
  rw [permTT, key, key, key, key]
  rfl

/-- A permuted table has four bits. -/
theorem permTT_lt (t m : ℕ) : permTT t m < 16 := by
  unfold permTT
  have := Bool.toNat_le (t.testBit (idx false false ^^^ m))
  have := Bool.toNat_le (t.testBit (idx false true ^^^ m))
  have := Bool.toNat_le (t.testBit (idx true false ^^^ m))
  have := Bool.toNat_le (t.testBit (idx true true ^^^ m))
  omega

/-- The negation bit `ln` absorbed for the argument code `c` when `v` is rerouted. -/
@[expose] def negBit (v ln c : ℕ) : ℕ :=
  if c = v + 2 then ln else 0

/-- The argument code `c` with `v` rerouted to the code `la`. -/
@[expose] def substCode (v la c : ℕ) : ℕ :=
  if c = v + 2 then la else c

/-- Reroute `v` to the literal with argument code `la` and negation bit `ln` in a gate row. -/
@[expose] def substRow (v la ln : ℕ) (r : GateRow) : GateRow :=
  ⟨permTT r.tt (2 * negBit v ln r.left + negBit v ln r.right), substCode v la r.left,
    substCode v la r.right⟩

/-- The code `v + 2` is the argument `node v`. -/
theorem argCode_eq_node {a : Arg} {v : ℕ} : argCode a = v + 2 ↔ a = .node v := by
  cases a with
  | const b => cases b <;> simp [argCode]
  | node i => simp [argCode]

private theorem negBit_argCode (v : ℕ) (ℓ : Lit) (a : Arg) :
    negBit v ℓ.neg.toNat (argCode a) = (Gate.substNeg a v ℓ).toNat := by
  unfold negBit Gate.substNeg
  by_cases h : a = .node v
  · simp [h, argCode]
  · rw [ite_eq_right (argCode_eq_node.not.mpr h), ite_eq_right h, Bool.toNat_false]

private theorem substCode_argCode (v : ℕ) (t a : Arg) :
    substCode v (argCode t) (argCode a) = argCode (a.substArg v t) := by
  unfold substCode Arg.substArg
  by_cases h : a = .node v
  · simp [h, argCode]
  · rw [ite_eq_right (argCode_eq_node.not.mpr h), ite_eq_right h]

/-- Rerouting in a gate row is `Gate.subst`. -/
theorem substRow_rowOf (g : Gate) (v : ℕ) (ℓ : Lit) :
    substRow v (argCode ℓ.arg) ℓ.neg.toNat (rowOf g) = rowOf (g.subst v ℓ) := by
  simp only [substRow, rowOf, negBit_argCode, substCode_argCode]
  rw [show 2 * (Gate.substNeg g.left v ℓ).toNat + (Gate.substNeg g.right v ℓ).toNat =
    idx (Gate.substNeg g.left v ℓ) (Gate.substNeg g.right v ℓ) from rfl, permTT_ttOf]
  rfl

/-- Rerouting keeps a row within range. -/
theorem rowLt_substRow {N v la ln : ℕ} {r : GateRow} (hr : RowLt N r) (hla : la < N + 2) :
    RowLt N (substRow v la ln r) := by
  obtain ⟨-, h2, h3⟩ := hr
  refine ⟨permTT_lt _ _, ?_, ?_⟩ <;> simp only [substRow, substCode] <;> split_ifs <;> assumption

/-- Reroute `v` to the literal with argument code `la` and negation bit `ln` in the output code
`o = 2 · argCode + neg`. -/
@[expose] def substOut (v la ln o : ℕ) : ℕ :=
  if o / 2 = v + 2 then 2 * la + (o % 2 ^^^ ln) else o

/-- Rerouting in the output code is `Lit.subst`. -/
theorem substOut_litCode (v : ℕ) (ℓ o : Lit) :
    substOut v (argCode ℓ.arg) ℓ.neg.toNat (litCode o) = litCode (o.subst v ℓ) := by
  obtain ⟨oa, on⟩ := o
  obtain ⟨la, ln⟩ := ℓ
  have hon := Bool.toNat_le on
  have h2 : litCode ⟨oa, on⟩ / 2 = argCode oa := by simp only [litCode]; omega
  have hm : litCode ⟨oa, on⟩ % 2 = on.toNat := by simp only [litCode]; omega
  unfold substOut Lit.subst
  dsimp only
  rw [h2, hm]
  by_cases h : oa = .node v
  · rw [ite_eq_left (argCode_eq_node.mpr h), ite_eq_left h]
    cases on <;> cases ln <;> simp [litCode]
  · rw [ite_eq_right (argCode_eq_node.not.mpr h), ite_eq_right h]

/-! ### Rows of literals, equations and moved gates -/

private theorem rowWord_symmDiff {N t : ℕ} (ht : t < N) (T : Finset ℕ) (c : Bool) :
    rowWord (toDenseRow N (T ∆ {t}) c) = rowWord (toDenseRow N T c) ^^^ 2 ^ t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_rowWord_toDenseRow, testBit_rowWord_toDenseRow,
    Nat.testBit_two_pow]
  by_cases hi : i < N
  · rw [show decide (t = i) = decide (i = t) from decide_eq_decide.2 eq_comm]
    simp only [hi, ↓reduceIte, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hit : i = t <;> by_cases hm : i ∈ T <;> simp_all
  · simp only [hi, ↓reduceIte, decide_eq_false (show t ≠ i by omega), Bool.xor_false]

private theorem rowWord_xor_rhs (N : ℕ) (T : Finset ℕ) (c b : Bool) :
    rowWord (toDenseRow N T (c ^^ b)) = rowWord (toDenseRow N T c) ^^^ b.toNat * 2 ^ N := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_rowWord_toDenseRow, testBit_rowWord_toDenseRow,
    Nat.testBit_mul_two_pow, Nat.testBit_bool_toNat]
  by_cases hi : i < N
  · simp [hi, show ¬ N ≤ i by omega]
  · by_cases hiN : i = N
    · subst hiN
      simp
    · simp [hi, hiN, show i - N ≠ 0 by omega]

private theorem rowWord_singleton {N J : ℕ} (hJ : J < N) (c : Bool) :
    rowWord (toDenseRow N {J} c) = 2 ^ J ^^^ c.toNat * 2 ^ N := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_rowWord_toDenseRow, Nat.testBit_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_bool_toNat]
  by_cases hi : i < N
  · rw [show decide (J = i) = decide (i = J) from decide_eq_decide.2 eq_comm]
    simp [hi, show ¬ N ≤ i by omega]
  · by_cases hiN : i = N
    · subst hiN
      simp [show J ≠ i by omega]
    · simp [hi, hiN, show J ≠ i by omega, show i - N ≠ 0 by omega]

/-- The row of an argument code: the constant `a` at bit `N` for `a < 2`, and the term `a - 2`
otherwise. -/
@[expose] def argWord (N a : ℕ) : ℕ :=
  if a < 2 then a * 2 ^ N else 2 ^ (a - 2)

/-- The row of the literal with argument code `la` and negation bit `ln`. -/
@[expose] def litWordOf (N la ln : ℕ) : ℕ :=
  argWord N la ^^^ ln * 2 ^ N

/-- `litWordOf` computes the row `litWord` of a literal from its codes. -/
theorem litWordOf_eq {N : ℕ} {ℓ : Lit} (h : ∀ y, ℓ.Reads y → y < N) :
    litWordOf N (argCode ℓ.arg) ℓ.neg.toNat = litWord N ℓ := by
  obtain ⟨a, neg⟩ := ℓ
  cases a with
  | const b =>
    have hb : b.toNat < 2 := by have := Bool.toNat_le b; omega
    change argWord N b.toNat ^^^ neg.toNat * 2 ^ N = rowWord (toDenseRow N ∅ (b ^^ neg))
    rw [argWord, ite_eq_left hb]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_mul_two_pow, Nat.testBit_bool_toNat, Nat.testBit_mul_two_pow,
      Nat.testBit_bool_toNat, testBit_rowWord_toDenseRow]
    by_cases hi : i < N
    · simp [hi, show ¬ N ≤ i by omega]
    · by_cases hiN : i = N
      · subst hiN
        simp
      · simp [hi, hiN, show i - N ≠ 0 by omega]
  | node y =>
    have hy : y < N := h y rfl
    change argWord N (y + 2) ^^^ neg.toNat * 2 ^ N = rowWord (toDenseRow N {y} neg)
    rw [argWord, ite_eq_right (by omega), Nat.add_sub_cancel, rowWord_singleton hy]

private theorem rowWord_addArg {N : ℕ} (T : Finset ℕ) (c b : Bool) {a : Arg}
    (ha : argCode a < N + 2) :
    rowWord (toDenseRow N (addArg (T, c) b a).1 (addArg (T, c) b a).2) =
      rowWord (toDenseRow N T c) ^^^ (if b then argWord N (argCode a) else 0) := by
  cases b
  · simp [addArg]
  · cases a with
    | node t =>
      have ht : t < N := by simp only [argCode] at ha; omega
      simp only [addArg, ↓reduceIte, argCode, argWord, show ¬ t + 2 < 2 by omega,
        Nat.add_sub_cancel]
      exact rowWord_symmDiff ht T c
    | const v =>
      have hv : v.toNat < 2 := by have := Bool.toNat_le v; omega
      simp only [addArg, ↓reduceIte, argCode, argWord, hv]
      exact rowWord_xor_rhs N T c v

/-- The equation word of the affine gate with row `r` moved into the affine system as `J`
(`affEqn`): the terms `J`, `left` (if the operation depends on it) and `right` (likewise), the
constant `op false false` at bit `N` and the alive flag at bit `N + 1`. -/
@[expose] def affWord (N : ℕ) (r : GateRow) (J : ℕ) : ℕ :=
  let c₀ := r.tt.testBit 0
  (2 ^ J ^^^ c₀.toNat * 2 ^ N ^^^ (if r.tt.testBit 2 ^^ c₀ then argWord N r.left else 0) ^^^
    (if r.tt.testBit 1 ^^ c₀ then argWord N r.right else 0)) ||| 2 ^ (N + 1)

/-- `affWord` computes the word of the equation `affEqn` from the row of the gate. -/
theorem affWord_rowOf {N J : ℕ} (hJ : J < N) {g : Gate} (hl : argCode g.left < N + 2)
    (hr : argCode g.right < N + 2) : affWord N (rowOf g) J = eqnWord N (affEqn g J) true := by
  have h0 : (ttOf g.op).testBit 0 = g.op false false := testBit_ttOf g.op false false
  have h1 : (ttOf g.op).testBit 1 = g.op false true := testBit_ttOf g.op false true
  have h2 : (ttOf g.op).testBit 2 = g.op true false := testBit_ttOf g.op true false
  simp only [affWord, rowOf, h0, h1, h2, eqnWord, ite_true]
  congr 1
  rw [← rowWord_singleton hJ, ← rowWord_addArg _ _ _ hl, ← rowWord_addArg _ _ _ hr]
  rfl

/-- The bits of an equation word: terms below `N`, the right-hand side at `N` and the alive flag
at `N + 1`. -/
theorem testBit_eqnWord (N : ℕ) (e : Equation) (alive : Bool) (i : ℕ) :
    (eqnWord N e alive).testBit i =
      ((if i < N then decide (i ∈ e.terms) else (decide (i = N) && e.rhs)) ||
        (decide (i = N + 1) && alive)) := by
  rw [eqnWord, Nat.testBit_or, testBit_rowWord_toDenseRow]
  congr 1
  cases alive
  · simp
  · simp only [ite_true, Nat.testBit_two_pow, Bool.and_true]
    exact decide_eq_decide.2 eq_comm

/-- **Equation update.** Rerouting `v` to `ℓ` in an equation (`Equation.subst`) is the row
substitution `substWord` of the parameter map applied to its word, with the row of `ℓ`. -/
theorem substWord_eqnWord {N v : ℕ} (hv : v < N) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N)
    {e : Equation} (he : ∀ j ∈ e.terms, j < N) (alive : Bool) :
    substWord v (litWord N ℓ) (eqnWord N e alive) = eqnWord N (e.subst v ℓ) alive := by
  have hbit : (eqnWord N e alive).testBit v = decide (v ∈ e.terms) := by
    rw [testBit_eqnWord]
    simp [hv, show v ≠ N + 1 by omega]
  unfold substWord
  rw [hbit]
  by_cases hve : v ∈ e.terms
  · simp only [hve, decide_true, ite_true]
    obtain ⟨T, r⟩ := e
    obtain ⟨a, neg⟩ := ℓ
    rw [Equation.subst, ite_eq_left hve]
    clear hbit
    cases a with
    | const b =>
      change eqnWord N ⟨T, r⟩ alive ^^^ 2 ^ v ^^^ rowWord (toDenseRow N ∅ (b ^^ neg)) =
        eqnWord N ⟨T.erase v, r ^^ b ^^ neg⟩ alive
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor, Nat.testBit_xor, testBit_eqnWord, testBit_eqnWord, Nat.testBit_two_pow,
        testBit_rowWord_toDenseRow]
      rcases lt_trichotomy i N with hi | hi | hi
      · have h3 : i ≠ N := by omega
        have h4 : i ≠ N + 1 := by omega
        rw [show decide (v = i) = decide (i = v) from decide_eq_decide.2 eq_comm]
        by_cases h1 : i ∈ T <;> by_cases h2 : i = v <;> simp_all
      · simp [hi, show v ≠ N by omega]
      · simp [show ¬ i < N by omega, show i ≠ N by omega, show v ≠ i by omega]
    | node t =>
      have ht : t < N := hℓ t rfl
      change eqnWord N ⟨T, r⟩ alive ^^^ 2 ^ v ^^^ rowWord (toDenseRow N {t} neg) =
        eqnWord N ⟨T.erase v ∆ {t}, r ^^ neg⟩ alive
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor, Nat.testBit_xor, testBit_eqnWord, testBit_eqnWord, Nat.testBit_two_pow,
        testBit_rowWord_toDenseRow]
      rcases lt_trichotomy i N with hi | hi | hi
      · have h3 : i ≠ N := by omega
        have h4 : i ≠ N + 1 := by omega
        rw [show decide (v = i) = decide (i = v) from decide_eq_decide.2 eq_comm]
        by_cases h1 : i ∈ T <;> by_cases h2 : i = v <;> by_cases h5 : i = t <;>
          simp_all [Finset.mem_symmDiff]
      · simp [hi, show v ≠ N by omega]
      · simp [show ¬ i < N by omega, show i ≠ N by omega, show v ≠ i by omega]
  · simp only [hve, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [Equation.subst_of_notMem hve]

/-! ### Packed operations -/

/-- The pair record `c` avoids the name `x`. -/
@[expose] def pairAvoids (x : ℕ) (c : ℕ × ℕ) : Bool :=
  c.1 / 2 != x && c.2 / 2 != x

/-- Reroute `v` to the literal with argument code `la` and negation bit `ln` in every gate row,
every equation word and the output (`SemiCircuit.subst`). -/
@[expose] def PackedState.subst (N v la ln : ℕ) (P : PackedState) : PackedState :=
  { P with
    gateRows := P.gateRows.map (substRow v la ln)
    eqnRows := P.eqnRows.map (substWord v (litWordOf N la ln))
    out := substOut v la ln P.out }

/-- Delete the gate `J`, rerouting it to the literal `(la, ln)` (`State.deleteGate`). -/
@[expose] def PackedState.deleteGate (N J la ln : ℕ) (P : PackedState) : PackedState :=
  { P.subst N J la ln with gates := clearBit P.gates J }

/-- Restrict the parameter `x` to the literal `(la, ln)`, keeping the pairs avoiding `x`
(`State.restrict x ℓ (S.pairsAvoid x)`, hence `State.fixConst`). -/
@[expose] def PackedState.restrictAvoid (N x la ln : ℕ) (P : PackedState) : PackedState :=
  { P.subst N x la ln with
    params := clearBit P.params x
    pairs := P.pairs.filter (pairAvoids x)
    phiRows := P.phiRows.map (substWord x (litWordOf N la ln)) }

/-- Delete the equation `e` and the auxiliary variable `v`, rerouting `v` to the literal
`(la, ln)` (`State.deleteEqn`). -/
@[expose] def PackedState.deleteEqn (N e v la ln : ℕ) (P : PackedState) : PackedState :=
  { P.subst N v la ln with
    aux := clearBit P.aux v
    eqnRows := (P.eqnRows.map (substWord v (litWordOf N la ln))).set e 0 }

/-- Drop the equation `e` and the auxiliary variable `v` (`State.dropEqn`). -/
@[expose] def PackedState.dropEqn (e v : ℕ) (P : PackedState) : PackedState :=
  { P with aux := clearBit P.aux v, eqnRows := P.eqnRows.set e 0 }

/-- Drop the equation `e` (`State.dropTrivialEqn`). -/
@[expose] def PackedState.dropTrivialEqn (e : ℕ) (P : PackedState) : PackedState :=
  { P with eqnRows := P.eqnRows.set e 0 }

/-- Move the gate `J` into the affine system with the equation name `e` (`State.moveAffine`). -/
@[expose] def PackedState.moveAffine (N J e : ℕ) (P : PackedState) : PackedState :=
  { P with
    gates := clearBit P.gates J
    aux := setBit P.aux J
    eqnRows := P.eqnRows.set e (affWord N (P.gateRows.getD J ⟨0, 0, 0⟩) J) }

/-- Exchange the parameter `x` and the auxiliary variable `Q`, substituting the row `u` for `x`
in the parameter map (`State.swap`). -/
@[expose] def PackedState.swap (x Q u : ℕ) (P : PackedState) : PackedState :=
  { P with
    params := setBit (clearBit P.params x) Q
    aux := setBit (clearBit P.aux Q) x
    phiRows := P.phiRows.map (substWord x u) }

/-- Append the pair record `c` (`State.addPair`). -/
@[expose] def PackedState.addPair (c : ℕ × ℕ) (P : PackedState) : PackedState :=
  { P with pairs := P.pairs ++ [c] }

/-! ### Representation of the packed operations -/

private theorem testBit_substWord_of_lt {x u r i : ℕ} (hx : x < i) (hu : u < 2 ^ i) :
    (substWord x u r).testBit i = r.testBit i := by
  unfold substWord
  split_ifs
  · rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_false (by omega),
      Nat.testBit_lt_two_pow hu]
    simp
  · rfl

private theorem nameSet_subset {S S' : State n} (hp : S'.params ⊆ S.params)
    (ha : S'.aux ⊆ S.aux) (hg : S'.gates ⊆ S.gates) : nameSet S' ⊆ nameSet S :=
  Finset.union_subset_union (Finset.union_subset_union hp ha) hg

/-- Setting one word of an equation table to `0` deletes that equation name. -/
private theorem eqnTable_set {N E : ℕ} {L : List ℕ} {s : Finset ℕ} (hlen : L.length = E)
    (halive : ∀ e < E, (L.getD e 0).testBit (N + 1) = decide (e ∈ s))
    (hlt : ∀ x ∈ L, x < 2 ^ (N + 2)) (e : ℕ) :
    (L.set e 0).length = E ∧ (∀ e' ≠ e, (L.set e 0).getD e' 0 = L.getD e' 0) ∧
      (∀ e' < E, ((L.set e 0).getD e' 0).testBit (N + 1) = decide (e' ∈ s.erase e)) ∧
      ∀ x ∈ L.set e 0, x < 2 ^ (N + 2) := by
  have hne : ∀ e' ≠ e, (L.set e 0).getD e' 0 = L.getD e' 0 := fun e' he' => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm he')]
  refine ⟨by rw [List.length_set, hlen], hne, fun e' he' => ?_, fun x hx => ?_⟩
  · by_cases h : e' = e
    · rw [h]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega : e < L.length)]
    · rw [hne e' h, halive e' he']
      simp [Finset.mem_erase, h]
  · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hlt x hx
    · exact Nat.two_pow_pos _

/-! ### Bounded states -/

/-- The names read by the equations, the gates and the output of `S` are below `N`. A valid
represented state is bounded (`Rep.bounded`). Gate deletion, restriction and equation deletion
by a literal reading names below `N`, dropping an equation, swapping, adding a pair, and moving a
gate below `N` preserve it (`Bounded.deleteGate` to `Bounded.moveAffine`). -/
structure Bounded (N : ℕ) (S : State n) : Prop where
  /-- Terms of equations are below `N`. -/
  terms : ∀ e ∈ S.eqns, ∀ j ∈ (S.eqn e).terms, j < N
  /-- Names read by gates are below `N`. -/
  reads : ∀ J ∈ S.gates, ∀ i, (S.gate J).Reads i → i < N
  /-- The name read by the output is below `N`. -/
  out : ∀ i, S.out.Reads i → i < N

namespace Bounded

variable {N : ℕ} {S : State n}

private theorem of_subst (hB : Bounded N S) {S' : State n} {v : ℕ} {ℓ : Lit}
    (hℓ : ∀ y, ℓ.Reads y → y < N) (hg : S'.gates ⊆ S.gates) (he : S'.eqns ⊆ S.eqns)
    (hgate : ∀ K, S'.gate K = (S.gate K).subst v ℓ)
    (heqn : ∀ e, S'.eqn e = (S.eqn e).subst v ℓ) (hout : S'.out = S.out.subst v ℓ) :
    Bounded N S' where
  terms e he' j hj := by
    rw [heqn] at hj
    rcases Equation.mem_of_mem_subst hj with hj | ⟨-, hj⟩
    · exact hB.terms e (he he') j hj
    · exact hℓ j hj
  reads K hK i hi := by
    rw [hgate] at hi
    rcases Gate.reads_of_reads_subst hi with hi | ⟨-, hi⟩
    · exact hB.reads K (hg hK) i hi
    · exact hℓ i hi
  out i hi := by
    rw [hout] at hi
    rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
    · exact hB.out i hi
    · exact hℓ i hi

private theorem of_le (hB : Bounded N S) {S' : State n} (hg : S'.gates ⊆ S.gates)
    (he : S'.eqns ⊆ S.eqns) (hgate : S'.gate = S.gate) (heqn : S'.eqn = S.eqn)
    (hout : S'.out = S.out) : Bounded N S' where
  terms e he' j hj := by
    rw [heqn] at hj
    exact hB.terms e (he he') j hj
  reads K hK i hi := by
    rw [hgate] at hi
    exact hB.reads K (hg hK) i hi
  out i hi := by
    rw [hout] at hi
    exact hB.out i hi

/-- Deleting a gate preserves boundedness. -/
theorem deleteGate (hB : Bounded N S) (J : ℕ) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) :
    Bounded N (S.deleteGate J ℓ) :=
  hB.of_subst hℓ (Finset.erase_subset _ _) (Finset.Subset.refl _) (fun _ => rfl) (fun _ => rfl)
    rfl

/-- Restriction preserves boundedness. -/
theorem restrict (hB : Bounded N S) (x : ℕ) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N)
    (Q : Finset ZeroPair) : Bounded N (S.restrict x ℓ Q) :=
  hB.of_subst hℓ (Finset.Subset.refl _) (Finset.Subset.refl _) (fun _ => rfl) (fun _ => rfl) rfl

/-- Deleting an equation preserves boundedness. -/
theorem deleteEqn (hB : Bounded N S) (e v : ℕ) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) :
    Bounded N (S.deleteEqn e v ℓ) :=
  hB.of_subst hℓ (Finset.Subset.refl _) (Finset.erase_subset _ _) (fun _ => rfl) (fun _ => rfl)
    rfl

/-- Dropping an equation preserves boundedness. -/
theorem dropEqn (hB : Bounded N S) (e v : ℕ) : Bounded N (S.dropEqn e v) :=
  hB.of_le (Finset.Subset.refl _) (Finset.erase_subset _ _) rfl rfl rfl

/-- Dropping a trivial equation preserves boundedness. -/
theorem dropTrivialEqn (hB : Bounded N S) (e : ℕ) : Bounded N (S.dropTrivialEqn e) :=
  hB.of_le (Finset.Subset.refl _) (Finset.erase_subset _ _) rfl rfl rfl

/-- The affine reparameterisation preserves boundedness. -/
theorem swap (hB : Bounded N S) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    Bounded N (S.swap x Q c T) :=
  hB.of_le (Finset.Subset.refl _) (Finset.Subset.refl _) rfl rfl rfl

/-- Pair creation preserves boundedness. -/
theorem addPair (hB : Bounded N S) (pr : ZeroPair) : Bounded N (S.addPair pr) :=
  hB.of_le (Finset.Subset.refl _) (Finset.Subset.refl _) rfl rfl rfl

/-- Moving a gate named below `N` into the affine system preserves boundedness. -/
theorem moveAffine (hB : Bounded N S) {J : ℕ} (hJ : J ∈ S.gates) (hJN : J < N) (e : ℕ) :
    Bounded N (S.moveAffine J e) where
  terms e' he' j hj := by
    change j ∈ (Function.update S.eqn e (affEqn (S.gate J) J) e').terms at hj
    by_cases h' : e' = e
    · subst h'
      rw [Function.update_self] at hj
      rcases mem_addArg hj with hj | hj
      · rcases mem_addArg hj with hj | hj
        · rw [Finset.mem_singleton.1 hj]; exact hJN
        · exact hB.reads J hJ j (Or.inl hj)
      · exact hB.reads J hJ j (Or.inr hj)
    · rw [Function.update_of_ne h'] at hj
      exact hB.terms e' ((Finset.mem_insert.1 he').resolve_left h') j hj
  reads K hK i hi := hB.reads K (Finset.mem_of_mem_erase hK) i hi
  out := hB.out

end Bounded

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n}

/-- A valid represented state is bounded. -/
theorem bounded (h : Rep N E P S) {f : BooleanFunction n} (hS : S.Valid f) : Bounded N S where
  terms _ he _ hj := h.terms_lt hS he hj
  reads J hJ i hi := Finset.mem_range.1 (h.names (hS.wf.reads_live J hJ i hi))
  out _ hi := h.out_lt hS hi

/-- A copy of the private `Rep.lt_of_mem_nameSet` of `PackedState`; it can go once that helper is
public. -/
private theorem lt_of_mem (h : Rep N E P S) {i : ℕ} (hi : i ∈ nameSet S) : i < N :=
  Finset.mem_range.1 (h.names hi)

/-- The state `S` with `v` rerouted to `ℓ` (`SemiCircuit.subst`), the common part of
`State.deleteGate`, `State.restrict` and `State.deleteEqn`. -/
private def substState (S : State n) (v : ℕ) (ℓ : Lit) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.subst v ℓ }

private theorem subst (h : Rep N E P S) (hB : Bounded N S) {v : ℕ}
    (hv : v < N) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) :
    Rep N E (P.subst N v (argCode ℓ.arg) ℓ.neg.toNat) (substState S v ℓ) := by
  have hlw : litWordOf N (argCode ℓ.arg) ℓ.neg.toNat = litWord N ℓ := litWordOf_eq hℓ
  -- An inline copy of the private `argCode_lt` of `PackedState`; it can go once that lemma is
  -- public.
  have hla : argCode ℓ.arg < N + 2 := by
    obtain ⟨a, _⟩ := ℓ
    cases a with
    | const b => have := Bool.toNat_le b; simp only [argCode]; omega
    | node y => have := hℓ y rfl; simp only [argCode]; omega
  have hlwlt := litWord_lt N ℓ
  have hgD : ∀ J, (P.gateRows.map (substRow v (argCode ℓ.arg) ℓ.neg.toNat)).getD J ⟨0, 0, 0⟩ =
      substRow v (argCode ℓ.arg) ℓ.neg.toNat (P.gateRows.getD J ⟨0, 0, 0⟩) := fun J => by
    have := List.getD_map (l := P.gateRows) (d := (⟨0, 0, 0⟩ : GateRow)) (n := J)
      (substRow v (argCode ℓ.arg) ℓ.neg.toNat)
    rwa [show substRow v (argCode ℓ.arg) ℓ.neg.toNat ⟨0, 0, 0⟩ = ⟨0, 0, 0⟩ by
      simp [substRow, substCode, permTT]] at this
  have heD : ∀ e, (P.eqnRows.map (substWord v (litWordOf N (argCode ℓ.arg) ℓ.neg.toNat))).getD e 0 =
      substWord v (litWordOf N (argCode ℓ.arg) ℓ.neg.toNat) (P.eqnRows.getD e 0) := fun e => by
    have := List.getD_map (l := P.eqnRows) (d := 0) (n := e)
      (substWord v (litWordOf N (argCode ℓ.arg) ℓ.neg.toNat))
    rwa [show substWord v (litWordOf N (argCode ℓ.arg) ℓ.neg.toNat) 0 = 0 by simp [substWord]]
      at this
  exact
    { names := h.names
      eqns := h.eqns
      params := h.params
      aux := h.aux
      gates := h.gates
      gateRows_length := by simp [PackedState.subst, h.gateRows_length]
      gateRow := fun J hJ => by
        have hJ' : J ∈ S.gates := hJ
        change (P.gateRows.map (substRow v (argCode ℓ.arg) ℓ.neg.toNat)).getD J ⟨0, 0, 0⟩ =
          rowOf ((S.gate J).subst v ℓ)
        rw [hgD, h.gateRow J hJ', substRow_rowOf]
      gateRow_lt := fun r hr => by
        obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
        exact rowLt_substRow (h.gateRow_lt r₀ hr₀) hla
      eqnRows_length := by simp [PackedState.subst, h.eqnRows_length]
      eqnRow := fun e he => by
        change (P.eqnRows.map (substWord v (litWordOf N (argCode ℓ.arg) ℓ.neg.toNat))).getD e 0 =
          eqnWord N ((S.eqn e).subst v ℓ) true
        rw [heD, h.eqnRow e he, hlw, substWord_eqnWord hv hℓ (hB.terms e he)]
      eqnRow_alive := fun e he => by
        change ((P.eqnRows.map (substWord v (litWordOf N (argCode ℓ.arg) ℓ.neg.toNat))).getD e
          0).testBit (N + 1) = decide (e ∈ S.eqns)
        rw [heD, hlw,
          testBit_substWord_of_lt (by omega) hlwlt, h.eqnRow_alive e he]
      eqnRow_lt := fun x hx => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
        rw [hlw]
        exact substWord_lt (N := N + 1) (by omega)
          (hlwlt.trans_le (Nat.pow_le_pow_right two_pos (by omega))) (h.eqnRow_lt r hr)
      out := by
        change substOut v (argCode ℓ.arg) ℓ.neg.toNat P.out = litCode (S.out.subst v ℓ)
        rw [h.out, substOut_litCode]
      pairs := h.pairs
      phi := ⟨h.phi.length, h.phi.lt, h.phi.eval⟩ }

/-- **Deleting a gate.** `PackedState.deleteGate` represents `State.deleteGate J ℓ`. -/
theorem deleteGate (h : Rep N E P S) (hB : Bounded N S) {J : ℕ}
    (hJ : J < N) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) :
    Rep N E (P.deleteGate N J (argCode ℓ.arg) ℓ.neg.toNat) (S.deleteGate J ℓ) :=
  have h' := h.subst hB hJ hℓ
  { h' with
    names := (nameSet_subset (S := S) (S' := S.deleteGate J ℓ) (Finset.Subset.refl _)
      (Finset.Subset.refl _) (Finset.erase_subset _ _)).trans h.names
    gates := by
      change clearBit P.gates J = maskOf (S.gates.erase J)
      rw [h.gates, maskOf_erase]
    gateRow := fun K hK => h'.gateRow K (Finset.mem_of_mem_erase hK)
    phi := ⟨h.phi.length, h.phi.lt, h.phi.eval⟩ }

/-- **Restriction.** `PackedState.restrictAvoid` represents `State.restrict x ℓ (S.pairsAvoid x)`.
-/
theorem restrictAvoid (h : Rep N E P S) (hB : Bounded N S) {x : ℕ}
    (hx : x < N) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) :
    Rep N E (P.restrictAvoid N x (argCode ℓ.arg) ℓ.neg.toNat)
      (S.restrict x ℓ (S.pairsAvoid x)) :=
  have h' := h.subst hB hx hℓ
  { h' with
    names := (nameSet_subset (S := S) (S' := S.restrict x ℓ (S.pairsAvoid x))
      (Finset.erase_subset _ _) (Finset.Subset.refl _) (Finset.Subset.refl _)).trans h.names
    params := by
      change clearBit P.params x = maskOf (S.params.erase x)
      rw [h.params, maskOf_erase]
    pairs := by
      obtain ⟨l, hl, hS, hP⟩ := h.pairs
      refine ⟨l.filter fun pr => !decide (config.Contains pr x), hl.filter _, ?_, ?_⟩
      · change (l.filter _).toFinset = S.pairsAvoid x
        ext pr
        rw [List.mem_toFinset, List.mem_filter,
          Cslib.Circuits.Boolean.AffineDisperserCore.State.pairsAvoid, Finset.mem_filter, ← hS,
          List.mem_toFinset]
        simp
      · change P.pairs.filter (pairAvoids x) = _
        rw [hP, List.filter_map]
        congr 1
        refine List.filter_congr fun pr _ => ?_
        have h1 : (pairCode pr).1 / 2 = pr.fst := by
          have := Bool.toNat_le pr.fstBias; simp only [pairCode]; omega
        have h2 : (pairCode pr).2 / 2 = pr.snd := by
          have := Bool.toNat_le pr.sndBias; simp only [pairCode]; omega
        rw [Function.comp_apply, pairAvoids, h1, h2]
        by_cases ha : pr.fst = x <;> by_cases hb : pr.snd = x <;>
          simp [ha, hb, Cslib.Circuits.Boolean.AffineDisperserCore.Config.Contains]
    phi := by
      have := h.phi.restrict hx hℓ (S.pairsAvoid x)
      rw [← litWordOf_eq hℓ] at this
      exact this }

/-- **Fixing a parameter.** `PackedState.restrictAvoid N w b.toNat 0` represents
`State.fixConst w b`. -/
theorem fixConst (h : Rep N E P S) (hB : Bounded N S) {w : ℕ}
    (hw : w < N) (b : Bool) : Rep N E (P.restrictAvoid N w b.toNat 0) (S.fixConst w b) :=
  h.restrictAvoid hB (ℓ := Lit.const b) hw fun y hy => absurd hy (by simp [Lit.Reads, Lit.const])

/-- **Deleting an equation.** `PackedState.deleteEqn` represents `State.deleteEqn e v ℓ`. -/
theorem deleteEqn (h : Rep N E P S) (hB : Bounded N S) (e : ℕ) {v : ℕ}
    (hv : v < N) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) :
    Rep N E (P.deleteEqn N e v (argCode ℓ.arg) ℓ.neg.toNat) (S.deleteEqn e v ℓ) :=
  have h' := h.subst hB hv hℓ
  have ht := eqnTable_set h'.eqnRows_length h'.eqnRow_alive h'.eqnRow_lt e
  { h' with
    names := (nameSet_subset (S := S) (S' := S.deleteEqn e v ℓ) (Finset.Subset.refl _)
      (Finset.erase_subset _ _) (Finset.Subset.refl _)).trans h.names
    eqns := (Finset.erase_subset _ _).trans h.eqns
    aux := by
      change clearBit P.aux v = maskOf (S.aux.erase v)
      rw [h.aux, maskOf_erase]
    eqnRows_length := ht.1
    eqnRow := fun e' he' =>
      (ht.2.1 e' (Finset.ne_of_mem_erase he')).trans (h'.eqnRow e' (Finset.mem_of_mem_erase he'))
    eqnRow_alive := ht.2.2.1
    eqnRow_lt := ht.2.2.2
    phi := ⟨h.phi.length, h.phi.lt, h.phi.eval⟩ }

/-- **Dropping an equation.** `PackedState.dropEqn` represents `State.dropEqn e v`. -/
theorem dropEqn (h : Rep N E P S) (e v : ℕ) : Rep N E (P.dropEqn e v) (S.dropEqn e v) :=
  have ht := eqnTable_set h.eqnRows_length h.eqnRow_alive h.eqnRow_lt e
  { h with
    names := (nameSet_subset (S := S) (S' := S.dropEqn e v) (Finset.Subset.refl _)
      (Finset.erase_subset _ _) (Finset.Subset.refl _)).trans h.names
    eqns := (Finset.erase_subset _ _).trans h.eqns
    aux := by
      change clearBit P.aux v = maskOf (S.aux.erase v)
      rw [h.aux, maskOf_erase]
    eqnRows_length := ht.1
    eqnRow := fun e' he' =>
      (ht.2.1 e' (Finset.ne_of_mem_erase he')).trans (h.eqnRow e' (Finset.mem_of_mem_erase he'))
    eqnRow_alive := ht.2.2.1
    eqnRow_lt := ht.2.2.2
    phi := ⟨h.phi.length, h.phi.lt, h.phi.eval⟩ }

/-- **Dropping a trivial equation.** `PackedState.dropTrivialEqn` represents
`State.dropTrivialEqn e`. -/
theorem dropTrivialEqn (h : Rep N E P S) (e : ℕ) :
    Rep N E (P.dropTrivialEqn e) (S.dropTrivialEqn e) :=
  have ht := eqnTable_set h.eqnRows_length h.eqnRow_alive h.eqnRow_lt e
  { h with
    eqns := (Finset.erase_subset _ _).trans h.eqns
    eqnRows_length := ht.1
    eqnRow := fun e' he' =>
      (ht.2.1 e' (Finset.ne_of_mem_erase he')).trans (h.eqnRow e' (Finset.mem_of_mem_erase he'))
    eqnRow_alive := ht.2.2.1
    eqnRow_lt := ht.2.2.2
    phi := ⟨h.phi.length, h.phi.lt, h.phi.eval⟩ }

/-- **Moving an affine gate.** `PackedState.moveAffine` represents `State.moveAffine J e` for a
gate `J` and an equation name `e < E`. -/
theorem moveAffine (h : Rep N E P S) {J e : ℕ} (hJ : J ∈ S.gates) (he : e < E) :
    Rep N E (P.moveAffine N J e) (S.moveAffine J e) := by
  have hJN : J < N := h.lt_of_mem (by simp [nameSet, hJ])
  have hJlen : J < P.gateRows.length := by rw [h.gateRows_length]; exact hJN
  have hrow : P.gateRows.getD J ⟨0, 0, 0⟩ = rowOf (S.gate J) := h.gateRow J hJ
  have hlt : RowLt N (rowOf (S.gate J)) := hrow ▸ h.gateRow_lt _ (by
    rw [List.getD_eq_getElem _ _ hJlen]; exact List.getElem_mem hJlen)
  have hw : affWord N (P.gateRows.getD J ⟨0, 0, 0⟩) J = eqnWord N (affEqn (S.gate J) J) true := by
    rw [hrow, affWord_rowOf hJN hlt.2.1 hlt.2.2]
  have helen : e < P.eqnRows.length := by rw [h.eqnRows_length]; exact he
  have hget : ∀ e', (P.moveAffine N J e).eqnRows.getD e' 0 =
      if e' = e then eqnWord N (affEqn (S.gate J) J) true else P.eqnRows.getD e' 0 := by
    intro e'
    change (P.eqnRows.set e _).getD e' 0 = _
    split_ifs with h'
    · subst h'
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self helen, Option.getD_some, hw]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h')]
  exact
    { names := fun i hi => h.names (by
        have hi' : i ∈ S.params ∪ insert J S.aux ∪ S.gates.erase J := hi
        simp only [nameSet, Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hi' ⊢
        rcases hi' with (hi | rfl | hi) | ⟨-, hi⟩ <;> tauto)
      eqns := Finset.insert_subset_iff.2 ⟨Finset.mem_range.2 he, h.eqns⟩
      params := h.params
      aux := by
        change setBit P.aux J = maskOf (insert J S.aux)
        rw [h.aux, maskOf_insert]
      gates := by
        change clearBit P.gates J = maskOf (S.gates.erase J)
        rw [h.gates, maskOf_erase]
      gateRows_length := h.gateRows_length
      gateRow := fun K hK => h.gateRow K (Finset.mem_of_mem_erase hK)
      gateRow_lt := h.gateRow_lt
      eqnRows_length := by
        change (P.eqnRows.set e _).length = E
        rw [List.length_set, h.eqnRows_length]
      eqnRow := fun e' he' => by
        rw [hget]
        change _ = eqnWord N (Function.update S.eqn e (affEqn (S.gate J) J) e') true
        split_ifs with h'
        · subst h'; rw [Function.update_self]
        · rw [Function.update_of_ne h']
          exact h.eqnRow e' ((Finset.mem_insert.1 he').resolve_left h')
      eqnRow_alive := fun e' he' => by
        rw [hget]
        change _ = decide (e' ∈ insert e S.eqns)
        split_ifs with h'
        · subst h'; simp
        · rw [h.eqnRow_alive e' he']
          simp [Finset.mem_insert, h']
      eqnRow_lt := fun x hx => by
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact h.eqnRow_lt x hx
        · rw [hw]; exact eqnWord_lt _ _ _
      out := h.out
      pairs := h.pairs
      phi := ⟨h.phi.length, h.phi.lt, h.phi.eval⟩ }

/-- **Affine reparameterisation.** `PackedState.swap` with the row of `∑ ((T \ {x}) ∆ {Q}) = c`
represents `State.swap x Q c T`. -/
theorem swap (h : Rep N E P S) {x Q : ℕ} (hx : x < N) (hQ : Q < N) {T : Finset ℕ}
    (hT : ∀ j ∈ T, j < N) (c : Bool) :
    Rep N E (P.swap x Q (rowWord (toDenseRow N (symmDiff (T.erase x) {Q}) c)))
      (S.swap x Q c T) :=
  { h with
    names := fun i hi => by
      have hi' : i ∈ insert Q (S.params.erase x) ∪ insert x (S.aux.erase Q) ∪ S.gates := hi
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hi'
      rcases hi' with ((rfl | ⟨-, hi⟩) | (rfl | ⟨-, hi⟩)) | hi
      · exact Finset.mem_range.2 hQ
      · exact h.names (by simp [nameSet, hi])
      · exact Finset.mem_range.2 hx
      · exact h.names (by simp [nameSet, hi])
      · exact h.names (by simp [nameSet, hi])
    params := by
      change setBit (clearBit P.params x) Q = maskOf (insert Q (S.params.erase x))
      rw [h.params, maskOf_insert, maskOf_erase]
    aux := by
      change setBit (clearBit P.aux Q) x = maskOf (insert x (S.aux.erase Q))
      rw [h.aux, maskOf_insert, maskOf_erase]
    phi := h.phi.swap hx hQ hT c }

/-- **Pair creation.** `PackedState.addPair (pairCode pr)` represents `State.addPair pr` for a
new pair `pr`. -/
theorem addPair (h : Rep N E P S) {pr : ZeroPair} (hpr : pr ∉ S.pairs) :
    Rep N E (P.addPair (pairCode pr)) (S.addPair pr) :=
  { h with
    pairs := by
      obtain ⟨l, hl, hS, hP⟩ := h.pairs
      refine ⟨l ++ [pr], ?_, ?_, ?_⟩
      · rw [List.nodup_append_comm]
        exact List.nodup_cons.2 ⟨fun hm => hpr (hS ▸ List.mem_toFinset.2 hm), hl⟩
      · change (l ++ [pr]).toFinset = insert pr S.pairs
        rw [List.toFinset_append, hS]
        ext
        simp
      · change P.pairs ++ [pairCode pr] = _
        rw [hP, List.map_append]
        rfl
    phi := ⟨h.phi.length, h.phi.lt, h.phi.eval⟩ }

end Rep

end Cslib.Algorithms.WordRAM.Refuter4n
