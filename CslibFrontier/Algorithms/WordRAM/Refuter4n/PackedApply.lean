/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedCases
-- `import all` for the bodies of `ChoiceSpec` and `NoDeletion`, which are not exposed, and for the
-- private search lemmas of `RefuterProofs` (`find?_sort_eq_some`, `findD4_eq_some`,
-- `exists_find_reader_gate`, `findAndOnPair_eq_none`, ...), used here as they are.
import all CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs

/-!
# The packed step of the `4n - 9d` refuter

`pApplyStep` performs a step `StepChoice` of the refuter `applyStep`
(`Cslib.Circuits.Boolean.AffineDisperser4n`) on the packed state `PackedState`, dispatching to the
packed steps of `PackedStep`, `PackedAffineRep` and `PackedCases`. On a valid represented state, at
every step that `chooseStep?` takes, it represents `applyStep` (`Rep.pApplyStep`). This completes
the pure layer of the step programs of issue `#4322` (Milestone 4); no program and no running time
is claimed here.

The side conditions of the packed steps (names below `N`, constraints that are deleted being
constraints, the hypotheses of `Valid.step_pairInSystem_of` in Case 4, a fresh first argument in
pair creation, and the deleted constraints of Case 5a) are discharged from `chooseStep?_spec` and
validity. The fresh equation name of a move is assumed below `E`, as in `Rep.applyStep_moveAffine`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.pApplyStep`: a refuter step on the packed state.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.pApplyStep`: on a valid represented state, the packed
  step represents `applyStep` at every step chosen by `chooseStep?`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Finset
open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.AffineDisperserCore Cslib.Circuits.Boolean.SemiCircuit

variable {n : ℕ}

/-- The refuter step `c` on the packed state. -/
@[expose] def pApplyStep (N E : ℕ) (P : PackedState) : StepChoice → PackedState
  | .deleteConstantGate J => pDeleteConstraint N P (.inl J)
  | .deleteDeadGate J => P.deleteGate N J 0 0
  | .deleteShortEqn e => pDeleteConstraint N P (.inr e)
  | .deleteUnitParam x e => pUnitDelete N E x e P
  | .moveAffine J => P.moveAffine N J (pFreshEqn N E P)
  | .degeneratePair p => pDegeneratePair N E p P
  | .partnersShareChild p => pPartnersShareChild N E p P
  | .pairInSystem p => pPairInSystem N E p P
  | .andOnPair G p => pAndOnPair N E G p P
  | .swapAuxIn G => pSwapAuxIn N E G P
  | .pairCreation G => pPairCreation N G P

/-! ### Pairs -/

/-- Members `p` and `pr.partner p` of a pair with a common child share a child. -/
private theorem share {S : State n} {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p : ℕ}
    (hp : pr.Contains p) (hne : pr.partner p ≠ p) {H : ℕ ⊕ ℕ} (h₁ : H ∈ S.children p)
    (h₂ : H ∈ S.children (pr.partner p)) : S.PartnersShareChild := by
  refine ⟨pr, hpr, H, Finset.mem_inter.2 ?_⟩
  rcases hp with h | h
  · have hpart : pr.partner p = pr.snd := by simp [ZeroPair.partner, h]
    rw [h]
    exact ⟨h₁, hpart ▸ h₂⟩
  · by_cases hf : pr.fst = p
    · exact absurd (show pr.partner p = p by simp [ZeroPair.partner, hf, h]) hne
    · have hpart : pr.partner p = pr.fst := by simp [ZeroPair.partner, hf]
      rw [h]
      exact ⟨hpart ▸ h₂, h₁⟩

/-- A second member of a pair is the partner of the first. -/
private theorem eq_partner {pr : ZeroPair} {x y : ℕ} (hx : pr.Contains x) (hy : pr.Contains y)
    (hxy : y ≠ x) : y = pr.partner x := by
  unfold ZeroPair.partner
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> split_ifs <;> omega

private theorem reads_cases {g : Gate} {p w x : ℕ}
    (hargs : (g.left = .node p ∧ g.right = .node w) ∨ (g.left = .node w ∧ g.right = .node p))
    (hx : g.Reads x) : x = p ∨ x = w := by
  rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rcases hx with hx | hx
  · exact .inl (Arg.node.inj (hx.symm.trans hl))
  · exact .inr (Arg.node.inj (hx.symm.trans hr))
  · exact .inr (Arg.node.inj (hx.symm.trans hl))
  · exact .inl (Arg.node.inj (hx.symm.trans hr))

/-! ### Pair creation -/

/-- In pair creation, the first argument of the minimal gate is the first member of no pair. -/
private theorem fresh_pairCreation {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hN : NoDeletion S) (hAOP : findAndOnPair S = none) (hne : S.gates.Nonempty)
    (haux : S.auxIn (S.gates.min' hne) = 0) :
    ∀ t, (S.gate (S.gates.min' hne)).left = .node t → ∀ pr ∈ S.pairs, pr.fst ≠ t := by
  obtain ⟨hD1, -, -, -, hMov⟩ := hN
  obtain ⟨hG, hmin⟩ := State.Valid.minGate_reads hS hne
  set G := S.gates.min' hne with hGdef
  obtain ⟨t₁, t₂, hl, hr, htne⟩ := exists_args_of_not_degenerate (findD1_eq_none hD1 G hG)
  have hnotaux : t₁ ∉ S.aux ∧ t₂ ∉ S.aux := by
    unfold State.auxIn at haux
    rw [hl, hr] at haux
    constructor <;> intro hm <;> simp [State.auxArg, hm] at haux
  have hpar : ∀ t, (S.gate G).Reads t → t ∉ S.aux → t ∈ S.params := fun t ht hta => by
    rcases Finset.mem_union.1 (hS.wf.reads_live G hG t ht) with hp | hg
    · exact (Finset.mem_union.1 hp).resolve_right hta
    · exact absurd hg (hmin t ht)
  have ht₁ := hpar t₁ (Or.inl hl) hnotaux.1
  have ht₂ := hpar t₂ (Or.inr hr) hnotaux.2
  have hna : ¬ IsAffineOp (S.gate G).op := fun haff => by
    rcases findMovable_eq_none hMov G hG haff with h | h
    · simp [hl, isGate, hmin t₁ (Or.inl hl)] at h
    · simp [hr, isGate, hmin t₂ (Or.inr hr)] at h
  intro t hlt pr hpr hfst
  exact (findAndOnPair_eq_none hAOP hG hna hl hr htne ht₁ ht₂).1
    ⟨pr, hpr, Or.inl (hfst.trans (Arg.node.inj (hlt.symm.trans hl)))⟩

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- **Case 5a.** On a valid represented state, at the step `.andOnPair G p` chosen by
`chooseStep?`, the packed Case 5a represents `applyStep`. -/
private theorem applyStep_andOnPair (h : Rep N E P S) (hS : S.Valid f) {u G p : ℕ}
    (hout : S.out.arg = .node u) (hN : NoDeletion S) (hDP : findDegeneratePair S = none)
    (hPSC : findPartnersShareChild S = none) (hAOP : findAndOnPair S = some (G, p))
    (huG : u ≠ G) :
    Rep N E (pAndOnPair N E G p P) (applyStep S (.andOnPair G p)) := by
  have hndeg := findDegeneratePair_eq_none hS hDP
  have hnsh := findPartnersShareChild_eq_none hS hPSC
  obtain ⟨hG, -, -, w, hpw, -, hwpar, hGp, hGw, hw⟩ := findAndOnPair_eq_some hAOP
  have hargs := Gate.args_of_reads hpw hGp hGw
  have hwN : w < N := Finset.mem_range.1 (h.names (by simp [nameSet, hwpar]))
  rw [h.pAndOnPair_eq hS hG p]
  simp only [applyStep]
  rw [hw]
  rcases hf : findPair S p with _ | pr
  · exact h
  obtain ⟨hprm, hprp⟩ := findPair_spec hf
  dsimp only
  rcases hl : getChildren S (pr.partner p) with _ | ⟨Hr, l⟩
  · exact h
  dsimp only
  have hHr : Hr ∈ S.children (pr.partner p) := mem_getChildren.1 (by rw [hl]; simp)
  have hrp : pr.partner p ≠ p := pr.partner_ne (hS.pair_mem pr hprm).2.2 hprp
  have hGch : ∀ {x}, (S.gate G).Reads x → (.inl G : ℕ ⊕ ℕ) ∈ S.children x := fun hx =>
    (inl_mem_children _).2 ⟨hG, hx⟩
  have hnotw : ¬ pr.Contains w := fun hcw => hnsh (share hprm hprp hrp (hGch hGp)
    (by rw [← eq_partner hprp hcw (Ne.symm hpw)]; exact hGch hGw))
  have hHrG : Hr ≠ .inl G := fun he => hnsh (share hprm hprp hrp (hGch hGp) (he ▸ hHr))
  refine h.andOnPairStep hS hG hprm hwN (fun q hq => (findPair_spec hq).1) _ _
    (elim_mem_of_mem_children hHr) hHrG ?_
  intro q hq hb
  obtain ⟨hqm, hqw⟩ := findPair_spec hq
  obtain ⟨K, hfK, hKm, hKr⟩ := exists_find_reader_gate hS hG hout hN.2.1 huG
  have hKG : K ≠ G := (of_decide_eq_true (find?_sort_eq_some hfK).2).1
  rw [hfK, Option.getD_some]
  refine ⟨hKm, hKG, fun hHK => ?_⟩
  rw [hq]
  dsimp only
  have hqp : S.Paired (q.partner w) := ⟨q, hqm, q.contains_partner hqw⟩
  obtain ⟨H', l', hl'⟩ := exists_getChildren_cons (S := S) (p := q.partner w)
    (by rw [State.Paired.deg_eq_one hndeg hqp])
  rw [hl', List.headD_cons]
  have hH' : H' ∈ S.children (q.partner w) := mem_getChildren.1 (by rw [hl']; simp)
  have hqpar : q.partner w ∈ S.params := hS.mem_params_of_contains hqm (q.contains_partner hqw)
  -- `q` contains a member of `pr`, so `q = pr` and `pr` contains `w`, which is impossible
  have hq_ne : ∀ x, pr.Contains x → q.partner w = x → False := fun x hx he => by
    have hcx : q.Contains x := he ▸ q.contains_partner hqw
    obtain rfl := hS.pair_unique hprm hqm hx hcx
    exact hnotw hqw
  refine ⟨elim_mem_of_mem_children hH', fun he => ?_, fun he => ?_⟩
  · have hGr : (S.gate G).Reads (q.partner w) := ((inl_mem_children _).1 (he ▸ hH')).2
    have hwq : q.partner w ≠ w := q.partner_ne (hS.pair_mem q hqm).2.2 hqw
    exact (reads_cases hargs hGr).elim (hq_ne p hprp) hwq
  · have hKr' : (S.gate K).Reads (pr.partner p) := ((inl_mem_children _).1 (hHK ▸ hHr)).2
    have hKq : (S.gate K).Reads (q.partner w) := ((inl_mem_children _).1 (he ▸ hH')).2
    have hGr : G ≠ pr.partner p := fun he' =>
      hS.wf.notMem_gates_of_mem_params (hS.mem_params_of_contains hprm
        (pr.contains_partner hprp)) (he' ▸ hG)
    rcases reads_cases (Gate.args_of_reads hGr hKr hKr') hKq with he' | he'
    · exact hS.wf.notMem_gates_of_mem_params hqpar (he' ▸ hG)
    · exact hq_ne _ (pr.contains_partner hprp) he'

/-- **The packed step.** On a valid represented state, at every step `c` chosen by
`chooseStep?`, `pApplyStep` represents `applyStep S c`, when the fresh equation name of `S` is
below `E` (used only by a move). -/
theorem pApplyStep (h : Rep N E P S) (hS : S.Valid f) {c : StepChoice}
    (hc : chooseStep? S = some c) (hE : S.freshEqn < E) :
    Rep N E (Refuter4n.pApplyStep N E P c) (applyStep S c) := by
  have hB := h.bounded hS
  have hpar : ∀ {i}, i ∈ S.params → i < N := fun hi =>
    Finset.mem_range.1 (h.names (by simp [nameSet, hi]))
  obtain ⟨u, hout, hu, hspec⟩ := chooseStep?_spec hc
  cases c with
  | deleteConstantGate J => exact h.applyStep_deleteConstantGate hB (findD1_eq_some hspec).1
  | deleteDeadGate J => exact h.applyStep_deleteDeadGate hB (findD2_eq_some hspec.2).1
  | deleteShortEqn e => exact h.applyStep_deleteShortEqn hB (findD3_eq_some hspec.2.2).1
  | deleteUnitParam x e =>
    exact h.applyStep_deleteUnitParam hS
      (hpar (State.mem_unpaired.1 (findD4_eq_some hspec.2.2.2).1).1) e
  | moveAffine J => exact h.applyStep_moveAffine (findMovable_eq_some hspec.2.2.2.2).1 hE
  | degeneratePair p =>
    exact h.applyStep_degeneratePair hS
      (hpar (hS.mem_params_of_paired (findDegeneratePair_eq_some hspec.2).1))
  | partnersShareChild p =>
    obtain ⟨pr, hpr, rfl, -⟩ := findPartnersShareChild_eq_some hspec.2.2
    exact h.applyStep_partnersShareChild hS (hpar (hS.pair_mem pr hpr).1)
  | pairInSystem p =>
    obtain ⟨-, hDP, hPSC, hPIS⟩ := hspec
    have hp := hS.mem_params_of_paired (findPairInSystem_eq_some hPIS).1
    exact h.applyStep_pairInSystem hS (findDegeneratePair_eq_none hS hDP)
      (findPartnersShareChild_eq_none hS hPSC) (hpar hp)
      fun hr => hu (Arg.node.inj (hout.symm.trans hr) ▸ hp)
  | andOnPair G p =>
    obtain ⟨hN, hDP, hPSC, -, hAOP, huG⟩ := hspec
    exact h.applyStep_andOnPair hS hout hN hDP hPSC hAOP huG
  | swapAuxIn G =>
    obtain ⟨-, -, -, -, -, hne, rfl, -⟩ := hspec
    exact h.applyStep_swapAuxIn hS (Finset.min'_mem _ hne)
  | pairCreation G =>
    obtain ⟨hN, -, -, -, hAOP, hne, rfl, haux, -⟩ := hspec
    exact h.applyStep_pairCreation hB (Finset.min'_mem _ hne)
      (fresh_pairCreation hS hN hAOP hne haux)

end Rep

end Cslib.Algorithms.WordRAM.Refuter4n
