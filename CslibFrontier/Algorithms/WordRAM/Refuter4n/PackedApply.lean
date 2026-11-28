/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedCases
-- `import all` for the bodies of `ChoiceSpec` and `NoDeletion`, which are not exposed.
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

/-! ### Searches of `chooseStep?` -/

private theorem find?_sort_some {s : Finset ℕ} {p : ℕ → Bool} {x : ℕ}
    (h : (s.sort (· ≤ ·)).find? p = some x) : x ∈ s ∧ p x = true :=
  ⟨(Finset.mem_sort _).1 (List.mem_of_find?_eq_some h), List.find?_some h⟩

private theorem find?_sort_none {s : Finset ℕ} {p : ℕ → Bool}
    (h : (s.sort (· ≤ ·)).find? p = none) {x : ℕ} (hx : x ∈ s) : p x = false := by
  simpa using List.find?_eq_none.1 h x ((Finset.mem_sort _).2 hx)

private theorem findSome?_sort_none {α : Type*} {s : Finset ℕ} {g : ℕ → Option α}
    (h : (s.sort (· ≤ ·)).findSome? g = none) {x : ℕ} (hx : x ∈ s) : g x = none :=
  List.findSome?_eq_none_iff.1 h x ((Finset.mem_sort _).2 hx)

private theorem mem_params_of_findD4 {S : State n} {x e : ℕ} (h : findD4 S = some (x, e)) :
    x ∈ S.params := by
  obtain ⟨x', hx', hg⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hg
  obtain ⟨e', -, he'⟩ := List.exists_of_findSome?_eq_some hg
  split_ifs at he'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he')
  exact (State.mem_unpaired.1 ((Finset.mem_sort _).1 hx')).1

private theorem not_degeneratePair {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (h : findDegeneratePair S = none) : ¬ S.DegeneratePair := fun ⟨p, hp, hd⟩ => by
  have := find?_sort_none h (hS.mem_params_of_paired hp)
  simp [hp, hd] at this

private theorem not_partnersShareChild {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (h : findPartnersShareChild S = none) : ¬ S.PartnersShareChild := fun ⟨pr, hpr, hsh⟩ => by
  have := find?_sort_none h (hS.pair_mem pr hpr).1
  simp only [decide_eq_false_iff_not] at this
  exact this ⟨pr, hpr, rfl, hsh⟩

private theorem elim_of_mem_children {S : State n} {p : ℕ} {c : ℕ ⊕ ℕ}
    (hc : c ∈ S.children p) : c.elim (· ∈ S.gates) (· ∈ S.eqns) := by
  rcases c with J | e
  · exact ((inl_mem_children _).1 hc).1
  · exact ((inr_mem_children _).1 hc).1

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

/-! ### The reader of a gate -/

private theorem exists_reader {S : State n} {f : BooleanFunction n} (hS : S.Valid f) {u G : ℕ}
    (hG : G ∈ S.gates) (hout : S.out.arg = .node u) (hD2 : findD2 S = none) (huG : u ≠ G) :
    ∃ K, (S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G ∧ (S.gate K).Reads G)) = some K ∧
      K ∈ S.gates ∧ K ≠ G ∧ (S.gate K).Reads G := by
  have h2 := find?_sort_none hD2 hG
  obtain ⟨K₀, hK₀, hK₀r⟩ : ∃ K ∈ S.gates, (S.gate K).Reads G := by
    by_contra hno
    have hno' : ∀ K ∈ S.gates, ¬ (S.gate K).Reads G := fun K hK hr => hno ⟨K, hK, hr⟩
    have hout' : S.out.arg ≠ .node G := fun he => huG (Arg.node.inj (hout.symm.trans he))
    exact absurd h2 (by rw [decide_eq_false_iff_not, not_not]; exact ⟨hno', hout'⟩)
  have hK₀G : K₀ ≠ G := fun he => hS.not_reads_self hK₀ (he ▸ hK₀r)
  rcases hfK : (S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G ∧ (S.gate K).Reads G)) with
    _ | K
  · have := find?_sort_none hfK hK₀
    simp [hK₀G, hK₀r] at this
  · obtain ⟨hK, hd⟩ := find?_sort_some hfK
    simp only [decide_eq_true_eq] at hd
    exact ⟨K, rfl, hK, hd.1, hd.2⟩

/-! ### Pair creation -/

private theorem args_of_not_degenerate {g : Gate} (hg : ¬ g.Degenerate) :
    ∃ u v, g.left = .node u ∧ g.right = .node v ∧ u ≠ v := by
  obtain ⟨hl, hr, hne⟩ := by simpa only [Gate.Degenerate, not_or, not_exists] using hg
  rcases hgl : g.left with c | u
  · exact absurd hgl (hl c)
  rcases hgr : g.right with c | v
  · exact absurd hgr (hr c)
  exact ⟨u, v, rfl, rfl, fun he => hne (hgl.trans (he ▸ hgr.symm))⟩

/-- In pair creation, the first argument of the minimal gate is the first member of no pair. -/
private theorem fresh_pairCreation {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hN : NoDeletion S) (hAOP : findAndOnPair S = none) (hne : S.gates.Nonempty)
    (haux : S.auxIn (S.gates.min' hne) = 0) :
    ∀ t, (S.gate (S.gates.min' hne)).left = .node t → ∀ pr ∈ S.pairs, pr.fst ≠ t := by
  obtain ⟨hD1, -, -, -, hMov⟩ := hN
  obtain ⟨hG, hmin⟩ := State.Valid.minGate_reads hS hne
  set G := S.gates.min' hne with hGdef
  have hnd : ¬ (S.gate G).Degenerate := fun hd => by
    have := find?_sort_none hD1 hG
    simp [(isDegenerate_iff _).2 hd] at this
  obtain ⟨t₁, t₂, hl, hr, htne⟩ := args_of_not_degenerate hnd
  intro t hlt pr hpr hfst
  have ht : t = t₁ := Arg.node.inj (hlt.symm.trans hl)
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
    have := find?_sort_none hMov hG
    simp [haff, hl, hr, isGate, hmin t₁ (Or.inl hl), hmin t₂ (Or.inr hr)] at this
  have := findSome?_sort_none hAOP hG
  simp only [hna, not_false_eq_true, ite_true, hl, hr, htne, ht₁, ht₂, ne_eq, and_self] at this
  split_ifs at this with h1
  exact h1 ⟨pr, hpr, Or.inl (hfst.trans ht)⟩

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n} {f : BooleanFunction n}

/-- **Case 5a.** On a valid represented state, at the step `.andOnPair G p` chosen by
`chooseStep?`, the packed Case 5a represents `applyStep`. -/
private theorem applyStep_andOnPair (h : Rep N E P S) (hS : S.Valid f) {u G p : ℕ}
    (hout : S.out.arg = .node u) (hN : NoDeletion S) (hDP : findDegeneratePair S = none)
    (hPSC : findPartnersShareChild S = none) (hAOP : findAndOnPair S = some (G, p))
    (huG : u ≠ G) :
    Rep N E (pAndOnPair N E G p P) (applyStep S (.andOnPair G p)) := by
  have hndeg := not_degeneratePair hS hDP
  have hnsh := not_partnersShareChild hS hPSC
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
    (elim_of_mem_children hHr) hHrG ?_
  intro q hq hb
  obtain ⟨hqm, hqw⟩ := findPair_spec hq
  obtain ⟨K, hfK, hKm, hKG, hKr⟩ := exists_reader hS hG hout hN.2.1 huG
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
  refine ⟨elim_of_mem_children hH', fun he => ?_, fun he => ?_⟩
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
  | deleteConstantGate J => exact h.applyStep_deleteConstantGate hB (find?_sort_some hspec).1
  | deleteDeadGate J => exact h.applyStep_deleteDeadGate hB (find?_sort_some hspec.2).1
  | deleteShortEqn e => exact h.applyStep_deleteShortEqn hB (find?_sort_some hspec.2.2).1
  | deleteUnitParam x e =>
    exact h.applyStep_deleteUnitParam hS (hpar (mem_params_of_findD4 hspec.2.2.2)) e
  | moveAffine J => exact h.applyStep_moveAffine (find?_sort_some hspec.2.2.2.2).1 hE
  | degeneratePair p => exact h.applyStep_degeneratePair hS (hpar (find?_sort_some hspec.2).1)
  | partnersShareChild p =>
    exact h.applyStep_partnersShareChild hS (hpar (find?_sort_some hspec.2.2).1)
  | pairInSystem p =>
    obtain ⟨-, hDP, hPSC, hPIS⟩ := hspec
    have hp := (find?_sort_some hPIS).1
    exact h.applyStep_pairInSystem hS (not_degeneratePair hS hDP) (not_partnersShareChild hS hPSC)
      (hpar hp) fun hr => hu (Arg.node.inj (hout.symm.trans hr) ▸ hp)
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
