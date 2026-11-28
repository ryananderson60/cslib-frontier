import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.LinearStrongExtractor

/-! Timing probe for the `rrvFunctions` compiler replacement (`rrvWeakDesign`).

* "old": `oldArgMinFin` / `oldPotential` / `oldBuildPrefix` / `oldFunctions` / `oldGraphBlock` are
  verbatim copies of the base commit's private `argMinFin` / `rrvPotential` / `rrvBuildPrefix` /
  `rrvFunctions` / `graphBlock` (renamed only). Compiled in this file, so the `@[csimp]` lemma does
  not apply to them.
* "now": `Cslib.AffineDisperser.Li.rrvWeakDesign`, which this tree compiles through the
  `@[csimp]` replacement.
* "ref": `refFunctions`, an independent `Array` implementation of the same greedy choice
  (first minimum on ties, as `argMinFin`).

Every row reports the blocks as sorted lists of element values and checks old = ref = now where
old ran. Under `lake env lean`, `#eval` runs the IR interpreter. -/

open Finset

def timeIt {α : Type} (label : String) (f : Unit → α) (render : α → String) : IO α := do
  let t0 ← IO.monoMsNow
  let v := f ()
  let s := render v
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms  [{s.take 60}{if s.length > 60 then "..." else ""}]"
  return v

/-! ### Verbatim copies of the base definitions -/

def oldArgMinFin : (d : ℕ) → 0 < d → (Fin d → ℕ) → Fin d
  | 0, hd, _ => absurd hd (Nat.lt_irrefl 0)
  | 1, _, _ => 0
  | d + 2, _, f =>
      let prev := oldArgMinFin (d + 1) (Nat.succ_pos d) (fun i => f i.castSucc)
      if f (Fin.last (d + 1)) < f prev.castSucc then Fin.last (d + 1) else prev.castSucc

def oldPotential {t d : ℕ} (prev : List (Fin t → Fin d)) :
    (u : ℕ) → u ≤ t → (Fin u → Fin d) → ℕ :=
  fun u hu chosen =>
    (prev.map fun g =>
      (∏ a : Fin u, if chosen a = g ⟨a.1, lt_of_lt_of_le a.2 hu⟩ then 2 * d else d) *
        (d + 1) ^ (t - u)).sum

def oldBuildPrefix {t d : ℕ} (hd : 0 < d) (prev : List (Fin t → Fin d)) :
    (u : ℕ) → u ≤ t → (Fin u → Fin d)
  | 0, _ => Fin.elim0
  | u + 1, hu =>
      let chosen := oldBuildPrefix hd prev u (Nat.le_of_succ_le hu)
      Fin.snoc (α := fun _ => Fin d) chosen
        (oldArgMinFin d hd fun v =>
          oldPotential prev (u + 1) hu (Fin.snoc (α := fun _ => Fin d) chosen v))

def oldFunctions (t d : ℕ) (hd : 0 < d) : (m : ℕ) → List (Fin t → Fin d)
  | 0 => []
  | m + 1 =>
      let prev := oldFunctions t d hd m
      prev ++ [oldBuildPrefix hd prev t le_rfl]

def oldGraphBlock {t d : ℕ} (f : Fin t → Fin d) : Finset (Fin (t * d)) :=
  Finset.univ.map ⟨fun u : Fin t => finProdFinEquiv (u, f u),
    fun _ _ h => congrArg Prod.fst (finProdFinEquiv.injective h)⟩

/-! ### Independent reference -/

def refFunctions (t d m : ℕ) : Array (Array ℕ) := Id.run do
  let mut fs : Array (Array ℕ) := #[]
  for _ in [0:m] do
    let mut chosen : Array ℕ := #[]
    for u in [0:t] do
      let mut best := 0
      let mut bestVal : Option ℕ := none
      for v in [0:d] do
        let mut pot := 0
        for g in fs do
          let mut p := 1
          for a in [0:u + 1] do
            let c := if a < u then chosen[a]! else v
            p := p * (if c == g[a]! then 2 * d else d)
          pot := pot + p * (d + 1) ^ (t - (u + 1))
        match bestVal with
        | none => best := v; bestVal := some pot
        | some b => if pot < b then best := v; bestVal := some pot
      chosen := chosen.push best
    fs := fs.push chosen
  return fs

/-- Element values of a block, sorted. -/
def blockVals {n : ℕ} (B : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter (· ∈ B)).map (·.val)

def refBlocks (t d m : ℕ) : List (List ℕ) :=
  (refFunctions t d m).toList.map fun f => (List.range t).map fun u => u * d + f[u]!

def oldBlocks (t d m : ℕ) (hd : 0 < d) : List (List ℕ) :=
  (oldFunctions t d hd m).map fun f => blockVals (oldGraphBlock f)

def nowBlocks (t d m : ℕ) (hd : 0 < d) : List (List ℕ) :=
  (List.finRange m).map fun i => blockVals ((Cslib.AffineDisperser.Li.rrvWeakDesign t d m hd).block i)

def showBlocks (b : List (List ℕ)) : String := toString b

def row (t d m : ℕ) (runOld : Bool) : IO Unit := do
  if hd : 0 < d then
    let r ← timeIt s!"ref t={t} d={d} m={m}" (fun _ => refBlocks t d m) showBlocks
    let n ← timeIt s!"now t={t} d={d} m={m}" (fun _ => nowBlocks t d m hd) showBlocks
    if runOld then
      let o ← timeIt s!"old t={t} d={d} m={m}" (fun _ => oldBlocks t d m hd) showBlocks
      IO.println s!"  equal(old,ref,now): {o == r && r == n}"
    else
      IO.println s!"  equal(ref,now): {r == n}"
  else
    IO.println "d = 0"
