/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FourPartInventoryMasks
import SkewClassInflation.PeriodicCutEncoding

/-!
# Actual reflected cut patterns for four-part discrepancies

The pattern-identification step in even-discrepancy reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Every Boolean entry is the actual composition cut indicator.  The
finite table is used only after both reflected subset patterns have
been identified from the actual type and sign relations.  Sorry-free.
-/

namespace SkewClassInflation

/-- Zero is never an actual proper cut. -/
theorem actualCutBool_zero {N : ℕ} (α : Composition N) : actualCutBool α 0 = false := by
  have hh : 0 ∉ properCuts α := fun h => (Nat.lt_irrefl 0) (properCuts_bounds α 0 h).1
  simp only [actualCutBool, hh, decide_false]

/-- The whole total weight is never an actual proper cut. -/
theorem actualCutBool_weight {N : ℕ} (α : Composition N) : actualCutBool α N = false := by
  have hh : N ∉ properCuts α := fun h => (Nat.lt_irrefl N) (properCuts_bounds α N h).2
  simp only [actualCutBool, hh, decide_false]

/-- Single-type actual cuts have complementary reflected Boolean indicators. -/
theorem actualCutBool_reflect_one {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : compositionCutType α x = 1) : actualCutBool α (N - x) = !actualCutBool α x := by
  classical
  by_cases h : x ∈ properCuts α <;> by_cases hr : N - x ∈ properCuts α <;>
    simp_all [actualCutBool, compositionCutType]

/-- Even-type actual cuts have identical reflected Boolean indicators. -/
theorem actualCutBool_reflect_even {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : compositionCutType α x ≠ 1) : actualCutBool α (N - x) = actualCutBool α x := by
  classical
  by_cases h : x ∈ properCuts α <;> by_cases hr : N - x ∈ properCuts α <;>
    simp_all [actualCutBool, compositionCutType]

/-- Disagreeing even types have complementary actual unreflected cut indicators. -/
theorem actualCutBool_even_opposite {N : ℕ} (α : Composition N) (x y : ℕ)
    (hx : compositionCutType α x ≠ 1) (hy : compositionCutType α y ≠ 1)
    (hne : compositionCutType α x ≠ compositionCutType α y) :
    actualCutBool α y = !actualCutBool α x := by
  classical
  by_cases h : x ∈ properCuts α <;> by_cases hr : N - x ∈ properCuts α <;>
    by_cases h' : y ∈ properCuts α <;> by_cases hr' : N - y ∈ properCuts α <;>
      simp_all [actualCutBool, compositionCutType]

/-- The actual two nontrivial prefix relations identify the entire left subset pattern. -/
theorem fourPartLeftCuts_pattern {N : ℕ} (α : Composition N) (m x z : ℕ)
    (hmx : actualCutBool α (m + x) = !actualCutBool α x)
    (hmz : actualCutBool α (m + z) = actualCutBool α z) :
    fourPartLeftCuts α m x z =
      discrepancyLeftCuts (actualCutBool α m) (actualCutBool α x) (actualCutBool α z)
        (actualCutBool α (x + z)) (actualCutBool α (m + x + z)) := by
  funext mask
  unfold fourPartLeftCuts threePartSubsetWeight discrepancyLeftCuts
  split <;> simp_all only [actualCutBool_zero]

/-- Actual reflected type relations identify the entire right subset pattern. -/
theorem fourPartRightCuts_pattern {N : ℕ} (α : Composition N) (m x z : ℕ)
    (hm : compositionCutType α m = 1) (hx : compositionCutType α x ≠ 1)
    (hmxt : compositionCutType α (m + x) ≠ 1) (hz : compositionCutType α z = 1)
    (hmzt : compositionCutType α (m + z) = 1)
    (hmx : actualCutBool α (m + x) = !actualCutBool α x)
    (hmz : actualCutBool α (m + z) = actualCutBool α z) :
    fourPartRightCuts α m x z =
      discrepancyRightCuts (actualCutBool α m) (actualCutBool α x) (actualCutBool α z)
        (actualCutBool α (N - (x + z))) (actualCutBool α (N - (m + x + z))) := by
  have hmr := actualCutBool_reflect_one α m hm
  have hxr := actualCutBool_reflect_even α x hx
  have hmxr := actualCutBool_reflect_even α (m + x) hmxt
  have hzr := actualCutBool_reflect_one α z hz
  have hmzr := actualCutBool_reflect_one α (m + z) hmzt
  funext mask
  unfold fourPartRightCuts threePartSubsetWeight discrepancyRightCuts
  split <;> simp_all only [Nat.sub_zero, actualCutBool_weight]

/-- The exact actual four-part inventory count has the stated discrepancy-pattern specialization. -/
theorem fourPart_actual_discrepancy_count {N : ℕ} (α : Composition N) (m x z : ℕ)
    (hm : compositionCutType α m = 1) (hx : compositionCutType α x ≠ 1)
    (hmxt : compositionCutType α (m + x) ≠ 1) (hz : compositionCutType α z = 1)
    (hmzt : compositionCutType α (m + z) = 1)
    (hmx : actualCutBool α (m + x) = !actualCutBool α x)
    (hmz : actualCutBool α (m + z) = actualCutBool α z) :
    fourPartMaskCount (fourPartLeftCuts α m x z) (fourPartRightCuts α m x z) =
      fourPartDiscrepancyCount (actualCutBool α m) (actualCutBool α x) (actualCutBool α z)
        (actualCutBool α (x + z)) (actualCutBool α (N - (x + z)))
        (actualCutBool α (m + x + z)) (actualCutBool α (N - (m + x + z))) := by
  rw [fourPartLeftCuts_pattern α m x z hmx hmz,
    fourPartRightCuts_pattern α m x z hm hx hmxt hz hmzt hmx hmz]
  rfl

end SkewClassInflation
