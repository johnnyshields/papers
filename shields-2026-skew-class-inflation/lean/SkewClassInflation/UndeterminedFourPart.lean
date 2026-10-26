/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FourPartDiscrepancyAlternatives

/-!
# Produced undetermined mates for four-part discrepancy counting

The actual witness step in even-discrepancy reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Undeterminedness supplies a genuine normalized same-inventory mate.
Determined subset coordinates supply both reflected indicators before
the four-part alternatives are invoked.  Sorry-free.
-/

namespace SkewClassInflation

/-- A determined coordinate supplies both reflected indicators of every normalized mate. -/
theorem cutDetermined_actual_pair {N : ℕ} (α β : Composition N) (k y : ℕ)
    (hβ : β ∈ normalizedInventoryMates α k) (hy : cutDetermined α k y) :
    actualCutBool β y = actualCutBool α y ∧
      actualCutBool β (N - y) = actualCutBool α (N - y) := by
  classical
  have hleft := hy β hβ
  have htype := coarseningInventory_cut_type β α hβ.1 y
  by_cases hA : y ∈ properCuts α <;> by_cases hAr : N - y ∈ properCuts α <;>
    by_cases hB : y ∈ properCuts β <;> by_cases hBr : N - y ∈ properCuts β <;>
      simp_all [actualCutBool, compositionCutType]

/-- Every undetermined coordinate produces a normalized mate with its cut indicator flipped. -/
theorem exists_undetermined_bool_flip {N : ℕ} (α : Composition N) (k m : ℕ)
    (hm : m ∈ undeterminedCuts α k) :
    ∃ β : Composition N, β ∈ normalizedInventoryMates α k ∧
      actualCutBool β m = !actualCutBool α m := by
  classical
  have hnot := (Finset.mem_filter.mp hm).2
  unfold cutDetermined at hnot
  push Not at hnot
  obtain ⟨β, hβ, hflip⟩ := hnot
  refine ⟨β, hβ, ?_⟩
  by_cases hA : m ∈ properCuts α <;> by_cases hB : m ∈ properCuts β <;>
    simp_all [actualCutBool]

/-- Actual undeterminedness and determined subset data produce the four-part alternatives. -/
theorem undetermined_fourPart_alternatives {N : ℕ} (α : Composition N) (k : ℕ)
    (m x z p : ℕ+) (hsum : m.val + x.val + z.val + p.val = N)
    (hm : m.val ∈ undeterminedCuts α k)
    (hx : compositionCutType α x.val ≠ 1)
    (hmxt : compositionCutType α (m.val + x.val) ≠ 1)
    (hz : compositionCutType α z.val = 1)
    (hmzt : compositionCutType α (m.val + z.val) = 1)
    (hmx : actualCutBool α (m.val + x.val) = !actualCutBool α x.val)
    (hmz : actualCutBool α (m.val + z.val) = actualCutBool α z.val)
    (hdet : ∀ y ∈ ({x.val, z.val, m.val + x.val, m.val + z.val,
        x.val + z.val, m.val + x.val + z.val} : Finset ℕ), cutDetermined α k y)
    (hsign : compositionCutSign α (x.val + z.val) =
      compositionCutSign α (m.val + x.val + z.val)) :
    (compositionCutCodeNat α (x.val + z.val) = compositionCutCodeNat α z.val ∧
      compositionCutCodeNat α (m.val + x.val + z.val) = compositionCutCodeNat α z.val) ∨
    (compositionCutCodeNat α (x.val + z.val) = compositionCutCodeNat α x.val ∧
      compositionCutCodeNat α (m.val + x.val + z.val) =
        compositionCutCodeNat α (m.val + x.val)) := by
  obtain ⟨β, hβ, hflip⟩ := exists_undetermined_bool_flip α k m.val hm
  apply fourPart_even_discrepancy_alternatives α β hβ.1 m x z p hsum
    (undeterminedCuts_type_one α k m.val hm) hx hmxt hz hmzt hmx hmz hflip
  · intro y hy
    exact cutDetermined_actual_pair α β k y hβ (hdet y hy)
  · exact hsign

end SkewClassInflation
