/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FourPartDiscrepancyTable

/-!
# Actual cut masks of four positive parts

The actual-coordinate bridge for the four-part discrepancy count in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Subset masks refer to distinct index labels, not to distinct numerical
part values.  The complementary part is read through reflection in
the true total weight.  Sorry-free.
-/

namespace SkewClassInflation

/-- The actual Boolean membership of a natural cut coordinate. -/
noncomputable def actualCutBool {N : ℕ} (α : Composition N) (x : ℕ) : Bool :=
  decide (x ∈ properCuts α)

/-- The four actual part values, with a distinguished complementary fourth label. -/
def fourPartValues (a b c d : ℕ) : Fin 4 → ℕ := ![a, b, c, d]

/-- The seven nonempty subset weights of the first three labeled parts. -/
def threePartSubsetWeight (a b c : ℕ) : ℕ → ℕ
  | 1 => a
  | 2 => b
  | 3 => a + b
  | 4 => c
  | 5 => a + c
  | 6 => b + c
  | 7 => a + b + c
  | _ => 0

/-- Actual unreflected subset cuts, retaining every possible coincidence of part values. -/
noncomputable def fourPartLeftCuts {N : ℕ} (α : Composition N) (a b c : ℕ) (mask : ℕ) : Bool :=
  actualCutBool α (threePartSubsetWeight a b c mask)

/-- The corresponding reflected actual subset cuts. -/
noncomputable def fourPartRightCuts {N : ℕ} (α : Composition N) (a b c : ℕ) (mask : ℕ) : Bool :=
  actualCutBool α (N - threePartSubsetWeight a b c mask)

/-- A singleton index mask reads exactly its actual part coordinate. -/
theorem fourPart_mask_single {N : ℕ} (α : Composition N) (a b c d : ℕ)
    (hsum : a + b + c + d = N) (i : Fin 4) :
    discrepancyMaskCut (fourPartLeftCuts α a b c) (fourPartRightCuts α a b c)
      (2 ^ i.val) = actualCutBool α (fourPartValues a b c d i) := by
  fin_cases i <;>
    simp [discrepancyMaskCut, fourPartLeftCuts, fourPartRightCuts,
      threePartSubsetWeight, fourPartValues]
  congr 1
  omega

/-- A pair of distinct index labels reads exactly the sum of its two actual parts. -/
theorem fourPart_mask_pair {N : ℕ} (α : Composition N) (a b c d : ℕ)
    (hsum : a + b + c + d = N) (i j : Fin 4) (hij : i ≠ j) :
    discrepancyMaskCut (fourPartLeftCuts α a b c) (fourPartRightCuts α a b c)
      (2 ^ i.val + 2 ^ j.val) = actualCutBool α
        (fourPartValues a b c d i + fourPartValues a b c d j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [discrepancyMaskCut, fourPartLeftCuts, fourPartRightCuts,
      threePartSubsetWeight, fourPartValues] <;> congr 1 <;> omega

/-- The three-label mask complementary to the last part reads its true reflected coordinate. -/
theorem fourPart_mask_complement {N : ℕ} (α : Composition N) (a b c d : ℕ)
    (hsum : a + b + c + d = N) (i : Fin 4) :
    discrepancyMaskCut (fourPartLeftCuts α a b c) (fourPartRightCuts α a b c)
      (15 - 2 ^ i.val) = actualCutBool α (N - fourPartValues a b c d i) := by
  fin_cases i <;>
    simp [discrepancyMaskCut, fourPartLeftCuts, fourPartRightCuts,
      threePartSubsetWeight, fourPartValues]
  congr 1
  omega

end SkewClassInflation
