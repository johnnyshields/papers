/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicDualClearing
import SkewCornerDescent.CyclicLastInventory

/-!
# Returning from cleared detectors to literal inventories

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`,
`thm:dual-general`). Complete literal class counts supply the normalization.
Nonzero response products make clearing reversible. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- The nonvanishing result of exposure returns to the actual period and last-window
inventories. This conversion requires no independence among response values. -/
theorem cleared_dual_implies_window_nonvanishing {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] [CharZero F]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (word : ZMod (r * d) → α) (response : α → F)
    (hreg : ∀ a, response a ≠ 0)
    (hcore :
      (s : F) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) ≠ 0 ∨
      (r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 (r * s - 1) 0 -
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) ≠ 0) :
    windowDefect (response ∘ word) response (classDefect word 1 d s (r * s - 1) 0)
        (k * d + s) (k * (r * d) + r * s) (r * d) ≠ 0 ∨
      lastWindowDefect (response ∘ word) response (classDefect word 1 d s (r * s - 1) 0)
        (k * d + s) (k * (r * d) + r * s) ≠ 0 := by
  classical
  have hA : (∏ i : ZMod (r * d), response (word i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hreg (word i))
  let _ : NeZero (r * s) := ⟨Nat.ne_of_gt (Nat.mul_pos hr hs)⟩
  have hsum := sum_reduced_classDefect hr hs word
  have hclear := windowDefect_period_cleared (k := k) hr hs hk word response hreg
  have hlong := windowDefect_full_eq_short (r := r) (d := d) (s := s)
    (response ∘ word) response (classDefect word 1 d s (r * s - 1) 0)
    (Nat.mul_le_mul_left r hsd) hk rfl rfl rfl
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)) hsum
  have hunit : ((k * d + s : ℕ) : F) / (s : F) *
      (∏ i : ZMod (r * d), response (word i))⁻¹ ^ k ≠ 0 :=
    mul_ne_zero (div_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (by omega : 0 < k * d + s)))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs))) (pow_ne_zero _ (inv_ne_zero hA))
  rw [← windowDefect_eq_last]
  by_contra hz
  obtain ⟨hn, hB⟩ := not_or.mp hz
  have hn := not_not.mp hn
  have hB := not_not.mp hB
  have hshort : windowDefect (response ∘ word) response
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * s) = 0 := by
    rw [hlong] at hB
    exact (mul_eq_zero.mp hB).resolve_left hunit
  rw [windowDefect_short (response ∘ word) response _
    (Nat.mul_le_mul_left r hsd) hk rfl hsum] at hshort
  have hshort' :
      (s : F) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) = 0 := by
    simpa only [inverseWindowSum, closureLabelSum, windowProduct, zero_add,
      nsmul_eq_mul, mul_one] using hshort
  have hfull' :
      (r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 (r * s - 1) 0 -
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) = 0 := by
    rw [hn, zero_mul, zero_mul] at hclear
    exact hclear.symm
  exact hcore.elim (fun h => h hshort') (fun h => h hfull')

end SkewCornerDescent.CyclicWindows
