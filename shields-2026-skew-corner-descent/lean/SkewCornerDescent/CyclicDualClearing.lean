/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicDetectors
import SkewCornerDescent.CyclicPeriodDetector
import SkewCornerDescent.CyclicInventoryDefects

/-!
# Unit clearing of the literal dual detectors

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `thm:dual-general`).
The literal closure-word inventories are identified with the complete expressions used
by the exposure proof. Every start and repeated wrap remains in both identities.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- Multiplying the literal full-period detector by its nonzero full-prefix unit gives
exactly the forward expression used in real exposure. -/
theorem windowDefect_period_cleared {α R : Type*}
    [Fintype α] [DecidableEq α] [Field R] {r d s k : ℕ} [NeZero (r * d)]
    [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hk : 0 < k)
    (word : ZMod (r * d) → α) (response : α → R) (hresponse : ∀ a, response a ≠ 0) :
    windowDefect (response ∘ word) response (classDefect word 1 d s (r * s - 1) 0)
        (k * d + s) (k * (r * d) + r * s) (r * d) *
        (windowProduct (response ∘ word) 1 (r * d) 0) ^ k *
        windowProduct (response ∘ word) 1 (r * s - 1) 0 =
      (r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 (r * s - 1) 0 -
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : R) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) := by
  classical
  let f := response ∘ word
  let A : R := ∏ i, f i
  let D := windowProduct f 1 (r * s - 1) 0
  have hB : r * d + ((k - 1) * (r * d) + r * s) = k * (r * d) + r * s := by
    have he : k - 1 + 1 = k := by omega
    calc
      _ = (k - 1 + 1) * (r * d) + r * s := by ring
      _ = _ := by rw [he]
  let _ : NeZero (r * d + ((k - 1) * (r * d) + r * s)) := ⟨by
    rw [hB]
    exact NeZero.ne _⟩
  have hperiod := windowDefect_period (C := (k - 1) * (r * d) + r * s)
    f response (classDefect word 1 d s (r * s - 1) 0)
    (fun i => hresponse (word i)) hresponse (sum_reduced_classDefect hr hs word)
    (dual_period_normalization hk rfl rfl rfl)
  simp only [hB] at hperiod
  have hlength : k * (r * d) + r * s - 1 = k * (r * d) + (r * s - 1) := by
    have hm := Nat.mul_pos hr hs
    omega
  have hprefix : (∏ i ∈ Finset.range (k * (r * d) + r * s - 1), f (i : ZMod (r * d))) =
      A ^ k * D := by
    have h := zmod_windowProduct_mul_add f k (r * s - 1) 0
    simpa only [← hlength, A, D, windowProduct, zero_add, nsmul_eq_mul, mul_one] using h
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hresponse (word i))
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hresponse (word (0 + i • 1)))
  have hpow : A ^ k = A ^ (k - 1) * A := by
    nth_rw 1 [← Nat.sub_add_cancel hk]
    exact pow_succ A (k - 1)
  change windowDefect f response _ _ _ _ * (windowProduct f 1 (r * d) 0) ^ k * D = _
  rw [hperiod, zmod_windowProduct_cycle, hprefix]
  change ((r * d : ℕ) * (d : R) * A⁻¹ -
    (∑ i, windowProduct f 1 ((k - 1) * (r * d) + r * s) i) *
      (A ^ k * D)⁻¹ * closureLabelSum (classDefect word 1 d s (r * s - 1) 0) response) *
      A ^ k * D = _
  simp only [closureLabelSum, Nat.cast_mul]
  rw [hpow]
  field_simp [hA, hD]
  ring

end SkewCornerDescent.CyclicWindows
