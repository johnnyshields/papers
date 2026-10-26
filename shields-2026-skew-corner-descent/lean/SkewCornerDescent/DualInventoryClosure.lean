/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicInventoryDefects
import SkewCornerDescent.ExposedDetectorComparison

/-!
# Closing the two actual cyclic count comparisons

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`).
The complete forward and reciprocal inventories force a full class defect and constant
short windows. The unique omitted position cannot hold two distinct such classes.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory Polynomial
open scoped BigOperators

/-- The two exact count comparisons close against the actual inventory averages. -/
theorem dual_counts_force_full_defect {α : Type*} [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r)
    (word : ZMod (r * d) → α) (a : α) (k : ℕ)
    (hshort : maximalClassWindowCount word 1 (r * s) a =
      windowSum (classMask word a) 1 (r * s - 1) 0 + 1)
    (hfull : minimalClassWindowCount word 1 ((k - 1) * (r * d) + r * s) a =
      (k - 1) * windowSum (classMask word a) 1 (r * d) 0 +
        windowSum (classMask word a) 1 (r * s - 1) 0 + 1) :
    classDefect word 1 d s (r * s - 1) 0 a = d ∧
      ∀ i, windowSum (classMask word a) 1 (r * s) i =
        windowSum (classMask word a) 1 (r * s - 1) 0 + 1 := by
  classical
  let c := ∑ i, classMask word a i
  let t := windowSum (classMask word a) 1 (r * s - 1) 0
  have hupper (i : ZMod (r * d)) : windowSum (classMask word a) 1 (r * s) i ≤ t + 1 := by
    rw [← hshort]
    exact Finset.le_sup (Finset.mem_univ i)
  have hlow (i : ZMod (r * d)) : (k - 1) * c + t + 1 ≤
      windowSum (classMask word a) 1 ((k - 1) * (r * d) + r * s) i := by
    change (k - 1) * (∑ x, classMask word a x) +
      windowSum (classMask word a) 1 (r * s - 1) 0 + 1 ≤ _
    rw [← zmod_windowSum_cycle (classMask word a) 0, ← hfull]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  have hu := inventory_le_of_window_bound (classMask word a) 1 (r * s) (t + 1) hupper
  have hl := inventory_ge_of_window_bound (classMask word a) 1
    ((k - 1) * (r * d) + r * s) ((k - 1) * c + t + 1) hlow
  simp only [ZMod.card] at hu hl
  change (r * s) * c ≤ (r * d) * (t + 1) at hu
  change (r * d) * ((k - 1) * c + t + 1) ≤ ((k - 1) * (r * d) + r * s) * c at hl
  have heq : s * c = d * (t + 1) := by nlinarith
  constructor
  · change (s : ℤ) * c - (d : ℤ) * t = d
    have hz : (s : ℤ) * c = (d : ℤ) * (t + 1) := by exact_mod_cast heq
    linarith
  · apply windows_constant_of_maximum_eq_average (classMask word a) 1 (r * s) (t + 1) hupper
    simp only [ZMod.card]
    change r * s * c = r * d * (t + 1)
    nlinarith [heq]

/-- The actual two detector identities supply both count comparisons and hence identify the
exposed active class with the unique omitted word position. The root and sign assumptions
describe the exposed coordinate slice; no count or valuation conclusion is assumed. -/
theorem exposed_dual_detector_omitted_class {α : Type*} [Fintype α] [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (word : ZMod (r * d) → α) (a : α) (k : ℕ) (num den : α → Polynomial ℝ)
    (root sign : ℝ) (hroot : eval root (num a) = 0)
    (hsimple : rootMultiplicity root (num a) = 1)
    (hden : ∀ Y, 0 < eval root (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval root (num Y))
    (he : classDefect word 1 d s (r * s - 1) 0 a ≠ 0)
    (hshort :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C (s : ℝ) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        RatFunc.C ((r * s : ℕ) : ℝ) *
          (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ Y, RatFunc.C (classDefect word 1 d s (r * s - 1) 0 Y : ℝ) *
            (response Y)⁻¹) = 0)
    (hfull :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C ((r * d * d : ℕ) : ℝ) *
          (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 (r * s - 1) 0 -
        (∑ Y, RatFunc.C (classDefect word 1 d s (r * s - 1) 0 Y : ℝ) *
          (response Y)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) = 0) :
    word ((r * s - 1 : ℕ) : ZMod (r * d)) = a := by
  classical
  have heR : (classDefect word 1 d s (r * s - 1) 0 a : ℝ) ≠ 0 := by
    exact_mod_cast he
  have hcshort := exposed_short_detector_count word 1 (r * s) (r * s - 1) 0 a
    num den (fun Y => (classDefect word 1 d s (r * s - 1) 0 Y : ℝ))
    root sign (s : ℝ) ((r * s : ℕ) : ℝ) hroot hsimple hden hsign heR
    (by exact_mod_cast hs.ne') (by exact_mod_cast (Nat.mul_pos hr hs).ne') hshort
  have hcfull := exposed_full_detector_count word 1 ((k - 1) * (r * d) + r * s)
    (r * d) (r * s - 1) k 0 a num den
    (fun Y => (classDefect word 1 d s (r * s - 1) 0 Y : ℝ))
    root sign ((r * d * d : ℕ) : ℝ) hroot hsimple hden hsign heR
    (by exact_mod_cast (Nat.mul_pos (Nat.mul_pos hr hd) hd).ne') hfull
  obtain ⟨hdefect, hconstant⟩ :=
    dual_counts_force_full_defect hr word a k hcshort hcfull
  exact class_at_omitted_phase hr hd hs word a _ hconstant hdefect

end SkewCornerDescent.CyclicWindows
