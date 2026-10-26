/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicInventoryDefects
import SkewCornerDescent.CyclicDetectors

/-!
# The automatic last-window identity

Formalizes the inventory identity in `shields-2026-skew-corner-descent.tex`
(`cor:automatic-open`). A one-position positive remainder makes both the short
and whole-word defects vanish for every response assignment. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- On the automatic locus the positive remainder is uniquely one, including
exclusion of the full-remainder convention. -/
theorem positive_remainder_one_unique {d k l s : ℕ} (hd : 2 ≤ d)
    (h : k * d + 1 = l * d + s) (hsd : s ≤ d) :
    s = 1 ∧ l = k := by
  have hmod : s % d = 1 := by
    have hm := congrArg (fun x : ℕ => x % d) h
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt (by omega : 1 < d)] using hm.symm
  have hslt : s < d := by
    by_contra hnot
    have he : s = d := by omega
    rw [he, Nat.mod_self] at hmod
    omega
  have hsone : s = 1 := by rwa [Nat.mod_eq_of_lt hslt] at hmod
  refine ⟨hsone, ?_⟩
  have he : l * d = k * d := by rw [hsone] at h; omega
  exact mul_right_cancel₀ (by omega : d ≠ 0) he

/-- The literal one-position defect cancels from its class counts alone. -/
theorem one_position_windowDefect_short_zero {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] {d k : ℕ}
    [NeZero d] [NeZero (k * d + 1)] (hd : 0 < d) (hk : 0 < k)
    (word : ZMod d → α) (response : α → F) :
    windowDefect (response ∘ word) response (classDefect word 1 d 1 0 0)
      (k * d + 1) (k * d + 1) 1 = 0 := by
  let _ : NeZero (1 : ℕ) := ⟨by decide⟩
  have he : ∑ a, classDefect word 1 d 1 0 0 a = (d : ℤ) := by
    simp only [sum_classDefect, ZMod.card, Nat.cast_one, one_mul, Nat.cast_zero,
      mul_zero, sub_zero]
  rw [windowDefect_short (response ∘ word) response _ hd hk rfl he]
  simpa only [Nat.cast_one, one_mul, inverseWindowSum, closureLabelSum,
    Nat.sub_self, windowProduct, Finset.range_zero, Finset.prod_empty, inv_one]
    using one_position_short_detector_zero word response 1 d 0

/-- The whole-word detector is identically zero on the automatic locus, without
positivity, regularity, or distinctness assumptions on the responses. -/
theorem one_position_windowDefect_full_zero {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] {d k : ℕ}
    [NeZero d] [NeZero (k * d + 1)] (hd : 0 < d) (hk : 0 < k)
    (word : ZMod d → α) (response : α → F) :
    windowDefect (response ∘ word) response (classDefect word 1 d 1 0 0)
      (k * d + 1) (k * d + 1) (k * d + 1) = 0 := by
  let _ : NeZero (1 : ℕ) := ⟨by decide⟩
  have he : ∑ a, classDefect word 1 d 1 0 0 a = (d : ℤ) := by
    simp only [sum_classDefect, ZMod.card, Nat.cast_one, one_mul, Nat.cast_zero,
      mul_zero, sub_zero]
  rw [windowDefect_full_eq_short (r := 1) (d := d) (s := 1)
    (response ∘ word) response _ hd hk rfl (by omega) rfl (by simp) he,
    one_position_windowDefect_short_zero hd hk word response, mul_zero]

end SkewCornerDescent.CyclicWindows
