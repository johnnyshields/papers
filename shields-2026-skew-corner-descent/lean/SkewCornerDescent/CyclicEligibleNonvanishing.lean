/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicWindowNonvanishing
import SkewCornerDescent.CyclicAutomaticInventory

/-!
# Eligible detector selection, including the one-position boundary

Supports `shields-2026-skew-corner-descent.tex` (`cor:many-active`). A nonzero
last inventory supplies a nonzero short inventory. Complete signed class counts
exclude length one, so every selected coefficient length is genuinely eligible.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- A nonzero short inventory cannot have length one, because that inventory
cancels identically from the literal signed class counts. -/
theorem short_window_nonvanishing_length_ge_two {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (word : ZMod (r * d) → α) (response : α → F)
    (hshort : windowDefect (response ∘ word) response
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * s) ≠ 0) : 2 ≤ r * s := by
  by_contra hnot
  have hone : r * s = 1 := by have := Nat.mul_pos hr hs; omega
  have hrone : r = 1 := by nlinarith
  have hsone : s = 1 := by nlinarith
  subst r
  subst s
  simp only [one_mul, Nat.sub_self] at hshort
  apply hshort
  simpa only [one_mul] using one_position_windowDefect_short_zero (by omega) hk word response

/-- Dual nonvanishing selects the period or a short length at least two. No
order-zero coefficient is extracted at the one-position remainder boundary. -/
theorem window_dual_eligible_nonvanishing {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] [CharZero F]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (word : ZMod (r * d) → α) (response : α → F)
    (hdual : windowDefect (response ∘ word) response
        (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
        (k * (r * d) + r * s) (r * d) ≠ 0 ∨
      lastWindowDefect (response ∘ word) response
        (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
        (k * (r * d) + r * s) ≠ 0) :
    windowDefect (response ∘ word) response (classDefect word 1 d s (r * s - 1) 0)
        (k * d + s) (k * (r * d) + r * s) (r * d) ≠ 0 ∨
      (2 ≤ r * s ∧ windowDefect (response ∘ word) response
        (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
        (k * (r * d) + r * s) (r * s) ≠ 0) := by
  rcases hdual with hn | hlast
  · exact Or.inl hn
  let _ : NeZero (r * s) := ⟨Nat.ne_of_gt (Nat.mul_pos hr hs)⟩
  have hfull := windowDefect_full_eq_short (r := r) (d := d) (s := s)
    (response ∘ word) response (classDefect word 1 d s (r * s - 1) 0)
    (Nat.mul_le_mul_left r hsd) hk rfl rfl rfl
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)) (sum_reduced_classDefect hr hs word)
  rw [windowDefect_eq_last] at hfull
  have hshort : windowDefect (response ∘ word) response
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * s) ≠ 0 := by
    intro hz
    exact hlast (by rw [hfull, hz, mul_zero])
  exact Or.inr ⟨short_window_nonvanishing_length_ge_two hr hs hsd hk word response hshort,
    hshort⟩

end SkewCornerDescent.CyclicWindows
