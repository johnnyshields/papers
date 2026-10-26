/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralIntervalRanks

/-!
# Constant finite displacement from periodic physical increments

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The integral starting-row displacement over a fixed number of phases is
constant whenever the actual consecutive row increments are periodic.
The endpoint bound is retained, so no fictitious wrapped row is used.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Finite periodic row increments give one common whole-period row displacement. -/
theorem finite_row_displacement_of_periodic_differences (s : ℕ → ℤ) (r B : ℕ)
    (hstep : ∀ i, i + r < B → s (i + r + 1) - s (i + r) = s (i + 1) - s i) :
    ∀ i, i + r ≤ B → s (i + r) - s i = s r - s 0 := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hi' : i + r < B := by omega
    have hd := hstep i hi'
    have hp := ih (by omega)
    have he : i + 1 + r = i + r + 1 := by omega
    change s (i + 1 + r) - s (i + 1) = _
    rw [he]
    omega

end SkewCornerDescent.Matrix
