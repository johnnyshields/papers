/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Arithmetic of the pencil's index convention

The pencil carries three indices — the degree `n`, the branch index `n - 1`, and the
exponent `r` of `z t ^ r` — and three facts about them recur across the tree.  Each is
short, and each was re-derived at ten to fourteen separate sites before being named here.

Two of the three are about **truncated subtraction**, which is why they are worth a name
rather than a `simp`: `n - 1` is `ℕ`-subtraction, so both statements are *false at*
`n = 0` and carry the positivity hypothesis that makes them true.  A site that inlines
them inlines the side condition too, where it is easy to lose.

* `even_add_pred_add_one` — the branch count `n + (n - 1) + 1` is even, because it is
  `2 * n`.  This is the parity the lower-endpoint sign argument runs on.
* `cast_pred_eq_sub_one` — the branch index commutes with the cast into `ℝ` exactly when
  `n` is positive.
* `pi_div_natCast_one` — the arc `π / r` is the half-turn at `r = 1`, which is the cubic
  pencil's own normalization.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`.

## Tags

pencil index, truncated subtraction, parity, Forgács–Tran
-/

namespace ForgacsTran

open Real

/-- The branch count is even, because it is `2 * n`.  **False at `n = 0`**, where
truncated subtraction makes the left side `1`. -/
theorem even_add_pred_add_one {n : ℕ} (hn : 0 < n) : Even (n + (n - 1) + 1) :=
  ⟨n, by omega⟩

/-- The branch index commutes with the cast into `ℝ`.  **False at `n = 0`**, where the
left side is `0` and the right side is `-1`. -/
theorem cast_pred_eq_sub_one {n : ℕ} (hn : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  rw [Nat.cast_sub hn, Nat.cast_one]

/-- The arc `π / r` is the half-turn at `r = 1`. -/
theorem pi_div_natCast_one : π / ((1 : ℕ) : ℝ) = π := by
  rw [Nat.cast_one, div_one]

end ForgacsTran
