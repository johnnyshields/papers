/-
Vendored from Mathlib pull request #42000, `feat: trivial estimates for the positive part of the
logarithm`, by Stefan Kebekus (GitHub `kebekus`).

  https://github.com/leanprover-community/mathlib4/pull/42000

The PR is merged upstream but postdates the pinned Mathlib revision.

Only the declarations *absent* from the pinned `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`
are copied, verbatim, under their upstream names.  Two of the PR's changes are therefore not
reproduced here, because they alter declarations the pin already carries and copying them would
clash:

* `Real.monotoneOn_posLog` is widened upstream from `Set.Ici 0` to `Set.Ici (-1)`;
* `Real.posLog_le_posLog` correspondingly weakens its hypothesis from `0 ≤ x` to `-1 ≤ x`.

Consuming code written against the merged form passes `neg_one_lt_zero.le.trans h` where the pin
wants the bare `h : 0 ≤ x`; those call sites are adapted at the call site and marked there.

`Real.antitoneOn_posLog`, also added by the PR, is not copied: its proof consumes the widened
`monotoneOn_posLog` and is unused here.

When the pin is bumped past this PR, delete this file and drop the call-site adaptations.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real

variable {x y : ℝ}

/-- Presentation of `|log|` in terms of the positive part of the logarithm. -/
theorem abs_log_eq_posLog_add_posLog_inv (x : ℝ) : |log x| = log⁺ x + log⁺ x⁻¹ := by
  grind [half_mul_log_add_log_abs (x := x), log_inv x ▸ half_mul_log_add_log_abs (x := x⁻¹)]

/-- The function `log⁺` commutes with real powers with nonnegative base and exponent. -/
@[simp] theorem posLog_rpow {x α : ℝ} (hx : -1 ≤ x) (hα : 0 ≤ α) : log⁺ (x ^ α) = α * log⁺ x := by
  rcases le_or_gt x 0 with h | h
  · have h₁ : |x| ≤ 1 := abs_le.2 ⟨hx, h.trans zero_le_one⟩
    rw [(posLog_eq_zero_iff x).2 h₁, mul_zero, (posLog_eq_zero_iff _).2]
    exact (abs_rpow_le_abs_rpow x α).trans (rpow_le_one (abs_nonneg x) h₁ hα)
  · rw [posLog_apply, posLog_apply, log_rpow h, mul_max_of_nonneg _ _ hα, mul_zero]

/-!
## Trivial Estimates
-/

/-- For nonnegative `x`, the positive part of the logarithm is bounded by `log (1 + x)`. -/
lemma posLog_le_log_one_add {x : ℝ} (hx : 0 ≤ x) : log⁺ x ≤ log (1 + x) := by
  rw [posLog_eq_log_max_one hx]
  exact log_le_log (by positivity) (max_le (by linarith) (by linarith))

/-- Converse to `posLog_le_log_one_add` up to the additive constant `log 2`. -/
lemma log_one_add_le_posLog {x : ℝ} : log (1 + x) ≤ log⁺ x + log 2 := by
  have h₁ : (1 : ℝ) ≤ max 1 |x| := le_max_left ..
  have h₂ : |1 + x| ≤ max 1 |x| * 2 := by
    linarith [abs_add_le 1 x, le_max_right 1 |x|, abs_one (α := ℝ)]
  calc log (1 + x)
  _ ≤ log⁺ (1 + x) := le_max_right ..
  _ = log⁺ |1 + x| := (posLog_abs _).symm
  -- Adapted to the pinned revision: the pinned `posLog_le_posLog` takes `0 ≤ x`, where upstream
  -- takes `-1 ≤ x` and this argument reads `neg_one_lt_zero.le.trans (abs_nonneg _)`.
  _ ≤ log⁺ (max 1 |x| * 2) := posLog_le_posLog (abs_nonneg _) h₂
  _ = log⁺ x + log 2 := by
    rw [posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; linarith),
      log_mul (by positivity) two_ne_zero, ← posLog_eq_log_max_one (abs_nonneg x), posLog_abs]

/-- The positive part of the logarithm is bounded by the absolute value: `log⁺ x ≤ |x|`. -/
lemma posLog_le_abs (x : ℝ) : log⁺ x ≤ |x| := by
  rcases le_or_gt |x| 1 with h | h
  · rw [(posLog_eq_zero_iff x).2 h]
    exact abs_nonneg x
  · rw [← posLog_abs, posLog_eq_log (by rw [abs_abs]; exact h.le)]
    linarith [log_le_sub_one_of_pos (lt_trans one_pos h)]

end Real
