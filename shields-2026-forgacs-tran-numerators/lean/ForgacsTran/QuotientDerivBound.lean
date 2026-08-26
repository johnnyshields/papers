/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# A quotient's derivative, bounded from bounds on its parts

The `C¹` half of `eq:local-strong-clock` needs the derivative of a normalized remainder
`N/D` bounded, where `N` and `N'` carry an exponentially small factor and `D` is bounded
below.  The analysis that supplies those three bounds is elsewhere; what is left is one
inequality over bare reals, and it is stated here so that it is proved once and instantiated
rather than re-derived inside each quotient it is wanted for.

`eq:C1-interior-remainder` is where the manuscript states the `C¹` smallness this feeds.

## Main statements

* `abs_div_deriv_le` — `|(N'D - ND')/D²| ≤ b_{N'}/(2A) + b_N b_{D'}/(4A²)` from `2A ≤ D`.
* `abs_div_deriv_le_of_scaled` — the same with every numerator bound carrying a common
  factor `s ≥ 0`, which is the shape the exponentially small bounds arrive in: the factor
  comes out front, so the constant is visibly free of it.

## Implementation notes

The hypothesis is `2A ≤ D` rather than `A ≤ D` because the consumer's floor is stated after
halving — a neighborhood of the parameter is what carries the derivative, and only half the
floor survives the motion across it.  Taking the halving into the statement means the
consumer instantiates at its own `A` rather than at `A/2`, where the factor of four in the
second term is easy to lose.

No `Complex` anywhere: the consumers apply this to `‖·‖` and to real parts, both already real.

Sorry-free.

## Tags

quotient rule, derivative bound, interior remainder
-/

namespace ForgacsTran

/-- **The quotient bound.**  With `|N| ≤ b_N`, `|N'| ≤ b_{N'}`, `|D'| ≤ b_{D'}` and
`2A ≤ D` for some `A > 0`, the quotient rule's numerator over `D²` is bounded by
`b_{N'}/(2A) + b_N b_{D'}/(4A²)`.

Both terms are needed: the first survives when `N` vanishes and the second when `N'` does,
so neither dominates the other in general. -/
theorem abs_div_deriv_le {N N' D D' A bN bN' bD' : ℝ}
    (hA : 0 < A) (hD : 2 * A ≤ D)
    (hN : |N| ≤ bN) (hN' : |N'| ≤ bN') (hD' : |D'| ≤ bD') :
    |(N' * D - N * D') / D ^ 2| ≤ bN' / (2 * A) + bN * bD' / (4 * A ^ 2) := by
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le h2A hD
  have hD2 : (0 : ℝ) < D ^ 2 := by positivity
  have hbN : 0 ≤ bN := le_trans (abs_nonneg N) hN
  have hbN' : 0 ≤ bN' := le_trans (abs_nonneg N') hN'
  have hbD' : 0 ≤ bD' := le_trans (abs_nonneg D') hD'
  have h4A : (0 : ℝ) < 4 * A ^ 2 := by positivity
  have hden : 4 * A ^ 2 ≤ D ^ 2 := by nlinarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hsplit : (N' * D - N * D') / D ^ 2 = N' / D + -(N * D' / D ^ 2) := by
    field_simp
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hDpos]
    calc |N'| / D ≤ bN' / D := by gcongr
      _ ≤ bN' / (2 * A) := by gcongr
  · rw [abs_neg, abs_div, abs_of_pos hD2, abs_mul]
    calc |N| * |D'| / D ^ 2 ≤ bN * bD' / D ^ 2 := by gcongr
      _ ≤ bN * bD' / (4 * A ^ 2) := by gcongr

/-- **The scaled form**, which is how the consumer meets it.  Both numerator bounds carry a
common factor `s` -- an exponentially small `σ^M`, times a polynomial factor in `M` for the
derivative -- and the conclusion carries it out front, so the constant is visibly free of it.

That the factor comes out is the whole point: it is what makes the bound `O(s)` with a
constant that does not move with `M`, rather than a bound whose constant hides the decay. -/
theorem abs_div_deriv_le_of_scaled {N N' D D' A cN cN' bD' s : ℝ}
    (hA : 0 < A) (hD : 2 * A ≤ D) (hs : 0 ≤ s)
    (hN : |N| ≤ s * cN) (hN' : |N'| ≤ s * cN') (hD' : |D'| ≤ bD') :
    |(N' * D - N * D') / D ^ 2| ≤ s * (cN' / (2 * A) + cN * bD' / (4 * A ^ 2)) := by
  have h := abs_div_deriv_le hA hD hN hN' hD'
  calc |(N' * D - N * D') / D ^ 2|
      ≤ s * cN' / (2 * A) + s * cN * bD' / (4 * A ^ 2) := h
    _ = s * (cN' / (2 * A) + cN * bD' / (4 * A ^ 2)) := by ring

end ForgacsTran
