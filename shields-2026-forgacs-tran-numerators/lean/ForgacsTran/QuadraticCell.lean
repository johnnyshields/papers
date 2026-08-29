/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.QuadraticWitness
import ForgacsTran.DominanceSupplyClosure

/-!
# The `(deg Q, r) = (2,1)` point, which the four cells exclude

`DominanceCellPartition.ft_dominance_cell_of_admissible` covers the admissible
class **minus one point**: `(deg Q, r) = (2,1)`, excluded because
`Forgacs2017RationalDenominator` Props. 1--2 exclude it.  The manuscript does not
inherit that exclusion — `rem:quadratic-case` closes it, in closed form.

Almost all of the remark is already formalized, parametrically in `q₀, q₁, q₂`:
`QuadraticWitness.quadMod` is the constant radius `√(q₀/q₂)`, `quadZ` is
`-q₁ - 2√(q₀q₂)cos θ`, `QuadraticCase.quadratic_z_strictMonoOn` is its
monotonicity, `quadDen_eq_sq_lower`/`quadDen_eq_sq_upper` are the two exactly
double endpoint collisions, and `quad_ftRemainder_eq_zero` is the exhaustion.

What that last one buys is the whole cell.  The pencil is quadratic in `t`, so the
principal pair **is** the zero set, `eq:principal-decomposition` is exact, and the
remainder is identically `0`.  So `eq:dominance-bound` holds on the **whole open
arc** — no retained range, no deleted windows, no threshold in `M` — because
`0 ≤ |W|/2` and nothing else is needed.

## What this pencil does not exercise

`τ` is **constant** here, so BANK-74's first entry applies in full: the curvature
quantity is constant rather than merely nonvanishing, and nothing that clears
because a derivative of `τ` vanishes is being tested.

And the two endpoint collisions are double **in the denominator**, which is
`ftCollisionOrder = 1` — the collision order counts the multiplicity in
`ftCritical`, one less than in `ftDen`.  So this pencil sits at `ν = 1` twice and
does **not** exercise the arbitrary-multiplicity collar; `CubicCollisionWitness`
remains the only `ν = 2`.  Indeed no quadratic pencil can reach `ν ≥ 2` at any
`r`, which `CubicCollisionWitness`'s own header proves.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `rem:quadratic-case`.

## Tags

quadratic pencil, dominance, cell partition, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

/-- **`eq:dominance-bound` at the `(2,1)` point, on the whole open arc.**  The
remainder vanishes identically, so the bound is `0 ≤ |W|/2` and holds with no
threshold, no retained range and no deleted window. -/
theorem quad_dominance {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) (M : ℕ)
    {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftRemainder (quadPoly q0 q1 q2) 1 1 (quadZ q0 q1 q2) (fun _ => quadMod q0 q2) M θ
      ≤ ftPrincipalAmp (quadPoly q0 q1 q2) 1 1 (quadZ q0 q1 q2)
          (fun _ => quadMod q0 q2) θ / 2 := by
  rw [quad_ftRemainder_eq_zero hq0 hq2 q1 M hsin, ftPrincipalAmp]
  positivity

/-- The same on the arc stated as a membership, which is the shape the retained
range is written in elsewhere. -/
theorem quad_dominance_on_arc {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    (M : ℕ) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    ftRemainder (quadPoly q0 q1 q2) 1 1 (quadZ q0 q1 q2) (fun _ => quadMod q0 q2) M θ
      ≤ ftPrincipalAmp (quadPoly q0 q1 q2) 1 1 (quadZ q0 q1 q2)
          (fun _ => quadMod q0 q2) θ / 2 :=
  quad_dominance hq0 hq2 q1 M (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

/-- **The collision order at the `(2,1)` endpoints is `1`, not `2`.**  The
denominator has a double root there — `quadDen_eq_sq_lower` — and
`ftCollisionOrder` counts the multiplicity in `ftCritical`, which is one less.
Recorded because the two numbers are easy to interchange and only the second is
what the collar's multiplicity parameter reads. -/
theorem quad_collisionOrder_lower {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) :
    rootMultiplicity (((Real.sqrt (q0 / q2) : ℝ)) : ℂ)
        (ftDen (quadPoly q0 q1 q2) 1 (((-q1 - 2 * Real.sqrt (q0 * q2) : ℝ)) : ℂ)) = 2 := by
  rw [quadDen_eq_sq_lower hq0 hq2]
  have hq2C : ((q2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq2.ne'
  rw [rootMultiplicity_mul (by
    refine mul_ne_zero (by simpa using hq2C) (pow_ne_zero 2 (X_sub_C_ne_zero _)))]
  rw [rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot, hq2C]),
    rootMultiplicity_X_sub_C_pow]

end ForgacsTran
