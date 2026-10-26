/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Finale

/-!
# The quadratic equation of two columns with the same start

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner, `A = B`).  For `a = x z^A g` and `b = y z^A c`
with `A + L + 1 = M`, the operator `𝒯^M_{a,b}` is `x y z^{2A}` times `𝒯^{L+1}_{g,c}`, and the
defect expression divided by `x y z^{2A}` is `eqL`, an equation at precision `2L + 2` in the two
components `g`, `c` with the top quotients `k_E = -1/x`, `k_F = -1/y` as scalars.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries SkewCoframeRigidity SkewCoframeRigidity.Coframe
open Polynomial hiding coeff

variable {K : Type*} [Field K]

theorem trunc_X_pow_mul_add (A N : ℕ) (f : K⟦X⟧) :
    trunc (A + N) (PowerSeries.X ^ A * f) = Polynomial.X ^ A * trunc N f := by
  ext i
  rw [coeff_trunc, Polynomial.coeff_X_pow_mul', coeff_trunc, PowerSeries.coeff_X_pow_mul']
  by_cases hi : A ≤ i
  · by_cases h2 : i - A < N
    · simp [hi, h2, show i < A + N by omega]
    · simp [hi, h2, show ¬ i < A + N by omega]
  · simp [hi]

theorem clippedOp_scale (A L : ℕ) (x y : K) (g c : K[X]) (u : K⟦X⟧) :
    clippedOp (A + L + 1) (Polynomial.C x * (Polynomial.X ^ A * g))
        (Polynomial.C y * (Polynomial.X ^ A * c)) u =
      Polynomial.C (x * y) * (Polynomial.X ^ (2 * A) * clippedOp (L + 1) g c u) := by
  have hT : ∀ (z : K) (f : K[X]), trunc (A + L + 1)
      (u * ((Polynomial.C z * (Polynomial.X ^ A * f) : K[X]) : K⟦X⟧)) =
      Polynomial.C z * (Polynomial.X ^ A * trunc (L + 1) (u * (f : K⟦X⟧))) := by
    intro z f
    have : u * ((Polynomial.C z * (Polynomial.X ^ A * f) : K[X]) : K⟦X⟧) =
        PowerSeries.C z * (PowerSeries.X ^ A * (u * (f : K⟦X⟧))) := by
      rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_X]; ring
    rw [this, trunc_C_mul, show A + L + 1 = A + (L + 1) by omega, trunc_X_pow_mul_add]
  unfold clippedOp
  rw [hT, hT]
  simp only [map_mul]
  have : 2 * A = A + A := by omega
  rw [this, pow_add]
  ring

/-- The equation of the pair of components at precision `2L + 2`, with scalar top quotients. -/
noncomputable def eqL (L p : ℕ) (g c : K[X]) (kE kF : K) (H : K⟦X⟧) : K⟦X⟧ :=
  ((clippedOp (L + 1) g c (H ^ p) : K[X]) : K⟦X⟧) -
    PowerSeries.C (p : K) * H ^ (p - 1) * ((clippedOp (L + 1) g c H : K[X]) : K⟦X⟧) -
    PowerSeries.C (p : K) * (PowerSeries.C (constantCoeff H ^ (p - 1)) - H ^ (p - 1)) *
      PowerSeries.X ^ L * (PowerSeries.C kF * (g : K⟦X⟧) - PowerSeries.C kE * (c : K⟦X⟧))

theorem defectExpr_scale (A L p : ℕ) (h : ℕ → K) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (g c : K[X]) :
    defectExpr (A + L + 1) p h (Polynomial.C x * (Polynomial.X ^ A * g))
        (Polynomial.C y * (Polynomial.X ^ A * c)) =
      PowerSeries.C (x * y) * (PowerSeries.X ^ (2 * A) *
        eqL L p g c (-1 / x) (-1 / y) (seriesOf h)) := by
  unfold defectExpr eqL
  rw [clippedOp_scale, clippedOp_scale]
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, map_mul,
    constantCoeff_seriesOf']
  have e : (PowerSeries.X : K⟦X⟧) ^ (A + L + 1 - 1) = PowerSeries.X ^ A * PowerSeries.X ^ L := by
    rw [← pow_add]; rfl
  rw [e]
  have hx' : PowerSeries.C x * PowerSeries.C (-1 / x) = -1 := by
    rw [← map_mul, show x * (-1 / x) = -1 by field_simp, map_neg, map_one]
  have hy' : PowerSeries.C y * PowerSeries.C (-1 / y) = -1 := by
    rw [← map_mul, show y * (-1 / y) = -1 by field_simp, map_neg, map_one]
  have e2 : (PowerSeries.X : K⟦X⟧) ^ (2 * A) = PowerSeries.X ^ A * PowerSeries.X ^ A := by
    rw [← pow_add]; congr 1; omega
  rw [e2]
  set P := PowerSeries.C (p : K) * (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1)) *
    (PowerSeries.X ^ A * PowerSeries.X ^ A * PowerSeries.X ^ L) with hP
  linear_combination (P * PowerSeries.C x * (g : K⟦X⟧)) * hy' - (P * PowerSeries.C y * (c : K⟦X⟧)) * hx'

end SkewCoframeRigidity.Unshifted
