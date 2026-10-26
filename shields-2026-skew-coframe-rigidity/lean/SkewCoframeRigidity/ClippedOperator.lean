/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The clipped alternating operator

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «The complete boundary solve»
(`sec:coframe-coordinates`, `sc:finite-operator`, `sc:exact-shift-cap`).  For two polynomials
`G`, `C` and a series `u`, the clipped alternating operator is
`G [u C]_{<M} - C [u G]_{<M}`; moving a factor of `z` through it leaves exactly the whole cap
polynomial.  Sorry-free.
-/

namespace SkewCoframeRigidity

open PowerSeries Polynomial

variable {R : Type*} [CommRing R]

/-- `T_{G,C}(u) = G [uC]_{<M} - C [uG]_{<M}`, the operator of `sc:finite-operator`. -/
noncomputable def clippedOp (M : ℕ) (G C : R[X]) (u : R⟦X⟧) : R[X] :=
  G * trunc M (u * (C : R⟦X⟧)) - C * trunc M (u * (G : R⟦X⟧))

/-- Clipping a series multiplied by `z` removes the single coefficient that crosses the cutoff. -/
theorem trunc_X_mul (M : ℕ) (hM : 1 ≤ M) (f : R⟦X⟧) :
    trunc M (PowerSeries.X * f) =
      Polynomial.X * trunc M f - Polynomial.X ^ M * Polynomial.C (coeff (M - 1) f) := by
  ext n
  simp only [coeff_trunc, Polynomial.coeff_sub]
  rcases n with _ | n
  · simp only [Polynomial.coeff_X_mul_zero, coeff_zero_X_mul, Polynomial.coeff_X_pow_mul', Nat.zero_sub]
    simp only [Polynomial.coeff_C]
    split_ifs <;> simp_all <;> omega
  · rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul', coeff_succ_X_mul, coeff_trunc]
    by_cases h : n + 1 < M
    · have : ¬ (M ≤ n + 1) := by omega
      simp [h, this, show n < M by omega]
    · by_cases h2 : n + 1 = M
      · subst h2
        simp
      · have : M ≤ n + 1 := by omega
        simp [h, this, show ¬ n < M by omega, Polynomial.coeff_C, show n + 1 - M ≠ 0 by omega]

/-- `sc:exact-shift-cap`: the exact polynomial identity for moving `z` through the clipped
operator, with the whole cap polynomial on the right. -/
theorem clippedOp_X_mul (M : ℕ) (hM : 1 ≤ M) (G C : R[X]) (u : R⟦X⟧) :
    clippedOp M G C (PowerSeries.X * u) - Polynomial.X * clippedOp M G C u =
      -(Polynomial.X ^ M *
        (G * Polynomial.C (coeff (M - 1) (u * (C : R⟦X⟧))) -
          C * Polynomial.C (coeff (M - 1) (u * (G : R⟦X⟧))))) := by
  unfold clippedOp
  rw [mul_assoc PowerSeries.X u, mul_assoc PowerSeries.X u, trunc_X_mul M hM,
    trunc_X_mul M hM]
  ring

end SkewCoframeRigidity
