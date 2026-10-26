/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.Endpoints
import SkewCoframeRigidity.Coframe.CoequalData
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The one-power stationary equation and its two retained endpoints

Formalizes the first step of `shields-2026-skew-coframe-rigidity.tex`, `sc:positive-power`: the
equation `𝒯_{G,C}(zH^p) + z D r(H) = 0 (mod z^{2M})` retains the coefficients of degrees `M` and
`M + 1`, and since `z D r(H)` has order at least `M + 2` these two coefficients give
`E₀ = 0` and `E₁ = 0` (`sc:two-endpoints`).
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial PowerSeries
open scoped Polynomial

/-- The rational potential `r(H) = P(H) / Q(H)` for polynomials `P`, `Q ≠ 0` over `ℚ`. -/
noncomputable def potential (P Q : ℚ[X]) : PowerSeries CohField :=
  Polynomial.aeval letterSeries P * (Polynomial.aeval letterSeries Q)⁻¹

/-- The left side of `sc:power-equation` as a series. -/
noncomputable def powerEquation {n m : ℕ} (D : BetaDiagram (n + 1)) (E : BetaDiagram (m + 1))
    (p : ℕ) (r : PowerSeries CohField) : PowerSeries CohField :=
  (clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
      PowerSeries CohField) + PowerSeries.X * (defect D E : PowerSeries CohField) * r

theorem coeff_defect_mul_eq_zero {R : Type*} [CommRing R] (d : R[X]) (r : PowerSeries R) (M j : ℕ)
    (hd : ∀ k ≤ M, d.coeff k = 0) (hj : j ≤ M) :
    PowerSeries.coeff j ((d : PowerSeries R) * r) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [Polynomial.coeff_coe, hd x.1 (by omega), zero_mul]

/-- The first two retained coefficients of the power equation are the two endpoint equations. -/
theorem endpoints_of_powerEquation {R : Type*} [CommRing R] (M p : ℕ) (hM : 2 ≤ M)
    (G C : R[X]) (H : PowerSeries R) (hG : G.coeff 0 = 1) (hC : C.coeff 0 = 1)
    (r : PowerSeries R) (hd : ∀ k ≤ M, (clippedOp M G C H).coeff k = 0)
    (h0 : PowerSeries.coeff M (((clippedOp M G C (PowerSeries.X * H ^ p) : R[X]) :
        PowerSeries R) + PowerSeries.X * ((clippedOp M G C H : R[X]) : PowerSeries R) * r) = 0)
    (h1 : PowerSeries.coeff (M + 1) (((clippedOp M G C (PowerSeries.X * H ^ p) : R[X]) :
        PowerSeries R) + PowerSeries.X * ((clippedOp M G C H : R[X]) : PowerSeries R) * r) = 0) :
    endpointZero M G C (H ^ p) = 0 ∧ endpointOne M G C (H ^ p) = 0 := by
  have hz : ∀ j, j ≤ M → PowerSeries.coeff (j + 1)
      (PowerSeries.X * ((clippedOp M G C H : R[X]) : PowerSeries R) * r) = 0 := by
    intro j hj
    rw [mul_assoc, PowerSeries.coeff_succ_X_mul]
    exact coeff_defect_mul_eq_zero _ _ M j hd hj
  have hzM : PowerSeries.coeff M
      (PowerSeries.X * ((clippedOp M G C H : R[X]) : PowerSeries R) * r) = 0 := by
    have := hz (M - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  rw [map_add, Polynomial.coeff_coe, coeff_clippedOp_shift_cutoff M (by omega) G C _ hG hC,
    hzM] at h0
  have hE0 : endpointZero M G C (H ^ p) = 0 := by linear_combination -h0
  refine ⟨hE0, ?_⟩
  rw [map_add, Polynomial.coeff_coe, coeff_clippedOp_shift_succ M (by omega) G C _ hG hC,
    hz M le_rfl] at h1
  rw [hE0, mul_zero] at h1
  linear_combination -h1

end SkewCoframeRigidity.Coframe
