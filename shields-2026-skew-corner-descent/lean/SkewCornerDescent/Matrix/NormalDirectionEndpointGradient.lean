/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalSeriesEndpointGradient
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Normal-direction gradients of complete retained responses

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Differentiation in the genuine normal series retains the whole removed inverse.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Normal differentiation changes only the selected original generator. -/
theorem normal_hh_normal_derivative (z : ℤ) :
    PowerSeries.C c.normalCoefficient *
      PowerSeries.derivative (R := OtherField c.top) (c.normalPolynomialSeries (hh z)) =
      if z = (c.top : ℤ) then 1 else 0 := by
  by_cases hn : z < 0
  · rw [hh_of_neg hn, map_zero, map_zero, mul_zero, ite_eq_right (by have := c.top.pos; omega)]
  by_cases hz : z = 0
  · subst z
    simp only [hh_zero, map_one, PowerSeries.derivative_one, mul_zero]
    rw [ite_eq_right (by have := c.top.pos; omega)]
  have hp : 0 < z := by omega
  let k : ℕ+ := ⟨z.toNat, by omega⟩
  have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hp.le
  rw [← hkz, hh_pnat]
  by_cases hk : k = c.top
  · rw [hk, c.normalPolynomialSeries_top]
    simp only [Derivation.leibniz, Derivation.map_sub, PowerSeries.derivative_X,
      PowerSeries.derivative_C, sub_zero, smul_eq_mul, mul_zero, zero_add, mul_one,
      ← map_mul, mul_inv_cancel₀ c.normalCoefficient_ne_zero, map_one, ite_true]
  · have he : c.normalPolynomialSeries (X k) =
        PowerSeries.C (residueGenerator c.top ⟨k, hk⟩) := by
      simp only [normalPolynomialSeries, RingHom.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, c.normalChart_other k hk, Polynomial.coe_C]
      rfl
    rw [he, PowerSeries.derivative_C, mul_zero, ite_eq_right (by
      intro h
      apply hk
      exact_mod_cast h)]

/-- The selected-generator raw profile product is the derivative of the full normal
response, multiplied by the actual affine normal coefficient. -/
theorem normal_interval_profile_normal_gradient {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ)
    [Invertible (vertexBetaMatrix c.normalPolynomialSeries row col)] :
    PowerSeries.C c.normalCoefficient * PowerSeries.derivative (R := OtherField c.top)
        (c.normalPolynomialSeries (hh (x - y)) -
          (vertexOutgoing c.normalPolynomialSeries col x *
            ⅟(vertexBetaMatrix c.normalPolynomialSeries row col) *
            vertexIncoming c.normalPolynomialSeries row y) () ()) =
      (endpointProfile (fun i => x - row i)
          (fun i => (vertexOutgoing c.normalPolynomialSeries col x *
            ⅟(vertexBetaMatrix c.normalPolynomialSeries row col)) () i) *
        endpointProfile (fun i => col i - y)
          (fun i => (⅟(vertexBetaMatrix c.normalPolynomialSeries row col) *
            vertexIncoming c.normalPolynomialSeries row y) i ())).coeff (x - y - (c.top : ℤ)) := by
  classical
  let δ := PowerSeries.C c.normalCoefficient •
    (PowerSeries.derivative (R := OtherField c.top))
  let B := vertexOutgoing c.normalPolynomialSeries col x
  let C := vertexIncoming c.normalPolynomialSeries row y
  let P := vertexBetaMatrix c.normalPolynomialSeries row col
  let Q := ⅟P
  have h := congrFun (congrFun (entryDeriv_retainedResponse (R := OtherField c.top) δ
    (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) B C P) ()) ()
  change δ (retainedResponse
    (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) B C P () ()) =
    (entryDeriv δ (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) -
      entryDeriv δ B * Q * C - B * Q * entryDeriv δ C +
      B * Q * entryDeriv δ P * Q * C) () () at h
  have hL : (entryDeriv δ B * (Q * C)) () () =
      ∑ i, if x - col i = (c.top : ℤ) then (Q * C) i () else 0 := by
    rw [Matrix.mul_apply]
    simp only [B, entryDeriv, vertexOutgoing, Matrix.of_apply, δ,
      Derivation.smul_apply, smul_eq_mul, c.normal_hh_normal_derivative,
      ite_mul, one_mul, zero_mul]
  have hR : ((B * Q) * entryDeriv δ C) () () =
      ∑ i, if row i - y = (c.top : ℤ) then (B * Q) () i else 0 := by
    rw [Matrix.mul_apply]
    simp only [C, entryDeriv, vertexIncoming, Matrix.of_apply, δ,
      Derivation.smul_apply, smul_eq_mul, c.normal_hh_normal_derivative,
      mul_ite, mul_one, mul_zero]
  have hI : ((B * Q) * entryDeriv δ P * (Q * C)) () () =
      ∑ i, ∑ k, if row i - col k = (c.top : ℤ) then
        (B * Q) () i * (Q * C) k () else 0 := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply (M := B * Q) (N := entryDeriv δ P), Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [P, entryDeriv, vertexBetaMatrix, Matrix.of_apply, δ,
      Derivation.smul_apply, smul_eq_mul, c.normal_hh_normal_derivative, mul_ite, ite_mul, mul_one,
      zero_mul, mul_zero]
  change δ (retainedResponse
    (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) B C P () ()) =
    (endpointProfile (fun i => x - row i) (fun i => (B * Q) () i) *
      endpointProfile (fun i => col i - y) (fun i => (Q * C) i ())).coeff _
  rw [h, endpointProfile_mul_coeff]
  change (entryDeriv δ (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) -
    entryDeriv δ B * Q * C - B * Q * entryDeriv δ C +
    B * Q * entryDeriv δ P * Q * C) () () = _
  rw [Matrix.mul_assoc (entryDeriv δ B) Q C,
    Matrix.mul_assoc (B * Q * entryDeriv δ P) Q C]
  simp only [Matrix.add_apply, Matrix.sub_apply, hL, hR, hI, entryDeriv, δ,
    Derivation.smul_apply, smul_eq_mul, c.normal_hh_normal_derivative]
  have hz : (x - y - (c.top : ℤ) = 0) ↔ x - y = (c.top : ℤ) := by omega
  have hl (i : ν) : (x - row i = x - y - (c.top : ℤ)) ↔ row i - y = (c.top : ℤ) := by omega
  have hr (i : ν) : (col i - y = x - y - (c.top : ℤ)) ↔ x - col i = (c.top : ℤ) := by omega
  have hi (i k : ν) : (x - row i + (col k - y) = x - y - (c.top : ℤ)) ↔
      row i - col k = (c.top : ℤ) := by omega
  simp only [hz, hl, hr, hi]
  abel

end SkewCornerDescent.Matrix.SelectedCoordinate
