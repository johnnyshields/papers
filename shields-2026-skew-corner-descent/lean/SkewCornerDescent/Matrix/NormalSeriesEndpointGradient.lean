/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalResponseProfiles

/-!
# Full higher-generator gradients of complete original normal responses

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The coefficientwise surviving derivative acts on the whole original interval
and its full inverse. Every endpoint-product coefficient retains all normal jets.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete normal interval has the full endpoint-product gradient at every
surviving generator above the selected span, without freezing its removed inverse. -/
theorem normal_interval_profile_gradient {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ) (j : ℕ+) (hj : c.top < j)
    [Invertible (vertexBetaMatrix c.normalPolynomialSeries row col)] :
    residueSeriesGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩
        (c.normalPolynomialSeries (hh (x - y)) -
          (vertexOutgoing c.normalPolynomialSeries col x *
            ⅟(vertexBetaMatrix c.normalPolynomialSeries row col) *
            vertexIncoming c.normalPolynomialSeries row y) () ()) =
      (endpointProfile (fun i => x - row i)
          (fun i => (vertexOutgoing c.normalPolynomialSeries col x *
            ⅟(vertexBetaMatrix c.normalPolynomialSeries row col)) () i) *
        endpointProfile (fun i => col i - y)
          (fun i => (⅟(vertexBetaMatrix c.normalPolynomialSeries row col) *
            vertexIncoming c.normalPolynomialSeries row y) i ())).coeff (x - y - (j : ℤ)) := by
  classical
  let δ := residueSeriesGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩
  let B := vertexOutgoing c.normalPolynomialSeries col x
  let C := vertexIncoming c.normalPolynomialSeries row y
  let P := vertexBetaMatrix c.normalPolynomialSeries row col
  let Q := ⅟P
  have h := congrFun (congrFun (entryDeriv_retainedResponse (R := ℚ) δ
    (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) B C P) ()) ()
  change δ (retainedResponse
    (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) B C P () ()) =
    (entryDeriv δ (fun _ _ : Unit => c.normalPolynomialSeries (hh (x - y))) -
      entryDeriv δ B * Q * C - B * Q * entryDeriv δ C +
      B * Q * entryDeriv δ P * Q * C) () () at h
  have hL : (entryDeriv δ B * (Q * C)) () () =
      ∑ i, if x - col i = (j : ℤ) then (Q * C) i () else 0 := by
    rw [Matrix.mul_apply]
    simp only [B, entryDeriv, vertexOutgoing, Matrix.of_apply, δ,
      c.normal_hh_higher_derivative j hj, ite_mul, one_mul, zero_mul]
  have hR : ((B * Q) * entryDeriv δ C) () () =
      ∑ i, if row i - y = (j : ℤ) then (B * Q) () i else 0 := by
    rw [Matrix.mul_apply]
    simp only [C, entryDeriv, vertexIncoming, Matrix.of_apply, δ,
      c.normal_hh_higher_derivative j hj, mul_ite, mul_one, mul_zero]
  have hI : ((B * Q) * entryDeriv δ P * (Q * C)) () () =
      ∑ i, ∑ k, if row i - col k = (j : ℤ) then
        (B * Q) () i * (Q * C) k () else 0 := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply (M := B * Q) (N := entryDeriv δ P), Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [P, entryDeriv, vertexBetaMatrix, Matrix.of_apply, δ,
      c.normal_hh_higher_derivative j hj, mul_ite, ite_mul, mul_one,
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
    c.normal_hh_higher_derivative j hj]
  have hz : (x - y - (j : ℤ) = 0) ↔ x - y = (j : ℤ) := by omega
  have hl (i : ν) : (x - row i = x - y - (j : ℤ)) ↔ row i - y = (j : ℤ) := by omega
  have hr (i : ν) : (col i - y = x - y - (j : ℤ)) ↔ x - col i = (j : ℤ) := by omega
  have hi (i k : ν) : (x - row i + (col k - y) = x - y - (j : ℤ)) ↔
      row i - col k = (j : ℤ) := by omega
  simp only [hz, hl, hr, hi]
  abel

end SkewCornerDescent.Matrix.SelectedCoordinate
