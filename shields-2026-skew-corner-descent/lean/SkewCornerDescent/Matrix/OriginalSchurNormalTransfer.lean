/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalLinearNormalTransfer
import SkewCornerDescent.Matrix.OriginalSignedFactors
import SkewCornerDescent.Matrix.NormalProductLog

/-!
# Fresh coefficients of the full original Schur germ

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The complete removed determinant and the produced orientation sign remain in the
normal germ. Their full jets omit every generator above the selected component bound;
the original Schur logarithm therefore has the actual response determinant's fresh
coefficient. Earlier intrinsic coefficients are not set to zero. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every complete removed-factor jet omits a generator above the actual component bound. -/
theorem originalRemoved_normalSeries_derivative_zero {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (l : ℕ) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l
        (c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det)) = 0 := by
  apply residueGeneratorDeriv_lower
  apply c.normalPolynomialSeries_coeff_mem_lower K hK
  apply mem_supported.mpr
  intro j hj
  have hs := originalRemovedMatrix_det_span_le (hD := hD) P (c.top : ℕ)
    (originalBlock_span_le_of_components P _ hmax)
  exact lt_of_le_of_lt ((Finset.le_sup hj).trans hs) hK

/-- Mapping the original local factorization retains the entire removed factor and sign. -/
theorem originalSchur_normalSeries_signed_factorization {n : ℕ} (P : Profile n) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      c.normalPolynomialSeries P.schur =
        (ε : PowerSeries (OtherField c.top)) *
          c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det *
          c.normalSeries (c.originalHessenbergResponse P).det := by
  obtain ⟨ε, hε, he⟩ := c.originalHessenberg_local_signed_factorization P
  refine ⟨ε, hε, ?_⟩
  have hn := congrArg c.normalSeries he
  simpa only [map_mul, map_intCast, c.normalSeries_polynomial] using hn

/-- The full original Schur germ inherits earlier independence and the fresh logarithmic
coefficient, rather than replacing its full removed factor by its residue. -/
theorem originalSchur_normalized_log_from_response {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hprev : ∀ l, l < m → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l (c.normalSeries (c.originalHessenbergResponse P).det)) = 0) :
    let f := c.normalPolynomialSeries P.schur
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    (∀ l, l < m → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l f) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f))) =
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) := by
  obtain ⟨ε, hε, he⟩ := c.originalSchur_normalSeries_signed_factorization P
  let A : PowerSeries (OtherField c.top) := (ε : PowerSeries (OtherField c.top)) *
    c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det
  have hA : ∀ l, residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩ (PowerSeries.coeff l A) = 0 := by
    intro l
    apply coeff_deriv_mul_zero
    · intro k _
      change residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff k (ε : PowerSeries (OtherField c.top))) = 0
      rw [show (ε : PowerSeries (OtherField c.top)) =
        PowerSeries.C (ε : OtherField c.top) by simp, PowerSeries.coeff_C]
      split_ifs
      · exact (residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩).map_intCast ε
      · exact map_zero _
    · intro k _
      exact c.originalRemoved_normalSeries_derivative_zero P hmax K hK k
  have hA0 : PowerSeries.constantCoeff A ≠ 0 := by
    dsimp only [A]
    rw [map_mul, map_intCast, c.normalPolynomialSeries_constant]
    apply mul_ne_zero
    · rcases hε with h | h <;> simp [h]
    · exact (c.originalRemoved_residue_lower_scalar P hmax).2
  have hp0 := c.originalHessenberg_normalSeries_constant_ne_zero P hB hmax
  dsimp only
  rw [he]
  constructor
  · intro l hl
    exact coeff_deriv_mul_zero _ A _ l (fun k _ => hA k)
      (fun k hk => hprev k (hk.trans_lt hl))
  · rw [coeff_deriv_normalized_mul_log_first _ A _ m hm hA0 hp0
      (fun l _ => hA l) hprev,
      coeff_deriv_normalized_log_first _ A m hm hA0 (fun l _ => hA l), hA m]
    simp

/-- The actual completed-gap period supplies all earlier jets and the literal internal
window coefficient of the full original Schur polynomial. -/
theorem originalSchur_normalized_log_linear_periodic {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P)
    (hlen : m + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z)) 1 r 0) :
    let f := c.normalPolynomialSeries P.schur
    (∀ l, l < m → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l f) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f))) =
      ((-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m) *
        linearInverseWindowSum (c.originalInternalResidue P) (m + 1) := by
  have hprev := (c.originalHessenberg_normalized_log_from_periodic_gaps P hB hmax
    r k m hm hmB hlen hp K hK hKeq).1
  have ht := c.originalSchur_normalized_log_from_response P hB hmax K hK m hm hprev
  dsimp only at ht ⊢
  exact ⟨ht.1, ht.2.trans (c.originalHessenberg_normalized_log_linear_periodic
    P hB hmax r k m hm hmB hlen hp K hK hKeq)⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
