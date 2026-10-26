/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureNormalQuotient
import SkewCornerDescent.Matrix.OriginalClosureNormalTransfer
import SkewCornerDescent.Matrix.NormalInverseCoefficient
import SkewCornerDescent.Matrix.OriginalClosureCyclicInventory

/-!
# Actual original closure quotient coefficient from source periodicity

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The literal closure is produced from the source. Its complete original quotient is
unit-normalized before logging, and both full determinant inverses remain present.
The source period is DERIVED; the full-window assembly must supply it. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual polynomial quotient has the original fresh logarithmic coefficient. All closure
geometry, units and earlier coefficient independence are supplied inside the proof. -/
theorem originalHorizontalClosure_quotient_log_from_source {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k d : ℕ) (hd : 0 < d) (hdB : d < originalSelectedCount (hD := hD) P)
    (hlen : d + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0) :
    ∃ m : ℕ, ∃ Q : Profile m, ∃ v : ℤ × ℤ,
      originalHorizontalClosure P = translate v Q.cells ∧
      let u := c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2
      residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff d
          (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff u)⁻¹ * u))) =
        ((-1 : OtherField c.top) ^ d * (c.normalCoefficient)⁻¹ ^ d) *
          (linearInverseWindowSum (c.originalInternalResidue Q) (d + 1) -
            2 * linearInverseWindowSum (c.originalInternalResidue P) (d + 1)) := by
  obtain ⟨m, Q, v, hQ, hc, hprevQ, hlogQ⟩ :=
    c.originalHorizontalClosure_normalized_log_from_source P hB hmax
      r k d hd hdB hlen hp K hK hKeq
  have hP := c.originalHessenberg_normalized_log_from_periodic_gaps P hB hmax
    r k d hd hdB hlen hp K hK hKeq
  have hlogP := c.originalHessenberg_normalized_log_linear_periodic P hB hmax
    r k d hd hdB hlen hp K hK hKeq
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  have hunitP := c.originalHessenberg_normalSeries_constant_ne_zero P hB hmax
  have hunitQ := c.originalHessenberg_normalSeries_constant_ne_zero Q hBQ hmaxQ
  let δ : Derivation ℚ (OtherField c.top) (OtherField c.top) :=
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  have he := coeff_deriv_normalized_quotient_log_first (F := OtherField c.top) δ
    (c.normalSeries (c.originalHessenbergResponse P).det)
    (c.normalSeries (c.originalHessenbergResponse Q).det) d hd hunitP hunitQ hP.1 hprevQ
  have hpLog := coeff_deriv_normalized_log_first
    (residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩)
    (c.normalSeries (c.originalHessenbergResponse P).det) d hd hunitP hP.1
  have hqLog := coeff_deriv_normalized_log_first
    (residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩)
    (c.normalSeries (c.originalHessenbergResponse Q).det) d hd hunitQ hprevQ
  refine ⟨m, Q, v, hQ, ?_⟩
  dsimp only
  rw [c.originalHorizontalClosure_normalized_quotient P Q v hQ hB hmax]
  dsimp only at he hpLog hqLog hlogP hlogQ
  simp only [smul_eq_mul] at hpLog hqLog
  rw [he]
  dsimp only [δ]
  rw [mul_assoc (2 : OtherField c.top), ← hpLog, ← hqLog, hlogP, hlogQ]
  ring

/-- The actual original closure quotient has the complete cyclic detector minus the
original linear inventory. All closure-cycle starts are retained, including full length. -/
theorem originalHorizontalClosure_quotient_log_cyclic {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k d : ℕ) (hd : 0 < d) (hdB : d < originalSelectedCount (hD := hD) P)
    (hlen : d + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0) :
    ∃ m : ℕ, ∃ Q : Profile m, ∃ v : ℤ × ℤ,
      ∃ hQ : originalHorizontalClosure P = translate v Q.cells,
      let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
        ⟨originalSelectedCount (hD := hD) P, by
          rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
      let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
      let u := c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2
      residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff d
          (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff u)⁻¹ * u))) =
        ((-1 : OtherField c.top) ^ d * (c.normalCoefficient)⁻¹ ^ d) *
          (CyclicWindows.inverseWindowSum
              (CyclicWindows.completeResponseCycle (c.originalInternalResidue P) S) (d + 1) -
            linearInverseWindowSum (c.originalInternalResidue P) (d + 1)) := by
  obtain ⟨m, Q, v, hQ, he⟩ :=
    c.originalHorizontalClosure_quotient_log_from_source P hB hmax r k d hd hdB
      hlen hp K hK hKeq
  refine ⟨m, Q, v, hQ, ?_⟩
  dsimp only
  dsimp only at he
  rw [he, c.originalHorizontalClosure_linear_inventory P Q v hQ hB (d + 1) (by omega)]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
