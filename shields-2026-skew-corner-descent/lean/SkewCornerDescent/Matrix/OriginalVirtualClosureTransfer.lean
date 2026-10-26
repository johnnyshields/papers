/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalSchurAffine
import SkewCornerDescent.Matrix.OriginalClosureCyclicInventory
import SkewCornerDescent.Matrix.OriginalClosureNormalTransfer
import SkewCornerDescent.Matrix.OriginalClosureNormalQuotient
import SkewCornerDescent.Matrix.NormalVirtualDifference
import SkewCornerDescent.Matrix.OriginalClosureVirtualUnits

/-!
# Exact virtual closure coefficient from original diagrams

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The actual closure geometry supplies its selected count, component bound and gap period.
Both full Schur summands are differentiated before the virtual difference is logged.
All complete closure-cycle starts remain, including the full-length boundary. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual virtual closure has the full residue-weighted cyclic coefficient.
The virtual-factor unit and earlier-jet independence are produced from literal closure
geometry and the actual completed-gap period; neither is an additional input. -/
theorem originalVirtualClosure_normalized_log_from_source {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
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
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0)
    (α : ℚ) :
    let f := c.normalPolynomialSeries P.schur
    let β := c.normalPolynomialSeries Q.schur
    let T := β - PowerSeries.C (α : OtherField c.top) * f ^ 2
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
    (∀ l, l < d → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l T) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff d
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff T)⁻¹ * T))) =
      ((-1 : OtherField c.top) ^ d * (c.normalCoefficient)⁻¹ ^ d) *
        (2 * linearInverseWindowSum (c.originalInternalResidue P) (d + 1) +
          c.residueMap Q.schur /
              (c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2) *
            (CyclicWindows.inverseWindowSum
                (CyclicWindows.completeResponseCycle (c.originalInternalResidue P) S) (d + 1) -
              linearInverseWindowSum (c.originalInternalResidue P) (d + 1))) ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩) β d := by
  have hunit := c.originalVirtualClosure_residue_ne_zero P Q v hQ hB hmax α
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by omega⟩
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  have hpQ := c.originalHorizontalClosure_completed_gap_period P Q v hQ r hp
  have hdQ : d < originalSelectedCount (hD := hD) Q := by omega
  have hKQ : (K : ℤ) = (c.top : ℤ) + k • CyclicWindows.windowSum
      (fun z => c.originalCompletedGap Q ((ZMod.finEquiv _).symm z)) 1 r 0 := by
    rw [c.originalHorizontalClosure_completed_gap_window P Q v hQ]
    exact hKeq
  have htP := c.originalSchur_normalized_log_linear_periodic P hB hmax
    r k d hd hdB hlen hp K hK hKeq
  have htQ := c.originalSchur_normalized_log_linear_periodic Q hBQ hmaxQ
    r k d hd hdQ hlen hpQ K hK hKQ
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  let f := c.normalPolynomialSeries P.schur
  let β := c.normalPolynomialSeries Q.schur
  have hf0 : PowerSeries.constantCoeff f ≠ 0 := by
    simpa only [f, c.normalPolynomialSeries_constant] using
      c.originalSchur_residue_ne_zero P hB hmax
  have hβ0 : PowerSeries.constantCoeff β ≠ 0 := by
    simpa only [β, c.normalPolynomialSeries_constant] using
      c.originalSchur_residue_ne_zero Q hBQ hmaxQ
  have hα : δ (α : OtherField c.top) = 0 := by
    apply residueGeneratorDeriv_lower
    exact SubfieldClass.ratCast_mem (residueLowerField c.top K) α
  have hsquare : ∀ l, l < d → δ (PowerSeries.coeff l (f ^ 2)) = 0 :=
    fun l hl => coeff_deriv_pow_zero δ f l (fun z hz => htP.1 z (hz.trans_lt hl)) 2
  have hsquare0 : PowerSeries.constantCoeff (f ^ 2) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hf0
  have he := coeff_deriv_normalized_difference_first δ β (f ^ 2) (α : OtherField c.top)
    hα d hd hβ0 hsquare0
    (by simpa only [map_pow, f, β, c.normalPolynomialSeries_constant] using hunit)
    htQ.1 hsquare
  rw [coeff_deriv_normalized_pow_log_first δ f d hd hf0 htP.1 2] at he
  dsimp only at htP htQ ⊢
  refine ⟨?_, ?_, c.originalSchur_jets_affine_periodic Q hBQ hmaxQ
    r k d hd hdQ hlen hpQ K hK hKQ⟩
  · intro l hl
    rw [map_sub, PowerSeries.coeff_C_mul, map_sub, Derivation.leibniz,
      htQ.1 l hl, hsquare l hl, hα, smul_zero, smul_zero, add_zero, sub_zero]
  · dsimp only [δ, f, β] at he
    rw [htP.2, htQ.2, map_pow, c.normalPolynomialSeries_constant,
      c.normalPolynomialSeries_constant,
      c.originalHorizontalClosure_linear_inventory P Q v hQ hB (d + 1) (by omega)] at he
    rw [he]
    field_simp
    ring

end SkewCornerDescent.Matrix.SelectedCoordinate
