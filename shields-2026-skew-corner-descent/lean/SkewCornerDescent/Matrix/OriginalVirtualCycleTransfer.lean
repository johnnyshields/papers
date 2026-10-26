/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalVirtualClosureTransfer
import SkewCornerDescent.FiniteVirtualClosureWindows

/-!
# Shifted closure cycles from actual Schur residues

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The virtual difference changes exactly the central response in the completed source
cycle. Its value is defined by the actual Schur quotient, preserving its orientation.
The determinant coefficient retains every crossing start. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual quotient rescales the central response, without assuming a monic
normalization sign or identifying two different virtual-class parameters. -/
noncomputable def originalVirtualCentralResponse {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (middle : Fin (originalSelectedCount (hD := hD) Q + 1)) (α : ℚ) :
    OtherField c.top :=
  c.regularResidue (c.originalHessenbergResponse Q middle middle) *
    (c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2) /
      c.residueMap Q.schur

/-- The full actual virtual determinant has one linear source inventory and one
completed shifted-cycle inventory. Earlier-jet independence is produced, not assumed. -/
theorem originalVirtualClosure_normalized_log_cycle {n m : ℕ}
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
    (∀ l, l < d → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l T) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff d
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff T)⁻¹ * T))) =
      ((-1 : OtherField c.top) ^ d * (c.normalCoefficient)⁻¹ ^ d) *
        (linearInverseWindowSum (c.originalInternalResidue P) (d + 1) +
          CyclicWindows.inverseWindowSum
            (CyclicWindows.completeResponseCycle (c.originalInternalResidue P)
              (c.originalVirtualCentralResponse P Q middle α)) (d + 1)) := by
  have ht := c.originalVirtualClosure_normalized_log_from_source P Q v hQ hB hmax
    r k d hd hdB hlen hp K hK hKeq α
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by omega⟩
  let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
  have hS : S ≠ 0 := c.originalHessenberg_residue_ne_zero Q hBQ hmaxQ middle
  have hβ : c.residueMap Q.schur ≠ 0 := c.originalSchur_residue_ne_zero Q hBQ hmaxQ
  have hunit := c.originalVirtualClosure_residue_ne_zero P Q v hQ hB hmax α
  have hshift : c.originalVirtualCentralResponse P Q middle α ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hS hunit) hβ
  have hi := CyclicWindows.inverseWindowSum_complete_replace
    (c.originalInternalResidue P) S (c.originalVirtualCentralResponse P Q middle α)
    hS hshift (d + 1) (by omega)
  dsimp only at ht ⊢
  constructor
  · exact ht.1
  · rw [ht.2.1, hi]
    unfold originalVirtualCentralResponse
    dsimp only [S, middle] at hS ⊢
    field_simp [hS, hβ, hunit]
    ring

/-- The actual closure orientation reindexes every rational virtual label at once.
The shifted response is the complete central response minus the signed cap product. -/
theorem originalVirtualCentralResponse_eq_signed_cap {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ α : ℚ,
      c.originalVirtualCentralResponse P Q middle α =
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (ε : OtherField c.top) * (α : OtherField c.top) * c.originalTrueCapProduct P := by
  obtain ⟨ε, hε, hr⟩ := c.originalHorizontalClosure_residue_quotient P Q v hQ hB hmax
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega
  have hf := c.originalSchur_residue_ne_zero P hB hmax
  have hβ := c.originalSchur_residue_ne_zero Q hBQ
    (c.originalHorizontalClosure_profile_component_span P Q v hQ hmax)
  have hcap := c.originalTrueCapProduct_ne_zero P hB hmax
  dsimp only at hr ⊢
  have hcross := (div_eq_div_iff (pow_ne_zero 2 hf) hcap).mp hr
  refine ⟨ε, hε, ?_⟩
  intro α
  unfold originalVirtualCentralResponse
  rcases hε with h | h
  · rw [h] at hcross ⊢
    norm_num only [Int.cast_one, one_mul] at hcross ⊢
    field_simp [hβ]
    linear_combination (α : OtherField c.top) * hcross
  · rw [h] at hcross ⊢
    norm_num only [Int.cast_neg, Int.cast_one, neg_one_mul] at hcross ⊢
    field_simp [hβ]
    linear_combination -(α : OtherField c.top) * hcross

end SkewCornerDescent.Matrix.SelectedCoordinate
