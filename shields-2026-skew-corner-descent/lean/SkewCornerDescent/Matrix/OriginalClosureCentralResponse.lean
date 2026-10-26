/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureEnumeration
import SkewCornerDescent.Matrix.OriginalClosureNormalResponse
import SkewCornerDescent.Matrix.OriginalCompletedGaps

/-!
# The canonical central original closure response

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`, `lem:original-transfer`). The central diagonal
response of every literal closure profile is identified using its canonical original
occurrence indices. Its protected top and every normal-jet derivative are produced from
that geometry, not supplied as response-matching data. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The middle state of the actual closure is the original cap-splice response. -/
theorem originalHorizontalClosure_central_distance {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    originalHessenbergDistance (hD := hD) Q middle middle =
      (c.top : ℤ) + c.originalCompletedGap P last := by
  dsimp only
  let B := originalSelectedCount (hD := hD) P
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  let a : Fin (originalSelectedCount (hD := hD) Q) := ⟨B - 1, by dsimp [B]; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) Q) := ⟨B, by dsimp [B]; omega⟩
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) := ⟨B, by dsimp [B]; omega⟩
  have ha : middle = a.succ := by apply Fin.ext; dsimp [middle, a, B]; omega
  have hb : middle = b.castSucc := rfl
  change originalHessenbergDistance (hD := hD) Q middle middle = _
  unfold originalHessenbergDistance
  rw [ha, originalHessenbergRows_succ, ← ha, hb, originalHessenbergCols_castSucc]
  rw [c.originalHorizontalClosure_response_endpoint_distance P Q v
    (originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩)
    (originalSelectedEnumeration (hD := hD) P ⟨B - 1, by dsimp [B]; omega⟩)
    (originalSelectedEnumeration (hD := hD) Q a)
    (originalSelectedEnumeration (hD := hD) Q b)
    (originalHorizontalClosure_enumeration_upper_cells P Q v hQ
      ⟨B - 1, by dsimp [B]; omega⟩)
    (by
      have he := originalHorizontalClosure_enumeration_lower_cells P Q v hQ ⟨0, hB⟩
      simpa only [Fin.val_zero, add_zero] using he)]
  rw [c.originalCompletedGap_last_eq_splice P hB]

/-- The actual closure profile inherits the complete original component span bound. -/
theorem originalHorizontalClosure_profile_component_span {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
  intro C hC
  have ht : translate v C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)) := by
    rw [hQ, interior_translate, edgeComponents_translate]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  have h := c.originalHorizontalClosure_component_span P hmax _ ht
  rwa [span_translate] at h

/-- The canonical middle response has a constructed protected top, a faithful monic residue,
and the exact derivative of every coefficient of its complete normal series. -/
theorem originalHorizontalClosure_central_normal_response {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    ∃ K : ℕ+, (K : ℤ) = (c.top : ℤ) + c.originalCompletedGap P last ∧
      ∃ hK : c.top < K,
        (∃ A ∈ residuePolynomialBand c.top K,
          c.regularResidue (c.originalHessenbergResponse Q middle middle) =
            c.residueMap (MvPolynomial.X K) + A) ∧
        ∀ k, residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
          (PowerSeries.coeff k
            (c.normalSeries (c.originalHessenbergResponse Q middle middle))) =
              if k = 0 then 1 else 0 := by
  dsimp only
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
    omega
  let K := c.originalHessenbergTop Q hBQ middle middle le_rfl
  have hK : c.top < K := by
    have hd := c.originalHessenbergDistance_gt_top Q hBQ middle middle le_rfl
    have hk := c.originalHessenbergTop_coe Q hBQ middle middle le_rfl
    exact_mod_cast (show (c.top : ℤ) < (K : ℤ) by rw [hk]; exact hd)
  have hd : originalHessenbergDistance (hD := hD) Q middle middle = (K : ℤ) :=
    (c.originalHessenbergTop_coe Q hBQ middle middle le_rfl).symm
  have hspan := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  have htop := c.originalHorizontalClosure_central_distance P Q v hQ hB
  refine ⟨K, hd.symm.trans htop, hK, ?_, ?_⟩
  · exact c.originalLocalResponse_residue_polynomial Q
      (originalHessenbergRows (hD := hD) Q middle)
      (originalHessenbergCols (hD := hD) Q middle) K hK hd hspan
  · exact c.originalLocalResponse_normalSeries_derivative Q
      (originalHessenbergRows (hD := hD) Q middle)
      (originalHessenbergCols (hD := hD) Q middle) K hK hd hspan

end SkewCornerDescent.Matrix.SelectedCoordinate
