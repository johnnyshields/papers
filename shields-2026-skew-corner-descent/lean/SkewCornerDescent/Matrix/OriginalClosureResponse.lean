/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalComponentSelection
import SkewCornerDescent.Matrix.ResiduePolynomialBand

/-!
# The protected response at the actual horizontal splice

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Both endpoint occurrences are produced in a
profile of the actual horizontal closure. Their retained full-inverse response has the true
cap-sum top, equal to the selected span plus the geometric splice distance. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every component of the actual horizontal closure has the original geometric span bound. -/
theorem originalHorizontalClosure_component_span {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∀ C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)),
      span C ≤ (c.top : ℕ) := by
  intro C hC
  rw [originalHorizontalClosure_components] at hC
  rcases Finset.mem_union.mp hC with hC | hC
  · exact hmax C hC
  · obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hC
    rw [span_translate]
    exact hmax E hE

/-- The actual horizontal closure, its two literal selected endpoint occurrences, and its
protected response are constructed from the original source, not supplied as matching data. -/
theorem originalHorizontalClosure_response {n : ℕ} (P : Profile n)
    (first last : OriginalSelectedBlocks (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ m : ℕ, ∃ Q : Profile m, ∃ v : ℤ × ℤ,
      originalHorizontalClosure P = translate v Q.cells ∧
      ∃ upper lower : OriginalSelectedBlocks (hD := hD) Q,
        translate v (interiorBlockCells Q upper.val.val) =
          translate (vH P.cells) (interiorBlockCells P last.val.val) ∧
        translate v (interiorBlockCells Q lower.val.val) = interiorBlockCells P first.val.val ∧
        ∃ K : ℕ+, (K : ℤ) = (c.top : ℤ) + originalCapSpliceDistance P first last ∧
          (K : ℤ) = originalFirstCapDistance P first + originalLastCapDistance P last ∧
          c.top < K ∧
          (∃ R ∈ supported ℚ {j : ℕ+ | j < K}, ∃ q : Lambda,
            q ≠ 0 ∧ ¬cellSchur D hD.1 ∣ q ∧ polynomialSpan q ≤ (c.top : ℕ) ∧
              c.regularEmbedding (c.originalLocalResponse Q (some upper) (some lower)) =
                originalMap (X K) + originalMap R / originalMap q) ∧
          ∃ A ∈ residuePolynomialBand c.top K,
            c.regularResidue (c.originalLocalResponse Q (some upper) (some lower)) =
              c.residueMap (X K) + A := by
  obtain ⟨m, Q, v, hv⟩ := (originalHorizontalClosure_connected P).exists_profile_cells
  have hf := originalBlockSelected_nonempty P first.val first.property
  have hl := originalBlockSelected_nonempty P last.val last.property
  have hcf := interiorBlockCells_mem_components P first.val.val hf
  have hcl := interiorBlockCells_mem_components P last.val.val hl
  have hF := (dvd_originalBlock_iff (hD := hD) P first.val.val hf).mp first.property
  have hL := (dvd_originalBlock_iff (hD := hD) P last.val.val hl).mp last.property
  have hfirst := originalHorizontalClosure_first_component P hcf
  have hlast := originalHorizontalClosure_second_component P hcl
  rw [hv] at hfirst hlast
  obtain ⟨lower, hLower⟩ := exists_originalSelectedBlock_of_translated_component (hD := hD) Q v
    (interiorBlockCells P first.val.val) hfirst hF
  have hLt : cellSchur D hD.1 =
      cellSchur (translate (vH P.cells) (interiorBlockCells P last.val.val))
        (isSkew_component (isSkew_translate v Q.isConnectedSkew_cells.1).interior hlast) := by
    rw [cellSchur_translate]
    exact hL
  obtain ⟨upper, hUpper⟩ := exists_originalSelectedBlock_of_translated_component (hD := hD) Q v
    (translate (vH P.cells) (interiorBlockCells P last.val.val)) hlast hLt
  have hminU := congrArg minContent hUpper
  have hminL := congrArg minContent hLower
  rw [minContent_translate (interiorBlockCells_connected Q upper.val.val
      (originalBlockSelected_nonempty Q upper.val upper.property)).2.1] at hminU
  rw [minContent_translate (interiorBlockCells_connected Q lower.val.val
      (originalBlockSelected_nonempty Q lower.val lower.property)).2.1] at hminL
  rw [interiorBlockCells_minContent Q upper.val.val
    (originalBlockSelected_nonempty Q upper.val upper.property)] at hminU
  rw [interiorBlockCells_minContent Q lower.val.val
    (originalBlockSelected_nonempty Q lower.val lower.property)] at hminL
  have hN := c.originalSelected_endpoint_distance Q upper
  have hdist : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some upper))) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some lower))) =
        (c.top : ℤ) + originalCapSpliceDistance P first last := by
    rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
    unfold originalCapSpliceDistance
    omega
  have hcap := c.originalCapSpliceDistance_cap_sum P first last
  have hcap0 := c.originalFirstCapDistance_gt_top P first
  have hcap1 := c.originalLastCapDistance_gt_top P last
  let K : ℕ+ := ⟨((c.top : ℤ) + originalCapSpliceDistance P first last).toNat, by
    have hpos := c.top.pos
    omega⟩
  have hK : (K : ℤ) = (c.top : ℤ) + originalCapSpliceDistance P first last := by
    apply Int.toNat_of_nonneg
    have hpos := c.top.pos
    omega
  have hNK : c.top < K := by
    exact_mod_cast (show (c.top : ℤ) < (K : ℤ) by omega)
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    intro C hC
    have hCt : translate v C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)) := by
      rw [hv, interior_translate, edgeComponents_translate]
      exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
    have h := c.originalHorizontalClosure_component_span P hmax _ hCt
    rwa [span_translate] at h
  obtain ⟨A, hA, he⟩ := c.originalLocalResponse_residue_polynomial Q
    (some upper) (some lower) K hNK (hdist.trans hK.symm) hmaxQ
  have hfrac := c.originalLocalResponse_triangular_fraction Q
    (some upper) (some lower) K hNK (hdist.trans hK.symm) hmaxQ
  exact ⟨m, Q, v, hv, upper, lower, hUpper, hLower, K, hK, hK.trans hcap, hNK,
    hfrac, A, hA, he⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
