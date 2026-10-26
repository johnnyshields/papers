/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureResponse
import SkewCornerDescent.Matrix.OriginalNormalDerivative
import SkewCornerDescent.Matrix.OriginalCompletedGaps

/-!
# Full normal protected response at the actual horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-elimination`,
`lem:actual-words`, `lem:original-transfer`). The literal closure and its actual
selected endpoints produce the protected top and the entire generator derivative.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Identifying the two actual closure component occurrences identifies their full retained
endpoint distance. No response equality or guessed protected index is used. -/
theorem originalHorizontalClosure_response_endpoint_distance {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (first last : OriginalSelectedBlocks (hD := hD) P)
    (upper lower : OriginalSelectedBlocks (hD := hD) Q)
    (hUpper : translate v (interiorBlockCells Q upper.val.val) =
      translate (vH P.cells) (interiorBlockCells P last.val.val))
    (hLower : translate v (interiorBlockCells Q lower.val.val) =
      interiorBlockCells P first.val.val) :
    Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some upper))) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some lower))) =
        (c.top : ℤ) + originalCapSpliceDistance P first last := by
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
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  unfold originalCapSpliceDistance
  omega

/-- The actual horizontal closure produces its entire fresh-generator derivative at every
normal order, in addition to its faithful monic residue response. -/
theorem originalHorizontalClosure_normal_response {n : ℕ} (P : Profile n)
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
          ∃ hK : c.top < K,
            (∃ A ∈ residuePolynomialBand c.top K,
              c.regularResidue (c.originalLocalResponse Q (some upper) (some lower)) =
                c.residueMap (MvPolynomial.X K) + A) ∧
            ∀ k, residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
              (PowerSeries.coeff k
                (c.normalSeries (c.originalLocalResponse Q (some upper) (some lower)))) =
                  if k = 0 then 1 else 0 := by
  obtain ⟨m, Q, v, hv, upper, lower, hUpper, hLower, K, hgap, hcap, hK,
    _, A, hA, he⟩ := c.originalHorizontalClosure_response P first last hmax
  have hdist := c.originalHorizontalClosure_response_endpoint_distance P Q v
    first last upper lower hUpper hLower
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    intro C hC
    have hCt : translate v C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)) := by
      rw [hv, interior_translate, edgeComponents_translate]
      exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
    have h := c.originalHorizontalClosure_component_span P hmax _ hCt
    rwa [span_translate] at h
  exact ⟨m, Q, v, hv, upper, lower, hUpper, hLower, K, hgap, hcap, hK, ⟨A, hA, he⟩,
    fun k => c.originalLocalResponse_normalSeries_derivative Q (some upper) (some lower)
      K hK (hdist.trans hgap.symm) hmaxQ k⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
