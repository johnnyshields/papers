/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureCapProducts
import SkewCornerDescent.Matrix.OriginalClosureInventory
import SkewCornerDescent.Matrix.OriginalSignedFactors

/-!
# Actual closure quotient with complete removed-factor cancellation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:residue-classifier`).
The literal two-copy inventory cancels the entire removed determinant, with no normal
truncation. The produced integer orientation sign is retained explicitly. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual full original quotient cancels the complete two-copy removed determinant. -/
theorem originalHorizontalClosure_original_quotient {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      originalMap Q.schur / originalMap P.schur ^ 2 =
        (ε : actualField) * c.regularEmbedding (c.originalHessenbergResponse Q).det /
          c.regularEmbedding (c.originalHessenbergResponse P).det ^ 2 := by
  obtain ⟨εP, hεP, hP⟩ := c.originalHessenberg_local_signed_factorization P
  obtain ⟨εQ, hεQ, hQ'⟩ := c.originalHessenberg_local_signed_factorization Q
  have hP' := congrArg c.regularEmbedding hP
  have hQ'' := congrArg c.regularEmbedding hQ'
  simp only [map_mul, map_intCast, c.regularEmbedding_polynomial] at hP' hQ''
  have hs : (εP : actualField) ^ 2 = 1 := by
    rcases hεP with h | h <;> simp only [h, Int.cast_one, Int.reduceNeg,
      Int.cast_neg, neg_one_sq, one_pow]
  have hr : (originalRemovedMatrix (hD := hD) P).det ≠ 0 := by
    intro hz
    exact not_dvd_originalRemovedMatrix (hD := hD) P (hz ▸ dvd_zero _)
  have ha : originalMap (originalRemovedMatrix (hD := hD) P).det ≠ 0 := by
    simpa only [ne_eq, originalMap_eq_zero] using hr
  refine ⟨εQ, hεQ, ?_⟩
  rw [hP', hQ'', mul_pow, mul_pow, hs, one_mul,
    originalHorizontalClosure_removed_square P Q v hQ, map_pow]
  calc
    _ = (originalMap (originalRemovedMatrix (hD := hD) P).det ^ 2 *
        ((εQ : actualField) * c.regularEmbedding (c.originalHessenbergResponse Q).det)) /
        (originalMap (originalRemovedMatrix (hD := hD) P).det ^ 2 *
          c.regularEmbedding (c.originalHessenbergResponse P).det ^ 2) := by
      congr 1
      ring
    _ = _ := by rw [mul_div_mul_left _ _ (pow_ne_zero 2 ha), mul_div_assoc]

/-- The actual original residue quotient is the central response divided by its true cap pair,
with the produced determinant orientation sign retained. -/
theorem originalHorizontalClosure_residue_quotient {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      c.residueMap Q.schur / c.residueMap P.schur ^ 2 =
        (ε : OtherField c.top) *
          c.regularResidue (c.originalHessenbergResponse Q middle middle) /
            c.originalTrueCapProduct P := by
  classical
  obtain ⟨εP, hεP, hP⟩ := c.originalHessenberg_residue_signed_factorization P
  obtain ⟨εQ, hεQ, hQ'⟩ := c.originalHessenberg_residue_signed_factorization Q
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
    omega
  rw [c.originalHessenberg_residue_cap_product P hB] at hP
  rw [c.originalHessenberg_residue_cap_product Q hBQ,
    c.originalHorizontalClosure_true_cap_product P Q v hQ hB,
    c.originalHorizontalClosure_internal_residue_product P Q v hQ hB,
    originalHorizontalClosure_removed_square P Q v hQ, map_pow] at hQ'
  have hs : (εP : OtherField c.top) ^ 2 = 1 := by
    rcases hεP with h | h <;> simp only [h, Int.cast_one, Int.reduceNeg,
      Int.cast_neg, neg_one_sq, one_pow]
  have hd := (c.originalRemoved_residue_lower_scalar P hmax).2
  have hF := c.originalTrueCapProduct_ne_zero P hB hmax
  have hT : (∏ i, c.originalInternalResidue P i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact c.originalHessenberg_residue_ne_zero P hB hmax ⟨i.val + 1, by omega⟩
  refine ⟨εQ, hεQ, ?_⟩
  rw [hP, hQ', mul_pow, mul_pow, mul_pow, hs, one_mul]
  field_simp

end SkewCornerDescent.Matrix.SelectedCoordinate
