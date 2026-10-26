/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.EmptyVerticalClosure
import SkewGluing.GeometricCompositionMap

/-!
# Complementary horizontal and vertical empty closures

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The actual empty composition map sends the two-cell row and column to the
complete horizontal and vertical closures. Their Schur functions sum to the
square of the complete source function. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- The literal two-cell column outer is a translate of the transposed row. -/
theorem antitranspose_two_row_cells :
    antitranspose (horizontalRow 2) = translate (-1, 0) (transpose (horizontalRow 2)) := by
  ext x
  rcases x with ⟨i, j⟩
  simp only [mem_antitranspose, mem_translate, mem_transpose, mem_horizontalRow,
    Prod.fst_sub, Prod.snd_sub, Prod.fst_swap, Prod.snd_swap]
  omega

/-- The actual column outer has elementary function `h₁²-h₂`. -/
theorem cellSchur_antitranspose_two_row :
    cellSchur (antitranspose (horizontalRow 2))
      (isConnectedSkew_antitranspose (isConnectedSkew_horizontalRow (by decide))).1 =
      X 1 ^ 2 - X 2 := by
  have hr := isConnectedSkew_horizontalRow (by decide : 0 < 2)
  change IsSkew (horizontalRow 2) ∧ IsEdgeConnected (horizontalRow 2) at hr
  rw [cellSchur_congr antitranspose_two_row_cells _
      (isSkew_translate _ (isSkew_transpose hr.1)),
    cellSchur_translate (transpose (horizontalRow 2)) (isSkew_transpose hr.1) (-1, 0),
    ← schurInvolution_cellSchur hr]
  exact (congrArg schurInvolution (cellSchur_horizontal_row 2)).trans
    ((schurInvolution_X (2 : ℕ+)).trans elem_two)

/-- The actual horizontal and vertical empty closures have complementary
functions. Every cell of both compositions is retained in this identity. -/
theorem empty_closure_schur_complement {n : ℕ} (P : Profile n) :
    cellSchur (Matrix.originalHorizontalClosure P)
        (Matrix.originalHorizontalClosure_connected P).1 +
      cellSchur (originalVerticalClosure P) (originalVerticalClosure_connected P).1 =
        P.schur ^ 2 := by
  let ω := emptyMarkH P.cells
  let h := emptyMarkH_isLegal P.isConnectedSkew_cells
  let φ := ω.modifiedCompositionMap h
  have hA : ω.normalA h = 1 := by
    simp only [MarkedInner.normalA, ω, emptyMarkH, Finset.not_nonempty_empty, dite_false]
  have hB : ω.normalB h = 1 := by
    simp only [MarkedInner.normalB, ω, emptyMarkH, Finset.not_nonempty_empty, dite_false]
  have hp : ω.compose (horizontalRow 1) = P.cells := by
    rw [ω.compose_horizontalRow (by decide), MarkedInner.rowCopies]
    change (({0} : Finset ℕ).biUnion
      fun j => translate ((j : ℤ) • vH P.cells) P.cells) = P.cells
    rw [Finset.singleton_biUnion]
    simp only [Nat.cast_zero, zero_smul, SkewGluing.translate_zero]
  have hx1 : φ (X 1) = P.schur := by
    change (ω.modifiedCompositionMap h) (X 1) = _
    rw [MarkedInner.modifiedCompositionMap, bind₁_X_right, MarkedInner.modifiedGenerator,
      MarkedInner.rowSchur]
    simp only [hA, one_pow, one_mul]
    exact (cellSchur_congr hp _ P.isSkew_cells).trans (cellSchur_cells P)
  have hx2 : φ (X 2) =
      cellSchur (Matrix.originalHorizontalClosure P)
        (Matrix.originalHorizontalClosure_connected P).1 := by
    change (ω.modifiedCompositionMap h) (X 2) = _
    rw [MarkedInner.modifiedCompositionMap, bind₁_X_right, MarkedInner.modifiedGenerator,
      MarkedInner.rowSchur]
    simp only [hA, one_pow, one_mul]
    rfl
  let C := antitranspose (horizontalRow 2)
  have hC := isConnectedSkew_antitranspose (isConnectedSkew_horizontalRow (by decide : 0 < 2))
  have hc : C.card = 2 := by
    change (antitranspose (horizontalRow 2)).card = 2
    unfold antitranspose
    rw [Finset.card_image_of_injective _ (by
      intro a b he
      simp only [Prod.mk.injEq, neg_inj] at he
      exact Prod.ext he.2 he.1)]
    exact (gluing_horizontalRow_statistics 2).1
  have hs : span C = 2 := by rw [span_antitranspose, span_horizontalRow]
  have hv := h.modifiedCompositionMap_cellSchur_ordinary (Or.inl (rfl : ω.case = .a)) hC
  rw [hA, hB, hc, hs, Nat.sub_self, pow_zero, one_pow, one_mul,
    cellSchur_antitranspose_two_row, map_sub, map_pow, hx1, hx2] at hv
  simp only [one_pow, one_mul, mul_one] at hv
  change P.schur ^ 2 -
      cellSchur (Matrix.originalHorizontalClosure P)
        (Matrix.originalHorizontalClosure_connected P).1 =
      cellSchur (originalVerticalClosure P) (originalVerticalClosure_connected P).1 at hv
  linear_combination -hv

end SkewCornerDescent
