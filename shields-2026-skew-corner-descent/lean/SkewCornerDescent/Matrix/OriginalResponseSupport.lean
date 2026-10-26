/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalSourceSplit
import SkewCornerDescent.Matrix.BlockResponseLocality

/-!
# Actual retained response support

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Every path-support hypothesis is supplied
by the original complementary Jacobi--Trudi geometry. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The literal last column remains in its original component's block. -/
theorem interiorBlockLast_label {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorBlock P (interiorBlockLast P i) = interiorBlock P i :=
  (mem_interiorBlockFiber P i _).mp (interiorBlockLast_mem P i)

/-- Actual retained-to-retained source entries vanish below their component order. -/
theorem originalSplitMatrix_selected_zero {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hlt : interiorBlock P d.val.val < interiorBlock P b.val.val) :
    (originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inl (some d)) = 0 := by
  change hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) = 0
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  exact interior_polynomial_blockTriangular P (by rw [interiorBlockLast_label]; exact hlt)

/-- Original geometry supplies the incoming lower cutoff for every selected source row. -/
theorem originalSplitMatrix_incoming_zero {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hlt : interiorBlock P j.1.val < interiorBlock P b.val.val) :
    (originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr j) = 0 := by
  change hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inr j))) = 0
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_removed]
  exact interior_polynomial_blockTriangular P
    (by rw [originalRemovedCol_block]; exact hlt)

/-- Original geometry supplies the outgoing upper cutoff for every selected source column. -/
theorem originalSplitMatrix_outgoing_zero {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hlt : interiorBlock P b.val.val < interiorBlock P j.1.val) :
    (originalSplitMatrix (hD := hD) P) (.inr j) (.inl (some b)) = 0 := by
  change hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inr j)) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))) = 0
  rw [originalRowSplitEquiv_removed, originalColSplitEquiv_selected]
  exact interior_polynomial_blockTriangular P
    (by rw [interiorBlockLast_label, originalRemovedRow_block]; exact hlt)

/-- The actual response entry is the full inverse contraction, with no omitted coupling. -/
theorem originalLocalResponse_entry {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    c.originalLocalResponse P b d =
      algebraMap Lambda c.RegularRing ((originalSplitMatrix (hD := hD) P) (.inl b) (.inl d)) -
        inverseContraction
          (fun j => algebraMap Lambda c.RegularRing
            ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j)))
          (fun j => algebraMap Lambda c.RegularRing
            ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d)))
          ((originalRemovedMatrix (hD := hD) P).map (algebraMap Lambda c.RegularRing)) := by
  let := c.originalRemovedLocalInverse P
  unfold originalLocalResponse localRetainedResponse retainedResponse inverseContraction
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Complete elimination preserves the original below-block zeros without any supplied support. -/
theorem originalLocalResponse_selected_zero {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hlt : interiorBlock P d.val.val < interiorBlock P b.val.val) :
    c.originalLocalResponse P (some b) (some d) = 0 := by
  let := c.originalRemovedLocalInverse P
  rw [c.originalLocalResponse_entry]
  have hM := (originalRemovedMatrix_blockTriangular (hD := hD) P).map
    (algebraMap Lambda c.RegularRing)
  have hz := inverseContraction_zero_of_order
    (fun j => algebraMap Lambda c.RegularRing
      ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr j)))
    (fun j => algebraMap Lambda c.RegularRing
      ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl (some d))))
    ((originalRemovedMatrix (hD := hD) P).map (algebraMap Lambda c.RegularRing))
    (fun j => interiorBlock P j.1.val) hM
    (interiorBlock P b.val.val) (interiorBlock P d.val.val) hlt
    (fun j hj => by rw [originalSplitMatrix_incoming_zero P b j hj, map_zero])
    (fun j hj => by rw [originalSplitMatrix_outgoing_zero P d j hj, map_zero])
  rw [hz, originalSplitMatrix_selected_zero P b d hlt, map_zero, sub_zero]

/-- The original block-label fiber is exactly the remaining indices of this canonical block. -/
def originalRemovedLabelFiberEquiv {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    Fin (originalRemovedSize (hD := hD) P b) ≃
      {j : OriginalRemainingIndices (hD := hD) P //
        interiorBlock P j.1.val = interiorBlock P b.val} where
  toFun j := ⟨⟨b, j⟩, rfl⟩
  invFun j := originalBlocks_label_injective P j.property ▸ j.val.2
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨⟨d, k⟩, he⟩
    have hb : d = b := originalBlocks_label_injective P he
    subst d
    rfl

/-- A same-component response is its complete proper-block contraction, not a truncated inverse. -/
theorem originalLocalResponse_diagonal {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    c.originalLocalResponse P (some b) (some b) =
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inl (some b))) -
      inverseContraction
        (fun j : Fin (originalRemovedSize (hD := hD) P b.val) =>
          algebraMap Lambda c.RegularRing
            ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr ⟨b.val, j⟩)))
        (fun j => algebraMap Lambda c.RegularRing
          ((originalSplitMatrix (hD := hD) P) (.inr ⟨b.val, j⟩) (.inl (some b))))
        ((originalRemovedDiagonal (hD := hD) P b.val).map
          (algebraMap Lambda c.RegularRing)) := by
  let := c.originalRemovedLocalInverse P
  rw [c.originalLocalResponse_entry]
  congr 1
  have hM := (originalRemovedMatrix_blockTriangular (hD := hD) P).map
    (algebraMap Lambda c.RegularRing)
  have hl := inverseContraction_same_block
    (fun j => algebraMap Lambda c.RegularRing
      ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr j)))
    (fun j => algebraMap Lambda c.RegularRing
      ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl (some b))))
    ((originalRemovedMatrix (hD := hD) P).map (algebraMap Lambda c.RegularRing))
    (fun j => interiorBlock P j.1.val) hM (interiorBlock P b.val.val)
    (fun j hj => by rw [originalSplitMatrix_incoming_zero P b j hj, map_zero])
    (fun j hj => by rw [originalSplitMatrix_outgoing_zero P b j hj, map_zero])
  rw [hl]
  exact (inverseContraction_equiv (originalRemovedLabelFiberEquiv (hD := hD) P b.val)
    _ _ _).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
