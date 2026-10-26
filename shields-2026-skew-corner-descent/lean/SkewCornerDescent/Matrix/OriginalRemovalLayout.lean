/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.SelectedBlockRegularity

/-!
# Original removed source layout

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Actual block representatives and divisibility
select the retained first rows and last columns. Source indices enumerate the complete remaining
rows and columns, without independent partition or regularity assumptions. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Exactly one representative for each produced original block. -/
abbrev OriginalBlocks {n : ℕ} (P : Profile n) :=
  {i : Fin n // interiorBlockFirst P i = i}

/-- Different canonical representatives cannot have the same block label. -/
theorem originalBlocks_label_injective {n : ℕ} (P : Profile n) :
    Function.Injective (fun b : OriginalBlocks P => interiorBlock P b.val) := by
  intro b d he
  apply Subtype.ext
  have h := interiorBlockFirst_eq_of_label_eq P he
  rwa [b.property, d.property] at h

namespace SelectedCoordinate

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual divisibility, not a supplied selection mask, chooses a component occurrence. -/
def originalBlockSelected {n : ℕ} (P : Profile n) (b : OriginalBlocks P) : Prop :=
  cellSchur D hD.1 ∣
    ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
      (interiorBlock P) (interiorBlock P b.val)).det

/-- All nonselected rows remain; precisely one row and column leave a selected component. -/
noncomputable def originalRemovedSize {n : ℕ} (P : Profile n) (b : OriginalBlocks P) : ℕ :=
  if originalBlockSelected (hD := hD) P b then interiorBlockLength P b.val
  else interiorBlockLength P b.val + 1

/-- Position of a remaining source row within its original component. -/
noncomputable def originalRemovedRowPosition {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) : Fin (interiorBlockLength P b.val + 1) := by
  classical
  by_cases hs : originalBlockSelected (hD := hD) P b
  · exact ⟨j.val + 1, by
      have hj := j.isLt
      simp only [originalRemovedSize, ite_eq_left hs] at hj
      omega⟩
  · exact ⟨j.val, by
      have hj := j.isLt
      simpa only [originalRemovedSize, ite_eq_right hs] using hj⟩

/-- Position of a remaining source column: a selected component omits its last column. -/
noncomputable def originalRemovedColPosition {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) : Fin (interiorBlockLength P b.val + 1) :=
  ⟨j.val, by
    classical
    have hj := j.isLt
    by_cases hs : originalBlockSelected (hD := hD) P b
    · simp only [originalRemovedSize, ite_eq_left hs] at hj
      omega
    · simpa only [originalRemovedSize, ite_eq_right hs] using hj⟩

/-- Remaining source row index in the original complementary list. -/
noncomputable def originalRemovedRow {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) : Fin n :=
  interiorSliceIndex (interiorBlockFirst P b.val).val (interiorBlockLength P b.val)
    (interiorBlock_interval_bound P b.val) (originalRemovedRowPosition (hD := hD) P b j)

/-- Remaining source column index in the original complementary list. -/
noncomputable def originalRemovedCol {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) : Fin n :=
  interiorSliceIndex (interiorBlockFirst P b.val).val (interiorBlockLength P b.val)
    (interiorBlock_interval_bound P b.val) (originalRemovedColPosition (hD := hD) P b j)

/-- Both surviving source endpoints stay in their produced original block. -/
theorem originalRemovedRow_block {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) :
    interiorBlock P (originalRemovedRow (hD := hD) P b j) = interiorBlock P b.val := by
  unfold originalRemovedRow
  have hfirst : interiorSliceIndex (interiorBlockFirst P b.val).val
      (interiorBlockLength P b.val) (interiorBlock_interval_bound P b.val) 0 = b.val := by
    apply Fin.ext
    simp only [interiorSliceIndex, Fin.val_zero, add_zero, b.property]
  exact (interiorBlock_slice_same P b.val _).trans (by rw [hfirst])

theorem originalRemovedCol_block {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) :
    interiorBlock P (originalRemovedCol (hD := hD) P b j) = interiorBlock P b.val := by
  unfold originalRemovedCol
  have hfirst : interiorSliceIndex (interiorBlockFirst P b.val).val
      (interiorBlockLength P b.val) (interiorBlock_interval_bound P b.val) 0 = b.val := by
    apply Fin.ext
    simp only [interiorSliceIndex, Fin.val_zero, add_zero, b.property]
  exact (interiorBlock_slice_same P b.val _).trans (by rw [hfirst])

/-- Every original removed row and column is retained in the assembled matrix. -/
noncomputable def originalRemovedMatrix {n : ℕ} (P : Profile n) :
    Matrix (Σ b : OriginalBlocks P, Fin (originalRemovedSize (hD := hD) P b))
      (Σ b : OriginalBlocks P, Fin (originalRemovedSize (hD := hD) P b)) Lambda :=
  Matrix.of fun j k =>
    hh (P.xi (originalRemovedRow (hD := hD) P j.1 j.2).succ -
      P.zeta (originalRemovedCol (hD := hD) P k.1 k.2).castSucc)

/-- The assembled actual removed matrix is block upper triangular in the original order. -/
theorem originalRemovedMatrix_blockTriangular {n : ℕ} (P : Profile n) :
    (originalRemovedMatrix (hD := hD) P).BlockTriangular
      (fun j => interiorBlock P j.1.val) := by
  intro j k hjk
  have hr := originalRemovedRow_block (hD := hD) P j.1 j.2
  have hc := originalRemovedCol_block (hD := hD) P k.1 k.2
  exact interior_polynomial_blockTriangular P
    (i := originalRemovedRow (hD := hD) P j.1 j.2)
    (j := originalRemovedCol (hD := hD) P k.1 k.2) (by rw [hr, hc]; exact hjk)

/-- Canonical block order gives the same triangularity with a finite block index type. -/
theorem originalRemovedMatrix_blockTriangular_fst {n : ℕ} (P : Profile n) :
    (originalRemovedMatrix (hD := hD) P).BlockTriangular Sigma.fst := by
  intro j k hjk
  have hle := interiorBlock_mono P (show k.1.val ≤ j.1.val from hjk.le)
  have hne : interiorBlock P k.1.val ≠ interiorBlock P j.1.val := by
    intro he
    have hb := originalBlocks_label_injective P he
    exact (ne_of_lt hjk) hb
  exact originalRemovedMatrix_blockTriangular (hD := hD) P (lt_of_le_of_ne hle hne)

/-- The diagonal sigma fiber contains precisely the remaining indices of this block. -/
def originalRemovedFiberEquiv {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    Fin (originalRemovedSize (hD := hD) P b) ≃
      {j : Σ d : OriginalBlocks P, Fin (originalRemovedSize (hD := hD) P d) // j.1 = b} where
  toFun j := ⟨⟨b, j⟩, rfl⟩
  invFun j := j.property ▸ j.val.2
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨⟨d, k⟩, he⟩
    change d = b at he
    subst d
    rfl

end SelectedCoordinate
end SkewCornerDescent.Matrix
