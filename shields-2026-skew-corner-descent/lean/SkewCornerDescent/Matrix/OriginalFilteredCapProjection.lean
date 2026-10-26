/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalBlockSubsetInverse
import SkewCornerDescent.Matrix.OriginalCapInverseProjection

/-!
# Full inverse projections of clipped actual caps

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The cap portion inside a complete window is a complete-block principal
selection. Its inverse is constructed from the original source, and literal
window copying transports every retained entry. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The clipped whole-window cap is exactly the corresponding window-selected
part of the full original cap interval. -/
noncomputable def originalFilteredCapIntervalEquiv {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P) :
    {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
      originalCapBlockSide upper b i.1.val} ≃
    {i : OriginalResponseInterval (hD := hD) P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) //
      originalBlockInWindow P lo hi i.1.1.1} where
  toFun i := by
    have hb := (originalCapInterval_block_bounds P upper b i.val.1.val).mpr i.property
    exact ⟨⟨⟨⟨i.val.1.val, i.val.2⟩, hb.2⟩, hb.1⟩, i.val.1.property⟩
  invFun i := by
    have hs := (originalCapInterval_block_bounds P upper b i.val.1.1.1).mp
      ⟨i.val.2, i.val.1.2⟩
    exact ⟨⟨⟨i.val.1.1.1, i.property⟩, i.val.1.1.2⟩, hs⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Every clipped actual cap receives the inverse of its complete retained
matrix, without a supplied determinant or entrywise inverse match. -/
@[instance_reducible]
noncomputable def originalFilteredCapInverse {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
        originalCapBlockSide upper b i.1.val} => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
      (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
        originalCapBlockSide upper b i.1.val} =>
          originalResponseCols P ⟨i.val.1.val, i.val.2⟩)) := by
  classical
  let keep := fun a : OriginalBlocks P => originalBlockInWindow P lo hi a
  let := c.originalResponseResidueIntervalInverse P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b)
  let := c.originalIntervalKeptBlockInverse P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b) keep
  let row := fun i : OriginalResponseInterval (hD := hD) P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b) =>
      originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b) =>
      originalResponseCols P i.1.1
  let M := (vertexBetaMatrix c.residueMap row col).toBlock
    (fun i => keep i.1.1.1) (fun i => keep i.1.1.1)
  let e := originalFilteredCapIntervalEquiv (hD := hD) P lo hi upper b
  have he : vertexBetaMatrix c.residueMap
      (fun i => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
      (fun i => originalResponseCols P ⟨i.val.1.val, i.val.2⟩) = M.submatrix e e := by
    apply Matrix.ext
    intro i j
    rfl
  rw [he]
  exact Matrix.submatrixEquivInvertible M e e

/-- The entire weighted inverse contraction of the actual clipped cap. -/
noncomputable def originalFilteredCapInverseProjection {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) : OtherField c.top :=
  letI := c.originalFilteredCapInverse P lo hi upper b
  let row := fun i : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
    originalCapBlockSide upper b i.1.val} => originalResponseRows P ⟨i.val.1.val, i.val.2⟩
  let col := fun i : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
    originalCapBlockSide upper b i.1.val} => originalResponseCols P ⟨i.val.1.val, i.val.2⟩
  profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z

/-- A literal window transports the full clipped-cap projection even when the
source's whole exterior cap is not contained in the window. -/
theorem originalLiteralWindow_filtered_cap_projection {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P)
    (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P lo hi b.val)
    (hb' : originalBlockInWindow Q (lo + q) (hi + q) b'.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    c.originalFilteredCapInverseProjection P lo hi upper b A T z =
      c.originalFilteredCapInverseProjection Q (lo + q) (hi + q) upper b' A T (z + q) := by
  classical
  obtain ⟨e, hend⟩ := originalLiteralWindow_filtered_cap_equiv (hD := hD) P Q lo hi q v hv
    hwindow hlo hloq hhiq hhi upper b b' hb hb' he
  let := c.originalFilteredCapInverse P lo hi upper b
  let := c.originalFilteredCapInverse Q (lo + q) (hi + q) upper b'
  dsimp only [originalFilteredCapInverseProjection]
  apply profileInverseProjection_affine_beta_copy c.residueMap e _ _ _ _ A T z q
  · intro i
    exact (hend i).1
  · intro i
    exact (hend i).2

/-- A whole cap contained in the window equals its clipped presentation with
every retained inverse entry unchanged. -/
theorem originalFilteredCap_projection_of_contained {n : ℕ}
    (P : Profile n) (lo hi : ℤ) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (hcontained : ∀ a, originalCapBlockSide upper b a → originalBlockInWindow P lo hi a)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    c.originalFilteredCapInverseProjection P lo hi upper b A T z =
      c.originalCapInverseProjection P upper b A T z := by
  classical
  let := c.originalFilteredCapInverse P lo hi upper b
  let := c.originalResponseResidueIntervalInverse P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b)
  let e := originalWindowCapIntervalEquiv (hD := hD) P lo hi upper b hcontained
  dsimp only [originalFilteredCapInverseProjection, originalCapInverseProjection]
  symm
  have hcopy := profileInverseProjection_affine_beta_copy c.residueMap e
    (fun i : OriginalResponseInterval (hD := hD) P
      (originalClosureCapLeft upper b) (originalClosureCapRight upper b) =>
        originalResponseRows P i.1.1)
    (fun i : OriginalResponseInterval (hD := hD) P
      (originalClosureCapLeft upper b) (originalClosureCapRight upper b) =>
        originalResponseCols P i.1.1)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
      originalCapBlockSide upper b i.1.val} => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
      originalCapBlockSide upper b i.1.val} => originalResponseCols P ⟨i.val.1.val, i.val.2⟩)
    A T z 0 (fun i => by simp only [add_zero]; rfl) (fun i => by simp only [add_zero]; rfl)
  simpa only [add_zero] using hcopy

end SkewCornerDescent.Matrix.SelectedCoordinate
