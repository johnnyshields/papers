/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalBlockSubsetInverse
import SkewCornerDescent.Matrix.PrivateUnitProjection

/-!
# The full actual private-cut unit correction

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The actual private unit is unique and occupies a complete singleton block.
Removing it supplies a genuine old inverse and strict no-feedback geometry;
full affine inverse transport then applies the exact insertion formula.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete weighted inverse contraction of the actual retained interval. -/
noncomputable def originalIntervalInverseProjection {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) : OtherField c.top :=
  letI := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
  profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z

/-- The literal whole interval is all nonunit positions plus its one actual unit. -/
noncomputable def originalIntervalPrivateUnitEquiv {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℤ)
    (u : OriginalResponseInterval (hD := hD) P b d)
    (hunit : originalResponseRows P u.1.1 = k ∧ originalResponseCols P u.1.1 = k) :
    ({i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} ⊕ Unit) ≃
      OriginalResponseInterval (hD := hD) P b d := by
  classical
  let p := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k
  let t : {i : OriginalResponseInterval (hD := hD) P b d // p i} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨u, hunit⟩
      left_inv := by
        intro i
        apply Subtype.ext
        have he := originalRemaining_private_unit_unique P k i.val.1.1 u.1.1 i.property hunit
        exact (Subtype.ext (Subtype.ext he)).symm
      right_inv := by intro v; cases v; rfl }
  exact ((Equiv.sumCongr (Equiv.refl _) t.symm).trans (Equiv.sumComm _ _)).trans
    (Equiv.sumCompl p)

/-- Removing the actual private unit changes the full inverse projection by
exactly its self-contraction. All geometry and both inverses are produced from
the original source; no matrix-compatibility or no-feedback premise is carried. -/
theorem originalInterval_private_unit_projection {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (u : OriginalResponseInterval (hD := hD) P b d)
    (hunit : originalResponseRows P u.1.1 = k ∧ originalResponseCols P u.1.1 = k)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0) :
    letI := c.originalIntervalWithoutPrivateUnitInverse P b d k hcur hprev u hunit
    let row := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseRows P i.val.1.1
    let col := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseCols P i.val.1.1
    c.originalIntervalInverseProjection P b d A T z =
      profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z +
        A.coeff (z - k) * T.coeff (k - z) := by
  classical
  let row := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseRows P i.val.1.1
  let col := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseCols P i.val.1.1
  let := c.originalIntervalWithoutPrivateUnitInverse P b d k hcur hprev u hunit
  let := c.originalResponseResidueIntervalInverse P b d
  have hsep (i) : (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i) :=
    originalRemaining_private_cut_without_unit P k hcur hprev ⟨i.val.1.1, i.property⟩
  let e := originalIntervalPrivateUnitEquiv (hD := hD) P b d k u hunit
  let row' := Sum.elim row (fun _ : Unit => k)
  let col' := Sum.elim col (fun _ : Unit => k)
  have hr (i) : originalResponseRows P (e i).1.1 = row' i := by
    rcases i with i | v
    · rfl
    · cases v
      exact hunit.1
  have hc (i) : originalResponseCols P (e i).1.1 = col' i := by
    rcases i with i | v
    · rfl
    · cases v
      exact hunit.2
  let M := vertexBetaMatrix c.residueMap row col
  let U := vertexIncoming c.residueMap row k
  let V := vertexOutgoing c.residueMap col k
  let := unitVertexInverse M U V (geometric_unit_vertex_feedback_zero c.residueMap row col k hsep)
  have hnew : Invertible (vertexBetaMatrix c.residueMap row' col') := by
    change Invertible (vertexBetaMatrix c.residueMap
      (Sum.elim row (fun _ : Unit => k)) (Sum.elim col (fun _ : Unit => k)))
    rw [vertexBetaMatrix_insert]
    exact unitVertexInverse M U V (geometric_unit_vertex_feedback_zero c.residueMap row col k hsep)
  let := hnew
  have hcopy := profileInverseProjection_affine_beta_copy c.residueMap e row' col'
    (fun i => originalResponseRows P i.1.1) (fun i => originalResponseCols P i.1.1)
    A T z 0 (fun i => by simpa only [add_zero] using hr i)
    (fun i => by simpa only [add_zero] using hc i)
  simp only [add_zero] at hcopy
  have hInv : ⅟(vertexBetaMatrix c.residueMap row' col') =
      ⅟(Matrix.fromBlocks M U V 1) := by
    simp only [Matrix.invOf_eq_nonsing_inv, row', col', vertexBetaMatrix_insert, M, U, V]
  dsimp only [originalIntervalInverseProjection]
  rw [← hcopy, hInv]
  exact geometric_unit_vertex_projection_insert c.residueMap row col k hsep A T z hA hT

end SkewCornerDescent.Matrix.SelectedCoordinate
