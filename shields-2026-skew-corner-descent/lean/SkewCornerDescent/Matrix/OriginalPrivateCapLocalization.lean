/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateUnitProjection
import SkewCornerDescent.Matrix.OriginalFilteredCapProjection
import SkewCornerDescent.Matrix.OriginalPrivateCapSides
import SkewCornerDescent.Matrix.SeparatedCapProjection

/-!
# Complete actual private interval localization to its clipped cap

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Private original geometry supplies strict endpoint separation. The actual
retained side has its own inverse and its literal whole-window presentation.
No nonrow inverse entry is dropped by a diagonal approximation. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A private interval without a cut unit localizes at or below the cut to its
complete clipped upper cap. The missing-unit condition defines this branch;
strict matrix geometry and both actual inverse producers are derived. -/
theorem originalInterval_private_lower_cap_without_unit {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hb : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (hno : ∀ i : OriginalResponseInterval (hD := hD) P (some b) (some d),
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k))
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : z ≤ k)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalFilteredCapInverseProjection P 0 k true d A T z := by
  classical
  let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseCols P i.1.1
  let := c.originalResponseResidueIntervalInverse P (some b) (some d)
  have hsep (i) : (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i) := by
    rcases originalInterval_private_cut_trichotomy P (some b) (some d) k hk hp i with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hno i h)
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // row i < k} =>
        row i.val)
      (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // row i < k} =>
        col i.val)) := by
    change Invertible ((vertexBetaMatrix c.residueMap row col).toBlock
      (fun i => row i < k) (fun i => row i < k))
    exact separatedBelowInverse c.residueMap row col k hsep
  let := c.originalFilteredCapInverse P 0 k true d
  let e := originalLowerPrivateCapEquiv (hD := hD) P b d k hk hp hb
  have hloc := profileInverseProjection_le_retained c.residueMap row col k hsep A T hA hT z hz
  have hcopy := profileInverseProjection_affine_beta_copy c.residueMap e
    (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // row i < k} =>
      row i.val)
    (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // row i < k} =>
      col i.val)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P 0 k //
      originalCapBlockSide true d i.1.val} => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P 0 k //
      originalCapBlockSide true d i.1.val} => originalResponseCols P ⟨i.val.1.val, i.val.2⟩)
    A T z 0 (fun i => by simp only [add_zero]; rfl) (fun i => by simp only [add_zero]; rfl)
  simp only [Matrix.invOf_eq_nonsing_inv, add_zero] at hloc hcopy
  dsimp only [originalIntervalInverseProjection, originalFilteredCapInverseProjection]
  simp only [Matrix.invOf_eq_nonsing_inv]
  exact hloc.trans hcopy

/-- The corresponding upper-side localization uses its complete clipped lower
cap, again with the inverse of the actual retained matrix. -/
theorem originalInterval_private_upper_cap_without_unit {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k)
    (hno : ∀ i : OriginalResponseInterval (hD := hD) P (some b) (some d),
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k))
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : k ≤ z)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalFilteredCapInverseProjection P k (P.xi 0) false b A T z := by
  classical
  let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseCols P i.1.1
  let := c.originalResponseResidueIntervalInverse P (some b) (some d)
  have hsep (i) : (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i) := by
    rcases originalInterval_private_cut_trichotomy P (some b) (some d) k hk hp i with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hno i h)
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // k < col i} =>
        row i.val)
      (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // k < col i} =>
        col i.val)) := by
    change Invertible ((vertexBetaMatrix c.residueMap row col).toBlock
      (fun i => k < col i) (fun i => k < col i))
    exact separatedAboveInverse c.residueMap row col k hsep
  let := c.originalFilteredCapInverse P k (P.xi 0) false b
  let e := originalUpperPrivateCapEquiv (hD := hD) P b d k hk hp hd
  have hloc := profileInverseProjection_ge_retained c.residueMap row col k hsep A T hA hT z hz
  have hcopy := profileInverseProjection_affine_beta_copy c.residueMap e
    (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // k < col i} =>
      row i.val)
    (fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) // k < col i} =>
      col i.val)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P k (P.xi 0) //
      originalCapBlockSide false b i.1.val} => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P k (P.xi 0) //
      originalCapBlockSide false b i.1.val} => originalResponseCols P ⟨i.val.1.val, i.val.2⟩)
    A T z 0 (fun i => by simp only [add_zero]; rfl) (fun i => by simp only [add_zero]; rfl)
  simp only [Matrix.invOf_eq_nonsing_inv, add_zero] at hloc hcopy
  dsimp only [originalIntervalInverseProjection, originalFilteredCapInverseProjection]
  simp only [Matrix.invOf_eq_nonsing_inv]
  exact hloc.trans hcopy

end SkewCornerDescent.Matrix.SelectedCoordinate
