/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateCapLocalization

/-!
# Actual private-cap localization with the literal unit correction

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The actual unit is removed with a produced complete old inverse. Strict
private-cut geometry localizes its projection to the retained cap, whose
whole-window presentation preserves every original remaining occurrence.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full actual private interval at or below the cut equals its complete
clipped upper-cap contraction plus the literal unit's self-contraction. -/
theorem originalInterval_private_lower_cap_with_unit {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hb : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (u : OriginalResponseInterval (hD := hD) P (some b) (some d))
    (hunit : originalResponseRows P u.1.1 = k ∧ originalResponseCols P u.1.1 = k)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : z ≤ k)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalFilteredCapInverseProjection P 0 k true d A T z +
        A.coeff (z - k) * T.coeff (k - z) := by
  classical
  let row := fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseRows P i.val.1.1
  let col := fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseCols P i.val.1.1
  let := c.originalIntervalWithoutPrivateUnitInverse P (some b) (some d) k hk hp u hunit
  have hsep (i) : (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i) :=
    originalRemaining_private_cut_without_unit P k hk hp ⟨i.val.1.1, i.property⟩
  have hbelow (i : OriginalResponseInterval (hD := hD) P (some b) (some d))
      (hi : originalResponseRows P i.1.1 < k) :
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k) := by
    intro h
    rw [h.1] at hi
    exact lt_irrefl _ hi
  let f := Equiv.subtypeSubtypeEquivSubtype
    (p := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k))
    (q := fun i => originalResponseRows P i.1.1 < k) (fun {i} hi => hbelow i hi)
  let e := f.trans (originalLowerPrivateCapEquiv (hD := hD) P b d k hk hp hb)
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : {i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} // row i < k} =>
          row i.val)
      (fun i : {i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} // row i < k} =>
          col i.val)) := by
    change Invertible ((vertexBetaMatrix c.residueMap row col).toBlock
      (fun i => row i < k) (fun i => row i < k))
    exact separatedBelowInverse c.residueMap row col k hsep
  let := c.originalFilteredCapInverse P 0 k true d
  have hloc := profileInverseProjection_le_retained c.residueMap row col k hsep A T hA hT z hz
  have hcopy := profileInverseProjection_affine_beta_copy c.residueMap e
    (fun i => row i.val) (fun i => col i.val)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P 0 k //
      originalCapBlockSide true d i.1.val} => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P 0 k //
      originalCapBlockSide true d i.1.val} => originalResponseCols P ⟨i.val.1.val, i.val.2⟩)
    A T z 0 (fun i => by simp only [add_zero]; rfl) (fun i => by simp only [add_zero]; rfl)
  simp only [Matrix.invOf_eq_nonsing_inv, add_zero] at hcopy hloc
  have hcap : profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z =
      c.originalFilteredCapInverseProjection P 0 k true d A T z := by
    dsimp only [originalFilteredCapInverseProjection]
    simp only [Matrix.invOf_eq_nonsing_inv]
    exact hloc.trans hcopy
  have hfull := c.originalInterval_private_unit_projection P (some b) (some d) k hk hp
    u hunit A T z hA hT
  dsimp only at hfull
  change c.originalIntervalInverseProjection P (some b) (some d) A T z =
    profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z +
      A.coeff (z - k) * T.coeff (k - z) at hfull
  rwa [hcap] at hfull

/-- The complete upper-side contraction has the same exact actual unit
correction, including coincident candidate positions at the private cut. -/
theorem originalInterval_private_upper_cap_with_unit {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k)
    (u : OriginalResponseInterval (hD := hD) P (some b) (some d))
    (hunit : originalResponseRows P u.1.1 = k ∧ originalResponseCols P u.1.1 = k)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : k ≤ z)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalFilteredCapInverseProjection P k (P.xi 0) false b A T z +
        A.coeff (z - k) * T.coeff (k - z) := by
  classical
  let row := fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseRows P i.val.1.1
  let col := fun i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseCols P i.val.1.1
  let := c.originalIntervalWithoutPrivateUnitInverse P (some b) (some d) k hk hp u hunit
  have hsep (i) : (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i) :=
    originalRemaining_private_cut_without_unit P k hk hp ⟨i.val.1.1, i.property⟩
  have habove (i : OriginalResponseInterval (hD := hD) P (some b) (some d))
      (hi : k < originalResponseCols P i.1.1) :
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k) := by
    intro h
    rw [h.2] at hi
    exact lt_irrefl _ hi
  let f := Equiv.subtypeSubtypeEquivSubtype
    (p := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k))
    (q := fun i => k < originalResponseCols P i.1.1) (fun {i} hi => habove i hi)
  let e := f.trans (originalUpperPrivateCapEquiv (hD := hD) P b d k hk hp hd)
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : {i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} // k < col i} =>
          row i.val)
      (fun i : {i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} // k < col i} =>
          col i.val)) := by
    change Invertible ((vertexBetaMatrix c.residueMap row col).toBlock
      (fun i => k < col i) (fun i => k < col i))
    exact separatedAboveInverse c.residueMap row col k hsep
  let := c.originalFilteredCapInverse P k (P.xi 0) false b
  have hloc := profileInverseProjection_ge_retained c.residueMap row col k hsep A T hA hT z hz
  have hcopy := profileInverseProjection_affine_beta_copy c.residueMap e
    (fun i => row i.val) (fun i => col i.val)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P k (P.xi 0) //
      originalCapBlockSide false b i.1.val} => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
    (fun i : {i : OriginalWholeWindowRemaining (hD := hD) P k (P.xi 0) //
      originalCapBlockSide false b i.1.val} => originalResponseCols P ⟨i.val.1.val, i.val.2⟩)
    A T z 0 (fun i => by simp only [add_zero]; rfl) (fun i => by simp only [add_zero]; rfl)
  simp only [Matrix.invOf_eq_nonsing_inv, add_zero] at hcopy hloc
  have hcap : profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z =
      c.originalFilteredCapInverseProjection P k (P.xi 0) false b A T z := by
    dsimp only [originalFilteredCapInverseProjection]
    simp only [Matrix.invOf_eq_nonsing_inv]
    exact hloc.trans hcopy
  have hfull := c.originalInterval_private_unit_projection P (some b) (some d) k hk hp
    u hunit A T z hA hT
  dsimp only at hfull
  change c.originalIntervalInverseProjection P (some b) (some d) A T z =
    profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z +
      A.coeff (z - k) * T.coeff (k - z) at hfull
  rwa [hcap] at hfull

end SkewCornerDescent.Matrix.SelectedCoordinate
