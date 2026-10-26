/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowExteriorContainment
import SkewCornerDescent.Matrix.OriginalWindowResponseIntervals
import SkewCornerDescent.Matrix.OriginalClosureCapCuts

/-!
# Full exterior response intervals inside complete end windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The actual
integer cap cuts retain precisely the whole blocks on the exterior side of their
selected endpoint. The complete interval includes that endpoint's proper minor.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Whole blocks on the true exterior side of a selected endpoint. -/
def originalCapBlockSide {n : ℕ} {P : Profile n} (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) (a : OriginalBlocks P) : Prop :=
  if upper then a ≤ b.val else b.val ≤ a

/-- The original integer cap cuts have exactly their one-sided whole-block meaning. -/
theorem originalCapInterval_block_bounds {n : ℕ} (P : Profile n) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) (a : OriginalBlocks P) :
    originalResponseLowerCut P (originalClosureCapLeft upper b) <
        (interiorBlock P a.val : ℤ) ∧
      (interiorBlock P a.val : ℤ) <
        originalResponseUpperCut P (originalClosureCapRight upper b) ↔
      originalCapBlockSide upper b a := by
  have hbound := interiorBlock_le_size P a.val
  cases upper
  · have hlabel := (originalBlocks_label_strictMono P).le_iff_le (a := b.val) (b := a)
    change (-1 + (interiorBlock P b.val.val : ℤ) < (interiorBlock P a.val : ℤ) ∧
      (interiorBlock P a.val : ℤ) < (n : ℤ) + 1) ↔ b.val ≤ a
    rw [← hlabel]
    omega
  · have hlabel := (originalBlocks_label_strictMono P).le_iff_le (a := a) (b := b.val)
    change (-1 < (interiorBlock P a.val : ℤ) ∧
      (interiorBlock P a.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1) ↔ a ≤ b.val
    rw [← hlabel]
    omega

/-- All complete remaining positions of a true cap, presented inside an intact end window. -/
noncomputable def originalWindowCapIntervalEquiv {n : ℕ} (P : Profile n)
    (lo hi : ℤ) (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P)
    (hcontained : ∀ a, originalCapBlockSide upper b a → originalBlockInWindow P lo hi a) :
    OriginalResponseInterval (hD := hD) P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) ≃
      {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
        originalCapBlockSide upper b i.1.val} where
  toFun i := by
    have hs := (originalCapInterval_block_bounds P upper b i.1.1.1).mp ⟨i.2, i.1.2⟩
    exact ⟨⟨⟨i.1.1.1, hcontained _ hs⟩, i.1.1.2⟩, hs⟩
  invFun i := by
    have hs := (originalCapInterval_block_bounds P upper b i.val.1.val).mpr i.property
    exact ⟨⟨⟨i.val.1.val, i.val.2⟩, hs.2⟩, hs.1⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
