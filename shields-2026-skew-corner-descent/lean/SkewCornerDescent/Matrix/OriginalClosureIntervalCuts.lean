/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureRemaining
import SkewCornerDescent.Matrix.OriginalEndpointProfiles

/-!
# Exact original response interval cuts in both closure copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The actual strict
block cuts retain precisely the copied source interval, including both selected boundary
proper minors. Every position from the other complete copy is excluded. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The geometric selected occurrence has its produced original block label. -/
theorem originalHorizontalClosure_selected_label {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    interiorBlock Q (originalHorizontalClosureSelectedCopy P Q v hQ upper b).val.val =
      if upper then interiorBlock P b.val.val
      else (interiorCuts P).card + 1 + interiorBlock P b.val.val := by
  rw [originalHorizontalClosureSelectedCopy_block]
  exact originalHorizontalClosure_complementary_copy_label P Q v hQ upper b.val.val

/-- Every actual remaining source index has the same produced copy offset as its entire block. -/
theorem originalHorizontalClosure_remaining_label {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (j : OriginalRemainingIndices (hD := hD) P) :
    interiorBlock Q (originalClosureRemainingCopy P Q v hQ upper j).1.val =
      if upper then interiorBlock P j.1.val
      else (interiorCuts P).card + 1 + interiorBlock P j.1.val :=
  originalHorizontalClosure_complementary_copy_label P Q v hQ upper j.1.val

/-- The full original interval condition is preserved at every copied remaining position. -/
theorem originalHorizontalClosure_interval_same_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b d : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P) :
    (originalResponseLowerCut Q (some (originalHorizontalClosureSelectedCopy P Q v hQ upper b)) <
        (interiorBlock Q (originalClosureRemainingCopy P Q v hQ upper j).1.val : ℤ) ∧
      (interiorBlock Q (originalClosureRemainingCopy P Q v hQ upper j).1.val : ℤ) <
        originalResponseUpperCut Q
          (some (originalHorizontalClosureSelectedCopy P Q v hQ upper d))) ↔
      (originalResponseLowerCut P (some b) < (interiorBlock P j.1.val : ℤ) ∧
        (interiorBlock P j.1.val : ℤ) < originalResponseUpperCut P (some d)) := by
  dsimp only [originalResponseLowerCut, originalResponseUpperCut]
  rw [originalHorizontalClosure_selected_label P Q v hQ upper b,
    originalHorizontalClosure_selected_label P Q v hQ upper d,
    originalHorizontalClosure_remaining_label P Q v hQ upper j]
  cases upper
  · simp only [Bool.false_eq_true, ite_false, Nat.cast_add, Nat.cast_one]
    omega
  · simp only [ite_true]

/-- No position from the other complete copy can lie between these actual selected cuts. -/
theorem originalHorizontalClosure_interval_other_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b d : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P) :
    ¬(originalResponseLowerCut Q (some (originalHorizontalClosureSelectedCopy P Q v hQ upper b)) <
        (interiorBlock Q (originalClosureRemainingCopy P Q v hQ (!upper) j).1.val : ℤ) ∧
      (interiorBlock Q (originalClosureRemainingCopy P Q v hQ (!upper) j).1.val : ℤ) <
        originalResponseUpperCut Q
          (some (originalHorizontalClosureSelectedCopy P Q v hQ upper d))) := by
  dsimp only [originalResponseLowerCut, originalResponseUpperCut]
  rw [originalHorizontalClosure_selected_label P Q v hQ upper b,
    originalHorizontalClosure_selected_label P Q v hQ upper d,
    originalHorizontalClosure_remaining_label P Q v hQ (!upper) j]
  have hj : interiorBlock P j.1.val ≤ (interiorCuts P).card := Finset.card_filter_le _ _
  have hd : interiorBlock P d.val.val ≤ (interiorCuts P).card := Finset.card_filter_le _ _
  cases upper <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true, Nat.cast_add, Nat.cast_one] <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
