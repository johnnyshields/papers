/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureResponseIntervals

/-!
# Complete original exterior-cap intervals of the literal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The upper left cap
and lower right cap retain exactly their complete source interval. Strict original cuts
exclude every position from the opposite copy. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The retained source row of a literal exterior cap. -/
def originalClosureCapLeft {n : ℕ} {P : Profile n} (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :=
  if upper then none else some b

/-- The retained source column of the same literal exterior cap. -/
def originalClosureCapRight {n : ℕ} {P : Profile n} (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :=
  if upper then some b else none

/-- Every same-copy remaining position satisfies exactly the source exterior-cap cuts. -/
theorem originalHorizontalClosure_cap_same_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P) :
    let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
    (originalResponseLowerCut Q (originalClosureCapLeft upper q) <
        (interiorBlock Q (originalClosureRemainingCopy P Q v hQ upper j).1.val : ℤ) ∧
      (interiorBlock Q (originalClosureRemainingCopy P Q v hQ upper j).1.val : ℤ) <
        originalResponseUpperCut Q (originalClosureCapRight upper q)) ↔
      (originalResponseLowerCut P (originalClosureCapLeft upper b) <
          (interiorBlock P j.1.val : ℤ) ∧
        (interiorBlock P j.1.val : ℤ) <
          originalResponseUpperCut P (originalClosureCapRight upper b)) := by
  have hp := interiorBlock_le_size P j.1.val
  have hq := interiorBlock_le_size Q (originalClosureRemainingCopy P Q v hQ upper j).1.val
  cases upper
  · simp only [originalClosureCapLeft, originalClosureCapRight,
      Bool.false_eq_true, ite_false, originalResponseLowerCut, originalResponseUpperCut]
    rw [originalHorizontalClosure_selected_label P Q v hQ false b,
      originalHorizontalClosure_remaining_label P Q v hQ false j]
    rw [originalHorizontalClosure_remaining_label P Q v hQ false j] at hq
    simp only [Bool.false_eq_true, ite_false, Nat.cast_add, Nat.cast_one] at *
    omega
  · simp only [originalClosureCapLeft, originalClosureCapRight,
      ite_true, originalResponseLowerCut, originalResponseUpperCut]
    rw [originalHorizontalClosure_selected_label P Q v hQ true b,
      originalHorizontalClosure_remaining_label P Q v hQ true j]
    simp only [ite_true]

/-- Every opposite-copy position is outside the actual exterior cap's strict original cuts. -/
theorem originalHorizontalClosure_cap_other_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P) :
    let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
    ¬(originalResponseLowerCut Q (originalClosureCapLeft upper q) <
        (interiorBlock Q (originalClosureRemainingCopy P Q v hQ (!upper) j).1.val : ℤ) ∧
      (interiorBlock Q (originalClosureRemainingCopy P Q v hQ (!upper) j).1.val : ℤ) <
        originalResponseUpperCut Q (originalClosureCapRight upper q)) := by
  have hj : interiorBlock P j.1.val ≤ (interiorCuts P).card := Finset.card_filter_le _ _
  have hb : interiorBlock P b.val.val ≤ (interiorCuts P).card := Finset.card_filter_le _ _
  cases upper <;>
    simp only [originalClosureCapLeft, originalClosureCapRight, Bool.false_eq_true,
      ite_false, ite_true, originalResponseLowerCut, originalResponseUpperCut] <;>
    rw [originalHorizontalClosure_selected_label,
      originalHorizontalClosure_remaining_label] <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true, Nat.cast_add, Nat.cast_one] <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
