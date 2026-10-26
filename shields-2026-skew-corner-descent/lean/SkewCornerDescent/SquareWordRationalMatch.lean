/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordRemainingResidues

/-!
# Actual rational residue match of the five-copy square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
All three complete original determinants supply the comparison. The equal-window
and closure placements are literal cell equalities in `SquareWordProfiles`.
No rational residue match is assumed. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial

/-- The genuine full horizontal closure quotient has the stated residue coordinate. -/
theorem square_word_actual_closure_coordinate {F : Type*} [Field F]
    (f : Lambda →+* F) (hf : f (X (1 : ℕ+)) = 0)
    (h2 : f (X 2) ≠ 0) (h4 : f (X 4) ≠ 0)
    (hdiff : f (X 4) - f (X 2) ^ 2 ≠ 0) :
    f closure.schur / f source.schur ^ 2 = f (X 4) / f (X 2) ^ 2 := by
  rw [closure_residue_determinant f hf, source_residue_determinant f hf]
  field_simp

/-- The original amalgamation comparison matches `(1-u)^4/u` on h-one zero.
Its source, union, and closure determinants are all computed inside the proof. -/
theorem square_word_original_residue_matching {F : Type*} [Field F]
    (f : Lambda →+* F) (hf : f (X (1 : ℕ+)) = 0)
    (h2 : f (X 2) ≠ 0) (h4 : f (X 4) ≠ 0)
    (hdiff : f (X 4) - f (X 2) ^ 2 ≠ 0) :
    f amalgamation.schur ^ 5 / f source.schur ^ 8 =
      (1 - f closure.schur / f source.schur ^ 2) ^ 4 /
        (f closure.schur / f source.schur ^ 2) := by
  rw [square_word_actual_closure_coordinate f hf h2 h4 hdiff,
    amalgamation_residue_determinant f hf, source_residue_determinant f hf]
  field_simp
  ring

/-- The source/window comparison independently yields the same rational function. -/
theorem square_word_window_residue_matching {F : Type*} [Field F]
    (f : Lambda →+* F) (hf : f (X (1 : ℕ+)) = 0)
    (h2 : f (X 2) ≠ 0) (h4 : f (X 4) ≠ 0) :
    f source.schur ^ 2 / f window.schur ^ 5 =
      (1 - f (X 4) / f (X 2) ^ 2) ^ 4 / (f (X 4) / f (X 2) ^ 2) := by
  rw [source_residue_determinant f hf, window_residue_determinant f hf]
  field_simp
  ring

end SkewCornerDescent.SquareWordProfiles
