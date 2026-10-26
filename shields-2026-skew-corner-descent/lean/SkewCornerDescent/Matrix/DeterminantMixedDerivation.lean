/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.DeterminantDerivation

/-!
# Complete mixed derivative of an affine-entry determinant

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Two column replacements retain every mixed path; the same-column term vanishes
only when its full mixed entry derivative does. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Every mixed derivative term replaces two distinct full original columns. -/
theorem derivation_det_mixed_columns {ν R A : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R] [CommRing A] [Algebra R A]
    (D E : Derivation R A A) (M : Matrix ν ν A)
    (hentries : ∀ i j, D (E (M i j)) = 0) :
    D (E M.det) = ∑ j, ∑ i,
      if i = j then 0 else
        ((M.updateCol j (fun r => E (M r j))).updateCol i (fun r => D (M r i))).det := by
  rw [derivation_det_columns, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [derivation_det_columns]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    rw [ite_eq_left rfl]
    have hcol : (fun r => D ((M.updateCol j (fun r => E (M r j))) r j)) = 0 := by
      funext r
      simp only [Matrix.updateCol_apply, ite_true, hentries, Pi.zero_apply]
    rw [hcol]
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro r
    simp
  · rw [ite_eq_right hij]
    congr 2
    funext r
    rw [Matrix.updateCol_apply, ite_eq_right hij]

end SkewCornerDescent.Matrix
