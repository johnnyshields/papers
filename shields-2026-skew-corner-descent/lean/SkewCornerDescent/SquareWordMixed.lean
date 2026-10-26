/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordResidue
import SkewCornerDescent.Matrix.DeterminantMixedDerivation

/-!
# Full mixed original Jacobi--Trudi derivatives for the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The actual two-generator derivative is transported through the complete
original determinant, without freezing an inverse or replacing a unit. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial
open scoped BigOperators

/-- A complete integer-index matrix supplies every mixed derivative path. -/
theorem hom_mixed_hh_det {ν R : Type*} [Fintype ν] [DecidableEq ν] [CommRing R]
    (f : Lambda →+* R) (index : Matrix ν ν ℤ) (p q : ℕ+) :
    f (pderiv p (pderiv q (Matrix.of fun i j => hh (index i j)).det)) =
      ∑ j, ∑ i, if i = j then 0 else
        (((Matrix.of fun r s => f (hh (index r s))).updateCol j
          (fun r => if index r j = (q : ℤ) then 1 else 0)).updateCol i
          (fun r => if index r i = (p : ℤ) then 1 else 0)).det := by
  rw [SkewCornerDescent.Matrix.derivation_det_mixed_columns]
  · simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i = j
    · simp only [hij, ite_true, map_zero]
    · rw [ite_eq_right hij, ite_eq_right hij, RingHom.map_det]
      congr 1
      ext r s
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply,
        Matrix.of_apply]
      split_ifs <;> simp_all [pderiv_hh]
  · intro i j
    simp only [Matrix.of_apply, pderiv_hh]
    split_ifs <;> simp

end SkewCornerDescent.SquareWordProfiles
