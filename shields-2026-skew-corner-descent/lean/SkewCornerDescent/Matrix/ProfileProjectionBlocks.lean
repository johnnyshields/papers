/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProfileInverseProjection
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Full profile inverse projections retain only same-component entries

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Cross-component entries vanish either by the actual inverse's triangular
support or because their row lies strictly below the earlier column, forcing
one of the two profile offsets negative. Complete within-component inverses
remain unrestricted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν F : Type*} [Fintype ν] [CommRing F]

/-- Ordinary endpoint support supplies zero at every negative integer offset. -/
theorem endpointProfile_coeff_negative (distance : ν → ℤ) (v : ν → F)
    (hd : ∀ i, 0 ≤ distance i) (z : ℤ) (hz : z < 0) :
    (endpointProfile distance v).coeff z = 0 := by
  rw [endpointProfile_coeff, ite_eq_right (Ne.symm (ne_of_lt hz))]
  have hs : (∑ i, if distance i = z then v i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (ne_of_gt (hz.trans_le (hd i)))
  rw [hs, sub_self]

/-- The complete projected inverse reduces to same-component entries.
No diagonal approximation is made within a component. -/
theorem profile_inverse_projection_same_blocks {α : Type*} [LinearOrder α]
    (row col : ν → ℤ) (I : Matrix ν ν F) (label : ν → α)
    (hI : I.BlockTriangular label)
    (hseparation : ∀ i j, label i < label j → row j < col i)
    (A B : LaurentPolynomial F)
    (hA : ∀ k, k < 0 → A.coeff k = 0) (hB : ∀ k, k < 0 → B.coeff k = 0) (z : ℤ) :
    profileInverseProjection row col I A B z =
      ∑ i, ∑ j, if label i = label j then
        A.coeff (z - col i) * I i j * B.coeff (row j - z) else 0 := by
  classical
  unfold profileInverseProjection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : label i = label j
  · rw [ite_eq_left he]
  · rw [ite_eq_right he]
    rcases lt_or_gt_of_ne he with hij | hji
    · have hs := hseparation i j hij
      by_cases ha : z - col i < 0
      · rw [hA _ ha, zero_mul, zero_mul]
      · have hb : row j - z < 0 := by omega
        rw [hB _ hb, mul_zero]
    · rw [hI hji, mul_zero, zero_mul]

end SkewCornerDescent.Matrix
