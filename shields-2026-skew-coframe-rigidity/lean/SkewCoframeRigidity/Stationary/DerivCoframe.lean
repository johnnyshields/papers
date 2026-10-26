/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.Deriv
import SkewCoframeRigidity.Stationary.ComponentColumn

/-!
# The derivative of the complete coframe in the top proper letter

Formalizes the first clause of `shields-2026-skew-coframe-rigidity.tex`, `sc:top-matching` and
`sc:positive-power`.  With `m = span D - 1`, the proper matrix of `D` involves no letter of index
`m`, and the right-hand side `t` involves `H_m` exactly in the row whose position is `m`.
Hence the derivative of the native coefficients is `-T⁻¹ e` for that row, and zero if no row
sits at `m`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem dRaw_properMatrix (D : BetaDiagram (n + 1)) (i j : Fin n) :
    dRaw (span D - 1) (properMatrixOf cohLetters D i j) = 0 := by
  simp only [properMatrixOf, Matrix.of_apply, letterOf]
  split_ifs with h
  · exact dRaw_zero _
  · rw [dRaw_letter, if_neg]
    rw [← rowPos_sub_colPos D i j] at *
    have := rowPos_lt_span D i
    have := colPos_pos D j
    omega

theorem dRaw_topVec (D : BetaDiagram (n + 1)) (i : Fin n) :
    dRaw (span D - 1) (topVecOf cohLetters D i) = if rowPos D i = span D - 1 then 1 else 0 := by
  simp only [topVecOf, letterOf]
  have h1 := rowPos_cast D i
  have h2 := rowPos_lt_span D i
  split_ifs with h h'
  · omega
  · omega
  · rw [dRaw_letter, if_pos]; omega
  · rw [dRaw_letter, if_neg]; omega

/-- The derivative of the native coefficients: `T * d g = - d t`. -/
theorem properMatrix_mulVec_dvec {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    properMatrixOf cohLetters D *ᵥ (fun j => dRaw (span D - 1) (coframeVecOf cohLetters D j)) =
      fun i => -(if rowPos D i = span D - 1 then (1 : CohField) else 0) := by
  have hnat := properMatrix_mulVec_coframeVec hD
  ext i
  have := congrArg (dRaw (span D - 1)) (congrFun hnat i)
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this ⊢
  rw [dRaw_neg, dRaw_sum, dRaw_topVec] at this
  simp only [dRaw_mul, dRaw_properMatrix, zero_mul, zero_add] at this
  linear_combination this

end SkewCoframeRigidity.Coframe
