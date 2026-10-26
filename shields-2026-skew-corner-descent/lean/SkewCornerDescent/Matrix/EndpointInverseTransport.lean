/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProjectionTransport

/-!
# Complete inverse coefficient transport under paired beta copying

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
A finite paired endpoint equivalence and common beta translation preserve
every full incoming and outgoing inverse coefficient. The inverse-entry
identity is produced from the actual beta-matrix identity; it is not a
compatibility premise. Genuine invertibility is supplied by the original
interval producers at the reconstruction applications. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing

/-- Full paired beta copying transports every incoming inverse coefficient;
the inverse-entry equality is produced by the original matrix identity. -/
theorem vertex_outgoing_inverse_affine_copy {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (ι : Lambda →+* F) (e : ν ≃ μ) (row col : ν → ℤ) (row' col' : μ → ℤ)
    (x shift : ℤ) (hr : ∀ i, row' (e i) = row i + shift)
    (hc : ∀ i, col' (e i) = col i + shift) (k : ν) :
    (vertexOutgoing ι col' (x + shift) * (vertexBetaMatrix ι row' col')⁻¹) () (e k) =
      (vertexOutgoing ι col x * (vertexBetaMatrix ι row col)⁻¹) () k := by
  have hM := vertexBetaMatrix_affine_reindex ι e row col row' col' shift hr hc
  have hI : ((vertexBetaMatrix ι row' col')⁻¹).submatrix e e =
      (vertexBetaMatrix ι row col)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv, hM]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_equiv e
  intro i
  have hik : (vertexBetaMatrix ι row' col')⁻¹ (e i) (e k) =
      (vertexBetaMatrix ι row col)⁻¹ i k := congrArg (fun M => M i k) hI
  change ι (hh (x - col i)) * (vertexBetaMatrix ι row col)⁻¹ i k =
    ι (hh (x + shift - col' (e i))) * (vertexBetaMatrix ι row' col')⁻¹ (e i) (e k)
  rw [hc, hik, add_sub_add_right_eq_sub]

/-- The symmetric complete outgoing coefficient is preserved by the same
original paired beta copy and common endpoint translation. -/
theorem vertex_incoming_inverse_affine_copy {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (ι : Lambda →+* F) (e : ν ≃ μ) (row col : ν → ℤ) (row' col' : μ → ℤ)
    (y shift : ℤ) (hr : ∀ i, row' (e i) = row i + shift)
    (hc : ∀ i, col' (e i) = col i + shift) (k : ν) :
    ((vertexBetaMatrix ι row' col')⁻¹ * vertexIncoming ι row' (y + shift)) (e k) () =
      ((vertexBetaMatrix ι row col)⁻¹ * vertexIncoming ι row y) k () := by
  have hM := vertexBetaMatrix_affine_reindex ι e row col row' col' shift hr hc
  have hI : ((vertexBetaMatrix ι row' col')⁻¹).submatrix e e =
      (vertexBetaMatrix ι row col)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv, hM]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_equiv e
  intro i
  have hki : (vertexBetaMatrix ι row' col')⁻¹ (e k) (e i) =
      (vertexBetaMatrix ι row col)⁻¹ k i := congrArg (fun M => M k i) hI
  change (vertexBetaMatrix ι row col)⁻¹ k i * ι (hh (row i - y)) =
    (vertexBetaMatrix ι row' col')⁻¹ (e k) (e i) * ι (hh (row' (e i) - (y + shift)))
  rw [hr, hki, add_sub_add_right_eq_sub]

end SkewCornerDescent.Matrix
