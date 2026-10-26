/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Two-dimensional adjugate minors

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`). This boundary
case retains arbitrary repeated indices and singular matrices over a commutative
ring. General imbalanced borders and the opposite-end geometric assembly are not
asserted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {R : Type*} [CommRing R]

/-- Every two-dimensional minor of a two-dimensional adjugate is divisible by the
original determinant, including repeated indices and singular matrices. -/
theorem adjugate_fin_two_minor_dvd (A : Matrix (Fin 2) (Fin 2) R) (i₁ i₂ j₁ j₂ : Fin 2) :
    A.det ∣ A.adjugate i₁ j₁ * A.adjugate i₂ j₂ - A.adjugate i₁ j₂ * A.adjugate i₂ j₁ := by
  rw [Matrix.det_fin_two, Matrix.adjugate_fin_two]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    first
    | (refine ⟨1, ?_⟩; ring; done)
    | (refine ⟨-1, ?_⟩; ring; done)
    | (refine ⟨0, ?_⟩; ring)

end SkewCornerDescent.Matrix
