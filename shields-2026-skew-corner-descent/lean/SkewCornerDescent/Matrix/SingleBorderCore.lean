/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BorderCondensation
import SkewCornerDescent.Matrix.CommonCoreFiniteFrame

/-!
# Integral single-border condensation on arbitrary finite cores

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
The core and all four unmatched rows and columns remain arbitrary. The identity
holds over every commutative ring, without a nonsingularity assumption. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {n F : Type*} [Fintype n] [DecidableEq n] [CommRing F]

/-- A complete single border on the boundary-first sum frame. -/
def singleCoreBorderSum (C : Matrix n n F) (r s : n → F) (z : F) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) F :=
  fun i j => match i, j with
    | .inl _, .inl _ => z
    | .inl _, .inr j => r j
    | .inr i, .inl _ => s i
    | .inr i, .inr j => C i j

/-- Simultaneous finite indexing changes no single-border determinant. -/
theorem singleCoreBorderSum_det (C : Matrix n n F) (r s : n → F) (z : F) :
    (singleCoreBorderSum C r s z).det =
      (singleCoreBorder (C.submatrix (Fintype.equivFin n).symm (Fintype.equivFin n).symm)
        (r ∘ (Fintype.equivFin n).symm) (s ∘ (Fintype.equivFin n).symm) z).det := by
  let e := (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin n)).trans
    (commonCoreFinEquiv (Fintype.card n))
  have hm : (singleCoreBorder (C.submatrix (Fintype.equivFin n).symm
      (Fintype.equivFin n).symm) (r ∘ (Fintype.equivFin n).symm)
      (s ∘ (Fintype.equivFin n).symm) z).submatrix e e =
      singleCoreBorderSum C r s z := by
    ext i j
    rcases i with u | i <;> rcases j with v | j <;>
      simp [e, commonCoreFinEquiv, singleCoreBorder, singleCoreBorderSum,
        Matrix.submatrix]
  rw [← hm, Matrix.det_submatrix_equiv_self]

/-- The entire common determinant, with every specialization multiplicity,
divides the complete single-border cross difference. -/
theorem singleCoreBorderSum_cross_difference_dvd
    (C : Matrix n n F) (r₁ r₂ s₁ s₂ : n → F) (z₁₁ z₁₂ z₂₁ z₂₂ : F) :
    C.det ∣ (singleCoreBorderSum C r₁ s₁ z₁₁).det *
        (singleCoreBorderSum C r₂ s₂ z₂₂).det -
      (singleCoreBorderSum C r₁ s₂ z₁₂).det *
        (singleCoreBorderSum C r₂ s₁ z₂₁).det := by
  simp only [singleCoreBorderSum_det]
  have hd := singleCoreBorder_cross_difference_dvd
    (C.submatrix (Fintype.equivFin n).symm (Fintype.equivFin n).symm)
    (r₁ ∘ (Fintype.equivFin n).symm) (r₂ ∘ (Fintype.equivFin n).symm)
    (s₁ ∘ (Fintype.equivFin n).symm) (s₂ ∘ (Fintype.equivFin n).symm)
    z₁₁ z₁₂ z₂₁ z₂₂
  simpa only [Matrix.det_submatrix_equiv_self] using hd

end SkewCornerDescent.Matrix
