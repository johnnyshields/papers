/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.CommonCoreBorders
import SkewCornerDescent.Matrix.SingularCoreColumn

/-!
# Singular common cores with arbitrary compatible borders

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`). A produced
invertible core change supplies a zero column. Both border imbalances then separate
square blocks, with every coupling retained until factorization. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {α β γ F : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

section Ring
variable [CommRing F]

/-- One zero core column gives the complete cross identity for arbitrary borders. -/
theorem commonCore_cross_difference_of_zero_column
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F)
    (hC : ∀ i, C i (.inl ()) = 0) :
    let M00 := borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j)
      (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z) C
        (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)
    let M10 := borderedCoreMatrix A R (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)
    let M01 := borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => q j) C S B
    let M11 := borderedCoreMatrix A R T C S B
    M11.det * M00.det - M10.det * M01.det = 0 := by
  have hr : (upperCoreBorder (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j)).det = r (.inl ()) := by
    rw [Matrix.det_eq_elem_of_card_eq_one (by simp) (.inr ())]
    rfl
  dsimp only
  rw [borderedCoreMatrix_det_of_zero_column A R T C S B hC,
    borderedCoreMatrix_det_of_zero_column (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j)
      (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F) hC,
    borderedCoreMatrix_det_of_zero_column A R (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F) hC,
    borderedCoreMatrix_det_of_zero_column (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => q j) C S B hC, hr]
  ring

end Ring

section Field
variable [Field F]

/-- A singular field-valued common core gives the complete cross identity for arbitrary
border sizes. The kernel column and its invertible lift are produced internally.

**Differs from the paper's route.** A kernel-column change replaces inversion of a
common proper minor. This field identity does not assert integral multiplicity divisibility. -/
theorem commonCore_cross_difference_of_singular
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F)
    (hC : C.det = 0) :
    let M00 := borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j)
      (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z) C
        (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)
    let M10 := borderedCoreMatrix A R (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)
    let M01 := borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => q j) C S B
    let M11 := borderedCoreMatrix A R T C S B
    M11.det * M00.det - M10.det * M01.det = 0 := by
  classical
  obtain ⟨P, hP, hzero⟩ := singularCore_zero_column_at C hC (.inl ())
  let r' := fun j => ∑ k, r k * P k j
  have hz := commonCore_cross_difference_of_zero_column A (R * P) T (C * P) S B
    r' s t q z hzero
  have h11 := borderedCoreMatrix_core_change_det A R T C S B P
  have h10 := borderedCoreMatrix_core_change_det A R
    (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F) P
  have h01 := borderedCoreMatrix_core_change_det (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
    (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => q j) C S B P
  have h00 := borderedCoreMatrix_core_change_det (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
    (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j)
    (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F) P
  have hrmul : (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) * P =
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r' j) := by
    ext i j
    rfl
  rw [hrmul] at h00 h01
  dsimp only at hz ⊢
  rw [h11, h00, h10, h01] at hz
  have hfactor (x y v w p : F) : x * p * (y * p) - v * p * (w * p) =
      (x * y - v * w) * p ^ 2 := by ring
  rw [hfactor] at hz
  exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 2 hP)

end Field

end SkewCornerDescent.Matrix
