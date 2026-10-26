/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.LeftBorderReduction

/-!
# The full compatible common-core cross difference

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
Names all four complete compatible matrices with the same extracted borders;
no singular-locus or selected-prime replacement is made. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {α β γ F : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]

/-- The complete cross difference of the four compatible bordered determinants. -/
noncomputable def commonCoreDifference
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F) : F :=
  (borderedCoreMatrix A R T C S B).det *
    (borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z)
      C (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)).det -
    (borderedCoreMatrix A R (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i)
      C (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)).det *
    (borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => q j) C S B).det

/-- Removing one left-border column gives the same complete smaller cross
difference in every cofactor term, with the full core unchanged. -/
theorem commonCoreDifference_left_option_expand
    (A : Matrix (Option α ⊕ Unit) (Option α) F)
    (R : Matrix (Option α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (Option α ⊕ Unit) (Unit ⊕ γ) F)
    (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (Option α ⊕ Unit) → F)
    (q : (Unit ⊕ γ) → F) (z : F) :
    commonCoreDifference A R T C S B r s t q z =
      A (.inl none) none *
        commonCoreDifference (A.submatrix (leftBorderKeep α) some)
          (R.submatrix (leftBorderKeep α) id) (T.submatrix (leftBorderKeep α) id)
          C S B r s (t ∘ leftBorderKeep α) q z -
      ∑ k : α ⊕ Unit, A (leftBorderKeep α k) none *
        commonCoreDifference (A.submatrix (leftBorderReplace α k) some)
          (R.submatrix (leftBorderReplace α k) id)
          (T.submatrix (leftBorderReplace α k) id) C S B r s
          (t ∘ leftBorderReplace α k) q z := by
  classical
  unfold commonCoreDifference
  rw [borderedCore_det_left_option_expand, borderedCore_det_left_option_expand]
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
  simp only [Matrix.submatrix, Matrix.of_apply, Function.comp_def]
  ring

/-- Full core divisibility of every smaller compatible left border supplies
the next integral border size, without reducing the core to a single prime. -/
theorem commonCoreDifference_left_option_dvd
    (A : Matrix (Option α ⊕ Unit) (Option α) F)
    (R : Matrix (Option α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (Option α ⊕ Unit) (Unit ⊕ γ) F)
    (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (Option α ⊕ Unit) → F)
    (q : (Unit ⊕ γ) → F) (z : F)
    (ih : ∀ (A' : Matrix (α ⊕ Unit) α F)
      (R' : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
      (T' : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (t' : (α ⊕ Unit) → F),
      C.det ∣ commonCoreDifference A' R' T' C S B r s t' q z) :
    C.det ∣ commonCoreDifference A R T C S B r s t q z := by
  rw [commonCoreDifference_left_option_expand]
  apply dvd_sub
  · exact dvd_mul_of_dvd_right (ih _ _ _ _) _
  · apply Finset.dvd_sum
    intro k _
    exact dvd_mul_of_dvd_right (ih _ _ _ _) _

end SkewCornerDescent.Matrix
