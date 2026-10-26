/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CommonCoreBorders
import SkewCornerDescent.Matrix.CommonCoreDifference

/-!
# Exact transposed duality of compatible bordered frames

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
The same complete row and column permutation exchanges the opposite borders.
The determinant is therefore unchanged, with no cardinality-dependent sign.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Exchange both complete borders and the two distinguished frame units. -/
def commonCoreDualEquiv (α β γ : Type*) :
    ((γ ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ α)) ≃ ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) where
  toFun
    | .inl (.inl g) => .inr (.inr g)
    | .inl (.inr u) => .inr (.inl (.inl u))
    | .inr (.inl (.inl u)) => .inl (.inr u)
    | .inr (.inl (.inr b)) => .inr (.inl (.inr b))
    | .inr (.inr a) => .inl (.inl a)
  invFun
    | .inl (.inl a) => .inr (.inr a)
    | .inl (.inr u) => .inr (.inl (.inl u))
    | .inr (.inl (.inl u)) => .inl (.inr u)
    | .inr (.inl (.inr b)) => .inr (.inl (.inr b))
    | .inr (.inr g) => .inl (.inl g)
  left_inv := by rintro ((g | u) | ((v | b) | a)) <;> rfl
  right_inv := by rintro ((a | u) | ((v | b) | g)) <;> rfl

/-- The complete dual compatible frame is an actual simultaneous row/column
reindexing of the transposed original frame. -/
theorem borderedCoreMatrix_dual {α β γ F : Type*} [Zero F]
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    borderedCoreMatrix (B.transpose.submatrix Sum.swap id)
      (S.transpose.submatrix Sum.swap id) (T.transpose.submatrix Sum.swap Sum.swap)
      C.transpose (R.transpose.submatrix id Sum.swap) (A.transpose.submatrix id Sum.swap) =
      (borderedCoreMatrix A R T C S B).transpose.submatrix
        (commonCoreDualEquiv α β γ) (commonCoreDualEquiv α β γ) := by
  ext i j
  rcases i with ((g | u) | ((v | b) | a)) <;>
    rcases j with ((g' | u') | ((v' | b') | a')) <;> rfl

/-- Both border determinants have the same exact value under complete duality. -/
theorem borderedCoreMatrix_dual_det {α β γ F : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    (borderedCoreMatrix (B.transpose.submatrix Sum.swap id)
      (S.transpose.submatrix Sum.swap id) (T.transpose.submatrix Sum.swap Sum.swap)
      C.transpose (R.transpose.submatrix id Sum.swap) (A.transpose.submatrix id Sum.swap)).det =
        (borderedCoreMatrix A R T C S B).det := by
  rw [borderedCoreMatrix_dual, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

/-- The complete compatible cross difference is unchanged by exchanging
the opposite borders and transposing the full common core. -/
theorem commonCoreDifference_dual {α β γ F : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F) :
    commonCoreDifference (B.transpose.submatrix Sum.swap id)
      (S.transpose.submatrix Sum.swap id) (T.transpose.submatrix Sum.swap Sum.swap)
      C.transpose (R.transpose.submatrix id Sum.swap) (A.transpose.submatrix id Sum.swap)
      s r (q ∘ Sum.swap) (t ∘ Sum.swap) z =
        commonCoreDifference A R T C S B r s t q z := by
  have h11 := borderedCoreMatrix_dual_det A R T C S B
  have h00 := borderedCoreMatrix_dual_det (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
    (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z)
    C (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)
  have h10 := borderedCoreMatrix_dual_det A R (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i)
    C (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) F)
  have h01 := borderedCoreMatrix_dual_det (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) F)
    (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => q j) C S B
  unfold commonCoreDifference
  rw [h11]
  simp only [Matrix.transpose_zero, Matrix.submatrix_zero] at h00 h10 h01
  simp only [Matrix.submatrix, Matrix.transpose, Matrix.of_apply, Function.comp_def]
    at h00 h10 h01 ⊢
  simp only [Pi.zero_apply, Function.id_def] at h00 h10 h01 ⊢
  rw [h00, h01, h10]
  ring

end SkewCornerDescent.Matrix
