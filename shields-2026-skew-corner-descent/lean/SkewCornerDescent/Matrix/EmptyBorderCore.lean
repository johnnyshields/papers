/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SingleBorderCore
import SkewCornerDescent.Matrix.CommonCoreDifference

/-!
# The integral common-core base with both imbalanced borders empty

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
The compatible frame differs from boundary-first condensation by one common
column swap. Its four determinant signs cancel in pairs. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {α β γ F : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]
  [IsEmpty α] [IsEmpty γ]

/-- Empty external states leave only the unmatched top row and complete core. -/
def emptyBorderFrameEquiv : (Unit ⊕ (Unit ⊕ β)) ≃
    ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) where
  toFun | .inl u => .inl (.inr u) | .inr i => .inr (.inl i)
  invFun
    | .inl (.inl a) => isEmptyElim a
    | .inl (.inr u) => .inl u
    | .inr (.inl i) => .inr i
    | .inr (.inr g) => isEmptyElim g
  left_inv := by rintro (u | i) <;> rfl
  right_inv := by
    rintro ((a | u) | (i | g))
    · exact isEmptyElim a
    · rfl
    · rfl
    · exact isEmptyElim g

/-- The actual compatible empty-border determinant has the one common column
swap sign, with every row, column and corner entry retained. -/
theorem borderedCoreMatrix_empty_det
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    (borderedCoreMatrix A R T C S B).det =
      -(singleCoreBorderSum C (R (.inr ())) (fun i => S i (.inl ()))
        (T (.inr ()) (.inl ()))).det := by
  classical
  let e := emptyBorderFrameEquiv (α := α) (β := β) (γ := γ)
  let σ := Equiv.swap (Sum.inl () : Unit ⊕ (Unit ⊕ β)) (.inr (.inl ()))
  have hm : (borderedCoreMatrix A R T C S B).submatrix e e =
      (singleCoreBorderSum C (R (.inr ())) (fun i => S i (.inl ()))
        (T (.inr ()) (.inl ()))).submatrix id σ := by
    ext i j
    rcases i with u | (v | i) <;> rcases j with w | (x | j) <;>
      simp [e, σ, emptyBorderFrameEquiv, borderedCoreMatrix,
        commonCoreColumnEquiv, singleCoreBorderSum, Matrix.submatrix, Equiv.swap_apply_def]
  rw [← Matrix.det_submatrix_equiv_self e, hm, Matrix.det_permute']
  simp [σ]

/-- Both empty imbalanced borders reduce to integral condensation, not merely
to vanishing at one selected prime. -/
theorem commonCoreDifference_empty_dvd
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F) :
    C.det ∣ commonCoreDifference A R T C S B r s t q z := by
  have hd := singleCoreBorderSum_cross_difference_dvd C
    (R (.inr ())) r (fun i => S i (.inl ())) s
    (T (.inr ()) (.inl ())) (t (.inr ())) (q (.inl ())) z
  unfold commonCoreDifference
  simp only [borderedCoreMatrix_empty_det, neg_mul_neg, Matrix.of_apply]
  exact hd

end SkewCornerDescent.Matrix
