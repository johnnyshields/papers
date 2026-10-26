/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Compatible column changes for arbitrary imbalanced borders

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`). The left border
has one fewer column than row; the right border has one fewer row than column.
A common core column change acts on all four bordered determinants with the same
nonzero determinant factor. These frames retain every row and column. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Regroup the core's first column with the left border and the right border's first
column with the remaining states. No cardinality-only equivalence is chosen. -/
def commonCoreColumnEquiv (α β γ : Type*) :
    (α ⊕ ((Unit ⊕ β) ⊕ (Unit ⊕ γ))) ≃ ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) where
  toFun
    | .inl a => .inl (.inl a)
    | .inr (.inl (.inl u)) => .inl (.inr u)
    | .inr (.inl (.inr b)) => .inr (.inl (.inr b))
    | .inr (.inr (.inl u)) => .inr (.inl (.inl u))
    | .inr (.inr (.inr g)) => .inr (.inr g)
  invFun
    | .inl (.inl a) => .inl a
    | .inl (.inr u) => .inr (.inl (.inl u))
    | .inr (.inl (.inl u)) => .inr (.inr (.inl u))
    | .inr (.inl (.inr b)) => .inr (.inl (.inr b))
    | .inr (.inr g) => .inr (.inr (.inr g))
  left_inv := by rintro (a | ((u | b) | (u | g))) <;> rfl
  right_inv := by rintro ((a | u) | ((u | b) | g)) <;> rfl

variable {α β γ F : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]

/-- The lifted core change fixes every external column and keeps the core transformation
entire, including its first column. -/
def liftCommonCoreColumns (P : Matrix (Unit ⊕ β) (Unit ⊕ β) F) :
    Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F :=
  (Matrix.fromBlocks (1 : Matrix α α F) 0 0
    (Matrix.fromBlocks P 0 0 (1 : Matrix (Unit ⊕ γ) (Unit ⊕ γ) F))).reindex
      (commonCoreColumnEquiv α β γ) (commonCoreColumnEquiv α β γ)

/-- The same determinant factor accompanies every compatible bordered matrix. -/
theorem liftCommonCoreColumns_det (P : Matrix (Unit ⊕ β) (Unit ⊕ β) F) :
    (liftCommonCoreColumns (α := α) (γ := γ) P).det = P.det := by
  simp [liftCommonCoreColumns, Matrix.det_fromBlocks_zero₂₁]

omit [DecidableEq β] in
/-- Multiplication changes only the core columns by the supplied full matrix. -/
theorem mul_liftCommonCoreColumns_core
    (M : Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F)
    (P : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (i : (α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) (j : Unit ⊕ β) :
    (M * liftCommonCoreColumns (α := α) (γ := γ) P) i
      (commonCoreColumnEquiv α β γ (.inr (.inl j))) =
      ∑ k, M i (commonCoreColumnEquiv α β γ (.inr (.inl k))) * P k j := by
  classical
  rw [Matrix.mul_apply]
  rw [← (commonCoreColumnEquiv α β γ).sum_comp
    (fun z => M i z * liftCommonCoreColumns (α := α) (γ := γ) P z
      (commonCoreColumnEquiv α β γ (.inr (.inl j))))]
  simp [liftCommonCoreColumns, Matrix.reindex, Fintype.sum_sum_type]

omit [DecidableEq β] in
/-- Every left external column is unchanged by the lifted core transformation. -/
theorem mul_liftCommonCoreColumns_left
    (M : Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F)
    (P : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (i : (α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) (j : α) :
    (M * liftCommonCoreColumns (α := α) (γ := γ) P) i
      (commonCoreColumnEquiv α β γ (.inl j)) =
        M i (commonCoreColumnEquiv α β γ (.inl j)) := by
  classical
  rw [Matrix.mul_apply]
  rw [← (commonCoreColumnEquiv α β γ).sum_comp
    (fun z => M i z * liftCommonCoreColumns (α := α) (γ := γ) P z
      (commonCoreColumnEquiv α β γ (.inl j)))]
  simp [liftCommonCoreColumns, Matrix.reindex, Matrix.one_apply, Fintype.sum_sum_type]

omit [DecidableEq β] in
/-- Every right external column is unchanged, including the first border column. -/
theorem mul_liftCommonCoreColumns_right
    (M : Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F)
    (P : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (i : (α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) (j : Unit ⊕ γ) :
    (M * liftCommonCoreColumns (α := α) (γ := γ) P) i
      (commonCoreColumnEquiv α β γ (.inr (.inr j))) =
        M i (commonCoreColumnEquiv α β γ (.inr (.inr j))) := by
  classical
  rw [Matrix.mul_apply]
  rw [← (commonCoreColumnEquiv α β γ).sum_comp
    (fun z => M i z * liftCommonCoreColumns (α := α) (γ := γ) P z
      (commonCoreColumnEquiv α β γ (.inr (.inr j))))]
  cases j <;>
    simp [liftCommonCoreColumns, Matrix.reindex, Matrix.one_apply, Fintype.sum_sum_type]

end SkewCornerDescent.Matrix
