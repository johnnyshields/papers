/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CommonCoreBorders
import SkewCornerDescent.Matrix.OptionLaplace

/-!
# Literal left-border reduction for integral common-core divisibility

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
Deleting the distinguished left column and its matched row preserves the entire
compatible smaller border frame. Every central and right entry remains.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Expose the distinguished left-border index without changing any core index. -/
def leftBorderOptionEquiv (α κ : Type*) :
    Option ((α ⊕ Unit) ⊕ κ) ≃ ((Option α ⊕ Unit) ⊕ κ) where
  toFun
    | none => .inl (.inl none)
    | some (.inl (.inl a)) => .inl (.inl (some a))
    | some (.inl (.inr u)) => .inl (.inr u)
    | some (.inr k) => .inr k
  invFun
    | .inl (.inl none) => none
    | .inl (.inl (some a)) => some (.inl (.inl a))
    | .inl (.inr u) => some (.inl (.inr u))
    | .inr k => some (.inr k)
  left_inv := by rintro (_ | ((a | u) | k)) <;> rfl
  right_inv := by rintro (((_ | a) | u) | k) <;> rfl

/-- The surviving left rows in the smaller actual frame. -/
def leftBorderKeep (α : Type*) : (α ⊕ Unit) → (Option α ⊕ Unit)
  | .inl a => .inl (some a)
  | .inr u => .inr u

/-- The distinguished-column minor is exactly the complete smaller compatible
border matrix; zero rectangles are preserved rather than imposed anew. -/
theorem borderedCore_left_option_minor {α β γ F : Type*} [Zero F]
    (A : Matrix (Option α ⊕ Unit) (Option α) F)
    (R : Matrix (Option α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (Option α ⊕ Unit) (Unit ⊕ γ) F)
    (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    ((borderedCoreMatrix A R T C S B).submatrix
      (leftBorderOptionEquiv α ((Unit ⊕ β) ⊕ γ))
      (leftBorderOptionEquiv α ((Unit ⊕ β) ⊕ γ))).submatrix some some =
      borderedCoreMatrix (A.submatrix (leftBorderKeep α) some)
        (R.submatrix (leftBorderKeep α) id) (T.submatrix (leftBorderKeep α) id) C S B := by
  ext i j
  rcases i with ((i | u) | ((v | b) | g)) <;>
    rcases j with ((j | u') | ((v' | b') | g')) <;> rfl

/-- A cofactor replaces precisely one surviving left row by the distinguished
row while retaining the entire compatible core and opposite border. -/
def leftBorderReplace (α : Type*) [DecidableEq α] (k : α ⊕ Unit) :
    (α ⊕ Unit) → (Option α ⊕ Unit) :=
  fun i => if i = k then .inl none else leftBorderKeep α i

/-- Every nonzero left-column cofactor is a complete smaller compatible
border frame, with the same row replacement in every neighboring determinant. -/
theorem borderedCore_left_option_replaced_minor {α β γ F : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [Zero F]
    (A : Matrix (Option α ⊕ Unit) (Option α) F)
    (R : Matrix (Option α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (Option α ⊕ Unit) (Unit ⊕ γ) F)
    (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (k : α ⊕ Unit) :
    ((borderedCoreMatrix A R T C S B).submatrix
      (leftBorderOptionEquiv α ((Unit ⊕ β) ⊕ γ))
      (leftBorderOptionEquiv α ((Unit ⊕ β) ⊕ γ))).submatrix
        (Function.update some (.inl k) none) some =
      borderedCoreMatrix (A.submatrix (leftBorderReplace α k) some)
        (R.submatrix (leftBorderReplace α k) id)
        (T.submatrix (leftBorderReplace α k) id) C S B := by
  ext i j
  rcases i with ((i | u) | ((v | b) | g)) <;>
    rcases j with ((j | u') | ((v' | b') | g')) <;>
    simp [Matrix.submatrix_apply, Function.update_apply, leftBorderOptionEquiv,
      leftBorderKeep, leftBorderReplace, borderedCoreMatrix, commonCoreColumnEquiv]
  all_goals split_ifs <;> rfl

/-- The complete left-column Laplace expansion has the same coefficients
for every compatible right border. Every surviving minor retains the full core. -/
theorem borderedCore_det_left_option_expand {α β γ F : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]
    (A : Matrix (Option α ⊕ Unit) (Option α) F)
    (R : Matrix (Option α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (Option α ⊕ Unit) (Unit ⊕ γ) F)
    (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    (borderedCoreMatrix A R T C S B).det =
      A (.inl none) none *
        (borderedCoreMatrix (A.submatrix (leftBorderKeep α) some)
          (R.submatrix (leftBorderKeep α) id) (T.submatrix (leftBorderKeep α) id) C S B).det -
      ∑ k : α ⊕ Unit, A (leftBorderKeep α k) none *
        (borderedCoreMatrix (A.submatrix (leftBorderReplace α k) some)
          (R.submatrix (leftBorderReplace α k) id)
          (T.submatrix (leftBorderReplace α k) id) C S B).det := by
  let e := leftBorderOptionEquiv α ((Unit ⊕ β) ⊕ γ)
  let M := (borderedCoreMatrix A R T C S B).submatrix e e
  have h := det_option_expand_column M
  have h0 : M none none = A (.inl none) none := rfl
  have hcol (k : (α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) :
      M (some k) none = match k with
        | .inl i => A (leftBorderKeep α i) none
        | .inr _ => 0 := by
    rcases k with ((i | u) | ((v | b) | g)) <;> rfl
  dsimp only [M, e] at h
  rw [Matrix.det_submatrix_equiv_self, borderedCore_left_option_minor] at h
  change (borderedCoreMatrix A R T C S B).det =
    M none none *
      (borderedCoreMatrix (A.submatrix (leftBorderKeep α) some)
        (R.submatrix (leftBorderKeep α) id) (T.submatrix (leftBorderKeep α) id) C S B).det -
      ∑ k, M (some k) none * (M.submatrix (Function.update some k none) some).det at h
  simp only [h0, Fintype.sum_sum_type, hcol, zero_mul, Finset.sum_const_zero] at h
  simpa only [M, e, borderedCore_left_option_replaced_minor,
    Fintype.sum_sum_type, add_zero] using h

end SkewCornerDescent.Matrix
