/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.CommonCoreColumns

/-!
# Arbitrary compatible borders around a common core

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`). The sum-type
frames encode both border imbalances exactly. Every external entry and coupling is
retained; a zero core column supplies the block factorization. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {α β γ F : Type*}

section Constructors
variable [Zero F]

/-- The full compatible bordered matrix, with one unmatched row on the left and one
unmatched column on the right. The core's first column shares the left square frame. -/
def borderedCoreMatrix
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F :=
  fun i j => match i, (commonCoreColumnEquiv α β γ).symm j with
    | .inl i, .inl j => A i j
    | .inl i, .inr (.inl j) => R i j
    | .inl i, .inr (.inr j) => T i j
    | .inr (.inl _), .inl _ => 0
    | .inr (.inl i), .inr (.inl j) => C i j
    | .inr (.inl i), .inr (.inr j) => S i j
    | .inr (.inr _), .inl _ => 0
    | .inr (.inr _), .inr (.inl _) => 0
    | .inr (.inr i), .inr (.inr j) => B i j

/-- The square left response retains the complete left border and the first core column. -/
def upperCoreBorder (A : Matrix (α ⊕ Unit) α F)
    (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F) : Matrix (α ⊕ Unit) (α ⊕ Unit) F :=
  fun i j => match j with
    | .inl j => A i j
    | .inr u => R i (.inl u)

/-- The square lower response retains every remaining core and right border column. -/
def lowerCoreBorder (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    Matrix ((Unit ⊕ β) ⊕ γ) ((Unit ⊕ β) ⊕ γ) F :=
  fun i j => match i, j with
    | .inl i, .inl (.inl u) => S i (.inl u)
    | .inl i, .inl (.inr j) => C i (.inr j)
    | .inl i, .inr j => S i (.inr j)
    | .inr i, .inl (.inl u) => B i (.inl u)
    | .inr _, .inl (.inr _) => 0
    | .inr i, .inr j => B i (.inr j)

/-- Three proved zero rectangles turn an actual complete matrix into the
compatible bordered frame. Every nonzero block is its literal extracted submatrix. -/
theorem borderedCoreMatrix_of_zero_rectangles
    (M : Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F)
    (hCL : ∀ (i : Unit ⊕ β) (j : α),
      M (.inr (.inl i)) (commonCoreColumnEquiv α β γ (.inl j)) = 0)
    (hBL : ∀ (i : γ) (j : α),
      M (.inr (.inr i)) (commonCoreColumnEquiv α β γ (.inl j)) = 0)
    (hBC : ∀ (i : γ) (j : Unit ⊕ β),
      M (.inr (.inr i)) (commonCoreColumnEquiv α β γ (.inr (.inl j))) = 0) :
    M = borderedCoreMatrix
      (M.submatrix Sum.inl (fun j => commonCoreColumnEquiv α β γ (.inl j)))
      (M.submatrix Sum.inl (fun j => commonCoreColumnEquiv α β γ (.inr (.inl j))))
      (M.submatrix Sum.inl (fun j => commonCoreColumnEquiv α β γ (.inr (.inr j))))
      (M.submatrix (fun i => .inr (.inl i))
        (fun j => commonCoreColumnEquiv α β γ (.inr (.inl j))))
      (M.submatrix (fun i => .inr (.inl i))
        (fun j => commonCoreColumnEquiv α β γ (.inr (.inr j))))
      (M.submatrix (fun i => .inr (.inr i))
        (fun j => commonCoreColumnEquiv α β γ (.inr (.inr j)))) := by
  ext i j
  obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv α β γ).surjective j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [borderedCoreMatrix, Equiv.symm_apply_apply, Matrix.submatrix_apply]
  · exact hCL i j
  · exact hBL i j
  · exact hBC i j

end Constructors

section Map
variable {G : Type*} [Zero F] [Zero G]

/-- A zero-preserving entrywise map retains the entire compatible border frame. -/
theorem borderedCoreMatrix_map (f : F → G) (hf : f 0 = 0)
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    (borderedCoreMatrix A R T C S B).map f =
      borderedCoreMatrix (A.map f) (R.map f) (T.map f) (C.map f) (S.map f) (B.map f) := by
  ext i j
  obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv α β γ).surjective j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [borderedCoreMatrix, Matrix.map_apply, hf]

end Map

variable [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]

/-- A proved zero core column separates the complete compatible matrix into two
square blocks. The entire upper-right coupling remains until determinant factorization. -/
theorem borderedCoreMatrix_det_of_zero_column
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (hC : ∀ i, C i (.inl ()) = 0) :
    (borderedCoreMatrix A R T C S B).det =
      (upperCoreBorder A R).det * (lowerCoreBorder C S B).det := by
  let M := borderedCoreMatrix A R T C S B
  have h11 : M.toBlocks₁₁ = upperCoreBorder A R := by
    ext i j
    cases j <;> rfl
  have h22 : M.toBlocks₂₂ = lowerCoreBorder C S B := by
    ext i j
    rcases i with i | i <;> rcases j with (u | j) | j <;> rfl
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | u
    · rfl
    · cases u
      exact hC i
    · rfl
    · rfl
  change M.det = _
  rw [← Matrix.fromBlocks_toBlocks M, h11, h22, h21, Matrix.det_fromBlocks_zero₂₁]

omit [DecidableEq β] in
/-- The lifted full core change produces the corresponding compatible bordered matrix.
All left and right external columns, including every upper-right coupling, remain intact. -/
theorem borderedCoreMatrix_mul_lift
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (P : Matrix (Unit ⊕ β) (Unit ⊕ β) F) :
    borderedCoreMatrix A R T C S B * liftCommonCoreColumns P =
      borderedCoreMatrix A (R * P) T (C * P) S B := by
  classical
  ext i j
  obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv α β γ).surjective j
  rcases j with j | j
  · rw [mul_liftCommonCoreColumns_left]
    rcases i with i | i
    · rfl
    · rcases i with i | i <;> rfl
  · rcases j with j | j
    · rw [mul_liftCommonCoreColumns_core]
      rcases i with i | i
      · simp [borderedCoreMatrix, Matrix.mul_apply]
      · rcases i with i | i <;> simp [borderedCoreMatrix, Matrix.mul_apply]
    · rw [mul_liftCommonCoreColumns_right]
      rcases i with i | i
      · simp [borderedCoreMatrix]
      · rcases i with i | i <;> simp [borderedCoreMatrix]

/-- A compatible core transformation has exactly its own determinant factor. -/
theorem borderedCoreMatrix_core_change_det
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (P : Matrix (Unit ⊕ β) (Unit ⊕ β) F) :
    (borderedCoreMatrix A (R * P) T (C * P) S B).det =
      (borderedCoreMatrix A R T C S B).det * P.det := by
  rw [← borderedCoreMatrix_mul_lift, Matrix.det_mul, liftCommonCoreColumns_det]

end SkewCornerDescent.Matrix
