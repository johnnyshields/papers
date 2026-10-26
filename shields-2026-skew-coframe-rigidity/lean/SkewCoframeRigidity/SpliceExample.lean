/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Splice

/-!
# The same-cell cap on the equal hook pair

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Rigidity with the same literal cap»
(`sec:fixed-caps`, `ex:same-cell-cap`).  The hooks `(2,1)` and `(2,2)/(1)` have full lists
`(3,1)/(1,0)` and `(3,2)/(2,0)`, equal skew Schur functions `h₁h₂ - h₃`, and the cell splices
have the distinct functions `h₁h₃ - h₄` and `h₂² - h₄`.  Sorry-free.
-/

namespace SkewCoframeRigidity

open SkewCofactorIndependence

/-- The one-cell cap, with lists `X = (1)`, `Y = (0)`. -/
def cellCap : BetaDiagram 1 where
  row _ := 1
  col _ := 0
  row_strictAnti := fun i j h => by exact absurd h (by simp [Subsingleton.elim i j])
  col_strictAnti := fun i j h => by exact absurd h (by simp [Subsingleton.elim i j])
  row_nonempty _ := by norm_num

/-- The hook `(2,1)`, with full lists `(3,1)/(1,0)`. -/
def hookA : BetaDiagram 2 where
  row := ![3, 1]
  col := ![1, 0]
  row_strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega
  col_strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega
  row_nonempty := by intro i; fin_cases i <;> simp

/-- The skew hook `(2,2)/(1)`, with full lists `(3,2)/(2,0)`. -/
def hookB : BetaDiagram 2 where
  row := ![3, 2]
  col := ![2, 0]
  row_strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega
  col_strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega
  row_nonempty := by intro i; fin_cases i <;> simp

private theorem cellCap_norm : IsNorm cellCap := rfl
private theorem hookA_norm : IsNorm hookA := rfl
private theorem hookB_norm : IsNorm hookB := rfl

open MvPolynomial BetaDiagram in
/-- The two hooks have the same function `h₁h₂ - h₃`. -/
theorem hooks_schur_eq : hookA.schur = hookB.schur := by
  have hA : hookA.schur = X 1 * X 2 - X 3 := by
    simp only [schur, matrix, Matrix.det_fin_two, Matrix.of_apply, hookA]
    simp [complete_of_pos, complete_zero]
    ring
  have hB : hookB.schur = X 1 * X 2 - X 3 := by
    simp only [schur, matrix, Matrix.det_fin_two, Matrix.of_apply, hookB]
    simp [complete_of_pos, complete_zero]
  rw [hA, hB]

/-- The two hooks are different diagrams. -/
theorem hooks_ne : hookA ≠ hookB := by
  intro h
  have := congrArg (fun D : BetaDiagram 2 => D.row 1) h
  simp [hookA, hookB] at this

open MvPolynomial BetaDiagram in
/-- The cell splice of the first hook has function `h₁h₃ - h₄`. -/
theorem cellSplice_schur_A :
    (splice cellCap hookA cellCap_norm hookA_norm).schur = X 1 * X 3 - X 4 := by
  unfold schur matrix
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, splice, spliceRow, spliceCol]
  simp [complete_of_pos, complete_zero, cellCap, hookA]
  ring_nf

open MvPolynomial BetaDiagram in
/-- The cell splice of the second hook has function `h₂² - h₄`. -/
theorem cellSplice_schur_B :
    (splice cellCap hookB cellCap_norm hookB_norm).schur = X 2 * X 2 - X 4 := by
  unfold schur matrix
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, splice, spliceRow, spliceCol]
  simp [complete_of_pos, complete_zero, cellCap, hookB]

open MvPolynomial in
/-- The same literal cell separates the equal-function hook pair. -/
theorem cellSplice_schur_ne :
    (splice cellCap hookA cellCap_norm hookA_norm).schur ≠
      (splice cellCap hookB cellCap_norm hookB_norm).schur := by
  rw [cellSplice_schur_A, cellSplice_schur_B]
  intro h
  have := congrArg (MvPolynomial.eval (fun j : ℕ+ => if j = 1 ∨ j = 3 then (1 : ℚ) else 0)) h
  simp at this

end SkewCoframeRigidity
