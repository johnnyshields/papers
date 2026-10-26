/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Cap

/-!
# The connected board over a cap

For a nonempty weak cap `c` and `T = X_1 + Y_1 + 1`, the lists `(T, X)` and `(Y, 0)` define a
connected skew diagram whose determinant expands along its first row as
`∑_p (-1)^p h_{T - cols p} · minor p`.  The labels `T - cols p` are fresh and distinct, so a
common factor of the minors cannot divide the determinant.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

namespace WeakCap

variable {m : ℕ} (c : WeakCap (m + 1))

/-- The top label of the board. -/
def topLabel : ℤ := c.X 0 + c.Y 0 + 1

/-- The connected skew diagram `(T, X) / (Y, 0)`. -/
def board : BetaDiagram (m + 2) where
  row := (Fin.cons c.topLabel c.X : Fin (m + 2) → ℤ)
  col := c.cols
  row_strictAnti := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero]
      have h1 : (Fin.cons c.topLabel c.X : Fin (m + 2) → ℤ) 1 = c.X 0 := Fin.cons_succ _ _ 0
      have h2 : (Fin.cons c.topLabel c.X : Fin (m + 2) → ℤ) 0 = c.topLabel := Fin.cons_zero _ _
      rw [h1, h2]
      have := c.Y_pos 0
      unfold topLabel; omega
    | succ j =>
      rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact c.X_anti (Fin.castSucc_lt_succ)
  col_strictAnti := c.cols_anti
  row_nonempty := by
    intro i
    induction i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      have h : c.cols 0 = c.Y 0 := c.cols_castSucc 0
      have := c.Y_pos 0
      have := c.Y_le 0
      unfold topLabel; omega
    | succ k =>
      rw [Fin.cons_succ]
      have h1 : c.cols k.succ < c.cols k.castSucc := c.cols_anti Fin.castSucc_lt_succ
      have h2 : c.cols k.castSucc ≤ c.X k := by simpa using c.Y_le k
      omega

theorem board_connected : c.board.Connected := by
  refine ⟨by omega, fun i hi => ?_⟩
  have hi' : i.val < m + 1 := by omega
  obtain ⟨k, rfl⟩ : ∃ k : Fin (m + 1), i = k.castSucc := ⟨⟨i.val, hi'⟩, rfl⟩
  have h1 : (⟨(k.castSucc).val + 1, hi⟩ : Fin (m + 2)) = k.succ := rfl
  change c.cols k.castSucc ≤ (Fin.cons c.topLabel c.X : Fin (m + 2) → ℤ) ⟨(k.castSucc).val + 1, hi⟩
  rw [h1, Fin.cons_succ]
  simpa using c.Y_le k

theorem board_schur : c.board.schur = ∑ p : Fin (m + 2), (-1 : CompleteRing) ^ (p : ℕ) *
    complete (c.topLabel - c.cols p) * c.minor p := by
  unfold BetaDiagram.schur
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h0 : c.board.matrix 0 p = complete (c.topLabel - c.cols p) := by
    simp [BetaDiagram.matrix, board]
  have h1 : c.board.matrix.submatrix Fin.succ p.succAbove =
      betaBoard c.X (c.cols ∘ p.succAbove) := by
    refine Matrix.ext fun i q => ?_
    simp [BetaDiagram.matrix, board, betaBoard]
  rw [h0, h1]
  rfl

end WeakCap

end SkewCoframeRigidity.CapRecognition
