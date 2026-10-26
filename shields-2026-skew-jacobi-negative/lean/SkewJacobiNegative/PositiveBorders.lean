/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.ExteriorGaps
import SkewJacobiNegative.FirstVariations

/-!
# Positive borders

The literal lists in `eq:border-definition` and the geometric producers for
`lem:border` in «Boundary coefficients and propagation» (`sec:boundary-tools`).
No restriction is imposed on the signs of the child's off-diagonal indices.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

variable {n : ℕ}

/-- Prepend the increased first row and append the decreased last column.
The core is not required to be connected or zero-free. -/
def positiveBorder (D : BetaDiagram (n + 1)) (u v : ℤ)
    (hu : 0 < u) (hv : 0 < v) : BetaDiagram (n + 2) where
  row := Fin.cons (D.row 0 + u) D.row
  col := Fin.snoc D.col (D.col (Fin.last n) - v)
  row_strictAnti := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        have h := D.row_strictAnti.antitone (Fin.zero_le j)
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        simpa only [Fin.cons_succ] using D.row_strictAnti
          (show i < j by simpa only [Fin.succ_lt_succ_iff] using hij)
  col_strictAnti := by
    intro i j hij
    cases j using Fin.lastCases with
    | last =>
      cases i using Fin.lastCases with
      | last => exact (lt_irrefl _ hij).elim
      | cast i =>
        have h := D.col_strictAnti.antitone (Fin.le_last i)
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        omega
    | cast j =>
      cases i using Fin.lastCases with
      | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
      | cast i =>
        simpa only [Fin.snoc_castSucc] using D.col_strictAnti
          (show i < j by simpa only [Fin.castSucc_lt_castSucc_iff] using hij)
  row_nonempty := by
    intro i
    cases i using Fin.lastCases with
    | last =>
      have h := D.row_nonempty (Fin.last n)
      simpa only [Fin.cons_last, Fin.snoc_last] using
        (show D.col (Fin.last n) - v < D.row (Fin.last n) by omega)
    | cast i =>
      cases i using Fin.cases with
      | zero =>
        have h := D.row_nonempty 0
        rw [Fin.snoc_castSucc, Fin.castSucc_zero, Fin.cons_zero]
        omega
      | succ i =>
        have h := D.row_nonempty i.succ
        have hr := D.row_strictAnti (show i.castSucc < i.succ by
          simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
        rw [Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ]
        omega

@[simp] theorem positiveBorder_row_zero (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).row 0 = D.row 0 + u := by
  simp [positiveBorder]

@[simp] theorem positiveBorder_row_succ (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (i : Fin (n + 1)) :
    (D.positiveBorder u v hu hv).row i.succ = D.row i := by
  simp [positiveBorder]

@[simp] theorem positiveBorder_col_castSucc (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (i : Fin (n + 1)) :
    (D.positiveBorder u v hu hv).col i.castSucc = D.col i := by
  simp [positiveBorder]

@[simp] theorem positiveBorder_col_last (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).col (Fin.last (n + 1)) = D.col (Fin.last n) - v := by
  simp [positiveBorder]

/-- Normalization gives the manuscript's last beta `-v`. -/
theorem positiveBorder_normalized_last (D : BetaDiagram (n + 1))
    (hD : D.Normalized) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).col (Fin.last (n + 1)) = -v := by
  have h := hD (by omega)
  have he : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext; simp
  rw [he] at h
  simp [h]

/-- Every new adjacent overlap is precisely an old nonempty diagonal row. -/
theorem positiveBorder_connected (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  let j : Fin (n + 1) := ⟨i.val, by omega⟩
  have he : i = j.castSucc := by apply Fin.ext; rfl
  have hs : (⟨i.val + 1, hi⟩ : Fin (n + 2)) = j.succ := by
    apply Fin.ext; rfl
  rw [hs, he, positiveBorder_col_castSucc, positiveBorder_row_succ]
  exact (D.row_nonempty j).le

/-- The border's actual maximal complementary diagonal is positive. -/
theorem positiveBorder_positiveCorner (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).PositiveCorner := by
  intro i
  simpa using D.row_nonempty i

@[simp] theorem positiveBorder_cornerDiagram (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).cornerDiagram
      (D.positiveBorder_positiveCorner u v hu hv) = D := by
  cases D
  simp [cornerDiagram, positiveBorder]

@[simp] theorem positiveBorder_largestLabel (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).largestLabel = D.largestLabel + u + v := by
  simp [largestLabel]; ring

@[simp] theorem positiveBorder_topMargin (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).topMargin = u := by
  unfold topMargin
  rw [positiveBorder_row_zero, positiveBorder_row_succ D u v hu hv 0]
  omega

@[simp] theorem positiveBorder_bottomMargin (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).bottomMargin = v := by
  simp [bottomMargin]

@[simp] theorem positiveBorder_secondLabel (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).secondLabel =
      D.largestLabel + u + v - min u v := by
  simp [secondLabel]

/-- Connectedness and zero-freeness, not nonnegativity, make the child's
complementary diagonal strictly positive (`lem:border`). -/
theorem positiveCorner_of_connected_zeroFree (D : BetaDiagram (n + 1))
    (hC : D.Connected) (hZ : D.ZeroFree) : D.PositiveCorner := by
  intro i
  have h := D.corner_diagonal_nonnegative hC i
  have hn := hZ i.succ i.castSucc
  omega

/-- Swapping the margins rotates the parent exactly when the core is symmetric. -/
theorem positiveBorder_swap_rotation (D : BetaDiagram (n + 1)) (hD : D.Symmetric)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).RotationEquivalent (D.positiveBorder v u hv hu) := by
  obtain ⟨c, hr, hc⟩ := hD
  refine ⟨c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      have h := hr 0
      rw [Fin.rev_zero] at h
      simpa only [positiveBorder_row_zero, Fin.rev_zero, positiveBorder_col_last,
        Fin.rev_zero] using (show D.row 0 + u = c - (D.col (Fin.last n) - u) by omega)
    | succ i => simpa only [positiveBorder_row_succ, Fin.rev_succ,
        positiveBorder_col_castSucc] using hr i
  · intro i
    cases i using Fin.lastCases with
    | last =>
      have h := hc (Fin.last n)
      rw [Fin.rev_last] at h
      simpa only [positiveBorder_col_last, Fin.rev_last, positiveBorder_row_zero,
        Fin.rev_last] using (show D.col (Fin.last n) - v = c - (D.row 0 + v) by omega)
    | cast i => simpa only [positiveBorder_col_castSucc, Fin.rev_castSucc,
        positiveBorder_row_succ] using hc i

end BetaDiagram
end SkewJacobiNegative
