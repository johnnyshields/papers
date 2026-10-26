import SkewJacobiNegative.NegativeBoards
import SkewJacobiNegative.FiveOpeningExpansion

/-!
# Exceptional five-row beta families

The actual beta lists in `eq:five-families`.  The parameter domain retains
`q = b`, where common row and column betas are permitted.
-/

namespace SkewJacobiNegative
namespace FiveExceptional

/-- The manuscript domain, including its common-beta boundary. -/
structure Parameters where
  q : ℤ
  b : ℤ
  g : ℤ
  q_pos : 1 ≤ q
  q_le_b : q ≤ b
  b_lt_g : b < g

/-- Common row betas of all four displayed representatives. -/
def rows (P : Parameters) : Fin 5 → ℤ :=
  ![P.b + 4 * P.g, P.b + 3 * P.g, P.b + 2 * P.g, P.b + P.g, P.b]

/-- Column betas of the middle-opening representatives. -/
def fCols (P : Parameters) (second : Bool) : Fin 5 → ℤ :=
  ![3 * P.g + (if second then P.q else 0), P.g + P.q, P.g, P.q, 0]

/-- Column betas of the end-opening representatives. -/
def hCols (P : Parameters) (second : Bool) : Fin 5 → ℤ :=
  ![2 * P.g + P.q, 2 * P.g, P.g + (if second then P.q else 0), P.q, 0]

private theorem rows_strict (P : Parameters) : StrictAnti (rows P) := by
  intro i j hij
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  fin_cases i <;> fin_cases j <;> simp_all [rows] <;> omega

/-- The genuine middle-opening exceptional board, not a polynomial surrogate. -/
def F (P : Parameters) (second : Bool) : BetaDiagram 5 where
  row := rows P
  col := fCols P second
  row_strictAnti := rows_strict P
  col_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases second <;> fin_cases i <;> fin_cases j <;>
      simp_all [fCols] <;> omega
  row_nonempty := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases second <;> fin_cases i <;> simp_all [rows, fCols] <;> omega

/-- The genuine end-opening exceptional board. -/
def H (P : Parameters) (second : Bool) : BetaDiagram 5 where
  row := rows P
  col := hCols P second
  row_strictAnti := rows_strict P
  col_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases second <;> fin_cases i <;> fin_cases j <;>
      simp_all [hCols] <;> omega
  row_nonempty := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases second <;> fin_cases i <;> simp_all [rows, hCols] <;> omega

theorem F_connected (P : Parameters) (second : Bool) : (F P second).Connected := by
  have hstep : ∀ j : Fin 4, fCols P second j.castSucc ≤ rows P j.succ := by
    intro j
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases second <;> fin_cases j <;> norm_num [rows,fCols] <;> omega
  refine ⟨by omega, ?_⟩
  intro i hi
  exact hstep ⟨i.val,by omega⟩

theorem H_connected (P : Parameters) (second : Bool) : (H P second).Connected := by
  have hstep : ∀ j : Fin 4, hCols P second j.castSucc ≤ rows P j.succ := by
    intro j
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases second <;> fin_cases j <;> norm_num [rows,hCols] <;> omega
  refine ⟨by omega, ?_⟩
  intro i hi
  exact hstep ⟨i.val,by omega⟩

/-- The negative sites do not change at `q = b`. -/
theorem F_negative_iff (P : Parameters) (second : Bool) (i j : Fin 5) :
    (F P second).row i < (F P second).col j ↔
      (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 0) ∨
      (i = 4 ∧ (j = 0 ∨ j = 1 ∨ j = 2)) := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases second <;> fin_cases i <;> fin_cases j <;>
    simp_all [F, rows, fCols] <;> omega

theorem H_negative_iff (P : Parameters) (second : Bool) (i j : Fin 5) :
    (H P second).row i < (H P second).col j ↔
      (i = 3 ∧ (j = 0 ∨ j = 1)) ∨
      (i = 4 ∧ (j = 0 ∨ j = 1 ∨ j = 2)) := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases second <;> fin_cases i <;> fin_cases j <;>
    simp_all [H, rows, hCols] <;> omega

theorem F_negativeCount (P : Parameters) (second : Bool) :
    negativeCount (F P second) = 5 := by
  simp only [negativeCount, negativeSites, F_negative_iff]
  decide

theorem H_negativeCount (P : Parameters) (second : Bool) :
    negativeCount (H P second) = 5 := by
  simp only [negativeCount, negativeSites, H_negative_iff]
  decide

theorem F_normalized (P : Parameters) (second : Bool) : (F P second).Normalized := by
  intro hn
  simp [F, fCols]

theorem H_normalized (P : Parameters) (second : Bool) : (H P second).Normalized := by
  intro hn
  simp [H, hCols]

/-- The displayed middle and end representatives differ literally. -/
theorem F_ne_H (P : Parameters) (second third : Bool) : F P second ≠ H P third := by
  intro he
  have h := congrArg (fun D : BetaDiagram 5 => D.col 1) he
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  simp [F, H, fCols, hCols] at h
  omega

private theorem negative_label (P : Parameters) (k : ℤ) (hk : k ≤ -1)
    (e : ℤ) (he : 0 ≤ e) :
    complete (P.b + k * P.g - e) = 0 := by
  apply complete_of_neg
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  have hg : 0 < P.g := by omega
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The two parameter-uniform determinant identities, retaining the unit boundary. -/
theorem F_schur_eq_H (P : Parameters) (second : Bool) :
    (F P second).schur = (H P second).schur := by
  have hq : 0 ≤ P.q := by have := P.q_pos; omega
  have hn1 := negative_label P (-1) (by omega) 0 (by omega)
  have hn2 := negative_label P (-2) (by omega) 0 (by omega)
  have hn3 := negative_label P (-3) (by omega) 0 (by omega)
  have hq1 := negative_label P (-1) (by omega) P.q hq
  have hq2 := negative_label P (-2) (by omega) P.q hq
  have hq3 := negative_label P (-3) (by omega) P.q hq
  ring_nf at hn1 hn2 hn3 hq1 hq2 hq3
  cases second <;>
    norm_num [BetaDiagram.schur, BetaDiagram.matrix, F, H, rows, fCols, hCols,
      Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
      Matrix.of_apply, Fin.sum_univ_succ, Fin.succAbove] <;>
    ring_nf <;>
    simp only [hn1, hn2, hn3, hq1, hq2, hq3] <;>
    ring

/-- No displayed middle representative is a half-turn of a displayed representative. -/
theorem F_not_rotation_F (P Q : Parameters) (s t : Bool) :
    ¬ (F P s).RotationEquivalent (F Q t) := by
  rintro ⟨c, hr, hc⟩
  have h0 := hr 0
  have h1 := hr 1
  have h3 := hr 3
  have h4 := hr 4
  have := Q.q_pos
  have := Q.q_le_b
  have := Q.b_lt_g
  cases t <;> norm_num [F, rows, fCols, Fin.rev] at h0 h1 h3 h4 <;> omega

theorem F_not_rotation_H (P Q : Parameters) (s t : Bool) :
    ¬ (F P s).RotationEquivalent (H Q t) := by
  rintro ⟨c, hr, hc⟩
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have := Q.q_pos
  have := Q.q_le_b
  have := Q.b_lt_g
  cases t <;> norm_num [F, H, rows, hCols, Fin.rev] at h0 h1 h2 h3 <;> omega

theorem H_not_rotation_H (P Q : Parameters) (s t : Bool) :
    ¬ (H P s).RotationEquivalent (H Q t) := by
  rintro ⟨c, hr, hc⟩
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have := Q.q_pos
  have := Q.q_le_b
  have := Q.b_lt_g
  cases t <;> norm_num [H, rows, hCols, Fin.rev] at h0 h1 h2 h3 <;> omega

/-- All four actual diagrams in either family have the same Schur polynomial. -/
theorem quartet_schur (P : Parameters) (s : Bool) :
    (F P s).schur = (F P s).rotate.schur ∧
    (F P s).schur = (H P s).schur ∧
    (F P s).schur = (H P s).rotate.schur :=
  ⟨(F P s).rotate_schur.symm, F_schur_eq_H P s,
    (F_schur_eq_H P s).trans (H P s).rotate_schur.symm⟩

/-- The two exceptional types have genuinely different opened matrix positions. -/
theorem F_opening (P : Parameters) (s : Bool) : FiveOpening.HasOpening (F P s) 1 := by
  intro i j
  rw [F_negative_iff]
  fin_cases i <;> fin_cases j <;>
    norm_num [FiveOpening.openedRow, FiveOpening.openedCol]

theorem H_opening (P : Parameters) (s : Bool) : FiveOpening.HasOpening (H P s) 0 := by
  intro i j
  rw [H_negative_iff]
  fin_cases i <;> fin_cases j <;>
    norm_num [FiveOpening.openedRow, FiveOpening.openedCol]

end FiveExceptional
end SkewJacobiNegative
