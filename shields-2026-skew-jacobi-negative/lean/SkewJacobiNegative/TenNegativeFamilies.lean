/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.NegativeRealizability
import SkewJacobiNegative.FirstVariations
import SkewJacobiNegative.WeightedReadings

/-!
# The seven-row ten-negative families

Actual beta lists, negative boards, and polynomial identities for
`prop:ten-negative-quartet`, `eq:ten-family-a-beta-lists`, and
`eq:ten-beta-lists` of `shields-2026-skew-jacobi-negative.tex`.
The parameter domain includes the unit-bearing boundary `d = 0`.
-/

namespace SkewJacobiNegative

/-- The standing integer parameter domain of the two families. -/
structure TenParameters where
  a : ℤ
  b : ℤ
  d : ℤ
  a_pos : 1 ≤ a
  d_nonneg : 0 ≤ d
  separated : a + d < b

/-- The two displayed representatives in each family. -/
inductive TenKind
  | fa | ha | fb | hb
  deriving DecidableEq

namespace TenParameters

variable (P : TenParameters)

/-- The four actual row beta lists, before the common addition of `d`. -/
def rowBase : TenKind → Fin 7 → ℤ
  | .fa => ![P.a + 6 * P.b, 6 * P.b, P.a + 5 * P.b, 5 * P.b,
      4 * P.b, P.a + 3 * P.b, 3 * P.b]
  | .ha => ![P.a + 6 * P.b, 6 * P.b, P.a + 5 * P.b, 5 * P.b,
      P.a + 4 * P.b, 4 * P.b, 2 * P.b]
  | .fb => ![P.a + 6 * P.b, 6 * P.b, P.a + 5 * P.b, 5 * P.b,
      P.a + 4 * P.b, P.a + 3 * P.b, 3 * P.b]
  | .hb => ![P.a + 6 * P.b, 6 * P.b, P.a + 5 * P.b, 5 * P.b,
      P.a + 4 * P.b, 4 * P.b, P.a + 2 * P.b]

/-- The common, normalized column beta list. -/
def column : Fin 7 → ℤ := ![6 * P.b, 5 * P.b, 4 * P.b, 3 * P.b, 2 * P.b, P.b, 0]

/-- The concrete seven-row diagram, with validity derived from the parameters. -/
def diagram (k : TenKind) : BetaDiagram 7 where
  row i := P.rowBase k i + P.d
  col := P.column
  row_strictAnti := by
    intro i j hij
    have ha := P.a_pos
    have hd := P.d_nonneg
    have hb := P.separated
    cases k <;> fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [rowBase]
    all_goals omega
  col_strictAnti := by
    intro i j hij
    have ha := P.a_pos
    have hd := P.d_nonneg
    have hb := P.separated
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [column]
    all_goals omega
  row_nonempty := by
    intro i
    have ha := P.a_pos
    have hd := P.d_nonneg
    have hb := P.separated
    cases k <;> fin_cases i
    all_goals norm_num [rowBase, column]
    all_goals omega

theorem connected (k : TenKind) : (P.diagram k).Connected := by
  refine ⟨by decide, ?_⟩
  intro i hi
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  cases k <;> fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [diagram, rowBase, column]
  all_goals omega

theorem normalized (k : TenKind) : (P.diagram k).Normalized := by
  intro hn
  norm_num [diagram, column]

/-- The displayed ordered row lengths, identified with the actual diagram. -/
theorem rowLengths_eq (k : TenKind) :
    (P.diagram k).rowLength = match k with
    | .fa => ![P.a + P.d, P.b + P.d, P.a + P.b + P.d, 2 * P.b + P.d,
        2 * P.b + P.d, P.a + 2 * P.b + P.d, 3 * P.b + P.d]
    | .ha => ![P.a + P.d, P.b + P.d, P.a + P.b + P.d, 2 * P.b + P.d,
        P.a + 2 * P.b + P.d, 3 * P.b + P.d, 2 * P.b + P.d]
    | .fb => ![P.a + P.d, P.b + P.d, P.a + P.b + P.d, 2 * P.b + P.d,
        P.a + 2 * P.b + P.d, P.a + 2 * P.b + P.d, 3 * P.b + P.d]
    | .hb => ![P.a + P.d, P.b + P.d, P.a + P.b + P.d, 2 * P.b + P.d,
        P.a + 2 * P.b + P.d, 3 * P.b + P.d, P.a + 2 * P.b + P.d] := by
  funext i
  cases k <;> fin_cases i <;>
    simp [BetaDiagram.rowLength, diagram, rowBase, column] <;> ring

/-- The profile gaps are overlap minus one, not intersection cardinalities. -/
theorem overlaps_eq (k : TenKind) :
    (fun j : Fin 6 => (P.diagram k).overlap j.castSucc
      (Nat.succ_lt_succ j.isLt)) = match k with
    | .fa => ![P.d, P.a + P.d, P.b + P.d, P.b + P.d,
        P.a + P.b + P.d, 2 * P.b + P.d]
    | .ha => ![P.d, P.a + P.d, P.b + P.d, P.a + P.b + P.d,
        2 * P.b + P.d, P.b + P.d]
    | .fb => ![P.d, P.a + P.d, P.b + P.d, P.a + P.b + P.d,
        P.a + P.b + P.d, 2 * P.b + P.d]
    | .hb => ![P.d, P.a + P.d, P.b + P.d, P.a + P.b + P.d,
        2 * P.b + P.d, P.a + P.b + P.d] := by
  funext i
  cases k <;> fin_cases i <;>
    simp [BetaDiagram.overlap, diagram, rowBase, column] <;> ring

/-- Counts in the original top-to-bottom order. -/
def rowCounts : TenKind → Fin 7 → ℕ
  | .fa | .fb => ![0, 0, 1, 1, 2, 3, 3]
  | .ha | .hb => ![0, 0, 1, 1, 2, 2, 4]

/-- Strict signs, including their behavior at `d = 0`, are read from the actual lists. -/
theorem negative_iff (k : TenKind) (i j : Fin 7) :
    (P.diagram k).row i < (P.diagram k).col j ↔ j.val < rowCounts k i := by
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [diagram, rowBase, column, rowCounts] <;> omega

theorem negativeRowCount_eq (k : TenKind) (i : Fin 7) :
    negativeRowCount (P.diagram k) i = rowCounts k i := by
  classical
  unfold negativeRowCount
  have hf : (Finset.univ.filter fun j => (P.diagram k).row i < (P.diagram k).col j) =
      Finset.univ.filter (fun j : Fin 7 => j.val < rowCounts k i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P.negative_iff]
  rw [hf]
  cases k <;> fin_cases i <;> decide

theorem negativePartition_eq (k : TenKind) :
    negativePartition (P.diagram k) =
      match k with
      | .fa | .fb => [3, 3, 2, 1, 1]
      | .ha | .hb => [4, 2, 2, 1, 1] := by
  have hr : negativeRowCount (P.diagram k) = rowCounts k := by
    funext i
    exact P.negativeRowCount_eq k i
  change ((List.ofFn (negativeRowCount (P.diagram k))).reverse).filter
    (fun r => decide (r ≠ 0)) = _
  rw [hr]
  cases k <;> decide

theorem rotated_negativePartition_eq (k : TenKind) :
    negativePartition (P.diagram k).rotate =
      match k with
      | .fa | .fb => [5, 3, 2]
      | .ha | .hb => [5, 3, 1, 1] := by
  let ρ : List ℕ := match k with
    | .fa | .fb => [5, 3, 2]
    | .ha | .hb => [5, 3, 1, 1]
  apply NegativePartitionTools.ext_getD
    (P.diagram k).rotate.negativePartition_isPartition.2
    (show ∀ r ∈ ρ, 0 < r by cases k <;> simp [ρ])
  intro j
  have h := (P.diagram k).rotate_partition_conjugate j
  rw [P.negativePartition_eq] at h
  rw [h]
  by_cases hj : j < 7
  · cases k <;> interval_cases j <;> norm_num [ρ]
  · have h2 : ¬ j < 2 := by omega
    have h3 : ¬ j < 3 := by omega
    have h4 : ¬ j < 4 := by omega
    have h5 : ¬ j < 5 := by omega
    have hj3 : 3 ≤ j := by omega
    have hj4 : 4 ≤ j := by omega
    cases k <;> simp [ρ, h2, h3, h4, h5, List.getD_eq_default, hj3, hj4] <;> omega

theorem negativeCount_eq_ten (k : TenKind) : negativeCount (P.diagram k) = 10 := by
  rw [← (P.diagram k).negativePartition_sum, P.negativePartition_eq]
  cases k <;> norm_num

theorem rotated_negativeCount_eq_ten (k : TenKind) :
    negativeCount (P.diagram k).rotate = 10 := by
  rw [← (P.diagram k).rotate.negativePartition_sum, P.rotated_negativePartition_eq]
  cases k <;> norm_num

theorem minimum_rows_eq_seven (k : TenKind) :
    minimumRealizingRows (negativePartition (P.diagram k)) = 7 := by
  rw [P.negativePartition_eq]
  cases k <;> decide

theorem rotated_minimum_rows_eq_seven (k : TenKind) :
    minimumRealizingRows (negativePartition (P.diagram k).rotate) = 7 := by
  rw [P.rotated_negativePartition_eq]
  cases k <;> decide

theorem area_eq (k : TenKind) :
    (P.diagram k).area =
      (match k with | .fa | .ha => 3 | .fb | .hb => 4) * P.a + 11 * P.b + 7 * P.d := by
  cases k <;> simp [BetaDiagram.area, diagram, rowBase, column, Fin.sum_univ_succ] <;> ring

theorem rotated_area_eq (k : TenKind) : (P.diagram k).rotate.area = (P.diagram k).area := by
  cases k <;>
    simp [BetaDiagram.area, BetaDiagram.rotate, diagram, rowBase, column,
      Fin.sum_univ_succ, Fin.rev] <;> ring

/-- A common beta at the boundary is exhibited, rather than discarded as a unit. -/
theorem zeroFree_iff (k : TenKind) : (P.diagram k).ZeroFree ↔ 0 < P.d := by
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  constructor
  · intro hz
    have h := hz 1 0
    simp only [diagram, rowBase, column] at h
    cases k <;> norm_num [rowBase, column] at h <;> omega
  · intro hd' i j
    cases k <;> fin_cases i <;> fin_cases j <;>
      norm_num [diagram, rowBase, column] <;> omega

theorem rotated_zeroFree_iff (k : TenKind) : (P.diagram k).rotate.ZeroFree ↔ 0 < P.d := by
  have he : (P.diagram k).rotate.ZeroFree ↔ (P.diagram k).ZeroFree := by
    constructor
    · intro h i j
      have hz := h j.rev i.rev
      simpa [BetaDiagram.rotate, ne_comm] using hz
    · intro h i j
      have hz := h j.rev i.rev
      simpa [BetaDiagram.rotate, ne_comm] using hz
  exact he.trans (P.zeroFree_iff k)

/-- Distinct representatives are not translates. -/
theorem not_translation (k l : TenKind) (hkl : k ≠ l) :
    ¬ (P.diagram k).TranslationEquivalent (P.diagram l) := by
  rintro ⟨c, hr, hc⟩
  have h0 := hc 6
  have h4 := hr 4
  have h6 := hr 6
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  cases k <;> cases l <;>
    norm_num [diagram, rowBase, column] at h0 h4 h6 hkl <;> omega

/-- Neither displayed representative is a rotation of any displayed representative.
Their top row has length `a+d`, while every possible reflected last row is longer. -/
theorem not_rotation (k l : TenKind) :
    ¬ (P.diagram k).RotationEquivalent (P.diagram l) := by
  rintro ⟨c, hr, hc⟩
  have h0 := hr 0
  have hc0 := hc 0
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  cases k <;> cases l <;>
    norm_num [diagram, rowBase, column, Fin.rev] at h0 hc0 <;> omega

/-- Distinctness between an unrotated representative and any rotated one. -/
theorem not_translation_to_rotate (k l : TenKind) :
    ¬ (P.diagram k).TranslationEquivalent (P.diagram l).rotate := by
  rintro ⟨c, hr, hc⟩
  apply P.not_rotation k l
  refine ⟨c, ?_, ?_⟩
  · intro i
    have h := hr i
    dsimp [BetaDiagram.rotate] at h
    linarith
  · intro i
    have h := hc i
    dsimp [BetaDiagram.rotate] at h
    linarith

theorem not_translation_from_rotate (k l : TenKind) :
    ¬ (P.diagram k).rotate.TranslationEquivalent (P.diagram l) := by
  rintro ⟨c, hr, hc⟩
  apply P.not_rotation k l
  refine ⟨-c, ?_, ?_⟩
  · intro i
    have h := hc i.rev
    dsimp [BetaDiagram.rotate] at h
    simp only [Fin.rev_rev] at h
    linarith
  · intro i
    have h := hr i.rev
    dsimp [BetaDiagram.rotate] at h
    simp only [Fin.rev_rev] at h
    linarith

theorem not_translation_both_rotate (k l : TenKind) (hkl : k ≠ l) :
    ¬ (P.diagram k).rotate.TranslationEquivalent (P.diagram l).rotate := by
  rintro ⟨c, hr, hc⟩
  apply P.not_translation k l hkl
  refine ⟨-c, ?_, ?_⟩
  · intro i
    have h := hc i.rev
    dsimp [BetaDiagram.rotate] at h
    simp only [Fin.rev_rev] at h
    linarith
  · intro i
    have h := hr i.rev
    dsimp [BetaDiagram.rotate] at h
    simp only [Fin.rev_rev] at h
    linarith

/-- All four members are distinct modulo translation.  Modulo rotation they
form two classes, not four: each starred member is its parent's rotation. -/
theorem quartet_pairwise_distinct (k l : TenKind) (hkl : k ≠ l) :
    [P.diagram k, (P.diagram k).rotate, P.diagram l, (P.diagram l).rotate].Pairwise
      (fun D E => ¬ D.TranslationEquivalent E) := by
  rw [List.pairwise_cons]
  constructor
  · intro E hE
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl
    · exact P.not_translation_to_rotate k k
    · exact P.not_translation k l hkl
    · exact P.not_translation_to_rotate k l
  · rw [List.pairwise_cons]
    constructor
    · intro E hE
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
      rcases hE with rfl | rfl
      · exact P.not_translation_from_rotate k l
      · exact P.not_translation_both_rotate k l hkl
    · rw [List.pairwise_cons]
      constructor
      · intro E hE
        simp only [List.mem_singleton] at hE
        subst E
        exact P.not_translation_to_rotate l l
      · simp

end TenParameters

/-- The original determinant matrices over arbitrary coefficients.
`u j` and `v j` stand for `h_(jb+d)` and `h_(a+jb+d)`. -/
def tenCoefficientMatrix {R : Type*} [Zero R] (u v : Fin 7 → R) :
    TenKind → Matrix (Fin 7) (Fin 7) R
  | .fa => ![
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6],
      ![u 0, u 1, u 2, u 3, u 4, u 5, u 6],
      ![0, v 0, v 1, v 2, v 3, v 4, v 5],
      ![0, u 0, u 1, u 2, u 3, u 4, u 5],
      ![0, 0, u 0, u 1, u 2, u 3, u 4],
      ![0, 0, 0, v 0, v 1, v 2, v 3],
      ![0, 0, 0, u 0, u 1, u 2, u 3]]
  | .ha => ![
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6],
      ![u 0, u 1, u 2, u 3, u 4, u 5, u 6],
      ![0, v 0, v 1, v 2, v 3, v 4, v 5],
      ![0, u 0, u 1, u 2, u 3, u 4, u 5],
      ![0, 0, v 0, v 1, v 2, v 3, v 4],
      ![0, 0, u 0, u 1, u 2, u 3, u 4],
      ![0, 0, 0, 0, u 0, u 1, u 2]]
  | .fb => ![
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6],
      ![u 0, u 1, u 2, u 3, u 4, u 5, u 6],
      ![0, v 0, v 1, v 2, v 3, v 4, v 5],
      ![0, u 0, u 1, u 2, u 3, u 4, u 5],
      ![0, 0, v 0, v 1, v 2, v 3, v 4],
      ![0, 0, 0, v 0, v 1, v 2, v 3],
      ![0, 0, 0, u 0, u 1, u 2, u 3]]
  | .hb => ![
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6],
      ![u 0, u 1, u 2, u 3, u 4, u 5, u 6],
      ![0, v 0, v 1, v 2, v 3, v 4, v 5],
      ![0, u 0, u 1, u 2, u 3, u 4, u 5],
      ![0, 0, v 0, v 1, v 2, v 3, v 4],
      ![0, 0, u 0, u 1, u 2, u 3, u 4],
      ![0, 0, 0, 0, v 0, v 1, v 2]]

/-- Finite Laplace expansion, with the coefficient-ring operations kept explicit. -/
def tenLaplace {R : Type*} [CommRing R] :
    (n : ℕ) → Matrix (Fin n) (Fin n) R → R
  | 0, _ => 1
  | n + 1, A => ∑ j : Fin (n + 1), (-1) ^ j.val * A 0 j *
      tenLaplace n (A.submatrix Fin.succ j.succAbove)

/-- The recursive expansion is the actual determinant at every order. -/
theorem tenLaplace_eq_det {R : Type*} [CommRing R]
    (n : ℕ) (A : Matrix (Fin n) (Fin n) R) : tenLaplace n A = A.det := by
  induction n with
  | zero => simp [tenLaplace, Matrix.det_fin_zero]
  | succ n ih =>
    rw [tenLaplace, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A polynomial identity on the actual seven-by-seven matrices.
This proof expands determinants in the coefficient ring and uses no localization. -/
theorem tenCoefficientMatrix_det_A {R : Type*} [CommRing R] (u v : Fin 7 → R) :
    (tenCoefficientMatrix u v .fa).det = (tenCoefficientMatrix u v .ha).det := by
  rw [← tenLaplace_eq_det, ← tenLaplace_eq_det]
  norm_num [tenLaplace, tenCoefficientMatrix, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  all_goals ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second universal polynomial identity, before any specialization. -/
theorem tenCoefficientMatrix_det_B {R : Type*} [CommRing R] (u v : Fin 7 → R) :
    (tenCoefficientMatrix u v .fb).det = (tenCoefficientMatrix u v .hb).det := by
  rw [← tenLaplace_eq_det, ← tenLaplace_eq_det]
  norm_num [tenLaplace, tenCoefficientMatrix, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  all_goals ring

namespace TenParameters
variable (P : TenParameters)

-- The finite entrywise proof has four times seven times seven branches.
set_option maxHeartbeats 2000000 in
/-- Entrywise identification retains every unit `h_0` when `d = 0`. -/
theorem matrix_eq (k : TenKind) :
    (P.diagram k).matrix = tenCoefficientMatrix
      (fun j => complete (j.val * P.b + P.d))
      (fun j => complete (P.a + j.val * P.b + P.d)) k := by
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  apply Matrix.ext
  intro i j
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [BetaDiagram.matrix, diagram, rowBase, column, tenCoefficientMatrix] <;>
    first
    | congr 1 <;> omega
    | apply complete_of_neg <;> omega

/-- Uniform equality in the original complete-generator ring, including `d = 0`. -/
theorem schur_eq_A : (P.diagram .fa).schur = (P.diagram .ha).schur := by
  unfold BetaDiagram.schur
  rw [P.matrix_eq, P.matrix_eq]
  exact tenCoefficientMatrix_det_A _ _

/-- Uniform equality for the second family. -/
theorem schur_eq_B : (P.diagram .fb).schur = (P.diagram .hb).schur := by
  unfold BetaDiagram.schur
  rw [P.matrix_eq, P.matrix_eq]
  exact tenCoefficientMatrix_det_B _ _

/-- Four Schur-equal actual diagrams in family A. -/
theorem quartet_A_schur :
    (P.diagram .fa).schur = (P.diagram .fa).rotate.schur ∧
    (P.diagram .fa).schur = (P.diagram .ha).schur ∧
    (P.diagram .fa).schur = (P.diagram .ha).rotate.schur := by
  exact ⟨(P.diagram .fa).rotate_schur.symm, P.schur_eq_A,
    P.schur_eq_A.trans (P.diagram .ha).rotate_schur.symm⟩

/-- Four Schur-equal actual diagrams in family B. -/
theorem quartet_B_schur :
    (P.diagram .fb).schur = (P.diagram .fb).rotate.schur ∧
    (P.diagram .fb).schur = (P.diagram .hb).schur ∧
    (P.diagram .fb).schur = (P.diagram .hb).rotate.schur := by
  exact ⟨(P.diagram .fb).rotate_schur.symm, P.schur_eq_B,
    P.schur_eq_B.trans (P.diagram .hb).rotate_schur.symm⟩

end TenParameters
end SkewJacobiNegative
