/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FiveExceptionalFamilies
import SkewJacobiNegative.TenNegativeFamilies
import SkewJacobiNegative.MinimumRowInvariant
import SkewJacobiNegative.ComponentCuts

/-!
# Six-row boundary quartets

The actual lists, profiles, negative masks, and polynomial identities of
`prop:six-row-quartets`, `eq:six-row-list`, `eq:six-column-lists`, and
`eq:six-profiles` in `shields-2026-skew-jacobi-negative.tex`.
The domain includes `b = q`; no bound on the whole Schur class is asserted.
-/

namespace SkewJacobiNegative
namespace SixRowBoundary

/-- The same exact integer domain as the five-row construction. -/
abbrev Parameters := FiveExceptional.Parameters

/-- The six displayed representatives. -/
inductive Kind
  | f7 | h7 | f8 | h8 | f9 | h9
  deriving DecidableEq

/-- The three quartet families; the number records the negative budget. -/
inductive Family
  | seven | eight | nine
  deriving DecidableEq

def Family.f : Family → Kind
  | .seven => .f7 | .eight => .f8 | .nine => .f9

def Family.h : Family → Kind
  | .seven => .h7 | .eight => .h8 | .nine => .h9

def Kind.budget : Kind → ℕ
  | .f7 | .h7 => 7 | .f8 | .h8 => 8 | .f9 | .h9 => 9

namespace Parameters
variable (P : Parameters)

def s : ℤ := P.b - P.q

def a : ℤ := P.s + P.g

def bigB : ℤ := P.s + 2 * P.g

theorem s_nonneg : 0 ≤ P.s := by
  have := P.q_le_b
  dsimp [s]
  omega

/-- The shared row beta list in its manuscript order. -/
def rows : Fin 6 → ℤ :=
  ![P.b + 5 * P.g, P.b + 4 * P.g, P.b + 3 * P.g,
    P.b + 2 * P.g, P.b + P.g, P.b]

/-- The column lists are genuine coordinates, not labels for prescribed functions. -/
def cols : Kind → Fin 6 → ℤ
  | .f7 => ![3 * P.g + P.q, 2 * P.g, P.g + P.q, P.g, P.q, 0]
  | .h7 => ![3 * P.g, 2 * P.g + P.q, P.g + P.q, P.g, P.q, 0]
  | .f8 => ![4 * P.g + P.q, 2 * P.g + P.q, P.g + P.q, P.g, P.q, 0]
  | .h8 => ![3 * P.g + P.q, 2 * P.g + P.q, 2 * P.g, P.g + P.q, P.q, 0]
  | .f9 => ![4 * P.g + P.q, 3 * P.g + P.q, P.g + P.q, P.g, P.q, 0]
  | .h9 => ![3 * P.g + P.q, 3 * P.g, 2 * P.g + P.q, P.g + P.q, P.q, 0]

/-- Validity follows from `1 ≤ q ≤ b < g`, without strictness at `q = b`. -/
def diagram (k : Kind) : BetaDiagram 6 where
  row := P.rows
  col := P.cols k
  row_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    fin_cases i <;> fin_cases j <;> norm_num [rows] at * <;> omega
  col_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases k <;> fin_cases i <;> fin_cases j <;> norm_num [cols] at * <;> omega
  row_nonempty := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases k <;> fin_cases i <;> norm_num [rows, cols] <;> omega

theorem connected (k : Kind) : (P.diagram k).Connected := by
  have hstep : ∀ i : Fin 5, P.cols k i.castSucc ≤ P.rows i.succ := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases k <;> fin_cases i <;> norm_num [rows, cols] <;> omega
  refine ⟨by decide, ?_⟩
  intro i hi
  exact hstep ⟨i.val, by omega⟩

theorem normalized (k : Kind) : (P.diagram k).Normalized := by
  intro hn
  cases k <;> norm_num [diagram, cols]

/-- Signed row lengths in the exact order of `eq:six-profiles`. -/
def profileRows : Kind → Fin 6 → ℤ
  | .f7 => ![P.bigB, P.bigB + P.q, P.bigB, P.a + P.q, P.a, P.b]
  | .h7 => ![P.bigB + P.q, P.bigB, P.bigB, P.a + P.q, P.a, P.b]
  | .f8 => ![P.a, P.bigB, P.bigB, P.a + P.q, P.a, P.b]
  | .h8 => ![P.bigB, P.bigB, P.a + P.q, P.a, P.a, P.b]
  | .f9 => ![P.a, P.a, P.bigB, P.a + P.q, P.a, P.b]
  | .h9 => ![P.bigB, P.a + P.q, P.a, P.a, P.a, P.b]

/-- These are overlap minus one; a zero is a connected unit boundary. -/
def profileGaps : Kind → Fin 5 → ℤ
  | .f7 => ![P.a, P.a + P.q, P.a, P.b, P.s]
  | .h7 => ![P.a + P.q, P.a, P.a, P.b, P.s]
  | .f8 => ![P.s, P.a, P.a, P.b, P.s]
  | .h8 => ![P.a, P.a, P.b, P.s, P.s]
  | .f9 => ![P.s, P.s, P.a, P.b, P.s]
  | .h9 => ![P.a, P.b, P.s, P.s, P.s]

theorem rowLengths_eq (k : Kind) : (P.diagram k).rowLength = P.profileRows k := by
  funext i
  cases k <;> fin_cases i <;>
    norm_num [BetaDiagram.rowLength, diagram, rows, cols, profileRows, bigB, a, s] <;> ring

theorem overlaps_eq (k : Kind) :
    (fun i : Fin 5 => (P.diagram k).overlap i.castSucc
      (Nat.succ_lt_succ i.isLt)) = P.profileGaps k := by
  funext i
  cases k <;> fin_cases i <;>
    norm_num [BetaDiagram.overlap, diagram, rows, cols, profileGaps, bigB, a, s] <;> ring

/-- The displayed profile satisfies the manuscript domain, including `s = 0`. -/
theorem profile_domain (k : Kind) :
    (∀ i, 0 < P.profileRows k i) ∧
    (∀ i : Fin 5, 0 ≤ P.profileGaps k i ∧
      P.profileGaps k i < P.profileRows k i.castSucc ∧
      P.profileGaps k i < P.profileRows k i.succ) := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  constructor
  · intro i
    cases k <;> fin_cases i <;> norm_num [profileRows, bigB, a, s] <;> omega
  · intro i
    cases k <;> fin_cases i <;> norm_num [profileGaps, profileRows, bigB, a, s] <;> omega

/-- The natural profile is the existing actual-board producer. -/
def profile (k : Kind) : Gluing.Profile 5 :=
  (P.diagram k).toProfile (P.connected k)

theorem profile_r (k : Kind) :
    (P.profile k).r = fun i => (P.profileRows k i).toNat := by
  funext i
  change ((P.diagram k).row i - (P.diagram k).col (Fin.last 5) -
    ((P.diagram k).col i - (P.diagram k).col (Fin.last 5))).toNat = _
  have hr := congrFun (P.rowLengths_eq k) i
  dsimp only [BetaDiagram.rowLength] at hr
  congr 1
  omega

theorem profile_g (k : Kind) :
    (P.profile k).g = fun i => (P.profileGaps k i).toNat := by
  funext i
  change ((P.diagram k).row i.succ - (P.diagram k).col (Fin.last 5) -
    ((P.diagram k).col i.castSucc - (P.diagram k).col (Fin.last 5))).toNat = _
  have hg := congrFun (P.overlaps_eq k) i
  dsimp only [BetaDiagram.overlap] at hg
  change (P.diagram k).row i.succ - (P.diagram k).col i.castSucc =
    P.profileGaps k i at hg
  congr 1
  omega

/-- Both profile beta lists equal the actual displayed normalized coordinates. -/
theorem profile_beta (k : Kind) :
    (P.profile k).xi = P.rows ∧ (P.profile k).zeta = P.cols k := by
  have hr := (P.diagram k).toProfile_xi (P.connected k)
  have hc := (P.diagram k).toProfile_zeta (P.connected k)
  constructor
  · cases k <;> simpa [profile, diagram, cols] using hr
  · cases k <;> simpa [profile, diagram, cols] using hc

theorem profile_schur (k : Kind) : (P.profile k).schur = (P.diagram k).schur :=
  (P.diagram k).toProfile_schur (P.connected k)

/-- Top-to-bottom row counts, with no removal of a zero-index unit. -/
def rowCounts : Kind → Fin 6 → ℕ
  | .f7 | .h7 => ![0, 0, 0, 1, 2, 4]
  | .f8 => ![0, 0, 1, 1, 2, 4]
  | .h8 => ![0, 0, 0, 1, 3, 4]
  | .f9 => ![0, 0, 1, 2, 2, 4]
  | .h9 => ![0, 0, 0, 2, 3, 4]

theorem negative_iff (k : Kind) (i j : Fin 6) :
    (P.diagram k).row i < (P.diagram k).col j ↔ j.val < rowCounts k i := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [diagram, rows, cols, rowCounts] <;> omega

theorem negativeRowCount_eq (k : Kind) (i : Fin 6) :
    negativeRowCount (P.diagram k) i = rowCounts k i := by
  classical
  unfold negativeRowCount
  have he : (Finset.univ.filter fun j => (P.diagram k).row i < (P.diagram k).col j) =
      Finset.univ.filter (fun j : Fin 6 => j.val < rowCounts k i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P.negative_iff]
  rw [he]
  cases k <;> fin_cases i <;> decide

/-- The precise source table `eq:six-patterns`. -/
theorem negativePartition_eq (k : Kind) :
    negativePartition (P.diagram k) = match k with
    | .f7 | .h7 => [4, 2, 1]
    | .f8 => [4, 2, 1, 1]
    | .h8 => [4, 3, 1]
    | .f9 => [4, 2, 2, 1]
    | .h9 => [4, 3, 2] := by
  have hr : negativeRowCount (P.diagram k) = rowCounts k :=
    funext (P.negativeRowCount_eq k)
  change ((List.ofFn (negativeRowCount (P.diagram k))).reverse).filter
    (fun r => decide (r ≠ 0)) = _
  rw [hr]
  cases k <;> decide

theorem negativeCount_eq (k : Kind) : negativeCount (P.diagram k) = k.budget := by
  rw [← (P.diagram k).negativePartition_sum, P.negativePartition_eq]
  cases k <;> norm_num [Kind.budget]

theorem minimum_rows_eq_six (k : Kind) :
    minimumRealizingRows (negativePartition (P.diagram k)) = 6 := by
  rw [P.negativePartition_eq]
  cases k <;> decide

/-- Six is the least order of an actual connected realization, not a formal label. -/
theorem minimum_actual_rows (k : Kind) :
    IsLeast {n : ℕ | NegativeRealizable (negativePartition (P.diagram k)) n} 6 := by
  simpa only [P.minimum_rows_eq_six k] using
    (P.diagram k).minimumRealizingRows_actual_isLeast

theorem rotated_connected (k : Kind) : (P.diagram k).rotate.Connected :=
  (P.diagram k).rotate_connected (P.connected k)

theorem rotated_minimum_rows_eq_six (k : Kind) :
    minimumRealizingRows (negativePartition (P.diagram k).rotate) = 6 := by
  rw [(P.diagram k).rotate.minimumRealizingRows_eq_of_schur_eq (P.diagram k)
    (P.rotated_connected k) (P.connected k) (P.diagram k).rotate_schur,
    P.minimum_rows_eq_six]

/-- Rotation gives the conjugate masks, not an assumption that the source mask is invariant. -/
theorem rotated_negativePartition_eq (k : Kind) :
    negativePartition (P.diagram k).rotate = match k with
    | .f7 | .h7 => [3, 2, 1, 1]
    | .f8 => [4, 2, 1, 1]
    | .h8 => [3, 2, 2, 1]
    | .f9 => [4, 3, 1, 1]
    | .h9 => [3, 3, 2, 1] := by
  let ρ : List ℕ := match k with
    | .f7 | .h7 => [3, 2, 1, 1]
    | .f8 => [4, 2, 1, 1]
    | .h8 => [3, 2, 2, 1]
    | .f9 => [4, 3, 1, 1]
    | .h9 => [3, 3, 2, 1]
  apply NegativePartitionTools.ext_getD
    (P.diagram k).rotate.negativePartition_isPartition.2
    (show ∀ r ∈ ρ, 0 < r by cases k <;> simp [ρ])
  intro j
  have hh := (P.diagram k).rotate_partition_conjugate j
  rw [P.negativePartition_eq] at hh
  rw [hh]
  by_cases hj : j < 6
  · cases k <;> interval_cases j <;> norm_num [ρ]
  · have h1 : ¬ j < 1 := by omega
    have h2 : ¬ j < 2 := by omega
    have h3 : ¬ j < 3 := by omega
    have h4 : ¬ j < 4 := by omega
    have hj4 : 4 ≤ j := by omega
    cases k <;> simp [ρ, h1, h2, h3, h4, List.getD_eq_default, hj4]

theorem rotated_negativeCount_eq (k : Kind) :
    negativeCount (P.diagram k).rotate = k.budget := by
  rw [← (P.diagram k).rotate.negativePartition_sum, P.rotated_negativePartition_eq]
  cases k <;> norm_num [Kind.budget]

theorem rotated_minimum_actual_rows (k : Kind) :
    IsLeast {n : ℕ | NegativeRealizable (negativePartition (P.diagram k).rotate) n} 6 := by
  simpa only [P.rotated_minimum_rows_eq_six k] using
    (P.diagram k).rotate.minimumRealizingRows_actual_isLeast

/-- Different displayed column lists cannot be related by a common translation. -/
theorem not_translation (k l : Kind) (hkl : k ≠ l) :
    ¬ (P.diagram k).TranslationEquivalent (P.diagram l) := by
  rintro ⟨c, hr, hc⟩
  have hlast := hc 5
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases k <;> cases l <;>
    norm_num [diagram, cols] at hlast h0 h1 h2 hkl <;> omega

/-- Each first row is strictly longer than every displayed last row. -/
theorem not_rotation (k l : Kind) :
    ¬ (P.diagram k).RotationEquivalent (P.diagram l) := by
  rintro ⟨c, hr, hc⟩
  have h0 := hr 0
  have hc0 := hc 0
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases k <;> cases l <;>
    norm_num [diagram, rows, cols, Fin.rev] at h0 hc0 <;> omega

theorem not_translation_to_rotate (k l : Kind) :
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

theorem not_translation_from_rotate (k l : Kind) :
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

theorem not_translation_both_rotate (k l : Kind) (hkl : k ≠ l) :
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

/-- The quartet has four different translation classes, even at `b = q`. -/
theorem quartet_pairwise_distinct (f : Family) :
    [P.diagram f.f, (P.diagram f.f).rotate,
      P.diagram f.h, (P.diagram f.h).rotate].Pairwise
      (fun D E => ¬ D.TranslationEquivalent E) := by
  have hfh : f.f ≠ f.h := by cases f <;> decide
  rw [List.pairwise_cons]
  constructor
  · intro E hE
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl
    · exact P.not_translation_to_rotate f.f f.f
    · exact P.not_translation f.f f.h hfh
    · exact P.not_translation_to_rotate f.f f.h
  · rw [List.pairwise_cons]
    constructor
    · intro E hE
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
      rcases hE with rfl | rfl
      · exact P.not_translation_from_rotate f.f f.h
      · exact P.not_translation_both_rotate f.f f.h hfh
    · rw [List.pairwise_cons]
      constructor
      · intro E hE
        simp only [List.mem_singleton] at hE
        subst E
        exact P.not_translation_to_rotate f.h f.h
      · simp

end Parameters

section CoefficientIdentities
variable {R : Type*} [CommRing R]

/-- The nilpotent down-shift used in `eq:shift-identity`. -/
def downShift (z : Fin 6 → R) : Fin 6 → R := ![0, z 0, z 1, z 2, z 3, z 4]

theorem downShift_nilpotent (z : Fin 6 → R) :
    downShift (downShift (downShift (downShift (downShift (downShift z))))) = 0 := by
  funext i
  fin_cases i <;> norm_num [downShift]

/-- Replace a single actual matrix column by its shifted column. -/
def shiftedColumn (A : Matrix (Fin 6) (Fin 6) R) (j : Fin 6) :
    Matrix (Fin 6) (Fin 6) R :=
  fun i k => if k = j then downShift (fun t => A t j) i else A i k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace-zero determinant shift identity on arbitrary six-vectors.
Finite multilinearity is evaluated by Laplace expansion, independently of the beta parameters. -/
theorem shift_identity (A : Matrix (Fin 6) (Fin 6) R) :
    (∑ j : Fin 6, (shiftedColumn A j).det) = 0 := by
  simp_rw [← tenLaplace_eq_det]
  norm_num [tenLaplace, shiftedColumn, downShift, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  ring

/-- Lower Toeplitz columns truncated at six entries; all negative indices are zero. -/
def shiftedVector (u : Fin 6 → R) (j : ℕ) : Fin 6 → R :=
  fun i => if h : j ≤ i.val then u ⟨i.val - j, by omega⟩ else 0

/-- The six column words in the row-reversed determinant calculation. -/
def wordMatrix (u v : Fin 6 → R) : Kind → Matrix (Fin 6) (Fin 6) R
  | .f7 => fun i => ![shiftedVector v 3 i, shiftedVector u 2 i,
      shiftedVector v 1 i, shiftedVector u 1 i, v i, u i]
  | .h7 => fun i => ![shiftedVector u 3 i, shiftedVector v 2 i,
      shiftedVector v 1 i, shiftedVector u 1 i, v i, u i]
  | .f8 => fun i => ![shiftedVector v 4 i, shiftedVector v 2 i,
      shiftedVector v 1 i, shiftedVector u 1 i, v i, u i]
  | .h8 => fun i => ![shiftedVector v 3 i, shiftedVector v 2 i,
      shiftedVector u 2 i, shiftedVector v 1 i, v i, u i]
  | .f9 => fun i => ![shiftedVector v 4 i, shiftedVector v 3 i,
      shiftedVector v 1 i, shiftedVector u 1 i, v i, u i]
  | .h9 => fun i => ![shiftedVector v 3 i, shiftedVector u 3 i,
      shiftedVector v 2 i, shiftedVector v 1 i, v i, u i]

/-- The seed for seven negatives. -/
def seedSeven (u v : Fin 6 → R) : Matrix (Fin 6) (Fin 6) R :=
  fun i => ![shiftedVector v 2 i, shiftedVector u 2 i,
    shiftedVector v 1 i, shiftedVector u 1 i, v i, u i]

/-- The seed for eight negatives. -/
def seedEight (u v : Fin 6 → R) : Matrix (Fin 6) (Fin 6) R :=
  fun i => ![shiftedVector v 3 i, shiftedVector v 2 i,
    shiftedVector v 1 i, shiftedVector u 1 i, v i, u i]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Seven negatives: specialization of the nilpotent shift identity. -/
theorem word_det_seven (u v : Fin 6 → R) :
    (wordMatrix u v .f7).det = (wordMatrix u v .h7).det := by
  have hs := shift_identity (seedSeven u v)
  simp_rw [← tenLaplace_eq_det] at hs ⊢
  norm_num [tenLaplace, shiftedColumn, downShift, seedSeven, wordMatrix,
    shiftedVector, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove] at hs ⊢
  linear_combination hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Eight negatives: the same shift identity, with its distinct seed word. -/
theorem word_det_eight (u v : Fin 6 → R) :
    (wordMatrix u v .f8).det = (wordMatrix u v .h8).det := by
  have hs := shift_identity (seedEight u v)
  simp_rw [← tenLaplace_eq_det] at hs ⊢
  norm_num [tenLaplace, shiftedColumn, downShift, seedEight, wordMatrix, shiftedVector,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove] at hs ⊢
  linear_combination hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Nine negatives: a universal polynomial identity on the genuine Toeplitz columns.
This proves the localization-cleared identity without inverting `v 0`, and hence retains
all specializations, in particular the actual unit `h_0` when `b = q`. -/
theorem word_det_nine (u v : Fin 6 → R) :
    (wordMatrix u v .f9).det = (wordMatrix u v .h9).det := by
  rw [← tenLaplace_eq_det, ← tenLaplace_eq_det]
  norm_num [tenLaplace, wordMatrix, shiftedVector, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  ring

/-- The original row order, before the common row reversal. -/
def coefficientMatrix (u v : Fin 6 → R) (k : Kind) :
    Matrix (Fin 6) (Fin 6) R :=
  (wordMatrix u v k).submatrix Fin.revPerm (Equiv.refl (Fin 6))

/-- A common row permutation preserves equality of two determinants. -/
theorem coefficientMatrix_det (u v : Fin 6 → R) (f : Family) :
    (coefficientMatrix u v f.f).det = (coefficientMatrix u v f.h).det := by
  unfold coefficientMatrix
  change ((wordMatrix u v f.f).submatrix Fin.revPerm id).det =
    ((wordMatrix u v f.h).submatrix Fin.revPerm id).det
  rw [Matrix.det_permute, Matrix.det_permute]
  have h : (wordMatrix u v f.f).det = (wordMatrix u v f.h).det := by
    cases f
    · exact word_det_seven u v
    · exact word_det_eight u v
    · exact word_det_nine u v
  rw [h]

end CoefficientIdentities

namespace Parameters
variable (P : Parameters)

set_option maxHeartbeats 0 in
/-- The actual six-by-six matrix bridge, including all zero-index units. -/
theorem matrix_eq (k : Kind) :
    (P.diagram k).matrix = coefficientMatrix
      (fun i => complete (P.b + i.val * P.g))
      (fun i => complete (P.b + i.val * P.g - P.q)) k := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  apply Matrix.ext
  intro i j
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [BetaDiagram.matrix, diagram, rows, cols, coefficientMatrix,
      wordMatrix, shiftedVector, Matrix.submatrix, Fin.revPerm, Fin.rev] <;>
    first
    | congr 1 <;> omega
    | apply complete_of_neg <;> omega

/-- Uniform equality of the actual Schur polynomials in all three families. -/
theorem schur_eq (f : Family) : (P.diagram f.f).schur = (P.diagram f.h).schur := by
  unfold BetaDiagram.schur
  rw [P.matrix_eq, P.matrix_eq]
  exact coefficientMatrix_det _ _ f

theorem quartet_schur (f : Family) :
    (P.diagram f.f).schur = (P.diagram f.f).rotate.schur ∧
    (P.diagram f.f).schur = (P.diagram f.h).schur ∧
    (P.diagram f.f).schur = (P.diagram f.h).rotate.schur :=
  ⟨(P.diagram f.f).rotate_schur.symm, P.schur_eq f,
    (P.schur_eq f).trans (P.diagram f.h).rotate_schur.symm⟩

/-- The boundary parameter is realized as a literal unit matrix entry. -/
theorem unit_boundary (hq : P.b = P.q) (k : Kind) :
    (P.diagram k).matrix 5 4 = 1 := by
  cases k <;> simp [BetaDiagram.matrix, diagram, rows, cols, hq, complete_zero]

/-- Consecutive restrictions of the actual maximal-cofactor board. -/
def cornerIndex (t m : ℕ) (ht : t + m ≤ 5) (i : Fin m) : Fin 5 :=
  ⟨t + i.val, by omega⟩

/-- Every actual cut in the five-row complementary board, in zero-based order. -/
def cornerCuts : Kind → List ℕ
  | .f7 | .h7 => [3]
  | .f8 => [0, 3]
  | .h8 => [2, 3]
  | .f9 => [0, 1, 3]
  | .h9 => [1, 2, 3]

/-- This tests geometric beta cuts, not a factorization guessed from the polynomial. -/
theorem corner_cut_iff (k : Kind) (i : Fin 4) :
    (P.diagram k).row i.succ.succ < (P.diagram k).col i.castSucc.castSucc ↔
      i.val ∈ cornerCuts k := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases k <;> fin_cases i <;>
    norm_num [diagram, rows, cols, cornerCuts] <;> omega

/-- The complementary diagonal records the singleton lengths and the nonlinear cores. -/
theorem corner_diagonal (k : Kind) :
    (fun i : Fin 5 => (P.diagram k).row i.succ - (P.diagram k).col i.castSucc) =
      match k with
      | .f7 => ![P.a, P.a + P.q, P.a, P.b, P.s]
      | .h7 => ![P.a + P.q, P.a, P.a, P.b, P.s]
      | .f8 => ![P.s, P.a, P.a, P.b, P.s]
      | .h8 => ![P.a, P.a, P.b, P.s, P.s]
      | .f9 => ![P.s, P.s, P.a, P.b, P.s]
      | .h9 => ![P.a, P.b, P.s, P.s, P.s] := by
  funext i
  cases k <;> fin_cases i <;>
    norm_num [diagram, rows, cols, a, s] <;> ring

/-- With positive singleton lengths, the corner is itself an actual diagram.
At `s = 0` its matrix is retained instead; no empty row is relabeled connected. -/
def sourceCorner (k : Kind) (hs : 0 < P.s) : BetaDiagram 5 :=
  (P.diagram k).cornerDiagram (by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases k <;> fin_cases i <;>
      norm_num [diagram, rows, cols] <;> dsimp [s] at hs <;> omega)

theorem sourceCorner_cuts (k : Kind) (hs : 0 < P.s) (i : Fin 4) :
    (P.sourceCorner k hs).row i.succ < (P.sourceCorner k hs).col i.castSucc ↔
      i.val ∈ cornerCuts k :=
  P.corner_cut_iff k i

/-- Four-row source cores of the seven-negative family. -/
def coreSeven (endOpening : Bool) : BetaDiagram 4 where
  row := ![P.b + 4 * P.g, P.b + 3 * P.g, P.b + 2 * P.g, P.b + P.g]
  col := if endOpening then ![3 * P.g, 2 * P.g + P.q, P.g + P.q, P.g]
    else ![3 * P.g + P.q, 2 * P.g, P.g + P.q, P.g]
  row_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    fin_cases i <;> fin_cases j <;> norm_num at * <;> omega
  col_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases endOpening <;> fin_cases i <;> fin_cases j <;> norm_num at * <;> omega
  row_nonempty := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases endOpening <;> fin_cases i <;> norm_num <;> omega

/-- The actual three-row `K` in the maximal cofactors of family eight. -/
def coreEight : BetaDiagram 3 where
  row := ![P.b + 2 * P.g, P.b + P.g, P.b]
  col := ![P.g + P.q, P.q, 0]
  row_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    fin_cases i <;> fin_cases j <;> norm_num at * <;> omega
  col_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    fin_cases i <;> fin_cases j <;> norm_num at * <;> omega
  row_nonempty := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    fin_cases i <;> norm_num <;> omega

/-- The actual two-row `R = (A,b;s)` in family nine. -/
def coreNine : BetaDiagram 2 where
  row := ![P.b + P.g, P.b]
  col := ![P.q, 0]
  row_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    fin_cases i <;> fin_cases j <;> norm_num at * <;> omega
  col_strictAnti := by
    intro i j hij
    have := P.q_pos
    have := P.q_le_b
    fin_cases i <;> fin_cases j <;> norm_num at * <;> omega
  row_nonempty := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    fin_cases i <;> norm_num <;> omega

theorem coreSeven_connected (e : Bool) : (P.coreSeven e).Connected := by
  have hh : ∀ i : Fin 3, (P.coreSeven e).col i.castSucc ≤ (P.coreSeven e).row i.succ := by
    intro i
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    cases e <;> fin_cases i <;> norm_num [coreSeven] <;> omega
  exact ⟨by decide, fun i hi => hh ⟨i.val, by omega⟩⟩

theorem coreEight_connected : P.coreEight.Connected := by
  have hh : ∀ i : Fin 2, P.coreEight.col i.castSucc ≤ P.coreEight.row i.succ := by
    intro i
    have := P.q_le_b
    fin_cases i <;> norm_num [coreEight] <;> omega
  exact ⟨by decide, fun i hi => hh ⟨i.val, by omega⟩⟩

theorem coreNine_connected : P.coreNine.Connected := by
  have hstep : ∀ i : Fin 1, P.coreNine.col i.castSucc ≤ P.coreNine.row i.succ := by
    intro i
    fin_cases i
    simpa [coreNine] using P.q_le_b
  exact ⟨by decide, fun i hi => hstep ⟨i.val, by omega⟩⟩

theorem coreSeven_profile (e : Bool) :
    (P.coreSeven e).rowLength =
      (if e then ![P.a + P.q, P.a, P.a, P.b]
        else ![P.a, P.a + P.q, P.a, P.b]) ∧
    (fun i : Fin 3 => (P.coreSeven e).overlap i.castSucc
      (Nat.succ_lt_succ i.isLt)) =
      (if e then ![P.b, P.s, P.s] else ![P.s, P.b, P.s]) := by
  constructor <;> funext i
  · cases e <;> fin_cases i <;>
      norm_num [coreSeven, BetaDiagram.rowLength, a, s] <;> ring
  · cases e <;> fin_cases i <;>
      norm_num [coreSeven, BetaDiagram.overlap, a, s] <;> ring

theorem coreEight_profile :
    P.coreEight.rowLength = ![P.a, P.a, P.b] ∧
    (fun i : Fin 2 => P.coreEight.overlap i.castSucc
      (Nat.succ_lt_succ i.isLt)) = ![P.s, P.s] := by
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [coreEight, BetaDiagram.rowLength, BetaDiagram.overlap, a, s] <;> ring

theorem coreNine_profile :
    P.coreNine.rowLength = ![P.a, P.b] ∧
    P.coreNine.overlap 0 (by decide) = P.s := by
  constructor
  · funext i
    fin_cases i <;> norm_num [coreNine, BetaDiagram.rowLength, a, s] <;> ring
  · norm_num [coreNine, BetaDiagram.overlap, s]

theorem coreSeven_not_rotation :
    ¬ (P.coreSeven false).RotationEquivalent (P.coreSeven true) := by
  rintro ⟨c, hr, hc⟩
  have h0 := hr 0
  have hc0 := hc 0
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  norm_num [coreSeven, Fin.rev] at h0 hc0
  omega

theorem coreSeven_not_translation :
    ¬ (P.coreSeven false).TranslationEquivalent (P.coreSeven true) := by
  intro h
  have hr := h.rowLength_eq 0
  have := P.q_pos
  norm_num [coreSeven, BetaDiagram.rowLength] at hr
  omega

/-- The seven-negative cores are literal restrictions of the actual corner. -/
theorem coreSeven_matrix (e : Bool) :
    ((P.diagram (if e then .h7 else .f7)).cornerBoard.submatrix
      Fin.castSucc Fin.castSucc) = (P.coreSeven e).matrix := by
  ext i j
  cases e <;> fin_cases i <;> fin_cases j <;>
    norm_num [BetaDiagram.cornerBoard, betaBoard, Matrix.submatrix,
      BetaDiagram.matrix, diagram, rows, cols, coreSeven]

/-- The middle and initial three-row blocks are the same `K`, by common translation. -/
theorem coreEight_matrix (e : Bool) :
    ((P.diagram (if e then .h8 else .f8)).cornerBoard.submatrix
      (cornerIndex (if e then 0 else 1) 3 (by cases e <;> decide))
      (cornerIndex (if e then 0 else 1) 3 (by cases e <;> decide))) =
      P.coreEight.matrix := by
  ext i j
  cases e <;> fin_cases i <;> fin_cases j <;>
    norm_num [BetaDiagram.cornerBoard, betaBoard, Matrix.submatrix,
      BetaDiagram.matrix, diagram, rows, cols, coreEight, cornerIndex] <;>
    congr 1 <;> ring

/-- Family nine has an actual two-row block in positions 2--3 or 0--1. -/
theorem coreNine_matrix (e : Bool) :
    ((P.diagram (if e then .h9 else .f9)).cornerBoard.submatrix
      (cornerIndex (if e then 0 else 2) 2 (by cases e <;> decide))
      (cornerIndex (if e then 0 else 2) 2 (by cases e <;> decide))) =
      P.coreNine.matrix := by
  ext i j
  cases e <;> fin_cases i <;> fin_cases j <;>
    norm_num [BetaDiagram.cornerBoard, betaBoard, Matrix.submatrix,
      BetaDiagram.matrix, diagram, rows, cols, coreNine, cornerIndex] <;>
    congr 1 <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The seven-negative maximal cofactor is its genuine four-row core times `h_s`. -/
theorem corner_seven_factor (e : Bool) :
    (P.diagram (if e then .h7 else .f7)).cornerPolynomial =
      (P.coreSeven e).schur * complete P.s := by
  unfold BetaDiagram.cornerPolynomial BetaDiagram.schur
  rw [← P.coreSeven_matrix e]
  change ((P.diagram (if e then .h7 else .f7)).matrix.submatrix
      Fin.succ Fin.castSucc).det =
    (((P.diagram (if e then .h7 else .f7)).matrix.submatrix
      Fin.succ Fin.castSucc).submatrix Fin.castSucc Fin.castSucc).det * complete P.s
  simp_rw [P.matrix_eq]
  simp_rw [← tenLaplace_eq_det]
  cases e <;>
    norm_num [tenLaplace, coefficientMatrix, wordMatrix, shiftedVector,
      Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, Fin.revPerm, Fin.rev, s] <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- At `s = 0` the two singleton factors remain actual units, not fictitious components. -/
theorem corner_eight_factor (e : Bool) :
    (P.diagram (if e then .h8 else .f8)).cornerPolynomial =
      complete P.s ^ 2 * P.coreEight.schur := by
  unfold BetaDiagram.cornerPolynomial BetaDiagram.schur
  rw [← P.coreEight_matrix e]
  change ((P.diagram (if e then .h8 else .f8)).matrix.submatrix
      Fin.succ Fin.castSucc).det =
    complete P.s ^ 2 * (((P.diagram (if e then .h8 else .f8)).matrix.submatrix
      Fin.succ Fin.castSucc).submatrix
      (cornerIndex (if e then 0 else 1) 3 (by cases e <;> decide))
      (cornerIndex (if e then 0 else 1) 3 (by cases e <;> decide))).det
  simp_rw [P.matrix_eq]
  simp_rw [← tenLaplace_eq_det]
  cases e <;>
    norm_num [tenLaplace, coefficientMatrix, wordMatrix, shiftedVector, cornerIndex,
      Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, Fin.revPerm, Fin.rev, s] <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Four genuine corner blocks in family nine give three singleton factors and `R`. -/
theorem corner_nine_factor (e : Bool) :
    (P.diagram (if e then .h9 else .f9)).cornerPolynomial =
      complete P.s ^ 3 * P.coreNine.schur := by
  unfold BetaDiagram.cornerPolynomial BetaDiagram.schur
  rw [← P.coreNine_matrix e]
  change ((P.diagram (if e then .h9 else .f9)).matrix.submatrix
      Fin.succ Fin.castSucc).det =
    complete P.s ^ 3 * (((P.diagram (if e then .h9 else .f9)).matrix.submatrix
      Fin.succ Fin.castSucc).submatrix
      (cornerIndex (if e then 0 else 2) 2 (by cases e <;> decide))
      (cornerIndex (if e then 0 else 2) 2 (by cases e <;> decide))).det
  simp_rw [P.matrix_eq]
  simp_rw [← tenLaplace_eq_det]
  cases e <;>
    norm_num [tenLaplace, coefficientMatrix, wordMatrix, shiftedVector, cornerIndex,
      Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, Fin.revPerm, Fin.rev, s] <;> ring

theorem corner_eight_coefficient (e : Bool) :
    (P.diagram (if e then .h8 else .f8)).cornerCoefficient =
      -(complete P.s ^ 2 * P.coreEight.schur) := by
  rw [BetaDiagram.cornerCoefficient, P.corner_eight_factor]
  norm_num

theorem corner_nine_coefficient (e : Bool) :
    (P.diagram (if e then .h9 else .f9)).cornerCoefficient =
      -(complete P.s ^ 3 * P.coreNine.schur) := by
  rw [BetaDiagram.cornerCoefficient, P.corner_nine_factor]
  norm_num

theorem coreSeven_negative_iff (e : Bool) (i j : Fin 4) :
    (P.coreSeven e).row i < (P.coreSeven e).col j ↔
      (i = 2 ∧ j = 0) ∨ (i = 3 ∧ (j = 0 ∨ j = 1)) := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases e <;> fin_cases i <;> fin_cases j <;> norm_num [coreSeven] <;> omega

theorem coreSeven_negativePartition (e : Bool) :
    negativePartition (P.coreSeven e) = [2, 1] := by
  have hc : negativeRowCount (P.coreSeven e) = ![0, 0, 1, 2] := by
    funext i
    unfold negativeRowCount
    simp only [P.coreSeven_negative_iff]
    fin_cases i <;> decide
  change ((List.ofFn (negativeRowCount (P.coreSeven e))).reverse).filter
    (fun r => decide (r ≠ 0)) = _
  rw [hc]
  decide

/-- The actual four-row cores themselves are Schur-equal nonmotion mates. -/
theorem coreSeven_schur_eq : (P.coreSeven false).schur = (P.coreSeven true).schur := by
  have hh := (P.diagram .f7).cornerPolynomial_eq_of_schur_eq (P.diagram .h7)
    (P.connected .f7) (P.connected .h7) (P.schur_eq .seven)
  have hf := P.corner_seven_factor false
  have hg := P.corner_seven_factor true
  simp only [Bool.false_eq_true, if_false, if_true] at hf hg
  rw [hf, hg] at hh
  exact mul_right_cancel₀ ((complete_ne_zero_iff _).mpr P.s_nonneg) hh

private theorem connected_of_steps {n : ℕ} (D : BetaDiagram (n + 1))
    (h : ∀ i : Fin n, D.col i.castSucc ≤ D.row i.succ) : D.Connected :=
  ⟨by omega, fun i hi => h ⟨i.val, by omega⟩⟩

/-- The source components are produced by literal restrictions at the actual cuts.
The positive-singleton guard belongs only to this geometric component statement;
all determinant identities above retain the full `s = 0` boundary. -/
def sourceDecomposition (k : Kind) (hs : 0 < P.s) :
    BetaDiagram.ComponentDecomposition (P.sourceCorner k hs) := by
  refine match k with
    | .f7 => BetaDiagram.ComponentDecomposition.cut (a := 4) (b := 1)
        _ (by decide) (by decide) rfl ?_ (.connected _ ?_) (.connected _ ?_)
    | .h7 => BetaDiagram.ComponentDecomposition.cut (a := 4) (b := 1)
        _ (by decide) (by decide) rfl ?_ (.connected _ ?_) (.connected _ ?_)
    | .f8 => BetaDiagram.ComponentDecomposition.cut (a := 1) (b := 4)
        _ (by decide) (by decide) rfl ?_ (.connected _ ?_)
        (BetaDiagram.ComponentDecomposition.cut (a := 3) (b := 1)
          _ (by decide) (by decide) rfl ?_ (.connected _ ?_) (.connected _ ?_))
    | .h8 => BetaDiagram.ComponentDecomposition.cut (a := 3) (b := 2)
        _ (by decide) (by decide) rfl ?_ (.connected _ ?_)
        (BetaDiagram.ComponentDecomposition.cut (a := 1) (b := 1)
          _ (by decide) (by decide) rfl ?_ (.connected _ ?_) (.connected _ ?_))
    | .f9 => BetaDiagram.ComponentDecomposition.cut (a := 1) (b := 4)
        _ (by decide) (by decide) rfl ?_ (.connected _ ?_)
        (BetaDiagram.ComponentDecomposition.cut (a := 1) (b := 3)
          _ (by decide) (by decide) rfl ?_ (.connected _ ?_)
          (BetaDiagram.ComponentDecomposition.cut (a := 2) (b := 1)
            _ (by decide) (by decide) rfl ?_ (.connected _ ?_) (.connected _ ?_)))
    | .h9 => BetaDiagram.ComponentDecomposition.cut (a := 2) (b := 3)
        _ (by decide) (by decide) rfl ?_ (.connected _ ?_)
        (BetaDiagram.ComponentDecomposition.cut (a := 1) (b := 2)
          _ (by decide) (by decide) rfl ?_ (.connected _ ?_)
          (BetaDiagram.ComponentDecomposition.cut (a := 1) (b := 1)
            _ (by decide) (by decide) rfl ?_ (.connected _ ?_) (.connected _ ?_)))
  all_goals try apply connected_of_steps
  all_goals try intro i
  all_goals try fin_cases i
  all_goals
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    dsimp [s] at hs
    norm_num [sourceCorner, BetaDiagram.cornerDiagram, BetaDiagram.reindexOrder,
      BetaDiagram.betaPrefix, BetaDiagram.suffix, diagram, rows, cols, Fin.cast,
      Fin.addNat, Fin.natAdd, Fin.castAdd, Fin.castLE] <;> omega

/-- Exact ordered component sizes: the nine-negative corners have four, not three. -/
theorem source_component_rows (k : Kind) (hs : 0 < P.s) :
    ((P.sourceDecomposition k hs).components.map Sigma.fst) = match k with
      | .f7 | .h7 => [4, 1]
      | .f8 => [1, 3, 1]
      | .h8 => [3, 1, 1]
      | .f9 => [1, 1, 2, 1]
      | .h9 => [2, 1, 1, 1] := by
  cases k <;> rfl

/-- Ordered row lengths of the actual connected leaves, not prescribed component names. -/
theorem source_component_lengths (k : Kind) (hs : 0 < P.s) :
    ((P.sourceDecomposition k hs).components.map
      (fun D => List.ofFn D.2.rowLength)) = match k with
      | .f7 => [[P.a, P.a + P.q, P.a, P.b], [P.s]]
      | .h7 => [[P.a + P.q, P.a, P.a, P.b], [P.s]]
      | .f8 => [[P.s], [P.a, P.a, P.b], [P.s]]
      | .h8 => [[P.a, P.a, P.b], [P.s], [P.s]]
      | .f9 => [[P.s], [P.s], [P.a, P.b], [P.s]]
      | .h9 => [[P.a, P.b], [P.s], [P.s], [P.s]] := by
  cases k <;>
    norm_num [sourceDecomposition, BetaDiagram.ComponentDecomposition.components,
      sourceCorner, BetaDiagram.cornerDiagram, BetaDiagram.reindexOrder,
      BetaDiagram.betaPrefix, BetaDiagram.suffix, diagram, rows, cols, Fin.cast,
      Fin.addNat, Fin.natAdd, Fin.castAdd, Fin.castLE, BetaDiagram.rowLength,
      List.ofFn_succ, a, s] <;> ring_nf <;> simp <;> ring

/-- The combined lower-inclusion statement; it carries no exhaustion premise. -/
theorem six_row_quartets (f : Family) :
    (P.diagram f.f).Connected ∧ (P.diagram f.h).Connected ∧
    (P.diagram f.f).rotate.Connected ∧ (P.diagram f.h).rotate.Connected ∧
    minimumRealizingRows (negativePartition (P.diagram f.f)) = 6 ∧
    minimumRealizingRows (negativePartition (P.diagram f.h)) = 6 ∧
    [P.diagram f.f, (P.diagram f.f).rotate,
      P.diagram f.h, (P.diagram f.h).rotate].Pairwise
      (fun D E => ¬ D.TranslationEquivalent E) ∧
    (P.diagram f.f).schur = (P.diagram f.f).rotate.schur ∧
    (P.diagram f.f).schur = (P.diagram f.h).schur ∧
    (P.diagram f.f).schur = (P.diagram f.h).rotate.schur :=
  ⟨P.connected _, P.connected _, P.rotated_connected _, P.rotated_connected _,
    P.minimum_rows_eq_six _, P.minimum_rows_eq_six _,
    P.quartet_pairwise_distinct _, P.quartet_schur _⟩

end Parameters
end SixRowBoundary
end SkewJacobiNegative
