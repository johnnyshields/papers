/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.GeneralHessenberg
import SkewJacobiNegative.MinimumRowInvariant
import SkewJacobiNegative.BetaProfiles
import SkewJacobiNegative.TenNegativeFamilies

/-! # A six-row ribbon at the staircase minimum

The actual ribbons of `rem:ribbon-staircase`.  Their equality is a finite
symbolic Jacobi--Trudi expansion; no classification oracle is used.
-/
namespace SkewJacobiNegative.RibbonMinimumSixExample
open Gluing
set_option backward.isDefEq.respectTransparency false

structure Parameters where
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  different : a ≠ b

def F (p : Parameters) : Profile 5 where
  r := ![p.a, p.b, p.a, p.a+p.b, p.a+p.b, p.b]
  g := fun _ => 0
  r_pos := by
    intro i
    have := p.a_pos; have := p.b_pos
    fin_cases i <;> simp <;> omega
  g_lt_castSucc := by
    intro i
    have := p.a_pos; have := p.b_pos
    fin_cases i <;> simp <;> omega
  g_lt_succ := by
    intro i
    have := p.a_pos; have := p.b_pos
    fin_cases i <;> simp <;> omega

def H (p : Parameters) : Profile 5 where
  r := ![p.a, p.a+p.b, p.a+p.b, p.b, p.a, p.b]
  g := fun _ => 0
  r_pos := by
    intro i
    have := p.a_pos; have := p.b_pos
    fin_cases i <;> simp <;> omega
  g_lt_castSucc := by
    intro i
    have := p.a_pos; have := p.b_pos
    fin_cases i <;> simp <;> omega
  g_lt_succ := by
    intro i
    have := p.a_pos; have := p.b_pos
    fin_cases i <;> simp <;> omega

def first (p : Parameters) : BetaDiagram 6 := (F p).toBetaDiagram

def second (p : Parameters) : BetaDiagram 6 := (H p).toBetaDiagram

theorem first_connected (p : Parameters) : (first p).Connected :=
  (F p).toBetaDiagram_connected

theorem second_connected (p : Parameters) : (second p).Connected :=
  (H p).toBetaDiagram_connected

private theorem ribbon_mask (P : Profile 5) (hg : ∀ j, P.g j = 0)
    (i j : Fin 6) : P.toBetaDiagram.row i < P.toBetaDiagram.col j ↔
      j.val + 1 < i.val := by
  change P.xi i < P.zeta j ↔ _
  simp only [Profile.xi, Profile.zeta]
  have hp := P.r_pos
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, hg] <;>
    have h0 := hp 0 <;> have h1 := hp 1 <;> have h2 := hp 2 <;>
    have h3 := hp 3 <;> have h4 := hp 4 <;> have h5 := hp 5 <;> omega

private theorem ribbon_partition (P : Profile 5) (hg : ∀ j, P.g j = 0) :
    negativePartition P.toBetaDiagram = [4,3,2,1] := by
  classical
  have hc : negativeRowCount P.toBetaDiagram = ![0,0,1,2,3,4] := by
    funext i
    fin_cases i <;>
      simp only [negativeRowCount, ribbon_mask P hg] <;> decide
  simp [negativePartition, negativePaddedPartition, hc, List.ofFn_succ]

theorem first_partition (p : Parameters) : negativePartition (first p) = [4,3,2,1] :=
  ribbon_partition (F p) (by intro j; rfl)

theorem second_partition (p : Parameters) : negativePartition (second p) = [4,3,2,1] :=
  ribbon_partition (H p) (by intro j; rfl)

theorem first_negative_count (p : Parameters) : negativeCount (first p) = 10 := by
  rw [← BetaDiagram.negativePartition_sum, first_partition]
  decide

theorem second_negative_count (p : Parameters) : negativeCount (second p) = 10 := by
  rw [← BetaDiagram.negativePartition_sum, second_partition]
  decide

theorem first_minimum (p : Parameters) :
    minimumRealizingRows (negativePartition (first p)) = 6 := by
  rw [first_partition]
  decide

theorem second_minimum (p : Parameters) :
    minimumRealizingRows (negativePartition (second p)) = 6 := by
  rw [second_partition]
  decide

/-- The actual ribbon matrices with each positive interval sum kept as a generator. -/
def coefficientMatrix {R : Type*} [Zero R] [One R] (c : ℕ → ℕ → R) :
    Bool → Matrix (Fin 6) (Fin 6) R
  | false => ![
      ![c 1 0, c 1 1, c 2 1, c 3 2, c 4 3, c 4 4],
      ![1, c 0 1, c 1 1, c 2 2, c 3 3, c 3 4],
      ![0, 1, c 1 0, c 2 1, c 3 2, c 3 3],
      ![0, 0, 1, c 1 1, c 2 2, c 2 3],
      ![0, 0, 0, 1, c 1 1, c 1 2],
      ![0, 0, 0, 0, 1, c 0 1]]
  | true => ![
      ![c 1 0, c 2 1, c 3 2, c 3 3, c 4 3, c 4 4],
      ![1, c 1 1, c 2 2, c 2 3, c 3 3, c 3 4],
      ![0, 1, c 1 1, c 1 2, c 2 2, c 2 3],
      ![0, 0, 1, c 0 1, c 1 1, c 1 2],
      ![0, 0, 0, 1, c 1 0, c 1 1],
      ![0, 0, 0, 0, 1, c 0 1]]

-- Finite Laplace expansion acts on coefficient-ring scalars, not beta records.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem coefficient_det_eq {R : Type*} [CommRing R] (c : ℕ → ℕ → R) :
    (coefficientMatrix c false).det = (coefficientMatrix c true).det := by
  rw [← tenLaplace_eq_det, ← tenLaplace_eq_det]
  norm_num [tenLaplace, coefficientMatrix, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  all_goals ring

private theorem complete_zero_index (k : ℤ) (hk : k = 0) : complete k = 1 := by
  rw [hk, complete_zero]

private theorem first_matrix (p : Parameters) : (first p).matrix =
    coefficientMatrix (fun m n => complete ((m : ℤ)*p.a + (n : ℤ)*p.b)) false := by
  have ha := p.a_pos
  have hb := p.b_pos
  apply Matrix.ext
  intro i j
  change complete ((F p).xi i - (F p).zeta j) = _
  fin_cases i <;> fin_cases j
  all_goals norm_num [Profile.xi, Profile.zeta, F, coefficientMatrix,
    Fin.sum_univ_succ]
  all_goals first
    | congr 1 <;> omega
    | apply complete_of_neg <;> omega
    | apply complete_zero_index <;> omega

private theorem second_matrix (p : Parameters) : (second p).matrix =
    coefficientMatrix (fun m n => complete ((m : ℤ)*p.a + (n : ℤ)*p.b)) true := by
  have ha := p.a_pos
  have hb := p.b_pos
  apply Matrix.ext
  intro i j
  change complete ((H p).xi i - (H p).zeta j) = _
  fin_cases i <;> fin_cases j
  all_goals norm_num [Profile.xi, Profile.zeta, H, coefficientMatrix,
    Fin.sum_univ_succ]
  all_goals first
    | congr 1 <;> omega
    | apply complete_of_neg <;> omega
    | apply complete_zero_index <;> omega

/-- Uniform equality in the actual complete-generator polynomial ring. -/
theorem schur_eq (p : Parameters) : (first p).schur = (second p).schur := by
  unfold BetaDiagram.schur
  rw [first_matrix, second_matrix]
  exact coefficient_det_eq _

/-- Ordered row lengths exclude translation, and endpoint lengths exclude a half-turn. -/
theorem different_rotation_orbits (p : Parameters) :
    ¬ (first p).TranslationEquivalent (second p) ∧
    ¬ (first p).rotate.TranslationEquivalent (second p) := by
  constructor
  · intro he
    have hr := he.rowLength_eq (1 : Fin 6)
    change (F p).xi 1 - (F p).zeta 1 = (H p).xi 1 - (H p).zeta 1 at hr
    simp only [Profile.xi_sub_zeta] at hr
    simp [F, H] at hr
    have := p.a_pos
    omega
  · intro he
    have hr := he.rowLength_eq (0 : Fin 6)
    rw [BetaDiagram.rotate_rowLength] at hr
    change (F p).xi (Fin.rev 0) - (F p).zeta (Fin.rev 0) =
      (H p).xi 0 - (H p).zeta 0 at hr
    simp only [Profile.xi_sub_zeta] at hr
    norm_num [F, H, Fin.rev] at hr
    exact p.different hr.symm

/-- The staircase's least realizing order is six, not the seven-row regime. -/
theorem outside_minimum_seven (p : Parameters) :
    minimumRealizingRows (negativePartition (first p)) ≠ 7 ∧
    minimumRealizingRows (negativePartition (second p)) ≠ 7 := by
  rw [first_minimum, second_minimum]
  decide

end SkewJacobiNegative.RibbonMinimumSixExample
