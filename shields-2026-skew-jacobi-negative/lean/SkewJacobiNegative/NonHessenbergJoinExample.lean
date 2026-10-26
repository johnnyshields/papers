/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.GeneralHessenberg

/-!
# A connected join outside the thick hypothesis

The explicit counterexample in `lem:staircase-minimum`.  Connectedness
does not supply the two strict joining inequalities.
-/
namespace SkewJacobiNegative.NonHessenbergJoinExample
open Gluing

/-- The connected three-row profile with both seams equal to one. -/
def source : Profile 2 where
  r := fun _ => 2
  g := fun _ => 1
  r_pos := by intro i; decide
  g_lt_castSucc := by intro i; decide
  g_lt_succ := by intro i; decide

def right : Profile 1 where
  r := fun _ => 2
  g := fun _ => 1
  r_pos := by intro i; decide
  g_lt_castSucc := by intro i; decide
  g_lt_succ := by intro i; decide

def merged : Profile 1 where
  r := ![2,3]
  g := fun _ => 1
  r_pos := by intro i; fin_cases i <;> decide
  g_lt_castSucc := by intro i; fin_cases i <;> decide
  g_lt_succ := by intro i; fin_cases i <;> decide

theorem connected : source.toBetaDiagram.Connected := source.toBetaDiagram_connected

theorem not_thick : ¬ Staircase.Thick source := by
  intro h
  have ht := h (0 : Fin 2) (1 : Fin 2) (by decide)
  norm_num [source] at ht

/-- Direct actual determinants give the stated nonzero defect. -/
theorem defect : source.toBetaDiagram.schur -
    (complete 2 * right.toBetaDiagram.schur - complete 1 * merged.toBetaDiagram.schur) =
      complete 3 ^ 2 - complete 2 * complete 4 := by
  unfold BetaDiagram.schur
  rw [Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [BetaDiagram.matrix, Profile.toBetaDiagram, Profile.xi, Profile.zeta,
    Fin.sum_univ_succ]
  norm_num [source, right, merged]
  ring

theorem defect_ne_zero : complete 3 ^ 2 - complete 2 * complete 4 ≠ 0 := by
  let ev : CompleteRing →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ)
    (fun v => if v.val = 3 then 1 else 0)
  intro h
  have he := congrArg ev h
  rw [complete_of_pos (by decide : 0 < (3 : ℤ)),
    complete_of_pos (by decide : 0 < (2 : ℤ)),
    complete_of_pos (by decide : 0 < (4 : ℤ))] at he
  norm_num [ev] at he

theorem joined_formula_fails : source.toBetaDiagram.schur ≠
    complete 2 * right.toBetaDiagram.schur - complete 1 * merged.toBetaDiagram.schur := by
  intro h
  have he := defect
  rw [h, sub_self] at he
  exact defect_ne_zero he.symm

end SkewJacobiNegative.NonHessenbergJoinExample
