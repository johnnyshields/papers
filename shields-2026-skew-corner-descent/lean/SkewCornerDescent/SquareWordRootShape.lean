/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordProfiles

/-!
# The only four-cell connected profile of span three

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Row positivity bounds the row count; the original overlap inequalities then
force the two-by-two square. No finite classification is assumed. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing
open scoped BigOperators

/-- The full original row intervals give the exact cell area. -/
theorem profile_actual_area {n : ℕ} (P : Profile n) :
    P.cells.card = ∑ i, P.r i := by
  rw [Profile.cells, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Int.card_Ico]
    have hi := P.xi_sub_zeta i
    omega
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    have h := congrArg Prod.fst (ha.trans hb.symm)
    change ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) at h
    apply hij
    apply Fin.ext
    exact_mod_cast h

/-- Area four and span three force the complete original square profile. -/
theorem four_cell_span_three_square {n : ℕ} (P : Profile n)
    (harea : ∑ i, P.r i = 4) (htop : P.xi 0 = 3) :
    n = 1 ∧ P.cells = square.cells := by
  have hbound : n + 1 ≤ ∑ i, P.r i := by
    calc
      n + 1 = ∑ _i : Fin (n + 1), (1 : ℕ) := by simp
      _ ≤ ∑ i, P.r i := Finset.sum_le_sum fun i _ => P.r_pos i
  rw [harea] at hbound
  have hn : n ≤ 3 := by omega
  interval_cases n
  · norm_num [Profile.xi, Profile.zeta, Fin.sum_univ_succ] at htop harea
    omega
  · have hg0 := P.g_lt_castSucc 0
    have hg1 := P.g_lt_succ 0
    norm_num [Profile.xi, Profile.zeta, Fin.sum_univ_succ] at htop harea hg0 hg1
    have hr0 : P.r 0 = 2 := by omega
    have hr1 : P.r 1 = 2 := by omega
    have hg : P.g 0 = 1 := by omega
    have he : P = square := by
      apply Profile.ext
      · funext i
        fin_cases i <;> simp [square, hr0, hr1]
      · funext i
        fin_cases i
        simp [square, hg]
    exact ⟨rfl, congrArg Profile.cells he⟩
  · have hp0 := P.r_pos 0
    have hp1 := P.r_pos 1
    have hp2 := P.r_pos 2
    have hg00 := P.g_lt_castSucc 0
    have hg01 := P.g_lt_succ 0
    have hg10 := P.g_lt_castSucc 1
    have hg11 := P.g_lt_succ 1
    norm_num [Profile.xi, Profile.zeta, Fin.sum_univ_succ] at htop harea hg00 hg01 hg10 hg11
    omega
  · have hp0 := P.r_pos 0
    have hp1 := P.r_pos 1
    have hp2 := P.r_pos 2
    have hp3 := P.r_pos 3
    have hg0 := P.g_lt_castSucc 0
    have hg1 := P.g_lt_castSucc 1
    have hg2 := P.g_lt_castSucc 2
    norm_num [Profile.xi, Profile.zeta, Fin.sum_univ_succ] at htop harea hg0 hg1 hg2
    omega

end SkewCornerDescent.SquareWordProfiles
