/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationMarkedCells

/-!
# Actual connected complements of the general end-row marks

Hypothesis III in `prop:saturation-chart` of
`shields-2026-skew-class-inflation.tex`.  Removing a mark shortens
exactly its original endpoint row.  The standing strict endpoint bounds
preserve every adjacent overlap and make both resulting profiles valid.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewGluing

variable (A : SaturationInner)

private theorem lower_trim_above_gap (i : Fin (A.k + 1)) :
    A.c < if i.val = A.k then A.r i - A.d else A.r i := by
  split_ifs with hi
  · have he : i = Fin.last A.k := Fin.ext hi
    rw [he]
    have hb := A.last_bound
    omega
  · exact A.row_above_gap i

private theorem upper_trim_above_gap (i : Fin (A.k + 1)) :
    A.c < if i.val = 0 then A.r i - A.d else A.r i := by
  split_ifs with hi
  · have he : i = 0 := Fin.ext hi
    rw [he]
    have ha := A.first_bound
    omega
  · exact A.row_above_gap i

/-- The normalized profile left by shortening the original last row by the actual mark length. -/
def removedLowerProfile : Profile A.k where
  r i := if i.val = A.k then A.r i - A.d else A.r i
  g _ := A.c
  r_pos i := (Nat.zero_le A.c).trans_lt (A.lower_trim_above_gap i)
  g_lt_castSucc j := A.lower_trim_above_gap j.castSucc
  g_lt_succ j := A.lower_trim_above_gap j.succ

/-- The normalized profile left by shortening the original first row by the actual mark length. -/
def removedUpperProfile : Profile A.k where
  r i := if i.val = 0 then A.r i - A.d else A.r i
  g _ := A.c
  r_pos i := (Nat.zero_le A.c).trans_lt (A.upper_trim_above_gap i)
  g_lt_castSucc j := A.upper_trim_above_gap j.castSucc
  g_lt_succ j := A.upper_trim_above_gap j.succ

/-- Exact beta coordinates of the actual shortened-last-row profile. -/
theorem removedLowerProfile_beta :
    A.removedLowerProfile.xi = (fun i => A.profile.xi i - (A.d : ℤ)) ∧
      A.removedLowerProfile.zeta =
        (fun i => if i.val = A.k then 0 else A.profile.zeta i - (A.d : ℤ)) := by
  have hh := A.removedLowerProfile.eq_beta_of_equations
    (x := fun i => A.profile.xi i - (A.d : ℤ))
    (z := fun i => if i.val = A.k then 0 else A.profile.zeta i - (A.d : ℤ))
    (by simp only [Fin.val_last, ite_true])
    (by
      intro i
      have hrow := A.profile.xi_sub_zeta i
      change A.profile.xi i - A.profile.zeta i = (A.r i : ℤ) at hrow
      by_cases hi : i.val = A.k
      · have he : i = Fin.last A.k := Fin.ext hi
        rw [he, A.profile.zeta_last] at hrow
        have hd : A.d ≤ A.r i := by rw [he]; have := A.last_bound; omega
        change A.profile.xi i - A.d - (if i.val = A.k then 0 else _) =
          ((if i.val = A.k then A.r i - A.d else A.r i : ℕ) : ℤ)
        simp only [ite_eq_left hi, Nat.cast_sub hd]
        rw [he]
        omega
      · change A.profile.xi i - A.d - (if i.val = A.k then 0 else _) =
          ((if i.val = A.k then A.r i - A.d else A.r i : ℕ) : ℤ)
        simp only [ite_eq_right hi]
        omega)
    (by
      intro j
      have hj : j.castSucc.val ≠ A.k := by
        have := j.isLt
        simpa only [Fin.val_castSucc] using ne_of_lt this
      have hg := A.profile.xi_succ_sub_zeta_castSucc j
      change A.profile.xi j.succ - A.profile.zeta j.castSucc = (A.c : ℤ) at hg
      simp only [ite_eq_right hj]
      change A.profile.xi j.succ - A.d - (A.profile.zeta j.castSucc - A.d) = (A.c : ℤ)
      omega)
  exact ⟨hh.1.symm, hh.2.symm⟩

/-- Exact beta coordinates of the actual shortened-first-row profile. -/
theorem removedUpperProfile_beta :
    A.removedUpperProfile.xi =
        (fun i => if i.val = 0 then A.profile.xi i - (A.d : ℤ) else A.profile.xi i) ∧
      A.removedUpperProfile.zeta = A.profile.zeta := by
  have hh := A.removedUpperProfile.eq_beta_of_equations
    (x := fun i => if i.val = 0 then A.profile.xi i - (A.d : ℤ) else A.profile.xi i)
    (z := A.profile.zeta) A.profile.zeta_last
    (by
      intro i
      have hrow := A.profile.xi_sub_zeta i
      change A.profile.xi i - A.profile.zeta i = (A.r i : ℤ) at hrow
      by_cases hi : i.val = 0
      · have he : i = 0 := Fin.ext hi
        have hd : A.d ≤ A.r i := by rw [he]; have := A.first_bound; omega
        change (if i.val = 0 then A.profile.xi i - A.d else _) - A.profile.zeta i =
          ((if i.val = 0 then A.r i - A.d else A.r i : ℕ) : ℤ)
        simp only [ite_eq_left hi, Nat.cast_sub hd]
        omega
      · change (if i.val = 0 then A.profile.xi i - A.d else _) - A.profile.zeta i =
          ((if i.val = 0 then A.r i - A.d else A.r i : ℕ) : ℤ)
        simp only [ite_eq_right hi]
        exact hrow)
    (by
      intro j
      have hj : j.succ.val ≠ 0 := by change j.val + 1 ≠ 0; omega
      simp only [ite_eq_right hj]
      exact A.profile.xi_succ_sub_zeta_castSucc j)
  exact ⟨hh.1.symm, hh.2.symm⟩

/-- The actual lower-mark complement is the translated shortened-row profile, cell for cell. -/
theorem lower_mark_removal_cells : A.markedInner.E \ A.markedInner.W =
    translate (0, (A.d : ℤ) - A.k) (profileCells A.removedLowerProfile) := by
  ext ⟨a, b⟩
  rw [Finset.mem_sdiff]
  change ((a, b) ∈ A.innerCells ∧ (a, b) ∉ A.lowerMark) ↔ _
  rw [A.mem_innerCells, A.mem_lowerMark, mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero]
  rw [mem_profileCells, A.removedLowerProfile_beta.1, A.removedLowerProfile_beta.2]
  dsimp only
  constructor
  · rintro ⟨⟨i, hi, hlo, hhi⟩, hnot⟩
    refine ⟨i, hi, ?_, ?_⟩
    · by_cases hil : i.val = A.k
      · have he : i = Fin.last A.k := Fin.ext hil
        rw [ite_eq_left hil]
        rw [he, A.profile.zeta_last] at hlo
        simp only [Fin.val_last] at hlo
        omega
      · rw [ite_eq_right hil]
        omega
    · omega
  · rintro ⟨i, hi, hlo, hhi⟩
    by_cases hil : i.val = A.k
    · rw [ite_eq_left hil] at hlo
      have he : i = Fin.last A.k := Fin.ext hil
      refine ⟨⟨i, hi, ?_, by omega⟩, ?_⟩
      · rw [he, A.profile.zeta_last]
        simp only [Fin.val_last]
        omega
      · omega
    · rw [ite_eq_right hil] at hlo
      exact ⟨⟨i, hi, by omega, by omega⟩, by omega⟩

/-- The actual upper-mark complement is its valid shortened-row profile in the original origin. -/
theorem upper_mark_removal_cells : A.markedInner.E \ A.markedInner.upper =
    translate (0, -(A.k : ℤ)) (profileCells A.removedUpperProfile) := by
  ext ⟨a, b⟩
  rw [Finset.mem_sdiff]
  change ((a, b) ∈ A.innerCells ∧ (a, b) ∉ A.markedInner.upper) ↔ _
  rw [A.mem_innerCells, A.mem_upperMark, mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero]
  rw [mem_profileCells, A.removedUpperProfile_beta.1, A.removedUpperProfile_beta.2]
  dsimp only
  constructor
  · rintro ⟨⟨i, hi, hlo, hhi⟩, hnot⟩
    refine ⟨i, hi, by omega, ?_⟩
    by_cases hi0 : i.val = 0
    · rw [ite_eq_left hi0]
      have hxi : A.profile.xi i = A.profile.xi 0 := congrArg A.profile.xi (Fin.ext hi0)
      omega
    · rw [ite_eq_right hi0]
      omega
  · rintro ⟨i, hi, hlo, hhi⟩
    by_cases hi0 : i.val = 0
    · rw [ite_eq_left hi0] at hhi
      have hxi : A.profile.xi i = A.profile.xi 0 := congrArg A.profile.xi (Fin.ext hi0)
      exact ⟨⟨i, hi, by omega, by omega⟩, by omega⟩
    · rw [ite_eq_right hi0] at hhi
      exact ⟨⟨i, hi, by omega, by omega⟩, by omega⟩

/-- Hypothesis III holds for both actual finite marked complements. -/
theorem markedInner_removalsConnected : A.markedInner.RemovalsConnected := by
  constructor
  · rw [A.lower_mark_removal_cells]
    exact isConnectedSkew_translate _ (profileCells_connected _)
  · rw [A.upper_mark_removal_cells]
    exact isConnectedSkew_translate _ (profileCells_connected _)

end SkewClassInflation.SaturationInner
