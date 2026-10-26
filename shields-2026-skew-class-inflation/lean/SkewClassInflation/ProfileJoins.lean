/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SeamCoefficients

/-!
# Literal joins and mergers of connected profiles

Formalizes the profile operations preceding `eq:repeated-blocks` in
`shields-2026-skew-class-inflation.tex`.  Endpoint inequalities are the
actual connected-join domain; they are not substituted for the stronger
Hessenberg joining inequalities in determinant identities.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative
open SkewJacobiNegative.GeneralHessenberg

namespace Profile

variable {n m : ℕ}

/-- Concatenate the full ordered row words. -/
def joinRows (P : Profile n) (Q : Profile m) (i : Fin (n + m + 2)) : ℕ :=
  if h : i.val < n + 1 then P.r ⟨i.val, h⟩
  else Q.r ⟨i.val - (n + 1), by have := i.isLt; omega⟩

/-- Insert the distinguished joining gap between the two complete gap words. -/
def joinGaps (P : Profile n) (Q : Profile m) (d : ℕ) (j : Fin (n + m + 1)) : ℕ :=
  if h : j.val < n then P.g ⟨j.val, h⟩
  else if he : j.val = n then d
  else Q.g ⟨j.val - (n + 1), by have := j.isLt; omega⟩

@[simp] theorem joinRows_left (P : Profile n) (Q : Profile m) (i : Fin (n + 1)) :
    joinRows P Q ⟨i.val, by have := i.isLt; omega⟩ = P.r i := by
  simp only [joinRows, dite_eq_left i.isLt]

@[simp] theorem joinRows_right (P : Profile n) (Q : Profile m) (i : Fin (m + 1)) :
    joinRows P Q ⟨n + 1 + i.val, by have := i.isLt; omega⟩ = Q.r i := by
  rw [joinRows, dite_eq_right (by change ¬ n + 1 + i.val < n + 1; omega)]
  congr 1
  apply Fin.ext
  simp

@[simp] theorem joinGaps_left (P : Profile n) (Q : Profile m) (d : ℕ) (j : Fin n) :
    joinGaps P Q d ⟨j.val, by have := j.isLt; omega⟩ = P.g j := by
  simp only [joinGaps, dite_eq_left j.isLt]

@[simp] theorem joinGaps_middle (P : Profile n) (Q : Profile m) (d : ℕ) :
    joinGaps P Q d ⟨n, by omega⟩ = d := by simp [joinGaps]

@[simp] theorem joinGaps_right (P : Profile n) (Q : Profile m) (d : ℕ) (j : Fin m) :
    joinGaps P Q d ⟨n + 1 + j.val, by have := j.isLt; omega⟩ = Q.g j := by
  rw [joinGaps, dite_eq_right (by change ¬ n + 1 + j.val < n; omega),
    dite_eq_right (by change n + 1 + j.val ≠ n; omega)]
  congr 1
  apply Fin.ext
  simp

/-- Join two literal profiles across one admissible seam. -/
def join (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) : Profile (n + m + 1) where
  r := joinRows P Q
  g := joinGaps P Q d
  r_pos i := by
    unfold joinRows
    split_ifs <;> first | exact P.r_pos _ | exact Q.r_pos _
  g_lt_castSucc j := by
    by_cases hj : j.val < n
    · have h := P.g_lt_castSucc ⟨j.val, hj⟩
      change P.g ⟨j.val, hj⟩ < P.r ⟨j.val, by omega⟩ at h
      simpa only [joinGaps, dite_eq_left hj, joinRows, Fin.val_castSucc,
        dite_eq_left (show j.val < n + 1 by omega)] using h
    · by_cases he : j.val = n
      · have hjn : j = (⟨n, by omega⟩ : Fin (n + m + 1)) := Fin.ext he
        rw [hjn]
        rw [joinGaps_middle]
        change d < joinRows P Q ⟨n, by omega⟩
        have hrow := joinRows_left P Q (Fin.last n)
        change joinRows P Q ⟨n, by omega⟩ = P.r (Fin.last n) at hrow
        rw [hrow]
        exact hP
      · have hjm : j.val - (n + 1) < m := by have := j.isLt; omega
        have h := Q.g_lt_castSucc ⟨j.val - (n + 1), hjm⟩
        change Q.g ⟨j.val - (n + 1), hjm⟩ < Q.r ⟨j.val - (n + 1), by omega⟩ at h
        simpa only [joinGaps, dite_eq_right hj, dite_eq_right he, joinRows,
          Fin.val_castSucc, dite_eq_right (show ¬ j.val < n + 1 by omega)] using h
  g_lt_succ j := by
    by_cases hj : j.val < n
    · have h := P.g_lt_succ ⟨j.val, hj⟩
      change P.g ⟨j.val, hj⟩ < P.r ⟨j.val + 1, by omega⟩ at h
      simpa only [joinGaps, dite_eq_left hj, joinRows, Fin.val_succ,
        dite_eq_left (show j.val + 1 < n + 1 by omega)] using h
    · by_cases he : j.val = n
      · have hjn : j = (⟨n, by omega⟩ : Fin (n + m + 1)) := Fin.ext he
        rw [hjn]
        have hrow : joinRows P Q (⟨n, by omega⟩ : Fin (n + m + 1)).succ = Q.r 0 := by
          change joinRows P Q ⟨n + 1, by omega⟩ = Q.r 0
          simpa only [Fin.val_zero, Nat.add_zero] using joinRows_right P Q (0 : Fin (m + 1))
        rw [joinGaps_middle, hrow]
        exact hQ
      · have hjm : j.val - (n + 1) < m := by have := j.isLt; omega
        have h := Q.g_lt_succ ⟨j.val - (n + 1), hjm⟩
        have hi : (⟨j.val + 1 - (n + 1), by have := j.isLt; omega⟩ : Fin (m + 1)) =
            (⟨j.val - (n + 1), hjm⟩ : Fin m).succ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
        simpa only [joinGaps, dite_eq_right hj, dite_eq_right he, joinRows,
          Fin.val_succ, dite_eq_right (show ¬ j.val + 1 < n + 1 by omega), hi] using h

/-- The ordinary connected zero join needs no extra domain assumptions. -/
def zeroJoin (P : Profile n) (Q : Profile m) : Profile (n + m + 1) :=
  join P Q 0 (P.r_pos _) (Q.r_pos _)

/-- Merging is the actual seam contraction of the literal admissible join. -/
def merge (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) : Profile (n + m) :=
  contract (join P Q d hP hQ) ⟨n, by omega⟩

/-- The merger retains the exact signed joining-row length. -/
theorem merge_joined_row (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    ((merge P Q d hP hQ).r ⟨n, by omega⟩ : ℤ) = P.r (Fin.last n) + Q.r 0 - d := by
  have h := contract_joined_row (join P Q d hP hQ) (⟨n, by omega⟩ : Fin (n + m + 1))
  simp only [join, joinGaps_middle] at h
  change ((merge P Q d hP hQ).r ⟨n, by omega⟩ : ℤ) =
    joinRows P Q ⟨n, by omega⟩ + joinRows P Q ⟨n + 1, by omega⟩ - d at h
  have hl := joinRows_left P Q (Fin.last n)
  change joinRows P Q ⟨n, by omega⟩ = P.r (Fin.last n) at hl
  have hr := joinRows_right P Q (0 : Fin (m + 1))
  simp only [Fin.val_zero, Nat.add_zero] at hr
  rw [hl, hr] at h
  exact h

/-- A zero join of thick profiles is thick; the endpoint inequalities are derived internally. -/
theorem zeroJoin_thick (P : Profile n) (Q : Profile m)
    (hP : SkewJacobiNegative.Staircase.Thick P)
    (hQ : SkewJacobiNegative.Staircase.Thick Q) :
    SkewJacobiNegative.Staircase.Thick (zeroJoin P Q) := by
  intro j k hjk
  have hv : j.val + 1 = k.val := congrArg Fin.val hjk
  have hj := j.isLt
  have hk := k.isLt
  change joinGaps P Q 0 j + joinGaps P Q 0 k < joinRows P Q j.succ
  rcases lt_trichotomy k.val n with hkn | hkn | hnk
  · have hjn : j.val < n := by omega
    have h := hP ⟨j.val, hjn⟩ ⟨k.val, hkn⟩ (Fin.ext hv)
    change P.g ⟨j.val, hjn⟩ + P.g ⟨k.val, hkn⟩ <
      P.r ⟨j.val + 1, by omega⟩ at h
    simpa only [joinGaps, dite_eq_left hjn, dite_eq_left hkn, joinRows,
      Fin.val_succ, dite_eq_left (show j.val + 1 < n + 1 by omega)] using h
  · have hjn : j.val < n := by omega
    have h := P.g_lt_succ ⟨j.val, hjn⟩
    change P.g ⟨j.val, hjn⟩ < P.r ⟨j.val + 1, by omega⟩ at h
    simpa only [joinGaps, dite_eq_left hjn, dite_eq_right (show ¬ k.val < n by omega),
      dite_eq_left hkn, add_zero, joinRows, Fin.val_succ,
      dite_eq_left (show j.val + 1 < n + 1 by omega)] using h
  · by_cases hjn : j.val = n
    · have hm : 0 < m := by omega
      have h := Q.g_lt_castSucc (⟨0, hm⟩ : Fin m)
      have hkg : (⟨k.val - (n + 1), by omega⟩ : Fin m) = ⟨0, hm⟩ :=
        Fin.ext (by change k.val - (n + 1) = 0; omega)
      have hjr : (⟨j.val + 1 - (n + 1), by omega⟩ : Fin (m + 1)) = 0 :=
        Fin.ext (by simp only [Fin.val_zero]; omega)
      change Q.g ⟨0, hm⟩ < Q.r 0 at h
      simpa only [joinGaps, dite_eq_right (show ¬ j.val < n by omega), dite_eq_left hjn,
        dite_eq_right (show ¬ k.val < n by omega), dite_eq_right (show k.val ≠ n by omega),
        zero_add, joinRows, Fin.val_succ, dite_eq_right (show ¬ j.val + 1 < n + 1 by omega),
        hkg, hjr] using h
    · have hjn' : n < j.val := by omega
      let a : Fin m := ⟨j.val - (n + 1), by omega⟩
      let b : Fin m := ⟨k.val - (n + 1), by omega⟩
      have hab : a.succ = b.castSucc := Fin.ext (by dsimp [a, b]; omega)
      have h := hQ a b hab
      have hr : (⟨j.val + 1 - (n + 1), by omega⟩ : Fin (m + 1)) = a.succ := by
        apply Fin.ext
        dsimp [a]
        omega
      simpa only [joinGaps, dite_eq_right (show ¬ j.val < n by omega), dite_eq_right hjn,
        dite_eq_right (show ¬ k.val < n by omega), dite_eq_right (show k.val ≠ n by omega),
        joinRows, Fin.val_succ, dite_eq_right (show ¬ j.val + 1 < n + 1 by omega),
        hr] using h

end Profile
end SkewClassInflation
