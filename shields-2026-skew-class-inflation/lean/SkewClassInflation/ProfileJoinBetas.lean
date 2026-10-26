/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoins

/-!
# Normalized beta coordinates of a literal join

Formalizes the joining-coordinate calculation used in
`eq:thin-beta-lists` of `shields-2026-skew-class-inflation.tex`.
The whole first block is translated by the second block's span minus
the joining gap; the second block stays normalized.  Sorry-free.
-/

namespace SkewClassInflation.Profile

open SkewJacobiNegative

variable {n m : ℕ}

/-- Full upper beta word, with the first block translated as a whole. -/
def joinUpper (P : Profile n) (Q : Profile m) (d : ℕ) (i : Fin (n + m + 2)) : ℤ :=
  if h : i.val < n + 1 then P.xi ⟨i.val, h⟩ + Q.xi 0 - d
  else Q.xi ⟨i.val - (n + 1), by have := i.isLt; omega⟩

/-- Full lower beta word, retaining every original zero beta at its actual new position. -/
def joinLower (P : Profile n) (Q : Profile m) (d : ℕ) (i : Fin (n + m + 2)) : ℤ :=
  if h : i.val < n + 1 then P.zeta ⟨i.val, h⟩ + Q.xi 0 - d
  else Q.zeta ⟨i.val - (n + 1), by have := i.isLt; omega⟩

/-- The candidate joined coordinates have the exact original row differences. -/
theorem join_coordinates_rows (P : Profile n) (Q : Profile m) (d : ℕ)
    (i : Fin (n + m + 2)) :
    joinUpper P Q d i - joinLower P Q d i = joinRows P Q i := by
  unfold joinUpper joinLower joinRows
  split_ifs with hi
  · have h := P.xi_sub_zeta (⟨i.val, hi⟩ : Fin (n + 1))
    omega
  · exact Q.xi_sub_zeta _

/-- The lower beta word remains normalized at its last position. -/
theorem join_coordinates_last (P : Profile n) (Q : Profile m) (d : ℕ) :
    joinLower P Q d (Fin.last (n + m + 1)) = 0 := by
  rw [joinLower, dite_eq_right (by simp only [Fin.val_last]; omega)]
  have hi : (⟨(Fin.last (n + m + 1)).val - (n + 1), by simp⟩ : Fin (m + 1)) =
      Fin.last m := Fin.ext (by simp)
  rw [hi, Q.zeta_last]

/-- The candidate beta words have exactly the old gaps and the specified new joining gap. -/
theorem join_coordinates_gaps (P : Profile n) (Q : Profile m) (d : ℕ)
    (j : Fin (n + m + 1)) :
    joinUpper P Q d j.succ - joinLower P Q d j.castSucc = joinGaps P Q d j := by
  by_cases hj : j.val < n
  · simp only [joinUpper, joinLower, joinGaps, Fin.val_succ, Fin.val_castSucc,
      dite_eq_left (show j.val + 1 < n + 1 by omega),
      dite_eq_left (show j.val < n + 1 by omega), dite_eq_left hj]
    have h := P.xi_succ_sub_zeta_castSucc (⟨j.val, hj⟩ : Fin n)
    change P.xi ⟨j.val + 1, by omega⟩ - P.zeta ⟨j.val, by omega⟩ = P.g ⟨j.val, hj⟩ at h
    omega
  · by_cases he : j.val = n
    · simp only [joinUpper, joinLower, joinGaps, Fin.val_succ, Fin.val_castSucc,
        dite_eq_right (show ¬ j.val + 1 < n + 1 by omega),
        dite_eq_left (show j.val < n + 1 by omega), dite_eq_right hj, dite_eq_left he]
      have h0 : (⟨j.val + 1 - (n + 1), by have := j.isLt; omega⟩ : Fin (m + 1)) = 0 :=
        Fin.ext (by simp only [Fin.val_zero]; omega)
      have hn : (⟨j.val, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext he
      rw [h0, hn, P.zeta_last]
      ring
    · have hjm : j.val - (n + 1) < m := by have := j.isLt; omega
      simp only [joinUpper, joinLower, joinGaps, Fin.val_succ, Fin.val_castSucc,
        dite_eq_right (show ¬ j.val + 1 < n + 1 by omega),
        dite_eq_right (show ¬ j.val < n + 1 by omega), dite_eq_right hj, dite_eq_right he]
      have h0 : (⟨j.val - (n + 1), by omega⟩ : Fin (m + 1)) =
          (⟨j.val - (n + 1), hjm⟩ : Fin m).castSucc := rfl
      have h1 : (⟨j.val + 1 - (n + 1), by have := j.isLt; omega⟩ : Fin (m + 1)) =
          (⟨j.val - (n + 1), hjm⟩ : Fin m).succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [h0, h1, Q.xi_succ_sub_zeta_castSucc]

/-- The literal join has precisely the constructed full beta words. -/
theorem join_beta (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (join P Q d hP hQ).xi = joinUpper P Q d ∧
      (join P Q d hP hQ).zeta = joinLower P Q d := by
  have he := (join P Q d hP hQ).eq_beta_of_equations
    (join_coordinates_last P Q d) (join_coordinates_rows P Q d) (join_coordinates_gaps P Q d)
  exact ⟨he.1.symm, he.2.symm⟩

/-- The entire first upper block is translated by the second span minus the joining gap. -/
theorem join_xi_left (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin (n + 1)) :
    (join P Q d hP hQ).xi ⟨i.val, by have := i.isLt; omega⟩ = P.xi i + Q.xi 0 - d := by
  rw [congrFun (join_beta P Q d hP hQ).1 _, joinUpper, dite_eq_left i.isLt]

/-- The same whole-block translation acts on the first lower block. -/
theorem join_zeta_left (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin (n + 1)) :
    (join P Q d hP hQ).zeta ⟨i.val, by have := i.isLt; omega⟩ = P.zeta i + Q.xi 0 - d := by
  rw [congrFun (join_beta P Q d hP hQ).2 _, joinLower, dite_eq_left i.isLt]

/-- The second upper block stays in its original normalized coordinates. -/
theorem join_xi_right (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin (m + 1)) :
    (join P Q d hP hQ).xi ⟨n + 1 + i.val, by have := i.isLt; omega⟩ = Q.xi i := by
  rw [congrFun (join_beta P Q d hP hQ).1 _, joinUpper,
    dite_eq_right (by change ¬ n + 1 + i.val < n + 1; omega)]
  congr 1
  apply Fin.ext
  simp

/-- The second lower block stays normalized by exactly the same embedding. -/
theorem join_zeta_right (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin (m + 1)) :
    (join P Q d hP hQ).zeta ⟨n + 1 + i.val, by have := i.isLt; omega⟩ = Q.zeta i := by
  rw [congrFun (join_beta P Q d hP hQ).2 _, joinLower,
    dite_eq_right (by change ¬ n + 1 + i.val < n + 1; omega)]
  congr 1
  apply Fin.ext
  simp

end SkewClassInflation.Profile
