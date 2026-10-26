/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CellProfiles
import SkewClassInflation.ProfileJoinBetas

/-!
# Literal cells of a connected profile join

The cell-set realization of the joining operation in `eq:repeated-blocks`
and `prop:saturation-chart` of `shields-2026-skew-class-inflation.tex`.
Both blocks retain their full row intervals, with their actual translations.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Joining translates the entire first block horizontally and the second block diagonally. -/
theorem profileCells_join {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    profileCells (Profile.join P Q d hP hQ) =
      SkewGluing.translate (0, Q.xi 0 - d) (profileCells P) ∪
        SkewGluing.translate (n + 1, n + 1) (profileCells Q) := by
  ext x
  rcases x with ⟨a, b⟩
  simp only [Finset.mem_union, SkewGluing.mem_translate, Prod.mk_sub_mk,
    sub_zero, mem_profileCells]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    by_cases hl : i.val < n + 1
    · let j : Fin (n + 1) := ⟨i.val, hl⟩
      have hx := Profile.join_xi_left P Q d hP hQ j
      have hz := Profile.join_zeta_left P Q d hP hQ j
      change (Profile.join P Q d hP hQ).xi i = P.xi j + Q.xi 0 - d at hx
      change (Profile.join P Q d hP hQ).zeta i = P.zeta j + Q.xi 0 - d at hz
      rw [hx] at hhi
      rw [hz] at hlo
      have hj : (j.val : ℤ) = i.val := rfl
      exact Or.inl ⟨j, hi, by omega, by omega⟩
    · let j : Fin (m + 1) := ⟨i.val - (n + 1), by have := i.isLt; omega⟩
      have hij : (⟨n + 1 + j.val, by have := j.isLt; omega⟩ : Fin (n + m + 2)) = i :=
        Fin.ext (by dsimp [j]; omega)
      have hx := Profile.join_xi_right P Q d hP hQ j
      have hz := Profile.join_zeta_right P Q d hP hQ j
      rw [hij] at hx hz
      rw [hx] at hhi
      rw [hz] at hlo
      have hj : (j.val : ℤ) = i.val - (n + 1) := by dsimp [j]; omega
      exact Or.inr ⟨j, by omega, by omega, by omega⟩
  · rintro (⟨j, hj, hlo, hhi⟩ | ⟨j, hj, hlo, hhi⟩)
    · let i : Fin (n + m + 2) := ⟨j.val, by have := j.isLt; omega⟩
      refine ⟨i, hj, ?_, ?_⟩
      · rw [Profile.join_zeta_left P Q d hP hQ j]
        dsimp [i]
        omega
      · rw [Profile.join_xi_left P Q d hP hQ j]
        dsimp [i]
        omega
    · let i : Fin (n + m + 2) := ⟨n + 1 + j.val, by have := j.isLt; omega⟩
      refine ⟨i, ?_, ?_, ?_⟩
      · dsimp [i]
        omega
      · rw [Profile.join_zeta_right P Q d hP hQ j]
        dsimp [i]
        omega
      · rw [Profile.join_xi_right P Q d hP hQ j]
        dsimp [i]
        omega

/-- Inflation retains the literal joining operation and increases its seam by the same amount. -/
theorem inflate_join {n m : ℕ} (P : Profile n) (Q : Profile m) (d t : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    Profile.inflate t (Profile.join P Q d hP hQ) =
      Profile.join (Profile.inflate t P) (Profile.inflate t Q) (d + t)
        (Nat.add_lt_add_right hP t) (Nat.add_lt_add_right hQ t) := by
  apply SkewJacobiNegative.Gluing.Profile.eq_of_beta_eq
  · funext i
    rw [Profile.xi_inflate,
      congrFun (Profile.join_beta P Q d hP hQ).1 i,
      congrFun (Profile.join_beta (Profile.inflate t P) (Profile.inflate t Q) (d + t)
        (Nat.add_lt_add_right hP t) (Nat.add_lt_add_right hQ t)).1 i]
    unfold Profile.joinUpper
    split_ifs
    · simp only [Profile.xi_inflate, Nat.cast_add]
      ring
    · simp only [Profile.xi_inflate]
  · funext i
    rw [Profile.zeta_inflate,
      congrFun (Profile.join_beta P Q d hP hQ).2 i,
      congrFun (Profile.join_beta (Profile.inflate t P) (Profile.inflate t Q) (d + t)
        (Nat.add_lt_add_right hP t) (Nat.add_lt_add_right hQ t)).2 i]
    unfold Profile.joinLower
    split_ifs
    · simp only [Profile.xi_inflate, Profile.zeta_inflate, Nat.cast_add]
      ring
    · simp only [Profile.zeta_inflate]

/-- The inflated zero join is a union across the new seam of width `t`, not a disjoint surrogate. -/
theorem profileCells_inflate_zeroJoin {n m : ℕ} (P : Profile n) (Q : Profile m) (t : ℕ) :
    profileCells (Profile.inflate t (Profile.zeroJoin P Q)) =
      SkewGluing.translate (0, Q.xi 0) (profileCells (Profile.inflate t P)) ∪
        SkewGluing.translate (n + 1, n + 1) (profileCells (Profile.inflate t Q)) := by
  have hp : t < (Profile.inflate t P).r (Fin.last n) := by
    change t < P.r (Fin.last n) + t
    have := P.r_pos (Fin.last n)
    omega
  have hq : t < (Profile.inflate t Q).r 0 := by
    change t < Q.r 0 + t
    have := Q.r_pos 0
    omega
  have he : Profile.inflate t (Profile.zeroJoin P Q) =
      Profile.join (Profile.inflate t P) (Profile.inflate t Q) t hp hq := by
    simpa only [Profile.zeroJoin, Nat.zero_add] using
      inflate_join P Q 0 t (P.r_pos _) (Q.r_pos _)
  rw [he, profileCells_join, Profile.xi_inflate, add_sub_cancel_right]

end SkewClassInflation
