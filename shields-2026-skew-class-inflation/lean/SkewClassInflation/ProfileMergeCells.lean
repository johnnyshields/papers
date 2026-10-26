/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoinCells
import SkewClassInflation.ProfileMergeReadings

/-!
# Literal cells of a profile merger

The endpoint-overlap realization of the merger in `eq:repeated-blocks`
of `shields-2026-skew-class-inflation.tex`.  The two endpoint intervals
occupy the same row and overlap in exactly the distinguished gap.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

namespace Profile

variable {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
  (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0)

/-- All first-block upper endpoints survive, including the merged endpoint. -/
theorem merge_xi_left (i : Fin (n + 1)) :
    (merge P Q d hP hQ).xi ⟨i.val, by have := i.isLt; omega⟩ =
      P.xi i + Q.xi 0 - d := by
  rw [merge, congrFun (contract_beta _ _).1]
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val < n + 1; exact i.isLt)]
  exact join_xi_left P Q d hP hQ i

/-- First-block lower endpoints survive strictly above the merged row. -/
theorem merge_zeta_left (i : Fin n) :
    (merge P Q d hP hQ).zeta ⟨i.val, by have := i.isLt; omega⟩ =
      P.zeta i.castSucc + Q.xi 0 - d := by
  rw [merge, congrFun (contract_beta _ _).2]
  rw [Fin.succAbove_of_castSucc_lt _ _ (by exact i.isLt)]
  exact join_zeta_left P Q d hP hQ i.castSucc

/-- Second-block upper endpoints survive strictly below the merged row. -/
theorem merge_xi_right (i : Fin m) :
    (merge P Q d hP hQ).xi ⟨n + 1 + i.val, by have := i.isLt; omega⟩ = Q.xi i.succ := by
  rw [merge, congrFun (contract_beta _ _).1]
  rw [Fin.succAbove_of_le_castSucc _ _ (by change n + 1 ≤ n + 1 + i.val; omega)]
  convert join_xi_right P Q d hP hQ i.succ using 2
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

/-- All second-block lower endpoints survive, including the merged endpoint. -/
theorem merge_zeta_right (i : Fin (m + 1)) :
    (merge P Q d hP hQ).zeta ⟨n + i.val, by have := i.isLt; omega⟩ = Q.zeta i := by
  rw [merge, congrFun (contract_beta _ _).2]
  rw [Fin.succAbove_of_le_castSucc _ _ (by change n ≤ n + i.val; omega)]
  convert join_zeta_right P Q d hP hQ i using 2
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

end Profile

/-- Merger identifies the endpoint rows; their actual intervals have no missing cell. -/
theorem profileCells_merge {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    profileCells (Profile.merge P Q d hP hQ) =
      SkewGluing.translate (0, Q.xi 0 - d) (profileCells P) ∪
        SkewGluing.translate (n, n) (profileCells Q) := by
  ext x
  rcases x with ⟨a, b⟩
  simp only [Finset.mem_union, SkewGluing.mem_translate, Prod.mk_sub_mk,
    sub_zero, mem_profileCells]
  have hlast : P.zeta (Fin.last n) = 0 := P.zeta_last
  have hp := P.xi_sub_zeta (Fin.last n)
  have hq := Q.xi_sub_zeta 0
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    rcases lt_trichotomy i.val n with hl | he | hr
    · let j : Fin n := ⟨i.val, hl⟩
      have hj : (j.val : ℤ) = i.val := rfl
      have hx := Profile.merge_xi_left P Q d hP hQ j.castSucc
      have hz := Profile.merge_zeta_left P Q d hP hQ j
      change (Profile.merge P Q d hP hQ).xi i =
        P.xi j.castSucc + Q.xi 0 - d at hx
      change (Profile.merge P Q d hP hQ).zeta i =
        P.zeta j.castSucc + Q.xi 0 - d at hz
      rw [hx] at hhi
      rw [hz] at hlo
      exact Or.inl ⟨j.castSucc, hi,
        by simp only [Fin.val_castSucc]; omega,
        by simp only [Fin.val_castSucc]; omega⟩
    · have hie : i = ⟨n, by omega⟩ := Fin.ext he
      rw [hie] at hi hlo hhi
      have hx := Profile.merge_xi_left P Q d hP hQ (Fin.last n)
      have hz := Profile.merge_zeta_right P Q d hP hQ (0 : Fin (m + 1))
      simp only [Fin.val_last, Fin.val_zero, Nat.add_zero] at hx hz
      rw [hx] at hhi
      rw [hz] at hlo
      by_cases hb : b < Q.xi 0 + n
      · exact Or.inr ⟨0, by simp only [Fin.val_zero] at *; omega,
          by simp only [Fin.val_zero] at *; omega,
          by simp only [Fin.val_zero] at *; omega⟩
      · exact Or.inl ⟨Fin.last n, hi, by rw [hlast]; simp only [Fin.val_last]; omega,
          by simp only [Fin.val_last]; omega⟩
    · let j : Fin m := ⟨i.val - (n + 1), by have := i.isLt; omega⟩
      have hj : (j.val : ℤ) = i.val - (n + 1) := by dsimp [j]; omega
      have hie : (⟨n + 1 + j.val, by have := j.isLt; omega⟩ : Fin (n + m + 1)) = i :=
        Fin.ext (by dsimp [j]; omega)
      have hje : (⟨n + j.succ.val, by have := j.isLt; omega⟩ : Fin (n + m + 1)) = i :=
        Fin.ext (by simp only [Fin.val_succ]; dsimp [j]; omega)
      have hx := Profile.merge_xi_right P Q d hP hQ j
      have hz := Profile.merge_zeta_right P Q d hP hQ j.succ
      rw [hie] at hx
      rw [hje] at hz
      rw [hx] at hhi
      rw [hz] at hlo
      exact Or.inr ⟨j.succ, by simp only [Fin.val_succ]; omega,
        by simp only [Fin.val_succ]; omega, by simp only [Fin.val_succ]; omega⟩
  · rintro (⟨j, hj, hlo, hhi⟩ | ⟨j, hj, hlo, hhi⟩)
    · by_cases hl : j.val < n
      · let k : Fin n := ⟨j.val, hl⟩
        let i : Fin (n + m + 1) := ⟨j.val, by have := j.isLt; omega⟩
        have hk : k.castSucc = j := Fin.ext rfl
        have hx := Profile.merge_xi_left P Q d hP hQ j
        have hz := Profile.merge_zeta_left P Q d hP hQ k
        rw [hk] at hz
        refine ⟨i, hj, ?_, ?_⟩
        · rw [hz]
          change P.zeta j + Q.xi 0 - d + j.val ≤ b
          omega
        · rw [hx]
          change b < P.xi j + Q.xi 0 - d + j.val
          omega
      · have he : j = Fin.last n := Fin.ext (by have := j.isLt; simp; omega)
        subst j
        let i : Fin (n + m + 1) := ⟨n, by omega⟩
        have hx := Profile.merge_xi_left P Q d hP hQ (Fin.last n)
        have hz := Profile.merge_zeta_right P Q d hP hQ (0 : Fin (m + 1))
        simp only [Fin.val_last, Fin.val_zero, Nat.add_zero] at hx hz
        refine ⟨i, hj, ?_, ?_⟩
        · rw [hz]
          rw [hlast] at hlo
          simp only [Fin.val_last] at hlo
          have hd : (d : ℤ) < Q.r 0 := by exact_mod_cast hQ
          change Q.zeta 0 + (n : ℤ) ≤ b
          omega
        · rw [hx]
          change b < P.xi (Fin.last n) + Q.xi 0 - d + (n : ℤ)
          simp only [Fin.val_last] at hhi
          omega
    · by_cases he : j.val = 0
      · have hj0 : j = 0 := Fin.ext he
        subst j
        let i : Fin (n + m + 1) := ⟨n, by omega⟩
        have hx := Profile.merge_xi_left P Q d hP hQ (Fin.last n)
        have hz := Profile.merge_zeta_right P Q d hP hQ (0 : Fin (m + 1))
        simp only [Fin.val_last, Fin.val_zero, Nat.add_zero] at hx hz
        refine ⟨i, by simp only [Fin.val_zero] at hj; dsimp [i]; omega, ?_, ?_⟩
        · rw [hz]
          change Q.zeta 0 + (n : ℤ) ≤ b
          simp only [Fin.val_zero] at hlo
          omega
        · rw [hx]
          simp only [Fin.val_zero] at hhi
          have hd : (d : ℤ) < P.r (Fin.last n) := by exact_mod_cast hP
          change b < P.xi (Fin.last n) + Q.xi 0 - d + (n : ℤ)
          omega
      · let k : Fin m := ⟨j.val - 1, by have := j.isLt; omega⟩
        have hk : k.succ = j := Fin.ext (by dsimp [k]; omega)
        let i : Fin (n + m + 1) := ⟨n + j.val, by have := j.isLt; omega⟩
        have hie : (⟨n + 1 + k.val, by have := k.isLt; omega⟩ : Fin (n + m + 1)) = i :=
          Fin.ext (by dsimp [k, i]; omega)
        have hx := Profile.merge_xi_right P Q d hP hQ k
        have hz := Profile.merge_zeta_right P Q d hP hQ j
        rw [hk, hie] at hx
        refine ⟨i, by dsimp [i]; omega, ?_, ?_⟩
        · rw [hz]
          dsimp [i]
          omega
        · rw [hx]
          dsimp [i]
          omega

end SkewClassInflation
