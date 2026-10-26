/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoinBetas
import SkewClassInflation.JoinBetaSets
import SkewClassInflation.InflationClasses

/-!
# Literal rows and gaps after a profile merger

The positional splitting readings underlying `lem:total-contraction-inverse`
and `thm:two-row-thin-class` in `shields-2026-skew-class-inflation.tex`.
Every unmerged row and every remaining gap is identified with its actual
original position.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- Away from the single joined row, a contraction retains exactly one original row. -/
theorem contract_row_of_ne {n : ℕ} (P : Profile (n + 1)) (c i : Fin (n + 1))
    (hi : i.val ≠ c.val) : (contract P c).r i = P.r (c.succ.succAbove i) := by
  have hidx : c.succ.succAbove i = c.castSucc.succAbove i := by
    by_cases h : i.val < c.val
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val < c.val + 1; omega),
        Fin.succAbove_of_castSucc_lt _ _ (by exact h)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by change c.val + 1 ≤ i.val; omega),
        Fin.succAbove_of_le_castSucc _ _ (by change c.val ≤ i.val; omega)]
  obtain ⟨hx, hz⟩ := contract_beta P c
  have h := (contract P c).xi_sub_zeta i
  rw [congrFun hx i, congrFun hz i, ← hidx, P.xi_sub_zeta] at h
  omega

/-- The first upper beta is never removed by a seam contraction. -/
theorem contract_xi_zero {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    (contract P c).xi 0 = P.xi 0 := by
  rw [congrFun (contract_beta P c).1 0,
    Fin.succAbove_succ_of_le c 0 (Fin.zero_le c)]
  rfl

/-- Full ordered row and gap words identify the complete normalized profile and its row count. -/
theorem profileSigma_eq_of_words {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hr : List.ofFn P.r = List.ofFn Q.r) (hg : List.ofFn P.g = List.ofFn Q.g) :
    (⟨n, P⟩ : ConnectedProfile) = ⟨m, Q⟩ := by
  have hn := congrArg List.length hr
  simp only [List.length_ofFn] at hn
  have hn' : n = m := by omega
  subst m
  congr 1
  apply Gluing.Profile.ext
  · exact List.ofFn_injective hr
  · exact List.ofFn_injective hg

namespace Profile

variable {n m : ℕ}

/-- All first-block rows before its last endpoint survive the merger unchanged. -/
theorem merge_r_left (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin n) :
    (merge P Q d hP hQ).r ⟨i.val, by have := i.isLt; omega⟩ = P.r i.castSucc := by
  let c : Fin (n + m + 1) := ⟨n, by omega⟩
  let j : Fin (n + m + 1) := ⟨i.val, by have := i.isLt; omega⟩
  have h := contract_row_of_ne (join P Q d hP hQ) c j
    (by dsimp [j, c]; have := i.isLt; omega)
  rw [Fin.succAbove_of_castSucc_lt _ _ (by
    change i.val < n + 1
    have := i.isLt
    omega)] at h
  change (merge P Q d hP hQ).r ⟨i.val, by have := i.isLt; omega⟩ =
    joinRows P Q ⟨i.val, by have := i.isLt; omega⟩ at h
  have hr := joinRows_left P Q i.castSucc
  change joinRows P Q ⟨i.val, by have := i.isLt; omega⟩ = P.r i.castSucc at hr
  exact h.trans hr

/-- Every second-block row after its first endpoint survives at its exact shifted position. -/
theorem merge_r_right (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin m) :
    (merge P Q d hP hQ).r ⟨n + 1 + i.val, by have := i.isLt; omega⟩ = Q.r i.succ := by
  let c : Fin (n + m + 1) := ⟨n, by omega⟩
  let j : Fin (n + m + 1) := ⟨n + 1 + i.val, by have := i.isLt; omega⟩
  have h := contract_row_of_ne (join P Q d hP hQ) c j (by dsimp [j, c]; omega)
  rw [Fin.succAbove_of_le_castSucc _ _ (by change n + 1 ≤ n + 1 + i.val; omega)] at h
  have hj : j.succ = (⟨n + 1 + i.succ.val, by have := i.isLt; omega⟩ : Fin (n + m + 2)) := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [hj] at h
  exact h.trans (joinRows_right P Q i.succ)

/-- Every first-block gap survives before the contracted joining seam. -/
theorem merge_g_left (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin n) :
    (merge P Q d hP hQ).g ⟨i.val, by have := i.isLt; omega⟩ = P.g i := by
  let c : Fin (n + m + 1) := ⟨n, by omega⟩
  let j : Fin (n + m) := ⟨i.val, by have := i.isLt; omega⟩
  have he := contract_gap (join P Q d hP hQ) c j
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val < n; exact i.isLt)] at he
  exact he.trans (joinGaps_left P Q d i)

/-- Every internal gap of the second block survives the merger, including coincident values. -/
theorem merge_g_right (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) (i : Fin m) :
    (merge P Q d hP hQ).g ⟨n + i.val, by have := i.isLt; omega⟩ = Q.g i := by
  let c : Fin (n + m + 1) := ⟨n, by omega⟩
  let j : Fin (n + m) := ⟨n + i.val, by have := i.isLt; omega⟩
  have h := contract_gap (join P Q d hP hQ) c j
  rw [Fin.succAbove_of_le_castSucc _ _ (by change n ≤ n + i.val; omega)] at h
  have hj : j.succ = (⟨n + 1 + i.val, by have := i.isLt; omega⟩ : Fin (n + m + 1)) := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [hj] at h
  exact h.trans (joinGaps_right P Q d i)

/-- The full span of a merger is the sum of the two original spans minus the joining gap. -/
theorem merge_span (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (merge P Q d hP hQ).xi 0 = P.xi 0 + Q.xi 0 - d := by
  rw [merge, contract_xi_zero, join_span]

end Profile
end SkewClassInflation
