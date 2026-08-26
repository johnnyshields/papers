/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Degree

/-!
# Sharp coefficientwise positivity (`thm:coefficientwise`, endpoint `κ = 1`)

Assembles `shields-2026-turan-bessel.tex`, «Endpoint coefficientwise
positivity» (`sec:endpoint`, `subsec:finite-defect`); the theorem itself is stated in
«Reciprocal-gamma formulation and positivity phase diagram» (`sec:main`, `thm:coefficientwise`). 
The `λⁿ` coefficient of the
Turán determinant is a positive multiple of
`Dcoeff a n = Σ_{k=0}^n s_k s_{n-k} MD(N_k, N_{n-k})`, so the main theorem is

  `coefficientwise_positivity : 0 < a → 1 ≤ n → 0 < Dcoeff a n`.

The argument: every mixed-determinant term is `≥ 0` except the possible
`N_1`-self-interaction (`0 < a < 1/2`), which occurs only at degree two and is
repaired by the sharp `Q_*` identity; the `(0,n)` pair is strictly positive.

Sorry-free.
-/

open scoped BigOperators

namespace TuranBessel

variable {a : ℝ}

/-- `MD(N_k, N_l) ≥ 0` for every pair except the degree-two self-pair `(1,1)`.
`N_m` is `⪰ 0` for `m ≠ 1`; the `N_1` mixed terms are handled by `MD_N0_N1_pos`
and `MD_N1_Nm_pos`. -/
theorem MD_Nmat_nonneg (ha : 0 < a) {k l : ℕ} (hkl : ¬(k = 1 ∧ l = 1)) :
    0 ≤ SymMat.MD (Nmat a k) (Nmat a l) := by
  have psd_of_ne1 : ∀ m, m ≠ 1 → SymMat.PSD (Nmat a m) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; exact Nmat_zero_psd ha
    · exact (Nmat_pd_two ha (by omega)).psd
  by_cases hk1 : k = 1
  · subst hk1
    have hl1 : l ≠ 1 := fun h => hkl ⟨rfl, h⟩
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst h0; rw [SymMat.MD_comm]; exact (MD_N0_N1_pos ha).le
    · exact (MD_N1_Nm_pos ha (by omega)).le
  · by_cases hl1 : l = 1
    · subst hl1
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; exact (MD_N0_N1_pos ha).le
      · rw [SymMat.MD_comm]; exact (MD_N1_Nm_pos ha (by omega)).le
    · exact SymMat.MD_nonneg (psd_of_ne1 k hk1) (psd_of_ne1 l hl1)

/-- The strictly positive `(0,n)` term: `MD(N_0, N_n) > 0` for `n ≥ 2`. -/
theorem MD_N0_Nn_pos (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) :
    0 < SymMat.MD (Nmat a 0) (Nmat a n) :=
  SymMat.MD_pos_of_psd_pd (Nmat_zero_psd ha) (Nmat_zero_ne ha) (Nmat_pd_two ha hn)

/-- **Sharp coefficientwise positivity** (`thm:coefficientwise`, endpoint `κ=1`):
`Δ_n(a) > 0` for every `a > 0` and `n ≥ 1`, in the form `Dcoeff a n > 0`. -/
theorem coefficientwise_positivity (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) : 0 < Dcoeff a n := by
  by_cases hhalf : 1 / 2 ≤ a
  · -- `a ≥ 1/2`: every `N_m` is `⪰ 0`, `N_{≥1}` is `≻ 0`.
    have psd_all : ∀ m, SymMat.PSD (Nmat a m) := by
      intro m
      rcases Nat.lt_or_ge m 1 with h | h
      · interval_cases m; exact Nmat_zero_psd ha
      · rcases Nat.lt_or_ge m 2 with h2 | h2
        · interval_cases m; exact (Nmat_pd_one hhalf).psd
        · exact (Nmat_pd_two ha h2).psd
    have pd_n : SymMat.PD (Nmat a n) := by
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · interval_cases n; exact Nmat_pd_one hhalf
      · exact Nmat_pd_two ha h2
    unfold Dcoeff
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (mul_nonneg (sred_pos ha k).le (sred_pos ha (n - k)).le)
        (SymMat.MD_nonneg (psd_all k) (psd_all (n - k)))
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      rw [show n - 0 = n from by omega]
      exact mul_pos (mul_pos (sred_pos ha 0) (sred_pos ha n))
        (SymMat.MD_pos_of_psd_pd (Nmat_zero_psd ha) (Nmat_zero_ne ha) pd_n)
  · push Not at hhalf
    -- `0 < a < 1/2`: `N_1` may be indefinite.  Degrees 1,2 are special.
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · interval_cases n
      · exact Dcoeff_one_pos ha
      · exact Dcoeff_two_pos ha
    · -- `n ≥ 3`: every term `≥ 0` (no `(1,1)` pair), `(0,n)` strict.
      unfold Dcoeff
      apply Finset.sum_pos'
      · intro k hk
        refine mul_nonneg (mul_nonneg (sred_pos ha k).le (sred_pos ha (n - k)).le) ?_
        apply MD_Nmat_nonneg ha
        rintro ⟨hk1, hnk1⟩
        omega
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        rw [show n - 0 = n from by omega]
        exact mul_pos (mul_pos (sred_pos ha 0) (sred_pos ha n))
          (MD_N0_Nn_pos ha (by omega))

end TuranBessel
