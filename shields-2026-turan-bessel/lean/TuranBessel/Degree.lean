/-
# Low-degree coefficients and the degree-two repair

Formalizes the coefficient-sector positivity of
`shields-2026-turan-bessel.tex`, §5 «Mixed determinants and coefficientwise
positivity» (`sec:determinant`).  `Δ_n` is a positive
multiple of
```
Dcoeff a n = Σ_{k=0}^n s_k s_{n-k} MD(N_k, N_{n-k}),      s_m = sred a m,
```
so `Δ_n > 0 ⇔ Dcoeff a n > 0`.  This file handles the two low degrees:

* `MD_N0_N1_pos`  — `MD(N_0,N_1) = (aψ₁(a)-1)/(a²ψ₁(a)) > 0` (`eq:Delta1-sharp`, `Δ_1`).
* `Dcoeff_two_pos` — the exceptional `Δ_2 > 0` (`lem:Delta2-positive`) via the
  sharp `Q_*` decomposition (eq:Delta2-Q, eq:Qstar-decomp):
  `Dcoeff a 2 = Q_*/(a⁶(a+1)³ψ₁(a))` with
  `Q_* = 2a⁴(a+1)²R² + 2a²(a+1)²(8a²+3a+1)R + 2a(a+1)(5a+3)`,
  `R = ψ₁(a+1)-1/(a+1) > 0`.
* `MD_N1_Nm_nonneg` — `MD(N_1,N_m) ≥ 0` for `m ≥ 2` (eq:M1-Mm-positive).

Sorry-free.
-/
import TuranBessel.Gram

open scoped BigOperators

namespace TuranBessel

variable {a : ℝ}

/-- The `λⁿ` coefficient sector, up to the positive factor `g Γ(a)^{-4}/2`. -/
noncomputable def Dcoeff (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), sred a k * sred a (n - k) * SymMat.MD (Nmat a k) (Nmat a (n - k))

/-- Trigamma recurrence in the form `ψ₁(a+1) = ψ₁(a) - a⁻²`. -/
theorem trigamma_succ' (ha : 0 < a) : trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹ := by
  have h := trigamma_succ ha
  rw [inv_pow] at h
  linarith

/-- `a ψ₁(a) > 1`. -/
theorem a_trigamma_gt_one (ha : 0 < a) : 1 < a * trigamma a := by
  have h := trigamma_gt_inv ha
  have hmul := mul_lt_mul_of_pos_left h ha
  rwa [mul_inv_cancel₀ ha.ne'] at hmul

/-- `MD(N_0,N_1) = (aψ₁(a)-1)/(a²ψ₁(a)) > 0` (`eq:Delta1-sharp`, `Δ_1`). -/
theorem MD_N0_N1_pos (ha : 0 < a) : 0 < SymMat.MD (Nmat a 0) (Nmat a 1) := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have ht1 : trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹ := trigamma_succ' ha
  have hval : SymMat.MD (Nmat a 0) (Nmat a 1)
      = (a * trigamma a - 1) / (a ^ 2 * trigamma a) := by
    simp only [SymMat.MD, Nmat_a11, Nmat_a12, Nmat_a22, αcoef, βcoef_zero, βcoef_one,
      ccoef_zero, ccoef_one, Nat.cast_zero, Nat.cast_one, add_zero]
    rw [ht1]
    field_simp
    ring
  rw [hval]
  exact div_pos (by linarith [a_trigamma_gt_one ha]) (mul_pos (pow_pos ha 2) hg)

theorem βcoef_two (a : ℝ) : βcoef a 2 = a / (a + 1) := by
  unfold βcoef; rw [if_neg (by omega)]
  push_cast
  rw [show (2 : ℝ) * a + 2 - 2 = 2 * a from by ring, show a + 2 - 1 = a + 1 from by ring]
  exact mul_div_mul_left a (a + 1) two_ne_zero

/-- `Δ_1 = 2 s_0 s_1 MD(N_0,N_1) > 0`. -/
theorem Dcoeff_one_pos (ha : 0 < a) : 0 < Dcoeff a 1 := by
  have h01 := MD_N0_N1_pos ha
  have hs0 := sred_pos ha 0
  have hs1 := sred_pos ha 1
  simp only [Dcoeff, Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_self,
    Nat.sub_zero, zero_add]
  have hcomm : SymMat.MD (Nmat a 1) (Nmat a 0) = SymMat.MD (Nmat a 0) (Nmat a 1) :=
    SymMat.MD_comm _ _
  rw [hcomm]
  nlinarith [mul_pos (mul_pos hs0 hs1) h01, mul_pos (mul_pos hs1 hs0) h01]

/-- `R = ψ₁(a+1) - 1/(a+1) = ψ₁(a) - a⁻² - (a+1)⁻¹` (the `R_a` of `lem:Delta2-positive`). -/
noncomputable def Rval (a : ℝ) : ℝ := trigamma a - (a ^ 2)⁻¹ - (a + 1)⁻¹

/-- The degree-two numerator `Q_*` in `R`-form (eq:Qstar-decomp). -/
noncomputable def Qstar2 (a : ℝ) : ℝ :=
  2 * a ^ 4 * (a + 1) ^ 2 * (Rval a) ^ 2
    + 2 * a ^ 2 * (a + 1) ^ 2 * (8 * a ^ 2 + 3 * a + 1) * (Rval a)
    + 2 * a * (a + 1) * (5 * a + 3)

/-- The meromorphic degree-two identity `Δ_2 = Q_*/(a⁶(a+1)³ψ₁(a))`
(eq:Delta2-Q), for any `a` where the recurrences hold. -/
theorem Dcoeff_two_eq (hane : a ≠ 0) (ha1ne : a + 1 ≠ 0) (h2a1 : (2 * a + 1) ≠ 0)
    (hgne : trigamma a ≠ 0)
    (ht1 : trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹)
    (ht2 : trigamma (a + 2) = trigamma a - (a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹) :
    Dcoeff a 2 = Qstar2 a / (a ^ 6 * (a + 1) ^ 3 * trigamma a) := by
  simp only [Dcoeff, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceSub, SymMat.MD, Nmat_a11, Nmat_a12, Nmat_a22, αcoef, Qstar2, Rval]
  rw [sred_zero, sred_one, sred_two, βcoef_zero, βcoef_one, βcoef_two, ccoef_zero,
    ccoef_one, ccoef_two]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero]
  rw [ht1, ht2]
  field_simp
  ring

/-- `R > 0` for `a > 0` (`eq:trig-lower`/`inverse-trig` at `a+1`). -/
theorem Rval_pos_of_pos (ha : 0 < a) : 0 < Rval a := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have h := trigamma_gt_inv ha1
  rw [trigamma_succ' ha] at h
  unfold Rval; linarith

/-- `Q_* > 0` for `a > 0`, manifestly (all coefficients positive, `R > 0`). -/
theorem Qstar2_pos_of_pos (ha : 0 < a) : 0 < Qstar2 a := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hR := Rval_pos_of_pos ha
  have h3 : (0 : ℝ) < 8 * a ^ 2 + 3 * a + 1 := by nlinarith
  have h5 : (0 : ℝ) < 5 * a + 3 := by linarith
  unfold Qstar2
  nlinarith [mul_pos (mul_pos (pow_pos ha 4) (pow_pos ha1 2)) (pow_pos hR 2),
    mul_pos (mul_pos (mul_pos (pow_pos ha 2) (pow_pos ha1 2)) h3) hR,
    mul_pos (mul_pos ha ha1) h5]

/-- The exceptional degree-two coefficient `Δ_2 > 0` (`κ=1`, `a>0`), via `Q_*`
(`lem:Delta2-positive`). -/
theorem Dcoeff_two_pos (ha : 0 < a) : 0 < Dcoeff a 2 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have ht1 : trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹ := trigamma_succ' ha
  have ht2 : trigamma (a + 2) = trigamma a - (a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹ := by
    have h := trigamma_succ' ha1
    rw [show a + 1 + 1 = a + 2 from by ring, ht1] at h
    exact h
  rw [Dcoeff_two_eq ha.ne' ha1.ne' (by linarith : (0 : ℝ) < 2 * a + 1).ne' hg.ne' ht1 ht2]
  exact div_pos (Qstar2_pos_of_pos ha) (mul_pos (mul_pos (pow_pos ha 6) (pow_pos ha1 3)) hg)

/-- `MD(N_1,N_m) ≥ 0` for `m ≥ 2` and any `a > 0` (eq:M1-Mm-positive).  For
`a ≥ 1/2` both matrices are `⪰ 0`; for `0 < a < 1/2`, `β_1 < 0 < β_m` makes every
term of `MD` positive. -/
theorem MD_N1_Nm_nonneg (ha : 0 < a) {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ SymMat.MD (Nmat a 1) (Nmat a m) := by
  by_cases h : 1 / 2 ≤ a
  · exact SymMat.MD_nonneg (Nmat_pd_one h).psd (Nmat_pd_two ha hm).psd
  · push_neg at h
    -- `0 < a < 1/2`: `β_1 < 0`, `β_m > 0`, positive diagonals.
    have hg : 0 < trigamma a := trigamma_pos ha
    have hβ1 : βcoef a 1 < 0 := by
      rw [βcoef_one]; apply div_neg_of_neg_of_pos <;> linarith
    have hβm : 0 < βcoef a m := βcoef_pos_of_two ha hm
    have hα1 : 0 < αcoef a 1 := αcoef_pos ha 1
    have hαm : 0 < αcoef a m := αcoef_pos ha m
    have hcm : 0 ≤ ccoef a m := ccoef_nonneg ha m
    have hgi : 0 < (trigamma a)⁻¹ := inv_pos.mpr hg
    have h22m : 0 < (trigamma a)⁻¹ + ccoef a m := add_pos_of_pos_of_nonneg hgi hcm
    have hprodβ : βcoef a 1 * βcoef a m < 0 := mul_neg_of_neg_of_pos hβ1 hβm
    simp only [SymMat.MD, Nmat_a11, Nmat_a12, Nmat_a22, ccoef_one, add_zero]
    nlinarith [mul_pos hα1 h22m, mul_pos hgi hαm, hprodβ]

end TuranBessel
