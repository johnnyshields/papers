/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Microcanonical
import TuranBessel.Bridge

/-!
# Four-copy determinant sectors

Formalizes `shields-2026-turan-bessel.tex`, «Four-copy determinant sectors»
(`subsec:four-copy`, `prop:four-copy`, `eq:Tn-Kn-law`, `eq:four-total-law`,
`eq:Delta-n-MD`, `eq:sector-density`, `eq:D-canonical-average`,
`rem:ensemble-positivity`).

`T_n = ∑_k S_kS_{n-k}` is `[λⁿ]Z⁴`, so the four-copy total `N = R + R'` of two
independent pair totals has law `T_nλⁿ/Z⁴` (`eq:four-total-law`) and dividing by
it leaves the `λ`-free law `S_kS_{n-k}/T_n` of the first pair total given `N = n`
(`eq:Tn-Kn-law`).  Against that law the mixed-determinant sum of `eq:Delta-n-MD`
is an expectation,
```
  Δ_n = (T_n/2) E MD(M_{K_n}, M_{n-K_n}),
```
and the sector densities `d_n = 4Δ_n/(gT_n)` of `eq:sector-density` average
against `eq:four-total-law` to the pointwise Bessel determinant
(`eq:D-canonical-average`), which is the statement `rem:ensemble-positivity`
reads the phase separation off.

Two scopes.  The `MD` recasting is proved at general `(κ,τ)` on the coefficient
sector `Phase.DcoeffKT`, since it needs no series.  `eq:D-canonical-average` is
proved at the endpoint `(κ,τ) = (1,1)`, where `Bridge.hasSum_turanDetCoeff`
supplies `Δ = ∑ Δ_nλⁿ` and `Bridge.besselDefect_eq` supplies
`eq:Dkappa-tau-Delta`; at general `(κ,τ)` the same argument needs the
general-`(κ,τ)` determinant series, and `sectorDensityKT` is the density it would
average, verified here only where it is choice-free — `d_0^{(κ,τ)} = 4(τ-1)`, the
vacuum sector of `rem:ensemble-positivity`.

Sorry-free.
-/

open scoped BigOperators
open Finset

namespace TuranBessel

variable {a lam : ℝ}

/-! ### `T_n = [λⁿ]Z⁴` -/

/-- `T_n = ∑_k S_kS_{n-k}` (`eq:Tn-Kn-law`). -/
noncomputable def tweight (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), sweight a k * sweight a (n - k)

theorem tweight_pos (ha : 0 < a) (n : ℕ) : 0 < tweight a n :=
  Finset.sum_pos (fun k _ => mul_pos (sweight_pos ha k) (sweight_pos ha (n - k)))
    ⟨0, mem_range.mpr (Nat.succ_pos n)⟩

theorem tweight_zero (a : ℝ) : tweight a 0 = sweight a 0 * sweight a 0 := by
  rw [tweight, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem sweight_zero_eq (a : ℝ) : sweight a 0 = (Real.Gamma a ^ 2)⁻¹ := by
  rw [sweight]
  norm_num

/-- Absolute summability of `∑ S_mλ^m`, the `τ = 1`, `g = 0` case of
`TuranDet.summable_norm_gamma_series`. -/
theorem summable_norm_sweight_series (ha : 0 < a) (lam : ℝ) :
    Summable fun m : ℕ => ‖sweight a m * lam ^ m‖ :=
  (summable_norm_gamma_series ha 0 1 1 lam).congr fun m => by norm_num

/-- **`eq:Tn-Kn-law`, second half.**  `T_n = [λⁿ]Z⁴`. -/
theorem Zfun_pow_four (ha : 0 < a) (lam : ℝ) :
    Zfun a lam ^ 4 = ∑' n : ℕ, tweight a n * lam ^ n := by
  have hn := summable_norm_sweight_series ha lam
  have hsq := Zfun_sq ha lam
  have h : Zfun a lam ^ 4 = (∑' m : ℕ, sweight a m * lam ^ m)
      * ∑' m : ℕ, sweight a m * lam ^ m := by
    rw [← hsq, ← sq, ← pow_mul]
  rw [h, tsum_cauchy_lam lam hn hn]
  exact tsum_congr fun n => by rw [tweight]

theorem summable_tweight (ha : 0 < a) (lam : ℝ) :
    Summable fun n : ℕ => tweight a n * lam ^ n := by
  have h := summable_norm_cauchy_lam (f := sweight a) (g := sweight a) lam
    (summable_norm_sweight_series ha lam) (summable_norm_sweight_series ha lam)
  exact (h.congr fun n => by rw [tweight]).of_norm

/-! ### `eq:four-total-law` -/

/-- `P_λ(N=n)` for the four-copy total `N = R + R'` (`eq:four-total-law`). -/
noncomputable def fourPMF (a lam : ℝ) (n : ℕ) : ℝ := tweight a n * lam ^ n / Zfun a lam ^ 4

/-- **`eq:four-total-law`.**  The four-copy total is the sum of two independent
pair totals, so its law is the convolution of `eq:pair-total-law` with itself. -/
theorem fourPMF_eq_conv (ha : 0 < a) (hlam : 0 ≤ lam) (n : ℕ) :
    ∑ k ∈ range (n + 1), pairPMF a lam k * pairPMF a lam (n - k) = fourPMF a lam n := by
  have hZ : Zfun a lam ≠ 0 := (Zfun_pos ha hlam).ne'
  have hterm : ∀ k ∈ range (n + 1), pairPMF a lam k * pairPMF a lam (n - k)
      = (sweight a k * sweight a (n - k) * lam ^ n) / Zfun a lam ^ 4 := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hpow : lam ^ k * lam ^ (n - k) = lam ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hkn]
    rw [pairPMF, pairPMF, div_mul_div_comm, show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    rw [← hpow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, fourPMF, tweight, Finset.sum_mul]

theorem fourPMF_nonneg (ha : 0 < a) (hlam : 0 ≤ lam) (n : ℕ) : 0 ≤ fourPMF a lam n := by
  have hZ := Zfun_pos ha hlam
  rw [fourPMF]
  exact div_nonneg (mul_nonneg (tweight_pos ha n).le (pow_nonneg hlam n)) (by positivity)

/-- **`eq:four-total-law` is a probability law.** -/
theorem hasSum_fourPMF (ha : 0 < a) (hlam : 0 ≤ lam) : HasSum (fourPMF a lam) 1 := by
  have hZ := Zfun_pos ha hlam
  have h := (summable_tweight ha lam).hasSum.div_const (Zfun a lam ^ 4)
  rw [← Zfun_pow_four ha lam, div_self (pow_ne_zero 4 hZ.ne')] at h
  exact h

/-! ### `eq:Tn-Kn-law`: the sector index law -/

/-- `P(K_n = k) = S_kS_{n-k}/T_n` (`eq:Tn-Kn-law`), independent of `λ`. -/
noncomputable def kPMF (a : ℝ) (n k : ℕ) : ℝ := sweight a k * sweight a (n - k) / tweight a n

theorem kPMF_pos (ha : 0 < a) (n k : ℕ) : 0 < kPMF a n k :=
  div_pos (mul_pos (sweight_pos ha k) (sweight_pos ha (n - k))) (tweight_pos ha n)

theorem sum_kPMF (ha : 0 < a) (n : ℕ) : ∑ k ∈ range (n + 1), kPMF a n k = 1 := by
  simp only [kPMF]
  rw [← Finset.sum_div, ← tweight, div_self (tweight_pos ha n).ne']

/-- **`eq:Tn-Kn-law`.**  `K_n` is the pair total `R` conditioned on the four-copy
total `N = n`, and the conditional law carries no `λ`. -/
theorem pairPMF_div_fourPMF (ha : 0 < a) (hlam : 0 < lam) {n k : ℕ} (hkn : k ≤ n) :
    pairPMF a lam k * pairPMF a lam (n - k) / fourPMF a lam n = kPMF a n k := by
  have hZ : Zfun a lam ≠ 0 := (Zfun_pos ha hlam.le).ne'
  have hT : tweight a n ≠ 0 := (tweight_pos ha n).ne'
  have hpow : lam ^ n ≠ 0 := pow_ne_zero n hlam.ne'
  have hpow' : lam ^ k * lam ^ (n - k) = lam ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [pairPMF, pairPMF, fourPMF, kPMF, div_mul_div_comm,
    show (4 : ℕ) = 2 + 2 from rfl, pow_add, div_div_div_eq, ← hpow']
  field_simp

/-! ### `eq:Delta-n-MD`: the mixed-determinant sum as a sector expectation -/

/-- `E f(K_n)` under `eq:Tn-Kn-law`. -/
noncomputable def kExp (a : ℝ) (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), f k * kPMF a n k

theorem tweight_mul_kExp (ha : 0 < a) (n : ℕ) (f : ℕ → ℝ) :
    tweight a n * kExp a n f
      = ∑ k ∈ range (n + 1), sweight a k * sweight a (n - k) * f k := by
  have hT : tweight a n ≠ 0 := (tweight_pos ha n).ne'
  rw [kExp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kPMF]
  field_simp

/-- The reduced sector sum as a sector expectation, at general `(κ,τ)`.  The two
weight conventions differ by `Γ(a)⁴`: `Zseries.sred_eq_sweight_mul`. -/
theorem DcoeffKT_eq_kExp (ha : 0 < a) (κ τ : ℝ) (n : ℕ) :
    DcoeffKT a κ τ n
      = Real.Gamma a ^ 4 * (tweight a n
          * kExp a n (fun k => SymMat.MD (NmatKT a κ τ k) (NmatKT a κ τ (n - k)))) := by
  rw [tweight_mul_kExp ha, DcoeffKT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sred_eq_sweight_mul ha k, sred_eq_sweight_mul ha (n - k)]
  ring

theorem Dcoeff_eq_kExp (ha : 0 < a) (n : ℕ) :
    Dcoeff a n
      = Real.Gamma a ^ 4 * (tweight a n
          * kExp a n (fun k => SymMat.MD (Nmat a k) (Nmat a (n - k)))) := by
  rw [tweight_mul_kExp ha, Dcoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sred_eq_sweight_mul ha k, sred_eq_sweight_mul ha (n - k)]
  ring

/-- **`eq:Delta-n-MD`, second equality.**  `Δ_n = (T_n/2)E MD(M_{K_n},M_{n-K_n})`.
Written on the normalized fibers `N_m = diag(1,g^{-1/2})M_m diag(1,g^{-1/2})`, under
which the mixed determinant scales by the determinant `g` of the congruence, so the
`ψ₁(a)/2` in front is the paper's `1/2` times that factor. -/
theorem turanDetCoeff_eq_kExp (ha : 0 < a) (n : ℕ) :
    turanDetCoeff a n
      = (trigamma a / 2) * (tweight a n
          * kExp a n (fun k => SymMat.MD (Nmat a k) (Nmat a (n - k)))) := by
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [turanDetCoeff_eq, turanCoeffFactor, Dcoeff_eq_kExp ha n]
  field_simp

/-! ### `eq:sector-density` and `eq:D-canonical-average` -/

/-- `d_n = 4Δ_n/(gT_n)` (`eq:sector-density`), at the endpoint `(κ,τ) = (1,1)`. -/
noncomputable def sectorDensity (a : ℝ) (n : ℕ) : ℝ :=
  4 * turanDetCoeff a n / (trigamma a * tweight a n)

/-- `d_n^{(κ,τ)}` (`eq:sector-density`) at general `(κ,τ)`, built from the reduced
sector `Phase.DcoeffKT`.  Its identification with `4[λⁿ]Δ^{(κ,τ)}/(gT_n)` is the
general-`(κ,τ)` determinant series; `sectorDensityKT_one_one` is the endpoint case,
where `Bridge.hasSum_turanDetCoeff` supplies that identification. -/
noncomputable def sectorDensityKT (a κ τ : ℝ) (n : ℕ) : ℝ :=
  4 * (turanCoeffFactor a * DcoeffKT a κ τ n) / (trigamma a * tweight a n)

theorem sectorDensityKT_one_one (ha : 0 < a) (n : ℕ) :
    sectorDensityKT a 1 1 n = sectorDensity a n := by
  rw [sectorDensityKT, sectorDensity, turanDetCoeff_eq, DcoeffKT, Dcoeff]
  refine congrArg (fun x => 4 * (turanCoeffFactor a * x) / (trigamma a * tweight a n)) ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show NmatKT a 1 1 k = Nmat a k from
      SymMat.ext rfl rfl (by rw [NmatKT_a22 ha, ddelta]; norm_num),
    show NmatKT a 1 1 (n - k) = Nmat a (n - k) from
      SymMat.ext rfl rfl (by rw [NmatKT_a22 ha, ddelta]; norm_num)]

/-- **`rem:ensemble-positivity`, the vacuum sector.**  `d_0^{(κ,τ)} = 4(τ-1)`: the
pointwise correction wall is visible before any positive-count sector is
populated. -/
theorem sectorDensityKT_zero (ha : 0 < a) (κ τ : ℝ) :
    sectorDensityKT a κ τ 0 = 4 * (τ - 1) := by
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  have hD : DcoeffKT a κ τ 0 = 2 * (τ - 1) := by
    rw [DcoeffKT, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sred_zero]
    simp only [Nat.sub_self, SymMat.MD, NmatKT_a11, NmatKT_a12, βcoef_zero,
      αcoef, Nat.cast_zero, add_zero]
    rw [NmatKT_a22 ha, Nmat_a22, ccoef_zero, ddelta]
    push_cast
    field
  rw [sectorDensityKT, hD, turanCoeffFactor, tweight_zero, sweight_zero_eq]
  field_simp

/-- **`eq:D-canonical-average`.**  The pointwise Bessel determinant is the canonical
average of the microcanonical sector densities: `4Δ/(gZ⁴) = E_λ d_N`. -/
theorem hasSum_sectorDensity (ha : 0 < a) (hlam : 0 ≤ lam) :
    HasSum (fun n : ℕ => sectorDensity a n * fourPMF a lam n)
      (4 * turanDet a lam / (trigamma a * Zfun a lam ^ 4)) := by
  have hZ := Zfun_pos ha hlam
  have hg := trigamma_pos ha
  have h := (hasSum_turanDetCoeff ha lam).div_const (trigamma a * Zfun a lam ^ 4 / 4)
  have hval : turanDet a lam / (trigamma a * Zfun a lam ^ 4 / 4)
      = 4 * turanDet a lam / (trigamma a * Zfun a lam ^ 4) := by
    field_simp
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  have hT : tweight a n ≠ 0 := (tweight_pos ha n).ne'
  rw [sectorDensity, fourPMF]
  field_simp

/-- **`eq:D-canonical-average` as `prop:four-copy` states it.**  With `a = ν+1` and
`λ = (z/2)²`, the Bessel--Schur defect `D_ν(z)` is the canonical average
`E_λ d_N` of the sector densities. -/
theorem besselDefect_eq_sectorAverage {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    HasSum (fun n : ℕ => sectorDensity (ν + 1) n * fourPMF (ν + 1) ((z / 2) ^ 2) n)
      (besselG ν z * (besselH ν z + 4 / trigamma (ν + 1)) - (1 + besselP ν z) ^ 2) := by
  have ha : 0 < ν + 1 := by linarith
  rw [besselDefect_eq hν hz]
  exact hasSum_sectorDensity ha (by positivity)

end TuranBessel
