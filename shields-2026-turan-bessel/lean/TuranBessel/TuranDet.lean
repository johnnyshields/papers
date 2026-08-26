/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.AlphaCoeff
import TuranBessel.BetaGammaCoeff
import TuranBessel.DetAssembly

/-!
# The Turán determinant and its Maclaurin coefficients

Closes the coefficient bridge of `shields-2026-turan-bessel.tex`, «Reciprocal-gamma convolution and
canonical--microcanonical structure»
(`sec:coefficients`, `eq:Tkt`, `eq:Delta-n-MD`).

`𝒯_{κ,τ}` of `eq:Tkt` is the symmetric matrix with entries `A`, `√g B`, `C_{κ,τ}`,
so its determinant is `Δ = AC - gB²`.  Each entry is a power series in `λ` whose
coefficients are identified elsewhere in this tree:

* `A`  by `AlphaCoeff.hasSum_Afun`   — `eq:alpha`, `[λᵐ]A = S_mψ₁(a+m)`
* `B`  by `BetaGammaCoeff.tsum_beta_eq_B`  — `eq:beta`, `[λᵐ]B = S_mβ_m`
* `C`  by `BetaGammaCoeff.tsum_gamma_eq_C` — `[λᵐ]C = S_m(τ+gc_m^{(κ)})`

and `DetAssembly.cauchy_eq_factor_mul_Dcoeff` turns the Cauchy product of those
three sequences into `Dcoeff`.  What remains, and is done here, is to run the
product: `turanDet_eq_tsum` and `hasSum_turanDet` show

```
  Δ(a,λ) = ∑_n [ψ₁(a) Γ(a)⁻⁴/2 · Dcoeff a n] λⁿ,
```

with the series converging for every real `λ`.  The bracket is
`Bridge.turanCoeffFactor a * Dcoeff a n`, so this is exactly the content that
`Bridge.turanDetCoeff_eq` used to assert: the `n`-th Maclaurin coefficient of the
genuine determinant is the mixed-determinant sum, up to that positive factor.

The absolute convergence needed for the Cauchy product is assembled from
`BetaGammaCoeff`'s `convCoeff` machinery — `summable_norm_beta_series` and
`summable_norm_gamma_series` here are the norm-level companions of its
`summable_convCoeff`, which it proves but does not export.

Sorry-free.
-/

open Finset

namespace TuranBessel

variable {a lam : ℝ}

/-! ### Absolute convergence of the three coefficient series -/

/-- Norm-summability survives a real linear combination of three sequences. -/
theorem summable_norm_lin3 {f₁ f₂ f₃ : ℕ → ℝ} (c₁ c₂ c₃ : ℝ)
    (h₁ : Summable fun m => ‖f₁ m‖) (h₂ : Summable fun m => ‖f₂ m‖)
    (h₃ : Summable fun m => ‖f₃ m‖) :
    Summable fun m => ‖c₁ * f₁ m + c₂ * f₂ m + c₃ * f₃ m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (((h₁.mul_left |c₁|).add (h₂.mul_left |c₂|)).add (h₃.mul_left |c₃|))
  calc ‖c₁ * f₁ m + c₂ * f₂ m + c₃ * f₃ m‖
      ≤ ‖c₁ * f₁ m + c₂ * f₂ m‖ + ‖c₃ * f₃ m‖ := norm_add_le _ _
    _ ≤ (‖c₁ * f₁ m‖ + ‖c₂ * f₂ m‖) + ‖c₃ * f₃ m‖ := by gcongr; exact norm_add_le _ _
    _ = |c₁| * ‖f₁ m‖ + |c₂| * ‖f₂ m‖ + |c₃| * ‖f₃ m‖ := by simp [Real.norm_eq_abs]

/-- The same for four. -/
theorem summable_norm_lin4 {f₁ f₂ f₃ f₄ : ℕ → ℝ} (c₁ c₂ c₃ c₄ : ℝ)
    (h₁ : Summable fun m => ‖f₁ m‖) (h₂ : Summable fun m => ‖f₂ m‖)
    (h₃ : Summable fun m => ‖f₃ m‖) (h₄ : Summable fun m => ‖f₄ m‖) :
    Summable fun m => ‖c₁ * f₁ m + c₂ * f₂ m + c₃ * f₃ m + c₄ * f₄ m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((((h₁.mul_left |c₁|).add (h₂.mul_left |c₂|)).add (h₃.mul_left |c₃|)).add (h₄.mul_left |c₄|))
  calc ‖c₁ * f₁ m + c₂ * f₂ m + c₃ * f₃ m + c₄ * f₄ m‖
      ≤ ‖c₁ * f₁ m + c₂ * f₂ m + c₃ * f₃ m‖ + ‖c₄ * f₄ m‖ := norm_add_le _ _
    _ ≤ ((‖c₁ * f₁ m‖ + ‖c₂ * f₂ m‖) + ‖c₃ * f₃ m‖) + ‖c₄ * f₄ m‖ := by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ = |c₁| * ‖f₁ m‖ + |c₂| * ‖f₂ m‖ + |c₃| * ‖f₃ m‖ + |c₄| * ‖f₄ m‖ := by
        simp [Real.norm_eq_abs]

/-- The antidiagonal form of `convCoeff`, at the level of individual terms. -/
theorem antidiagonal_eq_convCoeff (a lam : ℝ) (p q : ℕ → ℝ) (m : ℕ) :
    ∑ kl ∈ Finset.antidiagonal m, (p kl.1 * zterm a lam kl.1) * (q kl.2 * zterm a lam kl.2)
      = convCoeff a p q m * lam ^ m := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, convCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show p i * zterm a lam i * (q (m - i) * zterm a lam (m - i))
      = p i * q (m - i) * (zterm a lam i * zterm a lam (m - i)) by ring,
    zterm_mul_zterm a lam him]
  ring

/-- Norm-level companion of `BetaGammaCoeff.summable_convCoeff`. -/
theorem summable_norm_convCoeff {p q : ℕ → ℝ}
    (hp : Summable fun k => ‖p k * zterm a lam k‖)
    (hq : Summable fun k => ‖q k * zterm a lam k‖) :
    Summable fun m : ℕ => ‖convCoeff a p q m * lam ^ m‖ :=
  (summable_norm_sum_mul_antidiagonal_of_summable_norm hp hq).congr fun m => by
    rw [antidiagonal_eq_convCoeff]

/-- Norm-summability of the Cauchy product coefficients in `λ`, the companion of
`DetAssembly.tsum_cauchy_lam`. -/
theorem summable_norm_cauchy_lam {f g : ℕ → ℝ} (lam : ℝ)
    (hf : Summable fun m => ‖f m * lam ^ m‖) (hg : Summable fun m => ‖g m * lam ^ m‖) :
    Summable fun n : ℕ => ‖(∑ k ∈ range (n + 1), f k * g (n - k)) * lam ^ n‖ := by
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).congr fun n => ?_
  congr 1
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : lam ^ k * lam ^ (n - k) = lam ^ n := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  calc f k * lam ^ k * (g (n - k) * lam ^ (n - k))
      = f k * g (n - k) * (lam ^ k * lam ^ (n - k)) := by ring
    _ = f k * g (n - k) * lam ^ n := by rw [hpow]

/-- `∑ S_m β_m λᵐ` converges absolutely (`eq:beta`). -/
theorem summable_norm_beta_series (ha : 0 < a) (lam : ℝ) :
    Summable fun m : ℕ => ‖sweight a m * βcoef a m * lam ^ m‖ := by
  have h1 := summable_norm_one_zterm ha lam
  have hk := summable_norm_idx_zterm ha lam
  have hp := summable_norm_psi_zterm ha lam
  have hpk := summable_norm_psi_idx_zterm ha lam
  refine (summable_norm_lin3 (1 : ℝ) 1 (-1)
      (summable_norm_convCoeff h1 h1) (summable_norm_convCoeff h1 hpk)
      (summable_norm_convCoeff hp hk)).congr fun m => ?_
  congr 1
  rw [← bcoeffSum_eq ha]
  simp only [convCoeff, bcoeffSum, one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [← add_mul, ← sub_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine congrArg (· * lam ^ m) (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- `∑ S_m (τ + g c_m^{(κ)}) λᵐ` converges absolutely. -/
theorem summable_norm_gamma_series (ha : 0 < a) (g κ τ lam : ℝ) :
    Summable fun m : ℕ => ‖sweight a m * (τ + g * ckappa a κ m) * lam ^ m‖ := by
  have h1 := summable_norm_one_zterm ha lam
  have hk := summable_norm_idx_zterm ha lam
  have hk2 := summable_norm_sq_zterm ha lam
  refine (summable_norm_lin4 τ (g * κ) (-g) g
      (summable_norm_convCoeff h1 h1) (summable_norm_convCoeff h1 hk)
      (summable_norm_convCoeff h1 hk2) (summable_norm_convCoeff hk hk)).congr fun m => ?_
  congr 1
  rw [← ccoeffSum_eq ha]
  simp only [convCoeff, ccoeffSum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `∑ S_m ψ₁(a+m) λᵐ` converges absolutely (`eq:alpha`).  Over `ℝ` this is the
unconditional summability `hasSum_Afun` already carries. -/
theorem summable_norm_alpha_series (ha : 0 < a) (lam : ℝ) :
    Summable fun m : ℕ => ‖sweight a m * αcoef a m * lam ^ m‖ :=
  (hasSum_Afun ha lam).summable.abs.congr fun m => by simp [Real.norm_eq_abs, αcoef]

/-! ### The determinant -/

/-- `Δ = det 𝒯 = AC - gB²` of `eq:Tkt` at the endpoint `κ = τ = 1`. -/
noncomputable def turanDet (a lam : ℝ) : ℝ :=
  Afun a lam * Cseries a (trigamma a) 1 1 lam - trigamma a * Bseries a lam ^ 2

/-- **`eq:Delta-n-MD`.**  The Maclaurin coefficients of the genuine Turán
determinant are the mixed-determinant sums, up to `ψ₁(a)/(2Γ(a)⁴)`. -/
theorem turanDet_eq_tsum (ha : 0 < a) (lam : ℝ) :
    turanDet a lam
      = ∑' n : ℕ, (trigamma a / (2 * Real.Gamma a ^ 4) * Dcoeff a n) * lam ^ n := by
  have hA : Afun a lam = ∑' m : ℕ, (sweight a m * αcoef a m) * lam ^ m := Afun_eq_tsum ha lam
  have hB : Bseries a lam = ∑' m : ℕ, (sweight a m * βcoef a m) * lam ^ m := Bseries_eq_tsum ha lam
  have hC : Cseries a (trigamma a) 1 1 lam
      = ∑' m : ℕ, (sweight a m * (1 + trigamma a * ccoef a m)) * lam ^ m := by
    rw [Cseries_eq_tsum ha]
    exact tsum_congr fun m => by rw [ckappa_one_eq_ccoef ha]
  have hnA := summable_norm_alpha_series ha lam
  have hnB := summable_norm_beta_series ha lam
  have hnC : Summable fun m : ℕ => ‖sweight a m * (1 + trigamma a * ccoef a m) * lam ^ m‖ := by
    refine (summable_norm_gamma_series ha (trigamma a) 1 1 lam).congr fun m => ?_
    rw [ckappa_one_eq_ccoef ha]
  have hAC := tsum_cauchy_lam (f := fun m => sweight a m * αcoef a m)
      (g := fun m => sweight a m * (1 + trigamma a * ccoef a m)) lam hnA hnC
  have hBB := tsum_cauchy_lam (f := fun m => sweight a m * βcoef a m)
      (g := fun m => sweight a m * βcoef a m) lam hnB hnB
  have sAC := summable_norm_cauchy_lam (f := fun m => sweight a m * αcoef a m)
      (g := fun m => sweight a m * (1 + trigamma a * ccoef a m)) lam hnA hnC
  have sBB := summable_norm_cauchy_lam (f := fun m => sweight a m * βcoef a m)
      (g := fun m => sweight a m * βcoef a m) lam hnB hnB
  rw [turanDet, hA, hB, hC, sq, hAC, hBB, ← tsum_mul_left,
    ← Summable.tsum_sub sAC.of_norm (sBB.of_norm.mul_left _)]
  refine tsum_congr fun n => ?_
  rw [← mul_assoc, ← sub_mul]
  congr 1
  exact cauchy_eq_factor_mul_Dcoeff ha n

/-- The same statement as a `HasSum`: `Δ` is the sum of its Maclaurin series, for
every real `λ`. -/
theorem hasSum_turanDet (ha : 0 < a) (lam : ℝ) :
    HasSum (fun n : ℕ => (trigamma a / (2 * Real.Gamma a ^ 4) * Dcoeff a n) * lam ^ n)
      (turanDet a lam) := by
  have hnA := summable_norm_alpha_series ha lam
  have hnB := summable_norm_beta_series ha lam
  have hnC : Summable fun m : ℕ => ‖sweight a m * (1 + trigamma a * ccoef a m) * lam ^ m‖ := by
    refine (summable_norm_gamma_series ha (trigamma a) 1 1 lam).congr fun m => ?_
    rw [ckappa_one_eq_ccoef ha]
  have sAC := summable_norm_cauchy_lam (f := fun m => sweight a m * αcoef a m)
      (g := fun m => sweight a m * (1 + trigamma a * ccoef a m)) lam hnA hnC
  have sBB := summable_norm_cauchy_lam (f := fun m => sweight a m * βcoef a m)
      (g := fun m => sweight a m * βcoef a m) lam hnB hnB
  have hsum : Summable fun n : ℕ =>
      (trigamma a / (2 * Real.Gamma a ^ 4) * Dcoeff a n) * lam ^ n := by
    refine ((sAC.of_norm).sub ((sBB.of_norm).mul_left (trigamma a))).congr fun n => ?_
    rw [← mul_assoc, ← sub_mul]
    congr 1
    exact cauchy_eq_factor_mul_Dcoeff ha n
  exact hsum.hasSum_iff.mpr (turanDet_eq_tsum ha lam).symm

end TuranBessel
