/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.TuranDet
import TuranBessel.WallOrder

/-!
# The two-parameter determinant series

Formalizes `shields-2026-turan-bessel.tex`, «Reciprocal-gamma formulation and positivity phase
diagram»
(`sec:main`, `eq:Ckt-def`, `eq:Delta0-tau`, `thm:two-parameter-coeff`).

`TuranDet` runs the Cauchy product at the endpoint `κ = τ = 1`.  Everything it
consumes is already stated at general `(κ,τ)` — `BetaGammaCoeff.Cseries_eq_tsum`
identifies `[λᵐ]C_{κ,τ} = S_m(τ + g c_m^{(κ)})`, and
`summable_norm_gamma_series` is the norm-level companion at the same generality —
so the deformed determinant
```
  Δ^{(κ,τ)} = A C_{κ,τ} - g B²
```
has the same expansion with `Phase.DcoeffKT` in place of `Dcoeff`:
`turanDetKT_eq_tsum` and `hasSum_turanDetKT`.

The degree-zero coefficient is where the two parameters part company with the
coefficientwise theory.  `DcoeffKT_zero` is `2(τ-1)`, i.e. `eq:Delta0-tau`, and it
is **negative** for `τ < 1` while `WallOrder.DcoeffKT_pos_of_gt` keeps every
positive-degree coefficient strictly positive down to `τ_cw(a,κ) < 1`.  So
pointwise positivity of `Δ^{(κ,τ)}` on `λ > 0` needs `τ ≥ 1`, not merely
`τ > τ_cw`: `turanDetKT_pos` is stated on the quadrant `κ ≥ 1`, `τ ≥ 1`, and
`turanDetKT_lam_zero` records the boundary value `g(τ-1)/Γ(a)⁴` that a continuity
argument turns into that failure.

Sorry-free.
-/

open Finset

namespace TuranBessel

variable {a κ τ lam : ℝ}

/-- `Δ^{(κ,τ)} = A C_{κ,τ} - g B²` of `eq:Tkt`, the determinant of the deformed
matrix `𝒯_{κ,τ}`.  At `κ = τ = 1` this is `TuranDet.turanDet` on the nose. -/
noncomputable def turanDetKT (a κ τ lam : ℝ) : ℝ :=
  Afun a lam * Cseries a (trigamma a) κ τ lam - trigamma a * Bseries a lam ^ 2

theorem turanDetKT_endpoint (a lam : ℝ) : turanDetKT a 1 1 lam = turanDet a lam := rfl

/-! ### The Cauchy product at general `(κ,τ)` -/

/-- **The algebraic half of `eq:Delta-n-MD` at general `(κ,τ)`.**  Verbatim the
route of `DetAssembly.cauchy_eq_factor_mul_Dcoeff`: the deformation enters only
through the `(2,2)` entry `τ/g + c_m^{(κ)}`, and the reflection `k ↦ n-k` removes
the asymmetry exactly as it does at the endpoint. -/
theorem cauchy_eq_factor_mul_DcoeffKT (ha : 0 < a) (κ τ : ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1),
        (sweight a k * αcoef a k)
          * (sweight a (n - k) * (τ + trigamma a * ckappa a κ (n - k))))
      - trigamma a * ∑ k ∈ range (n + 1),
        (sweight a k * βcoef a k) * (sweight a (n - k) * βcoef a (n - k))
      = trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n := by
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  have hR : trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n
      = ∑ k ∈ range (n + 1), (trigamma a / 2) *
          (sweight a k * sweight a (n - k)
            * SymMat.MD (NmatKT a κ τ k) (NmatKT a κ τ (n - k))) := by
    rw [DcoeffKT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sred_eq_sweight_mul ha k, sred_eq_sweight_mul ha (n - k)]
    field_simp
  rw [hR, Finset.mul_sum, ← Finset.sum_sub_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ range (n + 1),
      ((sweight a k * αcoef a k)
            * (sweight a (n - k) * (τ + trigamma a * ckappa a κ (n - k)))
        - trigamma a * ((sweight a k * βcoef a k) * (sweight a (n - k) * βcoef a (n - k))))
      - (trigamma a / 2) *
          (sweight a k * sweight a (n - k)
            * SymMat.MD (NmatKT a κ τ k) (NmatKT a κ τ (n - k)))
      = (1 / 2) * ((fun j => sweight a j * sweight a (n - j) * αcoef a j
              * (τ + trigamma a * ckappa a κ (n - j))) k
          - (fun j => sweight a j * sweight a (n - j) * αcoef a j
              * (τ + trigamma a * ckappa a κ (n - j))) (n - k)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : n - (n - k) = k := Nat.sub_sub_self hkn
    simp only [SymMat.MD, NmatKT, h1]
    field
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hrefl : ∑ k ∈ range (n + 1),
      (fun j => sweight a j * sweight a (n - j) * αcoef a j
          * (τ + trigamma a * ckappa a κ (n - j))) (n - k)
      = ∑ k ∈ range (n + 1),
      (fun j => sweight a j * sweight a (n - j) * αcoef a j
          * (τ + trigamma a * ckappa a κ (n - j))) k := by
    simpa using Finset.sum_range_reflect
      (fun j => sweight a j * sweight a (n - j) * αcoef a j
          * (τ + trigamma a * ckappa a κ (n - j))) (n + 1)
  rw [hrefl, sub_self, mul_zero]

/-! ### The expansion -/

/-- **`eq:Delta-n-MD` at general `(κ,τ)`.** -/
theorem turanDetKT_eq_tsum (ha : 0 < a) (κ τ : ℝ) (lam : ℝ) :
    turanDetKT a κ τ lam
      = ∑' n : ℕ, (trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n) * lam ^ n := by
  have hA : Afun a lam = ∑' m : ℕ, (sweight a m * αcoef a m) * lam ^ m := Afun_eq_tsum ha lam
  have hB : Bseries a lam = ∑' m : ℕ, (sweight a m * βcoef a m) * lam ^ m := Bseries_eq_tsum ha lam
  have hC : Cseries a (trigamma a) κ τ lam
      = ∑' m : ℕ, (sweight a m * (τ + trigamma a * ckappa a κ m)) * lam ^ m :=
    Cseries_eq_tsum ha (trigamma a) κ τ lam
  have hnA := summable_norm_alpha_series ha lam
  have hnB := summable_norm_beta_series ha lam
  have hnC := summable_norm_gamma_series ha (trigamma a) κ τ lam
  have hAC := tsum_cauchy_lam (f := fun m => sweight a m * αcoef a m)
      (g := fun m => sweight a m * (τ + trigamma a * ckappa a κ m)) lam hnA hnC
  have hBB := tsum_cauchy_lam (f := fun m => sweight a m * βcoef a m)
      (g := fun m => sweight a m * βcoef a m) lam hnB hnB
  have sAC := summable_norm_cauchy_lam (f := fun m => sweight a m * αcoef a m)
      (g := fun m => sweight a m * (τ + trigamma a * ckappa a κ m)) lam hnA hnC
  have sBB := summable_norm_cauchy_lam (f := fun m => sweight a m * βcoef a m)
      (g := fun m => sweight a m * βcoef a m) lam hnB hnB
  rw [turanDetKT, hA, hB, hC, sq, hAC, hBB, ← tsum_mul_left,
    ← Summable.tsum_sub sAC.of_norm (sBB.of_norm.mul_left _)]
  refine tsum_congr fun n => ?_
  rw [← mul_assoc, ← sub_mul]
  congr 1
  exact cauchy_eq_factor_mul_DcoeffKT ha κ τ n

/-- The same statement as a `HasSum`, for every real `λ`. -/
theorem hasSum_turanDetKT (ha : 0 < a) (κ τ : ℝ) (lam : ℝ) :
    HasSum (fun n : ℕ => (trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n) * lam ^ n)
      (turanDetKT a κ τ lam) := by
  have hnA := summable_norm_alpha_series ha lam
  have hnB := summable_norm_beta_series ha lam
  have hnC := summable_norm_gamma_series ha (trigamma a) κ τ lam
  have sAC := summable_norm_cauchy_lam (f := fun m => sweight a m * αcoef a m)
      (g := fun m => sweight a m * (τ + trigamma a * ckappa a κ m)) lam hnA hnC
  have sBB := summable_norm_cauchy_lam (f := fun m => sweight a m * βcoef a m)
      (g := fun m => sweight a m * βcoef a m) lam hnB hnB
  have hsum : Summable fun n : ℕ =>
      (trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n) * lam ^ n := by
    refine ((sAC.of_norm).sub ((sBB.of_norm).mul_left (trigamma a))).congr fun n => ?_
    rw [← mul_assoc, ← sub_mul]
    congr 1
    exact cauchy_eq_factor_mul_DcoeffKT ha κ τ n
  exact hsum.hasSum_iff.mpr (turanDetKT_eq_tsum ha κ τ lam).symm

/-! ### The degree-zero sector, and pointwise positivity -/

/-- **`eq:Delta0-tau`.**  `N_0^{(κ,τ)} = (g, 1, τ/g)` has determinant `τ - 1`, so
the degree-zero sector is `2(τ-1)` — independent of `κ`, and negative below the
pointwise wall `τ = 1`.  Multiplying by `Bridge.turanCoeffFactor` gives the
paper's `[λ⁰]Δ^{(κ,τ)} = g(τ-1)/Γ(a)⁴`. -/
theorem DcoeffKT_zero (ha : 0 < a) (κ τ : ℝ) : DcoeffKT a κ τ 0 = 2 * (τ - 1) := by
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  have h : DcoeffKT a κ τ 0
      = sred a 0 * sred a 0 * SymMat.MD (NmatKT a κ τ 0) (NmatKT a κ τ 0) := by
    simp [DcoeffKT]
  rw [h, sred_zero]
  simp only [SymMat.MD, NmatKT, αcoef, βcoef_zero, ckappa_zero, Nat.cast_zero, add_zero]
  field

/-- The value at `λ = 0`: only the degree-zero term survives, so
`Δ^{(κ,τ)}(a,0) = g(τ-1)/Γ(a)⁴`, negative for every `τ < 1` and every `κ`. -/
theorem turanDetKT_lam_zero (ha : 0 < a) (κ τ : ℝ) :
    turanDetKT a κ τ 0 = trigamma a * (τ - 1) / Real.Gamma a ^ 4 := by
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hsingle : HasSum
      (fun n : ℕ => (trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n) * (0 : ℝ) ^ n)
      ((trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 0) * (0 : ℝ) ^ 0) :=
    hasSum_single 0 (fun n hn => by
      rw [zero_pow (by simpa using hn), mul_zero])
  have := (hasSum_turanDetKT ha κ τ 0).unique hsingle
  rw [this, DcoeffKT_zero ha]
  field_simp

/-- **`Δ^{(κ,τ)}(a,λ) > 0` on the quadrant `κ ≥ 1`, `τ ≥ 1`.**  The degree-zero
coefficient is `2(τ-1) ≥ 0` there, and `τ_cw(a,κ) < 1 ≤ τ` puts every
positive-degree coefficient strictly above zero by
`WallOrder.DcoeffKT_pos_of_gt`. -/
theorem turanDetKT_pos (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : 1 ≤ τ) (hlam : 0 < lam) :
    0 < turanDetKT a κ τ lam := by
  have hfac : 0 < trigamma a / (2 * Real.Gamma a ^ 4) :=
    div_pos (trigamma_pos ha)
      (mul_pos (by norm_num) (pow_pos (Real.Gamma_pos_of_pos ha) 4))
  have hwall : tauCw a κ < τ := lt_of_lt_of_le (tauCw_lt_one ha hκ) hτ
  have hsum := hasSum_turanDetKT ha κ τ lam
  have hnn : ∀ n : ℕ, 0 ≤ trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n * lam ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [DcoeffKT_zero ha]
      have : (0 : ℝ) ≤ 2 * (τ - 1) := by linarith
      positivity
    · exact (mul_pos (mul_pos hfac (DcoeffKT_pos_of_gt ha hκ hwall h)) (pow_pos hlam n)).le
  rw [← hsum.tsum_eq]
  exact hsum.summable.tsum_pos hnn 1
    (mul_pos (mul_pos hfac (DcoeffKT_pos_of_gt ha hκ hwall le_rfl)) (pow_pos hlam 1))

end TuranBessel
