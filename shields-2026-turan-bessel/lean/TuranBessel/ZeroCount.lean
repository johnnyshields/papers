/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Sharpness

/-!
# Exactly one zero below the pointwise wall

Formalizes `shields-2026-turan-bessel.tex`, «Reciprocal-gamma formulation and positivity phase
diagram»
(`sec:main`, `prop:bessel-sharpness`, `thm:two-parameter-coeff`, `eq:Delta0-tau`,
`eq:Dkappa-tau-Delta`).

The closing clause of `prop:bessel-sharpness`: for `κ ≥ 1` and
`τ_cw(a,κ) ≤ τ < 1` the deformed defect `D_ν^{(κ,τ)}` has exactly one zero on
`(0,∞)`.

Everything comes off the coefficient signs of `TuranDetKT.hasSum_turanDetKT`.
`TuranDetKT.DcoeffKT_zero` puts the degree-zero coefficient at `2(τ-1) < 0`;
`WallOrder.DcoeffKT_nonneg_of_ge` makes every positive-degree coefficient
nonnegative, and `DcoeffKT_pos_of_ge_two` — the two boundary regimes of
`thm:two-parameter-coeff` merged — makes every coefficient of degree at least
two strictly positive.  A power series with those signs is strictly increasing on
`[0,∞)` (`strictMonoOn_turanDetKT`) and diverges (`tendsto_turanDetKT_atTop`), so
it has exactly one positive zero.  `Sharpness.besselDefectKT_eq` transports that
zero along `λ = (x/2)²`, which is a bijection of `(0,∞)` onto itself, and the
factor `4/(gZ⁴)` is positive.

**Differs from the paper's route.**  The paper reaches the same clause through
`lem:large-argument-limit`, reading `Δ^{(κ,τ)}(a,λ) → +∞` off the large-argument
behavior of the Bessel quotients.  Here divergence is the two-term lower bound
`[λ⁰]Δ^{(κ,τ)} + [λ²]Δ^{(κ,τ)}λ²` over the nonnegative tail, so the coefficient
route needs no asymptotics at all — no Hankel expansion, and no `z → ∞` limit.

Sorry-free.
-/

open Filter Set Topology

namespace TuranBessel

variable {a κ τ ν lam : ℝ} {n : ℕ}

/-! ### The coefficient signs, merged across the two boundary regimes -/

/-- Every coefficient of degree at least two is strictly positive on the closed
half `τ ≥ τ_cw(a,κ)`: `WallOrder.two_parameter_boundary` on the boundary itself,
`WallOrder.DcoeffKT_pos_of_gt` above it. -/
theorem DcoeffKT_pos_of_ge_two (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ ≤ τ) (hn : 2 ≤ n) :
    0 < DcoeffKT a κ τ n := by
  rcases eq_or_lt_of_le hτ with h | h
  · rw [← h]
    exact DcoeffKT_boundary_kappa_pos ha hκ hn
  · exact DcoeffKT_pos_of_gt ha hκ h (by omega)

/-- The common positive prefactor of `eq:Delta-n-MD`. -/
theorem turanDetKT_coeff_factor_pos (ha : 0 < a) :
    0 < trigamma a / (2 * Real.Gamma a ^ 4) :=
  div_pos (trigamma_pos ha)
    (mul_pos (by norm_num) (pow_pos (Real.Gamma_pos_of_pos ha) 4))

/-- Each positive-degree term of the expansion is nonnegative for `λ ≥ 0`. -/
theorem turanDetKT_term_nonneg (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ ≤ τ)
    (hlam : 0 ≤ lam) (hn : 1 ≤ n) :
    0 ≤ trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n * lam ^ n :=
  mul_nonneg
    (mul_nonneg (turanDetKT_coeff_factor_pos ha).le (DcoeffKT_nonneg_of_ge ha hκ hτ hn))
    (pow_nonneg hlam n)

/-! ### Strict monotonicity -/

/-- **`Δ^{(κ,τ)}(a,·)` is strictly increasing on `[0,∞)`** whenever `κ ≥ 1` and
`τ ≥ τ_cw(a,κ)`.  Compare the two expansions termwise: the degree-zero terms
agree, every positive-degree coefficient is nonnegative, and the degree-two
coefficient is strictly positive by `DcoeffKT_pos_of_ge_two`, which is where the
strictness comes from — on the boundary `τ = τ_cw(a,κ)` the degree-one
coefficient vanishes, so degree two is the first one available.

This is the differentiated statement of `prop:bessel-sharpness`'s proof without
differentiating: the paper reads `dΔ^{(κ,τ)}/dλ > 0` off the same coefficient
signs. -/
theorem strictMonoOn_turanDetKT (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ ≤ τ) :
    StrictMonoOn (fun lam : ℝ => turanDetKT a κ τ lam) (Ici 0) := by
  intro u hu v _ huv
  have hu0 : (0 : ℝ) ≤ u := hu
  have hv0 : (0 : ℝ) ≤ v := hu0.trans huv.le
  have hle : (fun n : ℕ => trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n * u ^ n)
      ≤ fun n : ℕ => trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ n * v ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 huv.le n)
        (mul_nonneg (turanDetKT_coeff_factor_pos ha).le (DcoeffKT_nonneg_of_ge ha hκ hτ h))
  have hstrict : trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 2 * u ^ 2
      < trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 2 * v ^ 2 :=
    mul_lt_mul_of_pos_left (pow_lt_pow_left₀ huv hu0 two_ne_zero)
      (mul_pos (turanDetKT_coeff_factor_pos ha) (DcoeffKT_pos_of_ge_two ha hκ hτ le_rfl))
  exact hasSum_lt hle hstrict (hasSum_turanDetKT ha κ τ u) (hasSum_turanDetKT ha κ τ v)

/-! ### Divergence -/

/-- The two-term lower bound: keeping degrees `0` and `2` and discarding a
nonnegative tail. -/
theorem two_term_le_turanDetKT (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ ≤ τ)
    (hlam : 0 ≤ lam) :
    trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 0
        + trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 2 * lam ^ 2
      ≤ turanDetKT a κ τ lam := by
  have hpair : ∑ i ∈ ({0, 2} : Finset ℕ),
      trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ i * lam ^ i
      = trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 0
        + trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 2 * lam ^ 2 := by
    rw [Finset.sum_pair (by norm_num)]
    norm_num
  rw [← hpair]
  refine sum_le_hasSum _ (fun i hi => ?_) (hasSum_turanDetKT ha κ τ lam)
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact absurd (by simp [h] : i ∈ ({0, 2} : Finset ℕ)) hi
    · exact h
  exact turanDetKT_term_nonneg ha hκ hτ hlam hi1

/-- **`Δ^{(κ,τ)}(a,λ) → +∞` as `λ → ∞`**, for `κ ≥ 1` and `τ ≥ τ_cw(a,κ)`.
**Differs from the paper's route.**  The paper takes this divergence from
`lem:large-argument-limit`, the two-term large-argument expansion of the Bessel
quotients.  Here it is the degree-two term of the series alone, over a tail that
`turanDetKT_term_nonneg` makes nonnegative on `λ ≥ 0`, so the coefficient route
needs no asymptotics — no Hankel expansion and no `z → ∞` limit. -/
theorem tendsto_turanDetKT_atTop (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ ≤ τ) :
    Tendsto (fun lam : ℝ => turanDetKT a κ τ lam) atTop atTop := by
  have hc2 : 0 < trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 2 :=
    mul_pos (turanDetKT_coeff_factor_pos ha) (DcoeffKT_pos_of_ge_two ha hκ hτ le_rfl)
  have hlow : Tendsto (fun lam : ℝ => trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 0
      + trigamma a / (2 * Real.Gamma a ^ 4) * DcoeffKT a κ τ 2 * lam ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop _
      (Tendsto.const_mul_atTop hc2 (tendsto_pow_atTop two_ne_zero))
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
  exact two_term_le_turanDetKT ha hκ hτ hlam

/-! ### Exactly one positive zero of `Δ^{(κ,τ)}` -/

theorem continuous_turanDetKT_lam (ha : 0 < a) (κ τ : ℝ) :
    Continuous fun lam : ℝ => turanDetKT a κ τ lam :=
  continuous_iff_continuousAt.mpr fun lam => continuousAt_turanDetKT_lam ha κ τ lam

/-- **`prop:bessel-sharpness`'s zero-counting clause, on the reciprocal-gamma
side.**  For `κ ≥ 1` and `τ_cw(a,κ) ≤ τ < 1` the determinant series
`Δ^{(κ,τ)}(a,·)` has exactly one zero on `(0,∞)`.  Existence is the intermediate
value theorem between the negative value `g(τ-1)/Γ(a)⁴` at `λ = 0`
(`eq:Delta0-tau`) and a positive value supplied by `tendsto_turanDetKT_atTop`;
uniqueness is `strictMonoOn_turanDetKT`. -/
theorem exists_unique_zero_turanDetKT (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ ≤ τ)
    (hτ1 : τ < 1) :
    ∃! lam : ℝ, 0 < lam ∧ turanDetKT a κ τ lam = 0 := by
  have hcont : Continuous fun lam : ℝ => turanDetKT a κ τ lam := continuous_turanDetKT_lam ha κ τ
  have hneg : turanDetKT a κ τ 0 < 0 := by
    rw [turanDetKT_lam_zero ha]
    exact div_neg_of_neg_of_pos (by nlinarith [trigamma_pos ha])
      (pow_pos (Real.Gamma_pos_of_pos ha) 4)
  obtain ⟨b, hb0, hbpos⟩ :
      ∃ b : ℝ, 0 < b ∧ 0 < turanDetKT a κ τ b := by
    have h := (tendsto_turanDetKT_atTop ha hκ hτ).eventually_gt_atTop 0
    obtain ⟨b, hb, hb'⟩ := (h.and (eventually_gt_atTop (0 : ℝ))).exists
    exact ⟨b, hb', hb⟩
  obtain ⟨lam0, hlam0mem, hlam0⟩ :=
    intermediate_value_Ioo hb0.le hcont.continuousOn (mem_Ioo.mpr ⟨hneg, hbpos⟩)
  refine ⟨lam0, ⟨hlam0mem.1, hlam0⟩, ?_⟩
  rintro lam ⟨hlam, hlameq⟩
  exact (strictMonoOn_turanDetKT ha hκ hτ).injOn (mem_Ici.mpr hlam.le)
    (mem_Ici.mpr hlam0mem.1.le) (by rw [hlameq]; exact hlam0.symm)

/-! ### Transport to the Bessel defect -/

/-- **`prop:bessel-sharpness`, the zero-counting clause.**  For `ν > -1`,
`κ ≥ 1` and `τ_cw(ν+1,κ) ≤ τ < 1`, the deformed Bessel defect
`D_ν^{(κ,τ)} = G_ν(H_ν^{(κ)} + 4τ/g) - (1+P_ν)²` has exactly one zero on
`(0,∞)`.  `eq:Dkappa-tau-Delta` writes it as `4Δ^{(κ,τ)}(a,λ)/(gZ⁴)` with
`a = ν+1` and `λ = (x/2)²`; the factor is positive, so the zero sets match, and
`x ↦ (x/2)²` is a bijection of `(0,∞)` onto itself. -/
theorem exists_unique_zero_besselDefectKT (hν : -1 < ν) (hκ : 1 ≤ κ)
    (hτ : tauCw (ν + 1) κ ≤ τ) (hτ1 : τ < 1) :
    ∃! x : ℝ, 0 < x ∧
      besselG ν x * (besselHkappa κ ν x + 4 * τ / trigamma (ν + 1))
        - (1 + besselP ν x) ^ 2 = 0 := by
  have ha : 0 < ν + 1 := by linarith
  obtain ⟨lam0, ⟨hlam0pos, hlam0⟩, huniq⟩ := exists_unique_zero_turanDetKT ha hκ hτ hτ1
  -- the defect vanishes at `x > 0` exactly when `Δ^{(κ,τ)}` vanishes at `(x/2)²`
  have hiff : ∀ x : ℝ, 0 < x →
      (besselG ν x * (besselHkappa κ ν x + 4 * τ / trigamma (ν + 1))
        - (1 + besselP ν x) ^ 2 = 0 ↔ turanDetKT (ν + 1) κ τ ((x / 2) ^ 2) = 0) := by
    intro x hx
    have hlam : 0 < (x / 2) ^ 2 := by positivity
    have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha hlam.le
    have hden : trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 4 ≠ 0 :=
      (mul_pos (trigamma_pos ha) (pow_pos hZ 4)).ne'
    rw [besselDefectKT_eq hν κ τ, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hden
    · intro h; left; rw [h]; ring
  set x0 : ℝ := 2 * Real.sqrt lam0 with hx0def
  have hsqrt : 0 < Real.sqrt lam0 := Real.sqrt_pos.mpr hlam0pos
  have hx0 : 0 < x0 := by rw [hx0def]; linarith
  have hx0lam : (x0 / 2) ^ 2 = lam0 := by
    rw [hx0def, show 2 * Real.sqrt lam0 / 2 = Real.sqrt lam0 by ring,
      Real.sq_sqrt hlam0pos.le]
  refine ⟨x0, ⟨hx0, (hiff x0 hx0).mpr (by rw [hx0lam]; exact hlam0)⟩, ?_⟩
  rintro x ⟨hx, hxeq⟩
  have hlam : 0 < (x / 2) ^ 2 := by positivity
  have hxlam : (x / 2) ^ 2 = lam0 := huniq ((x / 2) ^ 2) ⟨hlam, (hiff x hx).mp hxeq⟩
  -- `(x/2)² = lam0 = (x0/2)²` with both halves positive forces `x = x0`
  have hhalf : x / 2 = x0 / 2 := by
    have hsq : (x / 2) ^ 2 = (x0 / 2) ^ 2 := by rw [hxlam, hx0lam]
    nlinarith [hsq, hx, hx0]
  linarith

end TuranBessel
