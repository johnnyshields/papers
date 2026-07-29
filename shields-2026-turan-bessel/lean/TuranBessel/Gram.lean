/-
# Gram representation and positive definiteness of the stable coefficients

Formalizes `shields-2026-turan-bessel.tex`, §4 «Gram structure and the
exceptional matrix M₁» (`sec:gram`, Theorem 4.2 = `thm:gram`).  In `ℓ²` set
`u_r = (x+r)⁻¹`, `v_r = q (x-1+r)⁻¹` with `x = a+m`, `q = a+m/2-1` (the Lean
identifier for the scale `q` is `gramP`).  Then `‖u‖² = ψ₁(x) = α_m`,
`⟨u,v⟩ = q/(x-1) = β_m`, `‖v‖² = q² ψ₁(x-1)`,
and Cauchy–Schwarz plus the positive Gram slack
`ρ_m = g⁻¹ + c_m - q² ψ₁(x-1) > 0` give `det N_m > 0`, hence `N_m ≻ 0`, for
`m ≥ 2` (all `a>0`) and for `m = 1` (all `a ≥ 1/2`).

The slack `ρ_m` (`eq:rho-m`, eq. (4.8)) is positive: the trigamma upper bound
`ψ₁(x-1) < 1/(x-3/2)` and `1/g > a-1/2` reduce it to the rational identity
`(a-1/2) + c_m - q²/(x-3/2) = (m-1)/(2(2a+2m-3)) > 0`.

Sorry-free.
-/
import TuranBessel.Coefficients

open scoped BigOperators

namespace TuranBessel

variable {a : ℝ}

/-- `p = a + m/2 - 1`. -/
noncomputable def gramP (a : ℝ) (m : ℕ) : ℝ := a + (m : ℝ) / 2 - 1

/-- Gram slack `ρ_m = g⁻¹ + c_m - p² ψ₁(x-1)`. -/
noncomputable def rho (a : ℝ) (m : ℕ) : ℝ :=
  (trigamma a)⁻¹ + ccoef a m - (gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1)

/-- `1/g > a - 1/2` (`eq:inverse-trig`): trivial for `a ≤ 1/2`, and the trigamma
upper bound for `a > 1/2`. -/
theorem inv_trigamma_gt (ha : 0 < a) : a - 1 / 2 < (trigamma a)⁻¹ := by
  have hg : 0 < trigamma a := trigamma_pos ha
  by_cases h : a ≤ 1 / 2
  · have : (0 : ℝ) < (trigamma a)⁻¹ := inv_pos.mpr hg
    linarith
  · push_neg at h
    have hub : trigamma a < (a - 1 / 2)⁻¹ := trigamma_lt_upper h
    have hkey := inv_strictAnti₀ hg hub
    rwa [inv_inv] at hkey

/-- The rational slack identity for `m ≥ 2` (in the proof of `thm:gram`). -/
theorem slack_identity (ha : 0 < a) {m : ℕ} (hm : 2 ≤ m) :
    (a - 1 / 2) + ccoef a m - (gramP a m) ^ 2 * (a + (m : ℝ) - 3 / 2)⁻¹
      = (((m : ℝ) - 1) / (2 * (2 * a + 2 * (m : ℝ) - 3))) := by
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hd1 : (2 * a + 2 * (m : ℝ) - 3) ≠ 0 := by nlinarith
  unfold ccoef gramP
  rw [if_neg (by omega)]
  rw [show a + (m : ℝ) - 3 / 2 = (2 * a + 2 * (m : ℝ) - 3) / 2 from by ring, inv_div]
  field_simp
  linear_combination (1 - 2 * a) * inv_mul_cancel₀ hd1

/-- `ρ_m > 0` for `m ≥ 2` and any `a > 0`. -/
theorem rho_pos_of_two (ha : 0 < a) {m : ℕ} (hm : 2 ≤ m) : 0 < rho a m := by
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- `x-1 = a+m-1 > 1/2`, so the trigamma upper bound applies.
  have hx1 : (1 : ℝ) / 2 < a + (m : ℝ) - 1 := by nlinarith
  have hub : trigamma (a + (m : ℝ) - 1) < (a + (m : ℝ) - 1 - 1 / 2)⁻¹ := trigamma_lt_upper hx1
  have hp2 : (0 : ℝ) < (gramP a m) ^ 2 := by
    have : 0 < gramP a m := by unfold gramP; nlinarith
    positivity
  -- `-p² ψ₁(x-1) > -p²/(x-3/2)` and `g⁻¹ > a-1/2`; combine with the slack identity.
  have hstep : (gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1)
      < (gramP a m) ^ 2 * (a + (m : ℝ) - 3 / 2)⁻¹ := by
    have hmul := mul_lt_mul_of_pos_left hub hp2
    have heq : (a + (m : ℝ) - 1 - 1 / 2)⁻¹ = (a + (m : ℝ) - 3 / 2)⁻¹ := by congr 1; ring
    rwa [heq] at hmul
  have hg : a - 1 / 2 < (trigamma a)⁻¹ := inv_trigamma_gt ha
  have hslack := slack_identity ha hm
  have hpos : 0 < ((m : ℝ) - 1) / (2 * (2 * a + 2 * (m : ℝ) - 3)) := by
    apply div_pos <;> nlinarith
  unfold rho
  linarith [hslack, hpos, hstep, hg]

/-- `ρ_1 > 0` for `a ≥ 1/2`. -/
theorem rho_pos_one (ha : 1 / 2 ≤ a) : 0 < rho a 1 := by
  have ha0 : 0 < a := by linarith
  have hg : 0 < trigamma a := trigamma_pos ha0
  have hpval : gramP a 1 = a - 1 / 2 := by unfold gramP; push_cast; ring
  unfold rho
  simp only [ccoef_one, add_zero, Nat.cast_one]
  rw [hpval, show a + (1 : ℝ) - 1 = a from by ring]
  -- goal: `0 < (trigamma a)⁻¹ - (a-1/2)² ψ₁(a)`
  rcases eq_or_lt_of_le ha with h | h
  · have hp0 : a - 1 / 2 = 0 := by linarith
    rw [hp0, show (0 : ℝ) ^ 2 = 0 from by norm_num, zero_mul, sub_zero]
    exact inv_pos.mpr hg
  · have hub : trigamma a < (a - 1 / 2)⁻¹ := trigamma_lt_upper h
    have hp : (0 : ℝ) < a - 1 / 2 := by linarith
    have h1 : (a - 1 / 2) * trigamma a < 1 := by
      have hmul := mul_lt_mul_of_pos_left hub hp
      rwa [mul_inv_cancel₀ hp.ne'] at hmul
    have hgi : (a - 1 / 2) ^ 2 * trigamma a < (trigamma a)⁻¹ := by
      nlinarith [h1, mul_pos hp hg, hg, inv_pos.mpr hg, mul_inv_cancel₀ hg.ne']
    linarith

/-- The Gram cross term `∑ u_r v_r`: `∑ ((x+r)(x-1+r))⁻¹ = (x-1)⁻¹`, `x = a+m`. -/
theorem cross_sum (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) :
    ∑' r : ℕ, (a + (m : ℝ) + (r : ℝ))⁻¹ * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹
      = (a + (m : ℝ) - 1)⁻¹ := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hc : 0 < a + (m : ℝ) - 1 := by linarith
  have hterm : ∀ r : ℕ, (a + (m : ℝ) + (r : ℝ))⁻¹ * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹
      = (a + (m : ℝ) - 1 + (r : ℝ))⁻¹ - (a + (m : ℝ) - 1 + (r : ℝ) + 1)⁻¹ := by
    intro r
    have hcr : 0 < a + (m : ℝ) - 1 + (r : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) r; linarith
    have hcr1 : 0 < a + (m : ℝ) - 1 + (r : ℝ) + 1 := by linarith
    rw [inv_sub_inv_succ hcr.ne' hcr1.ne', mul_inv,
      show a + (m : ℝ) + (r : ℝ) = a + (m : ℝ) - 1 + (r : ℝ) + 1 from by ring]
    ring
  rw [tsum_congr hterm]
  exact (telescope_hasSum hc).tsum_eq

/-- `β_m = p/(x-1)` with `p = a+m/2-1`, `x = a+m`, for `m ≥ 1`. -/
theorem βcoef_eq_gram (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) :
    βcoef a m = gramP a m * (a + (m : ℝ) - 1)⁻¹ := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hc : a + (m : ℝ) - 1 ≠ 0 := by
    have : 0 < a + (m : ℝ) - 1 := by linarith
    exact this.ne'
  unfold βcoef gramP
  rw [if_neg (by omega)]
  field_simp

/-- `det N_m > 0` for `m ≥ 1` given `ρ_m > 0`: Cauchy–Schwarz plus the Gram
slack.  This is `β_m² < α_m (g⁻¹ + c_m)`. -/
theorem Nmat_det_pos (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (hρ : 0 < rho a m) :
    (βcoef a m) ^ 2 < αcoef a m * ((trigamma a)⁻¹ + ccoef a m) := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : 0 < a + (m : ℝ) := by linarith
  have hxm1 : 0 < a + (m : ℝ) - 1 := by linarith
  have hu2 : Summable (fun r : ℕ => ((a + (m : ℝ) + (r : ℝ))⁻¹) ^ 2) :=
    trigamma_summable hx
  have hv2 : Summable (fun r : ℕ => (gramP a m * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹) ^ 2) := by
    simp_rw [mul_pow]
    exact (trigamma_summable hxm1).mul_left ((gramP a m) ^ 2)
  have hcs := tsum_mul_sq_le hu2 hv2
  -- identify the three tsums
  have hnu : (∑' r : ℕ, ((a + (m : ℝ) + (r : ℝ))⁻¹) ^ 2) = αcoef a m := by
    rw [αcoef, trigamma]
  have hnv : (∑' r : ℕ, (gramP a m * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹) ^ 2)
      = (gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1) := by
    simp_rw [mul_pow]; rw [tsum_mul_left, trigamma]
  have huv : (∑' r : ℕ, (a + (m : ℝ) + (r : ℝ))⁻¹ * (gramP a m * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹))
      = gramP a m * (a + (m : ℝ) - 1)⁻¹ := by
    rw [tsum_congr (fun r => by ring :
      ∀ r : ℕ, (a + (m : ℝ) + (r : ℝ))⁻¹ * (gramP a m * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹)
        = gramP a m * ((a + (m : ℝ) + (r : ℝ))⁻¹ * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹))]
    rw [tsum_mul_left, cross_sum ha hm]
  rw [hnu, hnv, huv] at hcs
  -- `p² ψ₁(x-1) = (g⁻¹ + c_m) - ρ_m`
  have hpm : αcoef a m * ((gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1))
      = αcoef a m * ((trigamma a)⁻¹ + ccoef a m) - αcoef a m * rho a m := by
    unfold rho; ring
  have hαpos : 0 < αcoef a m := αcoef_pos ha m
  rw [βcoef_eq_gram ha hm]
  linarith [hcs, hpm, mul_pos hαpos hρ]

/-- `N_m ≻ 0` for `m ≥ 2` and any `a > 0`. -/
theorem Nmat_pd_two (ha : 0 < a) {m : ℕ} (hm : 2 ≤ m) : SymMat.PD (Nmat a m) := by
  refine ⟨αcoef_pos ha m, ?_⟩
  simp only [Nmat_a11, Nmat_a12, Nmat_a22]
  exact Nmat_det_pos ha (by omega) (rho_pos_of_two ha hm)

/-- `N_1 ≻ 0` for `a ≥ 1/2`. -/
theorem Nmat_pd_one (ha : 1 / 2 ≤ a) : SymMat.PD (Nmat a 1) := by
  have ha0 : 0 < a := by linarith
  refine ⟨αcoef_pos ha0 1, ?_⟩
  simp only [Nmat_a11, Nmat_a12, Nmat_a22]
  exact Nmat_det_pos ha0 le_rfl (rho_pos_one ha)

end TuranBessel
