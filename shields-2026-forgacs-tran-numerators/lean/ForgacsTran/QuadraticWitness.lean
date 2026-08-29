/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.MainClauses
import ForgacsTran.QuadraticCase

/-!
# A witness for the branch data

`MainClauses.main_of_ftBranch` is conditional on `FTBranchData`, and a conditional theorem
whose hypothesis nothing satisfies proves nothing while looking finished.  The Favard case
`(deg Q, r) = (2,1)` of `rem:quadratic-case` satisfies it exactly, and does so with the degree
growing and the returned count growing with it — the half that `Bridge.ftInputsWitness`, which
exhibits `P_m = 1` with every `natDegree` zero, does not have.

Everything is explicit there.  The pencil is quadratic in `t`, so the principal pair exhausts
the denominator and `eq:principal-decomposition` has **no** remainder at all; the amplitude is
`i/(2s sin θ)` with `s = √(q₀q₂)`, so its argument is the constant `π/2` and the phase
derivative bound of `eq:phase-derivative-bound` holds at `κ = 0`.

Nothing here has a counterpart in the manuscript: `rem:quadratic-case` records the Favard
branch but poses no witness, and a non-vacuity certificate is an **addition** to the paper
rather than a different route through one of its proofs.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Eventual degree» (`sec:reduction`,
`rem:quadratic-case`) in the service of `thm:main`.

## Tags

witness, branch data, quadratic pencil
-/

namespace ForgacsTran

open Polynomial Set

/-- `s = √(q₀q₂)`, the half-width of the Favard interval. -/
noncomputable def quadHalf (q0 q2 : ℝ) : ℝ := Real.sqrt (q0 * q2)

/-- `τ = √(q₀/q₂)`, the *constant* modulus of the principal pair in the Favard case. -/
noncomputable def quadMod (q0 q2 : ℝ) : ℝ := Real.sqrt (q0 / q2)

/-- `z(θ) = -q₁ - 2s cos θ`, the reparametrization of `rem:quadratic-case`. -/
noncomputable def quadZ (q0 q1 q2 : ℝ) (θ : ℝ) : ℝ :=
  -q1 - 2 * quadHalf q0 q2 * Real.cos θ

theorem quadHalf_pos {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) : 0 < quadHalf q0 q2 :=
  Real.sqrt_pos.mpr (by positivity)

theorem quadMod_pos {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) : 0 < quadMod q0 q2 :=
  Real.sqrt_pos.mpr (by positivity)

/-- `q₂τ = s`: the two square roots are related by the leading coefficient. -/
theorem quadMod_mul {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) :
    q2 * quadMod q0 q2 = quadHalf q0 q2 := by
  have hdiv : (0 : ℝ) ≤ q0 / q2 := by positivity
  have h1 : (0 : ℝ) ≤ q2 * Real.sqrt (q0 / q2) := by positivity
  have h2 : (q2 * Real.sqrt (q0 / q2)) ^ 2 = q0 * q2 := by
    rw [mul_pow, Real.sq_sqrt hdiv]; field_simp
  rw [quadMod, quadHalf, ← h2, Real.sqrt_sq h1]

/-- `τ s = q₀`, which is what makes the Chebyshev normalization collapse. -/
theorem quadMod_mul_half {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) :
    quadMod q0 q2 * quadHalf q0 q2 = q0 := by
  rw [quadMod, quadHalf, ← Real.sqrt_mul (by positivity)]
  rw [show q0 / q2 * (q0 * q2) = q0 ^ 2 by field_simp]
  exact Real.sqrt_sq hq0.le

/-- **The amplitude in the Favard case.**  `𝒲 = -B/∂_t D` at `t_+ = τe^{iθ}` with `B = 1`
comes out purely imaginary: `∂_t D = 2s i sin θ`, so `𝒲 = i/(2s sin θ)`. -/
theorem quad_ftAmp {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) {θ : ℝ}
    (hsin : Real.sin θ ≠ 0) :
    ftAmp (quadPoly q0 q1 q2) 1 1 (((quadZ q0 q1 q2 θ : ℝ) : ℂ))
        (ftPrincipal (fun _ => quadMod q0 q2) θ)
      = Complex.I / ((2 * quadHalf q0 q2 * Real.sin θ : ℝ) : ℂ) := by
  have hroot := quadDen_eval_principal hq0 hq2 (q1 := q1) θ
  have hz : ((quadZ q0 q1 q2 θ : ℝ) : ℂ)
      = (((-q1 - 2 * Real.sqrt (q0 * q2) * Real.cos θ : ℝ)) : ℂ) := by
    rw [quadZ, quadHalf]
  have hpr : ftPrincipal (fun _ => quadMod q0 q2) θ
      = ((Real.sqrt (q0 / q2) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ftPrincipal, quadMod]
  rw [hz, hpr]
  rw [ftAmp_eq_neg_div_derivative (by rw [← hz, ← hpr] at hroot ⊢; exact hroot)]
  -- `∂_t D = q₁ + 2q₂ t + z`
  have hder : (derivative (ftDen (quadPoly q0 q1 q2) 1
      (((-q1 - 2 * Real.sqrt (q0 * q2) * Real.cos θ : ℝ)) : ℂ))).eval
      (((Real.sqrt (q0 / q2) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = ((2 * quadHalf q0 q2 : ℝ) : ℂ) * Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
    rw [ftDen, quadPoly]
    simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow, zero_mul, zero_add, mul_one, pow_one, Nat.cast_ofNat]
    have hq2τ : ((q2 : ℝ) : ℂ) * ((Real.sqrt (q0 / q2) : ℝ) : ℂ)
        = ((quadHalf q0 q2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      exact_mod_cast congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) (quadMod_mul hq0 hq2)
    rw [Complex.exp_mul_I]
    push_cast
    have hq2τ' : (q2 : ℂ) * ((Real.sqrt (q0 / q2) : ℝ) : ℂ) = ((quadHalf q0 q2 : ℝ) : ℂ) := by
      exact_mod_cast hq2τ
    have hhalf : ((Real.sqrt (q0 * q2) : ℝ) : ℂ) = ((quadHalf q0 q2 : ℝ) : ℂ) := by
      rw [quadHalf]
    rw [hhalf]
    linear_combination (2 * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)) * hq2τ'
  rw [hder]
  have hne : ((2 * quadHalf q0 q2 * Real.sin θ : ℝ) : ℂ) ≠ 0 := by
    have : (2 * quadHalf q0 q2 * Real.sin θ) ≠ 0 := by
      have := quadHalf_pos hq0 hq2
      intro h
      rcases mul_eq_zero.1 h with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h'' <;> [norm_num at h''; linarith]
      · exact hsin h'
    exact_mod_cast this
  rw [Polynomial.eval_one]
  rw [show ((2 * quadHalf q0 q2 : ℝ) : ℂ) * Complex.I * ((Real.sin θ : ℝ) : ℂ)
      = ((2 * quadHalf q0 q2 * Real.sin θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [div_eq_div_iff (mul_ne_zero hne Complex.I_ne_zero) hne]
  linear_combination (-(((2 * quadHalf q0 q2 * Real.sin θ : ℝ) : ℂ))) * Complex.I_sq

/-- **The amplitude modulus in the Favard case.**  `|W(θ)| = 1/(2s sin θ)`. -/
theorem quad_ftPrincipalAmp {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) {θ : ℝ}
    (hsin : 0 < Real.sin θ) :
    ftPrincipalAmp (quadPoly q0 q1 q2) 1 1 (quadZ q0 q1 q2) (fun _ => quadMod q0 q2) θ
      = 1 / (2 * quadHalf q0 q2 * Real.sin θ) := by
  have hc : 0 < 2 * quadHalf q0 q2 * Real.sin θ := by
    have := quadHalf_pos hq0 hq2; positivity
  rw [ftPrincipalAmp, quad_ftAmp hq0 hq2 q1 hsin.ne', norm_div, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

/-- **The amplitude is purely imaginary, so its argument is the constant `π/2`.**  This is
what makes `eq:phase-derivative-bound` hold at `κ = 0` here. -/
theorem quad_polar {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) {θ : ℝ}
    (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) 1 1 (((quadZ q0 q1 q2 θ : ℝ) : ℂ))
        (ftPrincipal (fun _ => quadMod q0 q2) θ)
      = ((ftPrincipalAmp (quadPoly q0 q1 q2) 1 1 (quadZ q0 q1 q2)
            (fun _ => quadMod q0 q2) θ : ℝ) : ℂ)
        * Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  have hc : 0 < 2 * quadHalf q0 q2 * Real.sin θ := by
    have := quadHalf_pos hq0 hq2; positivity
  have hexp : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  rw [quad_ftAmp hq0 hq2 q1 hsin.ne', quad_ftPrincipalAmp hq0 hq2 q1 hsin, hexp,
    one_div, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

/-! ### No remainder: the principal pair exhausts a quadratic denominator -/

/-- The Chebyshev closed form on the arc: `p_M(z(θ)) sin θ = (-s)^M sin((M+1)θ)`. -/
theorem quad_favard_on_arc {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) (M : ℕ) (θ : ℝ) :
    (quadFavard q0 q1 q2 M).eval (quadZ q0 q1 q2 θ) * Real.sin θ
      = (-quadHalf q0 q2) ^ M * Real.sin (((M : ℝ) + 1) * θ) := by
  have hs0 : 0 < quadHalf q0 q2 := quadHalf_pos hq0 hq2
  have hsq : Real.sqrt (q0 * q2) ≠ 0 := by simpa [quadHalf] using hs0.ne'
  have harg : (quadZ q0 q1 q2 θ + q1) / (2 * Real.sqrt (q0 * q2)) = Real.cos (Real.pi - θ) := by
    rw [quadZ, Real.cos_pi_sub]
    simp only [quadHalf]
    field
  have hU := Polynomial.Chebyshev.U_real_cos (Real.pi - θ) (M : ℤ)
  rw [Real.sin_pi_sub] at hU
  have hsplit : (((M : ℤ) : ℝ) + 1) * (Real.pi - θ)
      = ((M + 1 : ℕ) : ℝ) * Real.pi - (((M : ℝ) + 1) * θ) := by push_cast; ring
  rw [hsplit, Real.sin_nat_mul_pi_sub] at hU
  rw [quadFavard_eval_eq_chebyshev hq0 hq2 q1 M (quadZ q0 q1 q2 θ), harg,
    show Real.sqrt (q0 * q2) = quadHalf q0 q2 from rfl]
  calc quadHalf q0 q2 ^ M * (Polynomial.Chebyshev.U ℝ (M : ℤ)).eval (Real.cos (Real.pi - θ))
        * Real.sin θ
      = quadHalf q0 q2 ^ M
        * ((Polynomial.Chebyshev.U ℝ (M : ℤ)).eval (Real.cos (Real.pi - θ)) * Real.sin θ) := by
        ring
    _ = quadHalf q0 q2 ^ M * -((-1 : ℝ) ^ (M + 1) * Real.sin (((M : ℝ) + 1) * θ)) := by rw [hU]
    _ = (-quadHalf q0 q2) ^ M * Real.sin (((M : ℝ) + 1) * θ) := by
        rw [neg_pow, pow_succ]
        ring

/-- The normalization collapses: `τ^{M+1} p_M(z(θ)) / (q₀(-q₀)^M) = sin((M+1)θ)/(s sin θ)`. -/
theorem quad_norm_collapse {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (M : ℕ) {θ : ℝ}
    (hsin : Real.sin θ ≠ 0) (S : ℝ) :
    quadMod q0 q2 ^ (M + 1) * ((-quadHalf q0 q2) ^ M * S / Real.sin θ) / (q0 * (-q0) ^ M)
      = S / (quadHalf q0 q2 * Real.sin θ) := by
  obtain ⟨τv, Hv, hτv, hHv, hprod⟩ :
      ∃ τv Hv : ℝ, quadMod q0 q2 = τv ∧ quadHalf q0 q2 = Hv ∧ τv * Hv = q0 :=
    ⟨_, _, rfl, rfl, quadMod_mul_half hq0 hq2⟩
  have hτne : τv ≠ 0 := by rw [← hτv]; exact (quadMod_pos hq0 hq2).ne'
  have hHne : Hv ≠ 0 := by rw [← hHv]; exact (quadHalf_pos hq0 hq2).ne'
  have hεne : ((-1 : ℝ)) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hτv, hHv, ← hprod,
    show (-Hv) ^ M = (-1 : ℝ) ^ M * Hv ^ M from neg_pow Hv M,
    show (-(τv * Hv)) ^ M = (-1 : ℝ) ^ M * (τv * Hv) ^ M from neg_pow (τv * Hv) M, mul_pow]
  field

/-- The real part of `i/c · e^{iy}` is `-sin y / c`. -/
private theorem I_div_mul_exp_re {c y : ℝ} (hc : c ≠ 0) :
    (Complex.I / ((c : ℝ) : ℂ) * Complex.exp (((y : ℝ) : ℂ) * Complex.I)).re
      = -Real.sin y / c := by
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hval : Complex.I / ((c : ℝ) : ℂ) * Complex.exp (((y : ℝ) : ℂ) * Complex.I)
      = (((-Real.sin y / c : ℝ)) : ℂ) + (((Real.cos y / c : ℝ)) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    field_simp
    linear_combination (((Real.sin y : ℝ) : ℂ)) * Complex.I_sq
  rw [hval]
  simp [Complex.sin_ofReal_re]

/-- **No remainder.**  The pencil is quadratic in `t`, so the principal pair exhausts the
denominator: `eq:principal-decomposition` is exact and `R_M ≡ 0`.  That is what makes
`eq:dominance-bound` hold on the whole arc rather than only off the endpoint windows. -/
theorem quad_ftRemainder_eq_zero {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    (M : ℕ) {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftRemainder (quadPoly q0 q1 q2) 1 1 (quadZ q0 q1 q2) (fun _ => quadMod q0 q2) M θ = 0 := by
  have hs0 : 0 < quadHalf q0 q2 := quadHalf_pos hq0 hq2
  have hτ0 : 0 < quadMod q0 q2 := quadMod_pos hq0 hq2
  set c : ℝ := 2 * quadHalf q0 q2 * Real.sin θ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  -- the principal pair's contribution
  have hterm2 : (((quadMod q0 q2 : ℝ) : ℂ) ^ (M + 1)
      * (ftAmp (quadPoly q0 q1 q2) 1 1 (((quadZ q0 q1 q2 θ : ℝ) : ℂ))
          (ftPrincipal (fun _ => quadMod q0 q2) θ)
        / (ftPrincipal (fun _ => quadMod q0 q2) θ) ^ (M + 1))).re
      = Real.sin (((M : ℝ) + 1) * θ) / c := by
    rw [show (((quadMod q0 q2 : ℝ) : ℂ) ^ (M + 1)
        * (ftAmp (quadPoly q0 q1 q2) 1 1 (((quadZ q0 q1 q2 θ : ℝ) : ℂ))
            (ftPrincipal (fun _ => quadMod q0 q2) θ)
          / (ftPrincipal (fun _ => quadMod q0 q2) θ) ^ (M + 1)))
        = ftAmp (quadPoly q0 q1 q2) 1 1 (((quadZ q0 q1 q2 θ : ℝ) : ℂ))
            (ftPrincipal (fun _ => quadMod q0 q2) θ)
          * ((((quadMod q0 q2 : ℝ) : ℂ) ^ (M + 1))
            / (ftPrincipal (fun _ => quadMod q0 q2) θ) ^ (M + 1)) by ring]
    rw [quad_ftAmp hq0 hq2 q1 hsin.ne', ftPrincipal, ofReal_pow_div_principal_pow hτ0, ← hc,
      I_div_mul_exp_re hcpos.ne', Real.sin_neg]
    ring
  -- the coefficient itself
  have hterm1 : ((quadMod q0 q2 : ℝ) : ℂ) ^ (M + 1)
      * (ftCoeffPoly (quadPoly q0 q1 q2) 1 1 M).eval (((quadZ q0 q1 q2 θ : ℝ) : ℂ))
      = (((2 * (Real.sin (((M : ℝ) + 1) * θ) / c) : ℝ)) : ℂ) := by
    have hfav := quadFavard_eval_eq_coeffPoly (q1 := q1) (q2 := q2) hq0 M (quadZ q0 q1 q2 θ)
    have harc := quad_favard_on_arc hq0 hq2 q1 M θ
    have hq0c : ((q0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hcoeff : (ftCoeffPoly (quadPoly q0 q1 q2) 1 1 M).eval (((quadZ q0 q1 q2 θ : ℝ) : ℂ))
        = (((quadFavard q0 q1 q2 M).eval (quadZ q0 q1 q2 θ) : ℝ) : ℂ)
          / (((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ M) := by
      have hden : ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ M ≠ 0 :=
        mul_ne_zero hq0c (pow_ne_zero _ (neg_ne_zero.2 hq0c))
      rw [eq_div_iff hden, hfav]
      ring
    have hpM : (quadFavard q0 q1 q2 M).eval (quadZ q0 q1 q2 θ)
        = (-quadHalf q0 q2) ^ M * Real.sin (((M : ℝ) + 1) * θ) / Real.sin θ := by
      rw [eq_div_iff hsin.ne']; exact harc
    have hreal : quadMod q0 q2 ^ (M + 1)
        * ((-quadHalf q0 q2) ^ M * Real.sin (((M : ℝ) + 1) * θ) / Real.sin θ)
        / (q0 * (-q0) ^ M)
        = 2 * (Real.sin (((M : ℝ) + 1) * θ) / c) := by
      rw [quad_norm_collapse hq0 hq2 M hsin.ne', hc]
      field_simp
    rw [hcoeff, hpM, ← hreal]
    push_cast
    field_simp
  rw [ftRemainder, hterm1, hterm2]
  simp

/-! ### The coefficient sequence as a real polynomial -/

/-- `F_M = p_M/(q₀(-q₀)^M)`, the real form of `ftCoeffPoly` in the Favard case. -/
noncomputable def quadCoeff (q0 q1 q2 : ℝ) (M : ℕ) : Polynomial ℝ :=
  Polynomial.C ((q0 * (-q0) ^ M)⁻¹) * quadFavard q0 q1 q2 M

theorem quadCoeff_map {q0 : ℝ} (hq0 : 0 < q0) (q1 q2 : ℝ) (M : ℕ) :
    (quadCoeff q0 q1 q2 M).map (algebraMap ℝ ℂ)
      = ftCoeffPoly (quadPoly q0 q1 q2) 1 1 M := by
  have hq0c : ((q0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hden : ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ M ≠ 0 :=
    mul_ne_zero hq0c (pow_ne_zero _ (neg_ne_zero.2 hq0c))
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
  rintro w ⟨z, rfl⟩
  have hleft : ((quadCoeff q0 q1 q2 M).map (algebraMap ℝ ℂ)).eval ((z : ℝ) : ℂ)
      = (((quadCoeff q0 q1 q2 M).eval z : ℝ) : ℂ) := by
    rw [Polynomial.eval_map, show (((z : ℝ) : ℂ)) = (algebraMap ℝ ℂ) z from rfl,
      Polynomial.eval₂_at_apply]
    rfl
  have hfav := quadFavard_eval_eq_coeffPoly (q1 := q1) (q2 := q2) hq0 M z
  have hF : (ftCoeffPoly (quadPoly q0 q1 q2) 1 1 M).eval ((z : ℝ) : ℂ)
      = (((quadFavard q0 q1 q2 M).eval z : ℝ) : ℂ)
        / (((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ M) := by
    rw [eq_div_iff hden, hfav]; ring
  simp only [Set.mem_ofPred_eq]
  rw [hleft, hF]
  simp only [quadCoeff, Polynomial.eval_mul, Polynomial.eval_C]
  push_cast
  field_simp

theorem quadCoeff_natDegree {q0 : ℝ} (hq0 : 0 < q0) (q1 q2 : ℝ) (M : ℕ) :
    (quadCoeff q0 q1 q2 M).natDegree = M := by
  have hc : ((q0 * (-q0) ^ M)⁻¹ : ℝ) ≠ 0 := by
    refine inv_ne_zero (mul_ne_zero hq0.ne' (pow_ne_zero _ ?_))
    exact neg_ne_zero.2 hq0.ne'
  rw [quadCoeff, Polynomial.natDegree_C_mul hc, (quadFavard_monic_natDegree q0 q1 q2 M).2]

/-! ### The witness -/

theorem quadHalf_one : quadHalf 1 1 = 1 := by rw [quadHalf]; norm_num

theorem quadMod_one : quadMod 1 1 = 1 := by rw [quadMod]; norm_num

/-- The witness denominator `Q(t) = 1 - 4t + t²`.  Its zeros `2 ± √3` are positive, so it
satisfies `eq:Q-hypotheses`, and the pencil `Q(t) + zt` is the Favard case
`(deg Q, r) = (2, 1)` of `rem:quadratic-case`. -/
noncomputable def witQ : Polynomial ℂ := quadPoly 1 (-4) 1

/-- The witness reparametrization `z(θ) = 4 - 2 cos θ`, strictly increasing on `[0, π]` with
image `[2, 6]`. -/
noncomputable def witZ : ℝ → ℝ := quadZ 1 (-4) 1

/-- The witness modulus, the constant `τ = 1`. -/
noncomputable def witTau : ℝ → ℝ := fun _ => quadMod 1 1

/-- The witness coefficient sequence, of degree exactly `M`. -/
noncomputable def witP (M : ℕ) : Polynomial ℝ := quadCoeff 1 (-4) 1 M

/-! Three definitional unfoldings.  Each is `rfl`, and they exist so a consumer can
rewrite the witness back to its parametric form without unfolding a `def` in tactic
position.  `witness_ftBranchData` below uses all three, and `ClauseThreeWitness` uses
them at five further sites. -/

theorem witQ_eq : witQ = quadPoly 1 (-4) 1 := rfl

theorem witZfun_eq : witZ = quadZ 1 (-4) 1 := rfl

theorem witTau_eq : witTau = fun _ : ℝ => quadMod 1 1 := rfl

theorem witZ_eq (θ : ℝ) : witZ θ = 4 - 2 * Real.cos θ := by
  rw [witZ, quadZ, quadHalf_one]; ring

theorem witP_map (M : ℕ) : (witP M).map (algebraMap ℝ ℂ) = ftCoeffPoly witQ 1 1 M :=
  quadCoeff_map (by norm_num) _ _ M

theorem witP_natDegree (M : ℕ) : ((witP M).map (algebraMap ℝ ℂ)).natDegree = M := by
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, witP,
    quadCoeff_natDegree (by norm_num)]

/-- **The witness.**  `FTBranchData` holds for the Favard pencil `Q = 1 - 4t + t²`, `r = 1`,
`B = 1` at every index `M ≥ 1`, on the retained arc `[1/(M+1), π - 1/(M+1)]` of
`eq:retained-range`, with the single constant `C = 2`. -/
theorem witness_ftBranchData {M : ℕ} (hM : 1 ≤ M) :
    FTBranchData witQ 1 1 witZ witTau (witP M) M 1 7 2 := by
  have hπ : (3 : ℝ) < Real.pi := by
    have := Real.pi_gt_three; linarith
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  set a : ℝ := 1 / ((M : ℝ) + 1) with ha
  set b : ℝ := Real.pi - 1 / ((M : ℝ) + 1) with hb
  have hapos : 0 < a := by rw [ha]; positivity
  have hale : a ≤ 1 := by
    rw [ha, div_le_one hM1]; linarith
  have hab : a ≤ b := by rw [hb]; linarith
  have hbπ : b < Real.pi := by rw [hb]; linarith
  have hsub : Icc a b ⊆ Icc 0 Real.pi := Icc_subset_Icc hapos.le hbπ.le
  have hsin : ∀ θ ∈ Icc a b, 0 < Real.sin θ := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hapos hθ.1)
      (lt_of_le_of_lt hθ.2 hbπ)
  refine ⟨a, b, ((M : ℝ) + 1) * Real.pi - 2, fun _ => Real.pi / 2,
    fun θ => ((M : ℝ) + 1) * θ - Real.pi / 2, hab, ?_, ?_, ?_, ?_, ?_, fun θ _ => rfl,
    ⟨fun _ => 0, 0, fun θ _ => hasDerivAt_const θ (Real.pi / 2), fun θ _ => by simp, hM1⟩,
    ?_, ?_, ?_, ?_⟩
  · exact fun θ _ => by rw [witTau_eq]; simp only [quadMod_one]; norm_num
  · exact (quadratic_z_strictMonoOn (by norm_num) (by norm_num) (-4)).mono hsub
  · intro θ _
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    rw [witZ_eq]
    exact ⟨by linarith, by linarith⟩
  · intro θ hθ
    rw [witQ_eq, witZfun_eq, witTau_eq,
      quad_ftAmp (by norm_num) (by norm_num) (-4) (hsin θ hθ).ne']
    refine div_ne_zero Complex.I_ne_zero ?_
    have : (0 : ℝ) < 2 * quadHalf 1 1 * Real.sin θ := by
      rw [quadHalf_one]; have := hsin θ hθ; positivity
    exact_mod_cast this.ne'
  · intro θ hθ
    rw [witQ_eq, witZfun_eq, witTau_eq]
    exact quad_polar (by norm_num) (by norm_num) (-4) (hsin θ hθ)
  · -- `π ≤ L`
    nlinarith [hπ, hMR]
  · -- `L ≤ Φ b - Φ a`
    simp only
    rw [ha, hb]
    field_simp
    linarith
  · -- `eq:dominance-bound`: the remainder vanishes
    intro θ hθ
    rw [witQ_eq, witZfun_eq, witTau_eq,
      quad_ftRemainder_eq_zero (by norm_num) (by norm_num) (-4) M (hsin θ hθ)]
    have : (0 : ℝ) ≤ ftPrincipalAmp (quadPoly 1 (-4) 1) 1 1 (quadZ 1 (-4) 1)
        (fun _ => quadMod 1 1) θ := norm_nonneg _
    linarith
  · -- the degree--count comparison, uniformly in `M`
    rw [witP_natDegree]
    have hd : (((M : ℝ) + 1) * Real.pi - 2) / Real.pi = ((M : ℝ) + 1) - 2 / Real.pi := by
      field_simp
    rw [hd]
    have h2π : (2 : ℝ) / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; linarith
    push_cast
    linarith

/-- **The witness in action.**  All three clauses of `thm:main` hold for the Favard pencil at
every index `M ≥ 1` with the single constant `C = 2`, and the interior count `M - 2` grows
with the degree `M`.  So `FTBranchData` is inhabited **and** its conclusion is non-trivial —
the half that `Bridge.ftInputsWitness`, which exhibits `P_m = 1` with every `natDegree` zero,
does not have. -/
theorem witness_main_clauses (M : ℕ) (hM : 1 ≤ M) :
    (∃ Z : Finset ℂ, M - 2 ≤ Z.card ∧
        (∀ w ∈ Z, ((witP M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftInterval 1 7))
      ∧ (exceptionalRoots ((witP M).map (algebraMap ℝ ℂ)) (ftInterval 1 7)).card ≤ 2
      ∧ (exceptionalRoots ((witP M).map (algebraMap ℝ ℂ)) posRay).card ≤ 2 := by
  have hne : ∀ m : ℕ, 1 ≤ m → (witP m).map (algebraMap ℝ ℂ) ≠ 0 := by
    intro m hm h
    have := witP_natDegree m
    rw [h, Polynomial.natDegree_zero] at this
    omega
  have h := main_of_ftBranch (Q := witQ) (B := 1) (r := 1) (z := witZ) (τ := witTau)
    (P := witP) (aI := 1) (bI := 7) (C := 2) (m0 := 1)
    (fun m => witP_map m) hne (by norm_num)
    (fun m hm => witness_ftBranchData hm) M hM
  rwa [witP_natDegree] at h

end ForgacsTran
