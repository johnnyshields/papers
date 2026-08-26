/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.QuadraticCase
import ForgacsTran.ClauseThreeMonomial

/-!
# The `r > 1` branch: a pencil whose principal modulus is not constant

Every non-vacuity witness this development carries for the clause-3 chain runs on
`rem:quadratic-case`'s Favard pencil, which has `(deg Q, r) = (2, 1)` and a **constant**
principal modulus `τ = √{q_0/q_2}`.  That is a real limitation rather than a cosmetic
one: `eq:ab-def` puts `b = +∞` precisely when `r > 1`, and along the arc the modulus then
runs to `0` at the upper endpoint — the behaviour the upper-endpoint analysis of
`thm:weighted-dominance` exists to handle, and which no constant-modulus pencil exhibits at
all.

The smallest pencil that is still quadratic in `t` and has `r > 1` is
`D(t,z) = q_0 + q_1t + (q_2+z)t^2` at `r = 2`.  The principal pair is `τ e^{± iθ}`
on `θ ∈ (0, π/2) = (0, π/r)`, with

  `τ(θ) = -2q_0cosθ/q_1`,   `z(θ) = q_0/τ(θ)^2 - q_2`,

so `τ` is **not constant** and vanishes as `θ ↑ π/2`, while `z` increases to
`+∞` — the interval really is a ray.  The amplitude nonetheless comes out purely
imaginary, `𝒲 = iτ/(2q_0sinθ)`, so `arg𝒲 = π/2` is constant and
`eq:phase-derivative-bound` still holds at `κ = 0`.

`scripts/check_r2_quadratic_branch.py` checks all of this numerically at 50 digits, including
the two facts this file does not yet prove: that `eq:principal-decomposition` is exact here
(the pair exhausts a quadratic denominator whatever the modulus does), and the monomial shift
`R_M^{(t^k)} = τ^kR_{M-k}^{(1)}` at `τ ≠ 1`, which is
`ClauseThreeWitness.ftRemainder_X_pow_of_pos`.

The principal branch is written out as `τ e^{iθ}` rather than as `ftPrincipal`, which
is what `QuadraticCase` does and for the same reason: `ftPrincipal` lives in `DominanceFT`,
and this module has no other business there.  A one-line bridge belongs wherever the geometry
is assembled.

**A coercion trap in the arc identity.**  `push_cast` rewrites `↑(Real.sin x)` to
`Complex.sin ↑x` (`Complex.ofReal_sin` is a `norm_cast` lemma), after which every rewrite by a
real sine identity silently stops matching.  `ray_coeffPoly_on_arc` therefore keeps its indices
as `ℕ` casts and moves between `ℝ` and `ℂ` with the named `Complex.ofReal_*` lemmas rather than
`push_cast`.  The failure reads as a broken proof and is a normal-form problem.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry` and
`sec:dominance` for a case with `r > 1`.

## Tags

principal modulus, denominator pencil, defect, quadratic pencil
-/

namespace ForgacsTran

open Polynomial

/-- The principal modulus of the `r = 2` pencil, `τ(θ) = -2q_0cosθ/q_1`.
Unlike `quadMod` it depends on `θ`, and it vanishes at `θ = π/2`. -/
noncomputable def rayTau (q0 q1 : ℝ) (θ : ℝ) : ℝ := -2 * q0 * Real.cos θ / q1

/-- The reparametrization of the `r = 2` pencil, `z(θ) = q_0/τ(θ)^2 - q_2`.  It
increases to `+∞` as `θ ↑ π/2`, so `I_{Q,r}` is a ray. -/
noncomputable def rayZ (q0 q1 q2 : ℝ) (θ : ℝ) : ℝ := q0 / (rayTau q0 q1 θ) ^ 2 - q2

theorem rayTau_pos {q0 q1 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) : 0 < rayTau q0 q1 θ := by
  rw [rayTau, div_pos_iff]
  right
  exact ⟨by nlinarith, hq1⟩

/-- Vieta, first relation: the product of the principal pair is `τ^2 = q_0/(q_2+z)`. -/
theorem rayZ_mul_sq {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) :
    (q2 + rayZ q0 q1 q2 θ) * (rayTau q0 q1 θ) ^ 2 = q0 := by
  have hτ : 0 < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  rw [rayZ]
  field

/-- Vieta, second relation: the sum of the principal pair is `2τcosθ = -q_1/(q_2+z)`,
which after clearing is `q_1τ = -2q_0cosθ`. -/
theorem rayTau_mul {q0 q1 : ℝ} (hq1 : q1 < 0) (q2 : ℝ) (θ : ℝ) :
    q1 * rayTau q0 q1 θ = -2 * q0 * Real.cos θ := by
  have h : q1 ≠ 0 := hq1.ne
  rw [rayTau]
  field_simp

/-- **The principal pair is the root pair.**  `t_+ = τ e^{iθ}` is a zero of
`D(·, z(θ))`. -/
theorem rayDen_eval_principal {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) :
    (ftDen (quadPoly q0 q1 q2) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)).eval
      (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  set τ : ℝ := rayTau q0 q1 θ with hτdef
  set E : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hE
  set F : ℂ := Complex.exp (-(θ : ℂ) * Complex.I) with hF
  have hEF : E * F = 1 := by rw [hE, hF, ← Complex.exp_add]; simp
  have hsum : E + F = 2 * ((Real.cos θ : ℝ) : ℂ) := by
    rw [hE, hF, Complex.exp_mul_I,
      show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hprod : ((q2 + rayZ q0 q1 q2 θ : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ 2 = ((q0 : ℝ) : ℂ) := by
    exact_mod_cast rayZ_mul_sq hq0 hq1 hcos
  have hlin : ((q1 : ℝ) : ℂ) * ((τ : ℝ) : ℂ) = -2 * ((q0 : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) := by
    exact_mod_cast rayTau_mul hq1 q2 θ
  rw [ftDen_eval, quadPoly_eval]
  -- `q0 + q1 τE + (q2+z) τ²E² = E * (q0(E+F) + q1τ)`, and the bracket vanishes
  have hexp : ((q0 : ℝ) : ℂ) + ((q1 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E)
      + ((q2 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
      + ((rayZ q0 q1 q2 θ : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
      = E * (((q0 : ℝ) : ℂ) * (E + F) + ((q1 : ℝ) : ℂ) * ((τ : ℝ) : ℂ)) := by
    have hq : ((q2 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
        + ((rayZ q0 q1 q2 θ : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
        = ((q0 : ℝ) : ℂ) * E ^ 2 := by
      have : ((q2 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
          + ((rayZ q0 q1 q2 θ : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
          = (((q2 : ℝ) : ℂ) + ((rayZ q0 q1 q2 θ : ℝ) : ℂ)) * ((τ : ℝ) : ℂ) ^ 2 * E ^ 2 := by
        ring
      rw [this, show (((q2 : ℝ) : ℂ) + ((rayZ q0 q1 q2 θ : ℝ) : ℂ))
          = ((q2 + rayZ q0 q1 q2 θ : ℝ) : ℂ) by push_cast; ring, hprod]
    rw [show ((q0 : ℝ) : ℂ) + ((q1 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E)
        + ((q2 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
        + ((rayZ q0 q1 q2 θ : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
        = (((q2 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
            + ((rayZ q0 q1 q2 θ : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2)
          + (((q0 : ℝ) : ℂ) + ((q1 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E)) by ring, hq]
    linear_combination (-((q0 : ℝ) : ℂ)) * hEF
  rw [hexp, hsum, hlin]
  ring


/-- `e^{iθ} - cosθ = isinθ`, the step that turns the derivative into a purely
imaginary quantity. -/
theorem ray_exp_sub_cos (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) - ((Real.cos θ : ℝ) : ℂ)
      = ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- **`∂_tD` along the branch, cleared of denominators.**  `τ∂_tD(t_+)` is
`2q_0isinθ` — purely imaginary, which is what makes `arg𝒲` constant.  Both
Vieta relations are consumed here and nothing else is. -/
theorem ray_derivative_eval {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) :
    ((rayTau q0 q1 θ : ℝ) : ℂ)
        * (derivative (ftDen (quadPoly q0 q1 q2) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ))).eval
          (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = 2 * ((q0 : ℝ) : ℂ) * Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  set τ : ℝ := rayTau q0 q1 θ with hτdef
  set E : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hE
  have hprod : ((q2 + rayZ q0 q1 q2 θ : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ 2 = ((q0 : ℝ) : ℂ) := by
    exact_mod_cast rayZ_mul_sq hq0 hq1 hcos
  have hlin : ((q1 : ℝ) : ℂ) * ((τ : ℝ) : ℂ)
      = -2 * ((q0 : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) := by
    exact_mod_cast rayTau_mul hq1 q2 θ
  have hEc : E - ((Real.cos θ : ℝ) : ℂ) = ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [hE]; exact ray_exp_sub_cos θ
  rw [ftDen, quadPoly]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, zero_mul, zero_add, mul_one, Nat.cast_ofNat]
  have hsplit : ((q2 : ℝ) : ℂ) + ((rayZ q0 q1 q2 θ : ℝ) : ℂ)
      = ((q2 + rayZ q0 q1 q2 θ : ℝ) : ℂ) := by push_cast; ring
  linear_combination hlin + (2 * E) * hprod
    + (2 * ((q0 : ℝ) : ℂ)) * hEc
    + (2 * ((τ : ℝ) : ℂ) ^ 2 * E) * hsplit



/-- **The principal amplitude on the `r = 2` branch.**  `𝒲 = -B(t_+)/∂_tD(t_+)`
at `B = 1` comes out `iτ/(2q_0sinθ)` — **purely imaginary**, exactly as on the Favard
pencil, so `arg𝒲 = π/2` is constant and `eq:phase-derivative-bound` holds at
`κ = 0` even though `τ` is not constant.

That is the point of the pencil: the modulus varies and vanishes at the upper endpoint, while
the phase does not move at all. -/
theorem ray_ftAmp {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) 1 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.I * ((rayTau q0 q1 θ : ℝ) : ℂ)
        / (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) := by
  have hroot := rayDen_eval_principal (q2 := q2) hq0 hq1 hcos
  have hderiv := ray_derivative_eval (q2 := q2) hq0 hq1 hcos
  have hτ : (0 : ℝ) < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  have hτc : ((rayTau q0 q1 θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hs : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsin.ne'
  have hq : ((q0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  set D : ℂ := (derivative (ftDen (quadPoly q0 q1 q2) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ))).eval
      (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hDdef
  have hDne : D ≠ 0 := by
    intro h
    rw [h, mul_zero] at hderiv
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hq) Complex.I_ne_zero) hs)
      hderiv.symm
  have key : -(2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
      = Complex.I * ((rayTau q0 q1 θ : ℝ) : ℂ) * D := by
    linear_combination (-Complex.I) * hderiv
      - (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * Complex.I_sq
  rw [ftAmp_eq_neg_div_derivative hroot, Polynomial.eval_one, ← hDdef]
  field_simp
  linear_combination key



/-- The modulus `|𝒲| = τ/(2q_0sinθ)`.  Unlike the Favard pencil's
`1/(2ssinθ)` this carries the varying `τ`, and it vanishes with it at the upper
endpoint. -/
theorem ray_norm_ftAmp {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ‖ftAmp (quadPoly q0 q1 q2) 1 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
      = rayTau q0 q1 θ / (2 * q0 * Real.sin θ) := by
  have hτ : (0 : ℝ) < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  have hden : (0 : ℝ) < 2 * q0 * Real.sin θ := by positivity
  rw [ray_ftAmp hq0 hq1 hcos hsin, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ,
    show (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
      = ((2 * q0 * Real.sin θ : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]

/-- **The polar form, with the constant branch `ψ ≡ π/2`.**  This is the field
`FTChainGeom` asks for, and the constant `ψ` is what makes `eq:phase-derivative-bound` hold
at `κ = 0` and `eq:linear-phase-variation` at `κ_0 = κ_1 = 0` on this pencil —
the same collapse the `r = 1` witness enjoys, now at `r > 1` and with a non-constant
modulus. -/
theorem ray_polar {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) 1 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = ((‖ftAmp (quadPoly q0 q1 q2) 1 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
            (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ : ℝ) : ℂ)
        * Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  have hden : (0 : ℝ) < 2 * q0 * Real.sin θ := by positivity
  have hI : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  rw [ray_norm_ftAmp hq0 hq1 hcos hsin, hI, ray_ftAmp hq0 hq1 hcos hsin,
    Complex.ofReal_div,
    show ((2 * q0 * Real.sin θ : ℝ) : ℂ)
      = 2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ) by push_cast; ring]
  ring



/-! ### The coefficient sequence along the `r = 2` branch -/

/-- **The three-term recurrence at `r = 2`.**  The denominator-only coefficients
`H_M = [t^M](Q + zt^2)^{-1}` satisfy `q_0H_M + q_1H_{M-1} + (q_2+z)H_{M-2} = 0`.  This is
`QuadraticCase.quad_denominator_recurrence` with the parameter moved from the `t` coefficient
to the `t^2` coefficient — the two `ftDenCoeff` cases swap, and nothing else changes. -/
theorem ray_denominator_recurrence {q0 q1 q2 : ℝ} (hq0 : 0 < q0) {M : ℕ} (hM : 2 ≤ M) :
    C ((q0 : ℝ) : ℂ) * ftCoeffPoly (quadPoly q0 q1 q2) 1 2 M
      + C ((q1 : ℝ) : ℂ) * ftCoeffPoly (quadPoly q0 q1 q2) 1 2 (M - 1)
      + (C ((q2 : ℝ) : ℂ) + X) * ftCoeffPoly (quadPoly q0 q1 q2) 1 2 (M - 2) = 0 := by
  classical
  have hc0 : (quadPoly q0 q1 q2).coeff 0 = ((q0 : ℝ) : ℂ) := by simp [quadPoly]
  have hc1 : (quadPoly q0 q1 q2).coeff 1 = ((q1 : ℝ) : ℂ) := by simp [quadPoly]
  have hc2 : (quadPoly q0 q1 q2).coeff 2 = ((q2 : ℝ) : ℂ) := by simp [quadPoly]
  have hcj : ∀ j, 3 ≤ j → (quadPoly q0 q1 q2).coeff j = 0 := by
    intro j hj
    have h1 : j ≠ 0 := by omega
    have h2 : j ≠ 1 := by omega
    have h3 : ¬ (j = 2) := by omega
    simp [quadPoly, coeff_C, coeff_X, coeff_X_pow, h1, h3]
    intro h
    exact absurd h (by omega : ¬ ((1 : ℕ) = j))
  set Q := quadPoly q0 q1 q2 with hQ
  set H : ℕ → Polynomial ℂ := ftCoeffPoly Q 1 2 with hH
  have hd1 : ftDenCoeff Q 2 1 = C ((q1 : ℝ) : ℂ) := by
    simp [ftDenCoeff, hc1, show ¬ (1 = 2) by omega]
  have hd2 : ftDenCoeff Q 2 2 = C ((q2 : ℝ) : ℂ) + X := by simp [ftDenCoeff, hc2]
  have hdj : ∀ j, 3 ≤ j → ftDenCoeff Q 2 j = 0 := by
    intro j hj
    simp [ftDenCoeff, hcj j hj, show ¬ (j = 2) by omega]
  have hpair : (M - 2) ≠ (M - 1) := by omega
  have hsub : ({M - 2, M - 1} : Finset ℕ) ⊆ Finset.range M := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact Finset.mem_range.2 (by omega)
  have hzero : ∀ i ∈ Finset.range M, i ∉ ({M - 2, M - 1} : Finset ℕ) →
      ftDenCoeff Q 2 (M - i) * H i = 0 := by
    intro i hi hni
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hni
    have hlt : i < M := Finset.mem_range.1 hi
    rw [hdj (M - i) (by omega), zero_mul]
  have hsum : ∑ i ∈ Finset.range M, ftDenCoeff Q 2 (M - i) * H i
      = ftDenCoeff Q 2 2 * H (M - 2) + ftDenCoeff Q 2 1 * H (M - 1) := by
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair hpair]
    congr 2 <;> [skip; skip] <;> congr 1 <;> omega
  have hMcoeff : ((1 : Polynomial ℂ).coeff M) = 0 := by
    rw [Polynomial.coeff_one, if_neg (by omega)]
  have hrec : H M = C ((quadPoly q0 q1 q2).coeff 0)⁻¹
      * (C ((1 : Polynomial ℂ).coeff M)
        - ∑ i ∈ Finset.range M, ftDenCoeff Q 2 (M - i) * H i) := ftCoeffPoly_eq Q 1 2 M
  have hq0c : ((q0 : ℝ) : ℂ) ≠ 0 := by simpa using hq0.ne'
  have hcc : C ((q0 : ℝ) : ℂ) * C (((q0 : ℝ) : ℂ))⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hq0c, C_1]
  rw [hrec, hMcoeff, hsum, hd1, hd2, hc0, C_0, zero_sub, ← mul_assoc, hcc, one_mul]
  ring



/-- **The closed form along the arc.**  `q_0τ^Msinθ\,H_M = sin((M+1)θ)`, the
`r = 2` analogue of `QuadraticCase.quad_favard_on_arc`.

Both Vieta relations turn the three-term recurrence into the Chebyshev one:
`q_1τ = -2q_0cosθ` supplies the `2cosθ`, and `(q_2+z)τ^2 = q_0` makes the
second coefficient exactly `1`.  Since `τ` varies with `θ` here, it is the pair of
relations rather than a constant modulus that does the work. -/
theorem ray_coeffPoly_on_arc {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (M : ℕ) :
    ((q0 : ℝ) : ℂ) * ((rayTau q0 q1 θ : ℝ) : ℂ) ^ M * ((Real.sin θ : ℝ) : ℂ)
        * (ftCoeffPoly (quadPoly q0 q1 q2) 1 2 M).eval (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
      = ((Real.sin (((M + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
  have hq0c : ((q0 : ℝ) : ℂ) ≠ 0 := by simpa using hq0.ne'
  have hc0 : (quadPoly q0 q1 q2).coeff 0 = ((q0 : ℝ) : ℂ) := by simp [quadPoly]
  have hc1 : (quadPoly q0 q1 q2).coeff 1 = ((q1 : ℝ) : ℂ) := by simp [quadPoly]
  set τ : ℝ := rayTau q0 q1 θ with hτdef
  set z : ℝ := rayZ q0 q1 q2 θ with hzdef
  set H : ℕ → ℂ := fun m => (ftCoeffPoly (quadPoly q0 q1 q2) 1 2 m).eval ((z : ℝ) : ℂ) with hH
  set G : ℕ → ℂ := fun m =>
    ((q0 : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ m * ((Real.sin θ : ℝ) : ℂ) * H m with hG
  have hprod : ((q2 : ℝ) : ℂ) + ((z : ℝ) : ℂ) = ((q2 + z : ℝ) : ℂ) := by
    rw [Complex.ofReal_add]
  have hVprod : ((q2 + z : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ 2 = ((q0 : ℝ) : ℂ) := by
    exact_mod_cast rayZ_mul_sq hq0 hq1 hcos
  have hVlin : ((q1 : ℝ) : ℂ) * ((τ : ℝ) : ℂ)
      = -2 * ((q0 : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) := by
    exact_mod_cast rayTau_mul hq1 q2 θ
  have hH0 : H 0 = (((q0 : ℝ) : ℂ))⁻¹ := by
    change (ftCoeffPoly (quadPoly q0 q1 q2) 1 2 0).eval ((z : ℝ) : ℂ) = _
    simp [ftCoeffPoly_eq (quadPoly q0 q1 q2) 1 2 0, hc0]
  have hH1 : H 1 = -((((q0 : ℝ) : ℂ))⁻¹ * (((q1 : ℝ) : ℂ) * (((q0 : ℝ) : ℂ))⁻¹)) := by
    change (ftCoeffPoly (quadPoly q0 q1 q2) 1 2 1).eval ((z : ℝ) : ℂ) = _
    have h0 : (ftCoeffPoly (quadPoly q0 q1 q2) 1 2 0).eval ((z : ℝ) : ℂ)
        = (((q0 : ℝ) : ℂ))⁻¹ := hH0
    simp [ftCoeffPoly_eq (quadPoly q0 q1 q2) 1 2 1, hc0, ftDenCoeff, hc1, h0,
      Polynomial.coeff_one]
  -- the Chebyshev recurrence for the sines, on the real side
  have htrig : ∀ n : ℕ, Real.sin (((n + 3 : ℕ) : ℝ) * θ)
      = 2 * Real.cos θ * Real.sin (((n + 2 : ℕ) : ℝ) * θ) - Real.sin (((n + 1 : ℕ) : ℝ) * θ) := by
    intro n
    have h1 : ((n + 3 : ℕ) : ℝ) * θ = ((n + 2 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    have h2 : ((n + 1 : ℕ) : ℝ) * θ = ((n + 2 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  have key : ∀ n : ℕ,
      G n = ((Real.sin (((n + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) ∧
      G (n + 1) = ((Real.sin (((n + 2 : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp only [hG, hH0, pow_zero]
        rw [show (((0 + 1 : ℕ) : ℝ)) * θ = θ by norm_num]
        field_simp
      · simp only [hG, hH1]
        rw [show (((0 + 2 : ℕ) : ℝ)) * θ = 2 * θ by norm_num, Real.sin_two_mul,
          Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
        field_simp
        linear_combination (-((Real.sin θ : ℝ) : ℂ)) * hVlin
    | succ k ih =>
      obtain ⟨ihk, ihk1⟩ := ih
      refine ⟨ihk1, ?_⟩
      have hrecev := congrArg (Polynomial.eval (((z : ℝ) : ℂ)))
        (ray_denominator_recurrence (q0 := q0) (q1 := q1) (q2 := q2) hq0
          (M := k + 2) (by omega))
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero] at hrecev
      rw [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl] at hrecev
      have hrec : ((q0 : ℝ) : ℂ) * H (k + 2) + ((q1 : ℝ) : ℂ) * H (k + 1)
          + ((q2 + z : ℝ) : ℂ) * H k = 0 := by
        rw [← hprod]; simpa [hH] using hrecev
      have hsin3 : ((Real.sin (((k + 1 + 2 : ℕ) : ℝ) * θ) : ℝ) : ℂ)
          = 2 * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin (((k + 2 : ℕ) : ℝ) * θ) : ℝ) : ℂ)
            - ((Real.sin (((k + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
        rw [show k + 1 + 2 = k + 3 from rfl, htrig k]
        rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul,
          Complex.ofReal_ofNat]
      rw [hsin3, ← ihk, ← ihk1]
      simp only [hG]
      rw [show k + 1 + 1 = k + 2 from rfl,
        show ((τ : ℝ) : ℂ) ^ (k + 2) = ((τ : ℝ) : ℂ) ^ k * ((τ : ℝ) : ℂ) ^ 2 by ring,
        show ((τ : ℝ) : ℂ) ^ (k + 1) = ((τ : ℝ) : ℂ) ^ k * ((τ : ℝ) : ℂ) by ring]
      linear_combination
        (((τ : ℝ) : ℂ) ^ 2 * ((τ : ℝ) : ℂ) ^ k * ((Real.sin θ : ℝ) : ℂ)) * hrec
        - (((τ : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ k * ((Real.sin θ : ℝ) : ℂ) * H (k + 1)) * hVlin
        - (((τ : ℝ) : ℂ) ^ k * ((Real.sin θ : ℝ) : ℂ) * H k) * hVprod
  exact (key M).1


/-! ### `z` is strictly increasing, into a ray -/

/-- `z(θ) = q_1^2/(4q_0cos^2θ) - q_2`, the form the monotonicity is read off. -/
theorem rayZ_eq {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) :
    rayZ q0 q1 q2 θ = q1 ^ 2 / (4 * q0 * (Real.cos θ) ^ 2) - q2 := by
  have h1 : q1 ≠ 0 := hq1.ne
  have h2 : Real.cos θ ≠ 0 := hcos.ne'
  have h3 : q0 ≠ 0 := hq0.ne'
  rw [rayZ, rayTau]
  field

theorem rayCos_pos {a b θ : ℝ} (ha : 0 ≤ a) (hb : b < Real.pi / 2)
    (hθ : θ ∈ Set.Icc a b) : 0 < Real.cos θ := by
  refine Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

/-- **`z` is strictly increasing on the arc.**  `cos` is strictly decreasing and positive on
`(0, π/2)`, so `1/cos^2` is strictly increasing and `z` with it. -/
theorem rayZ_strictMonoOn {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b < Real.pi / 2) :
    StrictMonoOn (rayZ q0 q1 q2) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hcx : 0 < Real.cos x := rayCos_pos ha hb hx
  have hcy : 0 < Real.cos y := rayCos_pos ha hb hy
  have hlt : Real.cos y < Real.cos x :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hy.2, Real.pi_pos]) hxy
  have hsq : (Real.cos y) ^ 2 < (Real.cos x) ^ 2 := by nlinarith
  have hq1sq : 0 < q1 ^ 2 := by nlinarith
  have hby : 0 < 4 * q0 * (Real.cos y) ^ 2 := by positivity
  rw [rayZ_eq hq0 hq1 hcx, rayZ_eq hq0 hq1 hcy]
  have : q1 ^ 2 / (4 * q0 * (Real.cos x) ^ 2) < q1 ^ 2 / (4 * q0 * (Real.cos y) ^ 2) :=
    div_lt_div_of_pos_left hq1sq hby (by nlinarith)
  linarith

/-- The image lands in the Forgács--Tran **ray** `(q_1^2/(4q_0) - q_2, ∞)`: `cosθ < 1`
strictly for `θ > 0`, which is `eq:ab-def`'s `b = +∞` for `r > 1`. -/
theorem rayZ_mem_Ioi {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {a b θ : ℝ}
    (ha : 0 < a) (hb : b < Real.pi / 2) (hθ : θ ∈ Set.Icc a b) :
    rayZ q0 q1 q2 θ ∈ Set.Ioi (q1 ^ 2 / (4 * q0) - q2) := by
  have hcθ : 0 < Real.cos θ := rayCos_pos ha.le hb hθ
  have hθpos : 0 < θ := lt_of_lt_of_le ha hθ.1
  have hlt1 : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (by linarith [hθ.2, Real.pi_pos]) hθpos
    simpa using this
  have hsq : (Real.cos θ) ^ 2 < 1 := by nlinarith
  have hq1sq : 0 < q1 ^ 2 := by nlinarith
  rw [Set.mem_Ioi, rayZ_eq hq0 hq1 hcθ]
  have hpos : 0 < 4 * q0 * (Real.cos θ) ^ 2 := by positivity
  have : q1 ^ 2 / (4 * q0) < q1 ^ 2 / (4 * q0 * (Real.cos θ) ^ 2) :=
    div_lt_div_of_pos_left hq1sq hpos (by nlinarith)
  linarith



/-! ### The coefficient sequence is real

`PhaseSupply` wants `P : ℝ[X]` with `P` complexifying to `ftCoeffPoly`.  The pencil and
the weight both have real coefficients, and the convolution recurrence of
`prop:isolated-dominant-cancellation` uses only ring operations, so the whole sequence lies in
the image of `ℝ[X] → ℂ[X]`.  Stating that as membership in the range
**subring** rather than as a bare existential is what makes the induction one line per
ingredient. -/

theorem ftCoeffPoly_mem_range (q0 q1 q2 : ℝ) : ∀ M : ℕ,
    ftCoeffPoly (quadPoly q0 q1 q2) 1 2 M
      ∈ (Polynomial.mapRingHom (algebraMap ℝ ℂ)).range := by
  have hCmem : ∀ x : ℝ, (Polynomial.C ((x : ℝ) : ℂ))
      ∈ (Polynomial.mapRingHom (algebraMap ℝ ℂ)).range :=
    fun x => ⟨Polynomial.C x, by simp⟩
  have hcoeff : ∀ j : ℕ, ∃ x : ℝ, (quadPoly q0 q1 q2).coeff j = ((x : ℝ) : ℂ) := by
    intro j
    rcases j with _ | j
    · exact ⟨q0, by simp [quadPoly]⟩
    · rcases j with _ | j
      · exact ⟨q1, by simp [quadPoly]⟩
      · rcases j with _ | j
        · exact ⟨q2, by simp [quadPoly]⟩
        · refine ⟨0, ?_⟩
          have h1 : j + 3 ≠ 0 := by omega
          have h2 : j + 3 ≠ 1 := by omega
          have h3 : ¬ (j + 3 = 2) := by omega
          simp [quadPoly]
  have hden : ∀ j : ℕ, ftDenCoeff (quadPoly q0 q1 q2) 2 j
      ∈ (Polynomial.mapRingHom (algebraMap ℝ ℂ)).range := by
    intro j
    obtain ⟨x, hx⟩ := hcoeff j
    rw [ftDenCoeff, hx]
    by_cases hj : j = 2
    · rw [if_pos hj]
      exact Subring.add_mem _ (hCmem x) ⟨Polynomial.X, by simp⟩
    · rw [if_neg hj, add_zero]
      exact hCmem x
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rw [ftCoeffPoly_eq]
    obtain ⟨x0, hx0⟩ := hcoeff 0
    refine Subring.mul_mem _ ?_ (Subring.sub_mem _ ?_ ?_)
    · rw [hx0, ← Complex.ofReal_inv]
      exact hCmem x0⁻¹
    · refine ⟨Polynomial.C ((1 : Polynomial ℝ).coeff M), ?_⟩
      change (Polynomial.C ((1 : Polynomial ℝ).coeff M)).map (algebraMap ℝ ℂ)
        = Polynomial.C ((1 : Polynomial ℂ).coeff M)
      rw [Polynomial.map_C, Polynomial.coeff_one, Polynomial.coeff_one]
      split_ifs <;> simp
    · refine Subring.sum_mem _ fun i hi => ?_
      exact Subring.mul_mem _ (hden _) (ih i (Finset.mem_range.1 hi))

/-- The real coefficient sequence, extracted. -/
theorem exists_real_ftCoeffPoly (q0 q1 q2 : ℝ) (M : ℕ) :
    ∃ P : Polynomial ℝ, P.map (algebraMap ℝ ℂ) = ftCoeffPoly (quadPoly q0 q1 q2) 1 2 M := by
  obtain ⟨P, hP⟩ := ftCoeffPoly_mem_range q0 q1 q2 M
  exact ⟨P, hP⟩



/-! ### The weight `t^k`, at `r = 2`

`ClauseThreeMonomial` shifts the coefficient sequence and multiplies the amplitude by `t_+^k`
on any denominator.  Here that gives a family of weights of every degree over the ray pencil,
so `deg B` varies at `r > 1` exactly as it does at `r = 1` — and the argument branch acquires
the slope `k`, which is the numerator's own `κ` of `eq:phase-derivative-bound`. -/

/-- The argument branch at the weight `t^k`: `arg𝒲_{t^k} = kθ + π/2`. -/
noncomputable def rayPsi (k : ℕ) : ℝ → ℝ := fun θ => (k : ℝ) * θ + Real.pi / 2

theorem rayPsi_apply (k : ℕ) (θ : ℝ) : rayPsi k θ = (k : ℝ) * θ + Real.pi / 2 := rfl

theorem ray_ftAmp_pow (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) (X ^ k) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ k
        * (Complex.I * ((rayTau q0 q1 θ : ℝ) : ℂ)
          / (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) := by
  rw [ftAmp_X_pow, ray_ftAmp hq0 hq1 hcos hsin]

theorem ray_ftAmp_pow_ne_zero (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) (X ^ k) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
      (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
  have hτ : 0 < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  have hτc : ((rayTau q0 q1 θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hden : (0 : ℝ) < 2 * q0 * Real.sin θ := by positivity
  rw [ray_ftAmp_pow k hq0 hq1 hcos hsin]
  refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hτc (Complex.exp_ne_zero _))) ?_
  refine div_ne_zero (mul_ne_zero Complex.I_ne_zero hτc) ?_
  rw [show (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
      = ((2 * q0 * Real.sin θ : ℝ) : ℂ) by push_cast; ring]
  exact_mod_cast hden.ne'

/-- `|W_k| = τ^k·τ/(2q_0sinθ)`.  Both factors vanish at the upper endpoint
here, unlike the `r = 1` pencil where `τ ≡ 1` and only the weight's own degree shows. -/
theorem ray_norm_ftAmp_pow (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ‖ftAmp (quadPoly q0 q1 q2) (X ^ k) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
      = (rayTau q0 q1 θ) ^ k * (rayTau q0 q1 θ / (2 * q0 * Real.sin θ)) := by
  have hτ : 0 < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  rw [ray_ftAmp_pow k hq0 hq1 hcos hsin, norm_mul, norm_pow, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ, Complex.norm_exp_ofReal_mul_I,
    mul_one]
  congr 1
  have := ray_norm_ftAmp (q2 := q2) hq0 hq1 hcos hsin
  rw [ray_ftAmp hq0 hq1 hcos hsin] at this
  exact this

/-- **The polar form at the weight `t^k`**, with the branch `ψ_k(θ) = kθ + π/2`.
Its derivative is the constant `k` — the numerator-dependent `κ` of
`eq:phase-derivative-bound` — while the modulus carries the extra `τ^k`. -/
theorem ray_polar_pow (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) (X ^ k) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = ((‖ftAmp (quadPoly q0 q1 q2) (X ^ k) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
            (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ : ℝ) : ℂ)
        * Complex.exp (((rayPsi k θ : ℝ) : ℂ) * Complex.I) := by
  have hτ : 0 < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  have hden : (0 : ℝ) < 2 * q0 * Real.sin θ := by positivity
  have hI : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  have hsplit : Complex.exp (((rayPsi k θ : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) ^ k
        * Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, rayPsi_apply]
    congr 1
    push_cast
    ring
  rw [ray_norm_ftAmp_pow k hq0 hq1 hcos hsin, ray_ftAmp_pow k hq0 hq1 hcos hsin,
    hsplit, hI, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_pow]
  ring


end ForgacsTran
