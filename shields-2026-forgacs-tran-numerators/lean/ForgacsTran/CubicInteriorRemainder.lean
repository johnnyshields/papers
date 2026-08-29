/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CubicClockSpacing
import ForgacsTran.CubicWitnessComposition
import ForgacsTran.QuotientDerivBound
import ForgacsTran.ComplexPart

/-!
# The interior remainder at the cubic pencil

`cubic_local_strong_clock` carries one analytic binder, the remainder `e` of
`eq:principal-decomposition` with its `C^0` and `C^1` bounds.  This module
supplies the `C^0` half unconditionally at this pencil.

## Main statements

* `ftDen_cubicQ_eval_factor` — the denominator factors over its three zeros.
* `cubic_denominator_lower`, `cubic_denominator_floor`, `cubic_den_floor_nbhd` —
  hence `‖D‖` is bounded below on `‖t‖ = 1`, uniformly over a subarc, and stays
  so for every nearby spectral parameter.
* `cubic_pole_data` — the five pole-structure binders the `DominanceFT` and
  `EndpointDominance` interfaces share, at one angle.
* `cubic_interior_remainder` — `eq:interior-remainder` at this pencil: the
  remainder is `O(σ^M)` at the explicit `σ = τ(e) < 1`.
* `cubic_interior_cos_error` — `eq:principal-decomposition` normalized, with the
  error bounded by `Cσ^M` and the phase being `cubicPsi a` itself.
* `hasDerivAt_cubicZbranch`, `hasDerivAt_cubicAmpNorm`,
  `abs_cubicAmpNormDeriv_le` — the `C¹` ingredients: the spectral parameter's
  derivative along the branch, and the amplitude modulus differentiated off its
  zero with `|d‖W‖/dθ| ≤ ‖W'‖`.
* `cubic_interior_cos_error_C1` — `eq:C1-interior-remainder`: the error is `C¹`
  with derivative `O(Mσ^M)`, the `(M+1)` coming from the `τ^{M+1}` prefactor alone.
* `cubic_local_strong_clock_of_C1` — the capstone with the `C^0` side closed.
* `cubic_local_strong_clock_closed` — **`prop:local-strong-clock` at this pencil
  with nothing assumed.**

## Implementation notes

**The separating radius is `R₀ = 1`, and that is the whole geometric input.**
`D(t) = (1-t)^3 + zt` has three zeros; the principal pair sits at modulus `τ` and
the third at `1/τ²`, by Vieta on a cubic whose roots multiply to `1`.  Since
`τ < 1` on the open arc, one radius separates them at *every* angle, which is
what lets `σ` be chosen once for a whole subarc rather than per angle.  On
`‖t‖ = 1` the factorization then bounds `‖D‖` below by `(1-τ)²(1/τ²-1)` and hence
`‖B/D‖` above, which is the last binder of
`DominanceFTSupply.interior_remainder_uniform`.  Moving the spectral parameter by `δ`
moves `D` by at most `δ` there, so half the floor survives half the floor's worth
of motion — which is the neighborhood form
`PoleExpansion.hasDerivAt_ftContourRem_comp` asks for.

**Nothing is assumed.**  `cubic_local_strong_clock_closed` discharges every
binder, the remainder's included.  `DominanceFTSupply.ftCoeff_re_sub_principal_eq_contour_re`
puts the numerator on the contour, where `hasDerivAt_ftContourRem_comp`
differentiates it; `hasDerivAt_cubicAmpNorm` differentiates the denominator
`2‖W‖`; and `QuotientDerivBound.abs_div_deriv_le_of_scaled` folds the quotient
rule's two terms into one.

**The four arithmetic steps are top-level and proved in isolation**, each over
bare reals and norms with no branch object in it.  That is not tidiness:
assembling them inline produced `nlinarith` heartbeat timeouts and `positivity`
failures that looked like separate defects and were all one scope of twenty
hypotheses.

**Measured.**  `scripts/check_cubic_interior_remainder.py` checks every
inequality of the `C^0` chain against the remainder computed from the defining
recurrence — the separation `τ ≤ 0.786 < 1 < 1.62 ≤ 1/τ²` on `[e, π-e]` at
`e = 1/2`, the floor `‖D‖ ≥ 0.0287` on the unit circle, and
`|R_M| ≤ τ(e)(4/D_lo)τ(e)^M` at `M = 8..50` — and then instantiates
`cubic_local_strong_clock_of_C1`'s window binders, which need `Φ` to turn by more
than `2π + 2δ` before an admissible `u₀` exists: on `[1.75, 2.55]` with
`δ = π/4` that is `M ≥ 10`, and a witness `u₀` is exhibited there.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Weighted
principal-pair dominance» (`sec:dominance`, `thm:weighted-dominance`,
`lem:contour-separation`, `eq:interior-relative-remainder`) at the witness
pencil, feeding «Local phase quantization and strong-clock spacing»
(`subsec:strong-clock`, `prop:local-strong-clock`).

## Tags

interior remainder, contour separation, cubic pencil
-/

open Polynomial Complex

namespace ForgacsTran

open Real Set

/-- The conjugate member of the principal pair, in the `e^{-iθ}` spelling
`DominanceFTSupply.interior_remainder_uniform` writes it in. -/
noncomputable def cubicArcPoint (θ : ℝ) : ℂ :=
  ((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)

theorem cubicArcPoint_eq_conj (θ : ℝ) :
    cubicArcPoint θ = (starRingEnd ℂ) (ftPrincipal cubicTau θ) := by
  rw [cubicArcPoint, ftPrincipal, map_mul, ← Complex.exp_conj]
  simp

theorem cubicArcPoint_eq_conj' (θ : ℝ) :
    ((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) :=
  cubicArcPoint_eq_conj θ

theorem norm_cubicArcPoint (θ : ℝ) : ‖cubicArcPoint θ‖ = cubicTau θ := by
  rw [cubicArcPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cubicTau_pos θ), Complex.norm_exp]
  simp

private theorem exp_mul_exp_neg (θ : ℝ) :
    Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)
      = 1 := by
  rw [← Complex.exp_add]
  have : ((θ : ℝ) : ℂ) * Complex.I + -((θ : ℝ) : ℂ) * Complex.I = 0 := by ring
  rw [this, Complex.exp_zero]

private theorem exp_add_exp_neg (θ : ℝ) :
    Complex.exp (((θ : ℝ) : ℂ) * Complex.I) + Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)
      = 2 * ((Real.cos θ : ℝ) : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  ring

/-- **The principal pair's quadratic factor.**  `(t - γ)(t - γ̄) = t² - 2τcos θ t + τ²`,
with the two exponentials eliminated by `e^{iθ}e^{-iθ} = 1` and
`e^{iθ} + e^{-iθ} = 2cos θ`. -/
theorem cubic_pair_quadratic (θ : ℝ) (t : ℂ) :
    (t - ftPrincipal cubicTau θ) * (t - cubicArcPoint θ)
      = t ^ 2 - 2 * ((cubicTau θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) * t
          + ((cubicTau θ : ℝ) : ℂ) ^ 2 := by
  rw [ftPrincipal, cubicArcPoint]
  linear_combination (((cubicTau θ : ℝ) : ℂ) ^ 2) * exp_mul_exp_neg θ
    - (((cubicTau θ : ℝ) : ℂ) * t) * exp_add_exp_neg θ

/-- **The denominator factors over its three zeros.**  `D = -(t-γ)(t-γ̄)(t-1/τ²)`,
the single algebraic fact behind both the separation of the principal pair from
the third zero and the lower bound on `‖D‖` off them.  The only branch input is
`cubicTau_branch`. -/
theorem ftDen_cubicQ_eval_factor (θ : ℝ) (t : ℂ) :
    (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t
      = -((t - ftPrincipal cubicTau θ) * (t - cubicArcPoint θ)
            * (t - ((cubicThird θ : ℝ) : ℂ))) := by
  have hτ0 : (0 : ℝ) < cubicTau θ := cubicTau_pos θ
  have hτc : ((cubicTau θ : ℝ) : ℂ) ≠ 0 := by
    simpa using hτ0.ne'
  have hbrC : 2 * ((Real.cos θ : ℝ) : ℂ) * ((cubicTau θ : ℝ) : ℂ) ^ 3
      - 3 * ((cubicTau θ : ℝ) : ℂ) ^ 2 + 1 = 0 := by
    have := cubicTau_branch θ
    exact_mod_cast congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) this
  have hc : Complex.cos ((θ : ℝ) : ℂ) = ((Real.cos θ : ℝ) : ℂ) := (Complex.ofReal_cos θ).symm
  rw [ftDen_eval, cubicQ_eval, pow_one, cubic_pair_quadratic, cubicThird, cubicZ]
  push_cast
  field_simp
  ring_nf
  linear_combination (-(t ^ 2)) * hbrC
    + (-(2 * ((cubicTau θ : ℝ) : ℂ) ^ 3 * t ^ 2)) * hc

/-! ### `‖D‖` off the zeros, and the binders of `interior_remainder_uniform` -/

theorem one_lt_cubicThird {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : 1 < cubicThird θ := by
  have h0 : (0 : ℝ) < cubicTau θ := cubicTau_pos θ
  have h1 : cubicTau θ < 1 := cubicTau_lt_one hθ
  rw [cubicThird, lt_div_iff₀ (by positivity)]
  nlinarith

/-- **`‖D‖` is bounded below on the unit circle.**  Off the three zeros the
factorization is a product of three moduli, each bounded by the triangle
inequality against `‖t‖ = 1`: the pair sits at `τ < 1` and the third zero at
`1/τ² > 1`, so the circle is separated from all three at once. -/
theorem cubic_denominator_lower {θ : ℝ} (hθ : θ ∈ Ioo 0 π) {t : ℂ} (ht : ‖t‖ = 1) :
    (1 - cubicTau θ) ^ 2 * (cubicThird θ - 1)
      ≤ ‖(ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t‖ := by
  have hτ0 : (0 : ℝ) < cubicTau θ := cubicTau_pos θ
  have hτ1 : cubicTau θ < 1 := cubicTau_lt_one hθ
  have h3 : 1 < cubicThird θ := one_lt_cubicThird hθ
  have hnp : ‖ftPrincipal cubicTau θ‖ = cubicTau θ := by
    rw [ftPrincipal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτ0, Complex.norm_exp]
    simp
  have hb1 : 1 - cubicTau θ ≤ ‖t - ftPrincipal cubicTau θ‖ := by
    have := norm_sub_norm_le t (ftPrincipal cubicTau θ)
    rw [ht, hnp] at this
    exact this
  have hb2 : 1 - cubicTau θ ≤ ‖t - cubicArcPoint θ‖ := by
    have := norm_sub_norm_le t (cubicArcPoint θ)
    rw [ht, norm_cubicArcPoint] at this
    exact this
  have hb3 : cubicThird θ - 1 ≤ ‖t - ((cubicThird θ : ℝ) : ℂ)‖ := by
    have := norm_sub_norm_le ((cubicThird θ : ℝ) : ℂ) t
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    rw [norm_sub_rev]
    exact this
  rw [ftDen_cubicQ_eval_factor, norm_neg, norm_mul, norm_mul]
  have hq : (1 - cubicTau θ) * (1 - cubicTau θ)
      ≤ ‖t - ftPrincipal cubicTau θ‖ * ‖t - cubicArcPoint θ‖ :=
    mul_le_mul hb1 hb2 (by linarith) (le_trans (by linarith) hb1)
  have hfin := mul_le_mul hq hb3 (by linarith) (le_trans (by nlinarith) hq)
  nlinarith [hfin]

/-- **The pole-structure binders, at one angle.**  `interior_remainder_uniform`,
`ftRemainder_eq_contour` and `ftCoeff_re_sub_principal_eq_contour_re` share five
hypotheses about where the denominator's zeros are; all five hold at this pencil
at every interior angle, with the separating radius `R₀ = 1`. -/
theorem cubic_pole_data {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval (ftPrincipal cubicTau θ) = 0 ∧
    (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval
        (ftPrincipal cubicTau θ) ≠ 0 ∧
    (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval
        (((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) ≠ 0 ∧
    ftPrincipal cubicTau θ ≠ ((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) ∧
    (∀ t : ℂ, ‖t‖ ≤ 1 → (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal cubicTau θ ∨
        t = ((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) := by
  refine ⟨ftDen_cubicQ_eval_cubicTau θ,
    derivative_ftDen_cubicQ_ne_zero hθ (by simp [cubicRootSet, ftPrincipal]), ?_, ?_, ?_⟩
  · rw [cubicArcPoint_eq_conj' θ]
    exact derivative_ftDen_cubicQ_ne_zero hθ (by simp [cubicRootSet])
  · rw [cubicArcPoint_eq_conj' θ]
    exact cubic_pair_ne hθ
  · intro t hnorm hroot
    have h3 : 1 < cubicThird θ := one_lt_cubicThird hθ
    rcases cubicRoot_eq_of_eval_zero hθ hroot with h | h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, cubicArcPoint_eq_conj'])
    · exfalso
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hnorm
      linarith

/-- The uniform floor for `‖D‖` on the unit circle over a subarc: `τ ≤ τ(e) < 1`
there, and both factors of `cubic_denominator_lower` are monotone in `τ`. -/
noncomputable def cubicDenFloor (e : ℝ) : ℝ :=
  (1 - cubicTau e) ^ 2 * (1 / cubicTau e ^ 2 - 1)

theorem cubicDenFloor_pos {e : ℝ} (he : 0 < e) (he2 : e < π) : 0 < cubicDenFloor e := by
  have hτe0 : 0 < cubicTau e := cubicTau_pos e
  have hτe1 : cubicTau e < 1 := cubicTau_lt_one ⟨he, he2⟩
  have h1 : 1 < 1 / cubicTau e ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have h2 : 0 < (1 - cubicTau e) ^ 2 := by positivity
  rw [cubicDenFloor]; nlinarith

theorem cubicTau_le_of_mem {e θ : ℝ} (he : 0 < e) (he2 : e < π / 2)
    (hθ : θ ∈ Icc e (π - e)) : cubicTau θ ≤ cubicTau e := by
  have hpi := Real.pi_pos
  rcases eq_or_lt_of_le hθ.1 with h | h
  · exact le_of_eq (by rw [h])
  · exact (cubicTau_strictAntiOn ⟨he.le, by linarith⟩
      ⟨le_trans he.le hθ.1, by linarith [hθ.2]⟩ h).le

/-- **`‖D‖` is bounded below on the unit circle, uniformly over a subarc.** -/
theorem cubic_denominator_floor {e : ℝ} (he : 0 < e) (he2 : e < π / 2)
    {θ : ℝ} (hθ : θ ∈ Icc e (π - e)) {t : ℂ} (ht : ‖t‖ = 1) :
    cubicDenFloor e ≤ ‖(ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t‖ := by
  have hpi := Real.pi_pos
  have harc : θ ∈ Ioo 0 π := ⟨lt_of_lt_of_le he hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  refine le_trans ?_ (cubic_denominator_lower harc ht)
  have hle := cubicTau_le_of_mem he he2 hθ
  have hτ0 : 0 < cubicTau θ := cubicTau_pos θ
  have hτe0 : 0 < cubicTau e := cubicTau_pos e
  have hτe1 : cubicTau e < 1 := cubicTau_lt_one ⟨he, by linarith⟩
  have hsq : 1 / cubicTau e ^ 2 ≤ cubicThird θ := by
    rw [cubicThird, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlin : (1 - cubicTau e) ^ 2 ≤ (1 - cubicTau θ) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) < 1 / cubicTau e ^ 2 - 1 := by
    have : 1 < 1 / cubicTau e ^ 2 := by rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  rw [cubicDenFloor]
  nlinarith [hlin, hsq, h3, sq_nonneg (1 - cubicTau e)]

theorem norm_witB_eval_le {t : ℂ} (ht : ‖t‖ = 1) : ‖witB.eval t‖ ≤ 4 := by
  rw [witB_eval]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_pow, ht, norm_one]
  norm_num

/-- **`eq:interior-remainder` at the cubic pencil, unconditionally.**  On every
compact subarc `[e, π-e]` the remainder of `eq:principal-decomposition` is
`O(σ^M)` at the explicit `σ = τ(e) < 1`, with no analytic hypothesis.

Every binder of `DominanceFTSupply.interior_remainder_uniform` is discharged here.  The
separating radius is `R₀ = 1`: the principal pair has modulus `τ ≤ τ(e) < 1` and
the third zero `1/τ² ≥ 1/τ(e)² > 1`, so one radius separates them at every angle
of the subarc, which is what lets `σ` be chosen once. -/
theorem cubic_interior_remainder {e : ℝ} (he : 0 < e) (he2 : e < π / 2) :
    ∀ (M : ℕ), ∀ θ ∈ Icc e (π - e),
      |ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ|
        ≤ cubicTau e * (4 / cubicDenFloor e) * cubicTau e ^ M := by
  have hpi := Real.pi_pos
  have hτe0 : 0 < cubicTau e := cubicTau_pos e
  have hτe1 : cubicTau e < 1 := cubicTau_lt_one ⟨he, by linarith⟩
  have hDlopos := cubicDenFloor_pos he (by linarith)
  intro M θ hθ
  refine interior_remainder_uniform (Q := cubicQ) (B := witB)
    hasRealCoeffs_cubicQ hasRealCoeffs_witB le_rfl (by simp [cubicQ])
    (R₀ := 1) (τmax := cubicTau e) (C := 4 / cubicDenFloor e) (σ := cubicTau e)
    (lo := e) (hi := π - e) one_pos (by rw [div_one]) (by positivity)
    (fun θ' _ _ => cubicTau_pos θ') (fun θ' h1 h2 => cubicTau_le_of_mem he he2 ⟨h1, h2⟩)
    (fun θ' h1 h2 => cubicTau_lt_one ⟨lt_of_lt_of_le he h1, by linarith⟩)
    (fun θ' _ _ => ftDen_cubicQ_eval_cubicTau θ')
    (fun θ' h1 h2 => (cubic_pole_data ⟨lt_of_lt_of_le he h1, by linarith⟩).2.1)
    (fun θ' h1 h2 => (cubic_pole_data ⟨lt_of_lt_of_le he h1, by linarith⟩).2.2.1)
    (fun θ' h1 h2 => (cubic_pole_data ⟨lt_of_lt_of_le he h1, by linarith⟩).2.2.2.1)
    (fun θ' h1 h2 t hnorm hroot =>
      (cubic_pole_data ⟨lt_of_lt_of_le he h1, by linarith⟩).2.2.2.2 t hnorm hroot)
    (fun θ' h1 h2 t ht => ?_) M θ hθ.1 hθ.2
  have htn : ‖t‖ = 1 := by simpa using Metric.mem_sphere.1 ht
  have hDge := cubic_denominator_floor he he2 ⟨h1, h2⟩ htn
  rw [norm_div, div_le_div_iff₀ (by linarith) hDlopos]
  nlinarith [norm_witB_eval_le htn, norm_nonneg (witB.eval t), hDlopos]

/-- **`eq:interior-remainder` on the contour side.**  The bound of
`cubic_interior_remainder` carried across `ftRemainder_eq_contour` to the quantity
the `C⁰` and `C¹` estimates actually differentiate and divide, `τ^{M+1}E_M`.

This is where `cubic_pole_data`'s five clauses are spent, and it is the only place
they are needed on this route: past it the remainder is an ordinary normed
quantity with a geometric bound and no pole structure left in it. -/
theorem cubic_interior_remainder_norm {e : ℝ} (he : 0 < e) (he2 : e < π / 2)
    {θ : ℝ} (harc : θ ∈ Ioo 0 π) (hθ : θ ∈ Icc e (π - e)) (M : ℕ) :
    cubicTau θ ^ (M + 1)
        * ‖ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖
      ≤ cubicTau e * (4 / cubicDenFloor e) * cubicTau e ^ M := by
  obtain ⟨hr, hs, hsm, hne, hpair⟩ := cubic_pole_data harc
  have heq := ftRemainder_eq_contour (Q := cubicQ) (B := witB)
    hasRealCoeffs_cubicQ hasRealCoeffs_witB le_rfl (by simp [cubicQ])
    (z := fun θ' => cubicZ (cubicTau θ') θ') (τ := cubicTau)
    (cubicTau_pos θ) one_pos (cubicTau_lt_one harc) hr hs hsm hne hpair M
  have hb := cubic_interior_remainder he he2 M θ hθ
  rwa [heq, abs_of_nonneg (mul_nonneg (pow_nonneg (cubicTau_pos θ).le _)
    (norm_nonneg _))] at hb

/-- **The same bound on the real part**, which is the shape both estimates consume:
the numerator they divide by `2‖W‖` is `Re(τ^{M+1}E_M)`, not its modulus.

The step is `|Re w| ≤ ‖w‖` and nothing else — the scalar `τ^{M+1}` is a positive
real, so it passes through the norm unchanged. -/
theorem abs_re_scaled_ftContourRem_le {e : ℝ} (he : 0 < e) (he2 : e < π / 2)
    {θ : ℝ} (harc : θ ∈ Ioo 0 π) (hθ : θ ∈ Icc e (π - e)) (M : ℕ) :
    |((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
        * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re|
      ≤ cubicTau e * (4 / cubicDenFloor e) * cubicTau e ^ M := by
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cubicTau_pos θ)]
  exact cubic_interior_remainder_norm he he2 harc hθ M

/-! ### `eq:principal-decomposition` at the cubic pencil, with its `C^0` bound

`cubic_interior_remainder` bounds the remainder; the amplitude floor turns that
into a bound on the *normalized* error `e` of the cosine decomposition, which is
the object `prop:local-strong-clock` quantizes against.  The subarc must avoid
`π/2` for the floor to exist at all — that is the zero-free hypothesis, and here
it is produced by `cubicAmp_ne_zero` rather than assumed. -/

/-- **The cosine decomposition at the cubic pencil, with nothing assumed.**  On a
compact subarc of the retained range, the normalized coefficient is
`cos Φ_M + e` with `|e| ≤ C σ^M` at an `M`-free `C` and an explicit `σ < 1`.

The phase is `cubicPsi a`, the branch `cubicAmp_eq_polar` constructs, so this is
the `hdec` of `cubic_local_strong_clock` verbatim rather than up to a choice of
`arg`. -/
theorem cubic_interior_cos_error {e a b : ℝ} (he : 0 < e) (he2 : e < π / 2)
    (hab : a ≤ b) (hsubR : Icc a b ⊆ cubicRetained) (hsube : Icc a b ⊆ Icc e (π - e)) :
    ∃ Ce ≥ (0 : ℝ), ∃ σ, 0 < σ ∧ σ < 1 ∧ ∀ M : ℕ, ∃ ee : ℝ → ℝ,
      (∀ θ ∈ Icc a b,
        ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
              * (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re
            / (2 * ftPrincipalAmp cubicQ witB 1
                (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ)
          = Real.cos (((M : ℝ) + 1) * θ - cubicPsi a θ) + ee θ) ∧
      (∀ θ ∈ Icc a b, |ee θ| ≤ Ce * σ ^ M) := by
  classical
  have hτe0 : 0 < cubicTau e := cubicTau_pos e
  have hτe1 : cubicTau e < 1 := cubicTau_lt_one ⟨he, by linarith [Real.pi_pos]⟩
  have hDlopos := cubicDenFloor_pos he (by linarith [Real.pi_pos])
  set CI : ℝ := cubicTau e * (4 / cubicDenFloor e) with hCIdef
  have hCI : 0 ≤ CI := by rw [hCIdef]; positivity
  set σ : ℝ := cubicTau e with hσdef
  have hσ0 : 0 < σ := hτe0
  have hσ1 : σ < 1 := hτe1
  have hrem := cubic_interior_remainder he he2
  -- the amplitude floor, from nonvanishing on the retained range
  obtain ⟨A, hA, hfloor⟩ :=
    exists_amplitude_floor_on_subarc (Q := cubicQ) (B := witB) (r := 1)
      (z := fun θ' => cubicZ (cubicTau θ') θ') (τ := cubicTau) (a := a) (b := b)
      (fun θ hθ => (continuousAt_cubicAmp (hsubR hθ)).continuousWithinAt)
      (fun θ hθ => cubicAmp_ne_zero (hsubR hθ))
  refine ⟨CI / (2 * A), by positivity, σ, hσ0, hσ1, fun M => ?_⟩
  refine ⟨fun θ =>
    ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
        * (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re
      / (2 * ftPrincipalAmp cubicQ witB 1
          (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ)
      - Real.cos (((M : ℝ) + 1) * θ - cubicPsi a θ), fun θ _ => by ring, fun θ hθ => ?_⟩
  have hpolar : ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
      (ftPrincipal cubicTau θ)
      = ((ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ')
          cubicTau θ : ℝ) : ℂ) * Complex.exp ((cubicPsi a θ : ℂ) * Complex.I) := by
    rw [ftPrincipalAmp_cubic_eq]
    exact cubicAmp_eq_polar hab hsubR hθ
  obtain ⟨ee, heq, hbd⟩ := interior_cos_error_geometric (Q := cubicQ) (B := witB) (r := 1)
    (M := M) (z := fun θ' => cubicZ (cubicTau θ') θ') (τ := cubicTau)
    (ψ := cubicPsi a) (θ := θ) (CI := CI) (A := A) (σ := σ)
    (cubicTau_pos θ) hA hσ0.le (hfloor θ hθ) (hrem M θ (hsube hθ)) hpolar
  have hE : ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
        * (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re
      / (2 * ftPrincipalAmp cubicQ witB 1
          (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ)
      - Real.cos (((M : ℝ) + 1) * θ - cubicPsi a θ) = ee := by
    rw [heq]; ring
  dsimp only
  rw [hE]
  exact hbd

/-! ### `eq:C1-interior-remainder`: the pieces

`ftCoeff_re_sub_principal_eq_contour_re` puts the numerator of the normalized
error on the contour, where `PoleExpansion.hasDerivAt_ftContourRem_comp`
differentiates it.  Differentiating in `w` never touches `t^{-M-1}`, so the
derivative carries the same `R^{-M}` as the value and no factor of `M` — the
`(M+1)` in the final bound comes from the `τ^{M+1}` prefactor alone.  What is
assembled here is the rest: the branch's own derivatives, the amplitude modulus,
and the suprema the quotient rule needs. -/

/-- A continuous function on a compact interval is bounded there, with a
nonnegative bound so the empty case needs no separate treatment downstream. -/
private theorem exists_sup_on {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) :
    ∃ C ≥ (0 : ℝ), ∀ θ ∈ Icc a b, |f θ| ≤ C := by
  rcases (Icc a b).eq_empty_or_nonempty with hemp | hne
  · exact ⟨0, le_rfl, fun θ hθ => absurd hθ (by rw [hemp]; exact fun h => h)⟩
  obtain ⟨θ₀, hθ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf.abs
  exact ⟨|f θ₀|, abs_nonneg _, fun θ hθ => hmax hθ⟩

/-- The spectral parameter's derivative along the branch. -/
noncomputable def cubicZbranchDeriv (θ : ℝ) : ℝ :=
  -2 * (cubicTau θ ^ 2 - 1) ^ 2 * (cubicTau θ ^ 2 + 2) / cubicTau θ ^ 5 * cubicTauDeriv θ

theorem hasDerivAt_cubicZbranch {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (fun s => cubicZ (cubicTau s) s) (cubicZbranchDeriv θ) θ := by
  have hτ : (0 : ℝ) < cubicTau θ := cubicTau_pos θ
  have hcomp := (hasDerivAt_cubicZofTau hτ.ne').comp θ (hasDerivAt_cubicTau hθ)
  refine (hcomp.congr_deriv rfl).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => cubicZ_eq_cubicZofTau s

theorem continuousAt_cubicZbranchDeriv {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ContinuousAt cubicZbranchDeriv θ := by
  have hτ : (0 : ℝ) < cubicTau θ := cubicTau_pos θ
  have hc : ContinuousAt cubicTau θ := (hasDerivAt_cubicTau hθ).continuousAt
  have hd : ContinuousAt cubicTauDeriv θ := continuousAt_cubicTauDeriv ⟨hθ.1.le, hθ.2.le⟩
  refine ContinuousAt.mul ?_ hd
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 5 hτ.ne')

/-! ### The four arithmetic steps of the `C¹` bound

Each is stated over bare reals and norms with no branch object in it, and proved
in isolation, so that the tactics run in a scope of three or four hypotheses
rather than of twenty.  That is not a stylistic preference: assembling these
inline produced `nlinarith` heartbeat timeouts and `positivity` failures that
looked like separate defects and were all the one scope. -/

/-- The first term's norm: a `ℕ` cast, a real power, a real factor, a complex
value. -/
private theorem norm_cast_pow_real_mul {n k : ℕ} {t d : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖((n : ℂ)) * ((t : ℝ) : ℂ) ^ k * ((d : ℝ) : ℂ) * w‖ = (n : ℝ) * t ^ k * |d| * ‖w‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Complex.norm_natCast]

/-- The second term's norm: a real power times a real scalar action. -/
private theorem norm_pow_real_mul_smul {k : ℕ} {t z' : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖((t : ℝ) : ℂ) ^ k * (z' • w)‖ = t ^ k * (|z'| * ‖w‖) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    norm_smul, Real.norm_eq_abs]

/-- Dropping one power of a factor bounded below by `1/2` costs a factor of two.
This is what turns the `C⁰` bound on `τ^{M+1}‖R‖` into one on `τ^M‖R‖`, which is
the shape the product rule's first term needs. -/
private theorem pow_mul_le_two_of_half {k : ℕ} {t v c : ℝ} (ht : 1 / 2 ≤ t) (hv : 0 ≤ v)
    (h : t ^ (k + 1) * v ≤ c) : t ^ k * v ≤ 2 * c := by
  have ht0 : 0 < t := by linarith
  have hpk : (0 : ℝ) ≤ t ^ k := pow_nonneg ht0.le k
  have hexp : t ^ (k + 1) * v = t * (t ^ k * v) := by ring
  rw [hexp] at h
  nlinarith [mul_nonneg hpk hv]

/-- The two term bounds fold into the scaled shape
`QuotientDerivBound.abs_div_deriv_le_of_scaled` consumes: the `(M+1)` is carried
by the first term alone, and the second is absorbed because `M + 1 ≥ 1`. -/
private theorem add_le_scaled {m x y s p q : ℝ} (hm : 1 ≤ m) (hs : 0 ≤ s)
    (hq : 0 ≤ q) (hx : x ≤ m * s * p) (hy : y ≤ s * q) :
    x + y ≤ m * s * (p + q) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hm) (mul_nonneg hs hq)]

/-! ### The amplitude modulus is differentiable off its zero -/

/-- `d‖W‖/dθ = Re(W'\overline W)/‖W‖`. -/
noncomputable def cubicAmpNormDeriv (θ : ℝ) : ℝ :=
  (cubicAmpLogDeriv θ * cubicAmp θ * (starRingEnd ℂ) (cubicAmp θ)).re / ‖cubicAmp θ‖

theorem hasDerivAt_cubicAmpNorm {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    HasDerivAt (fun s => ‖cubicAmp s‖) (cubicAmpNormDeriv θ) θ := by
  have hne := cubicAmp_ne_zero hθ
  have hW := hasDerivAt_cubicAmp hθ.1 hθ.2
  have hre := hW.re
  have him := hW.im
  have hns : HasDerivAt
      (fun s => (cubicAmp s).re * (cubicAmp s).re + (cubicAmp s).im * (cubicAmp s).im)
      ((cubicAmpLogDeriv θ * cubicAmp θ).re * (cubicAmp θ).re
          + (cubicAmp θ).re * (cubicAmpLogDeriv θ * cubicAmp θ).re
        + ((cubicAmpLogDeriv θ * cubicAmp θ).im * (cubicAmp θ).im
          + (cubicAmp θ).im * (cubicAmpLogDeriv θ * cubicAmp θ).im)) θ :=
    (hre.mul hre).add (him.mul him)
  have hpos : 0 < (cubicAmp θ).re * (cubicAmp θ).re + (cubicAmp θ).im * (cubicAmp θ).im := by
    have h := Complex.normSq_pos.2 hne
    rwa [Complex.normSq_apply] at h
  refine ((hns.sqrt hpos.ne').congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by
      simp only [Complex.norm_def, Complex.normSq_apply])
  have hs : 0 < Real.sqrt ((cubicAmp θ).re * (cubicAmp θ).re
      + (cubicAmp θ).im * (cubicAmp θ).im) := Real.sqrt_pos.2 hpos
  rw [cubicAmpNormDeriv, Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field

/-- `|d‖W‖/dθ| ≤ ‖W'‖`, which is what the quotient rule needs and all it needs. -/
theorem abs_cubicAmpNormDeriv_le {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    |cubicAmpNormDeriv θ| ≤ ‖cubicAmpLogDeriv θ * cubicAmp θ‖ := by
  have hne := cubicAmp_ne_zero hθ
  have hpos : 0 < ‖cubicAmp θ‖ := norm_pos_iff.2 hne
  rw [cubicAmpNormDeriv, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul, RCLike.norm_conj]

theorem half_le_cubicTau {θ : ℝ} (hθ : θ ∈ Icc 0 π) : 1 / 2 ≤ cubicTau θ := by
  have hc : 0 < Real.cos ((π - θ) / 3) := cos_third_pos hθ
  have hc1 : Real.cos ((π - θ) / 3) ≤ 1 := Real.cos_le_one _
  rw [cubicTau_closed_form hθ, le_div_iff₀ (by positivity)]
  linarith

/-- **`‖D‖` stays bounded below on the unit circle for every nearby spectral
parameter.**  `hasDerivAt_ftContourRem_comp` asks for the floor on a whole real
neighborhood of `z(θ)`, not just at it; moving `z` by `δ` moves `D` by at most
`δ` on `‖t‖ = 1`, so half the floor survives half the floor's worth of motion. -/
theorem cubic_den_floor_nbhd {e : ℝ} (he : 0 < e) (he2 : e < π / 2)
    {θ : ℝ} (hθ : θ ∈ Icc e (π - e)) :
    ∀ x : ℝ, |x - cubicZ (cubicTau θ) θ| ≤ cubicDenFloor e / 2 →
      ∀ t ∈ Metric.sphere (0 : ℂ) 1,
        cubicDenFloor e / 2 ≤ ‖(ftDen cubicQ 1 ((x : ℝ) : ℂ)).eval t‖ := by
  intro x hx t ht
  have htn : ‖t‖ = 1 := by simpa using Metric.mem_sphere.1 ht
  have hz := cubic_denominator_floor he he2 hθ htn
  have hdiff : (ftDen cubicQ 1 ((x : ℝ) : ℂ)).eval t
      = (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t
        + ((x - cubicZ (cubicTau θ) θ : ℝ) : ℂ) * t := by
    simp only [ftDen_eval, pow_one]
    push_cast
    ring
  have hsmall : ‖((x - cubicZ (cubicTau θ) θ : ℝ) : ℂ) * t‖ ≤ cubicDenFloor e / 2 := by
    rw [norm_mul, htn, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hlow := norm_sub_norm_le
    ((ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t)
    (-(((x - cubicZ (cubicTau θ) θ : ℝ) : ℂ) * t))
  rw [sub_neg_eq_add, norm_neg] at hlow
  rw [hdiff]
  linarith

/-- **`eq:C1-interior-remainder` at the cubic pencil, unconditionally.**  The
normalized error of `eq:principal-decomposition` is not merely `O(σ^M)` but `C¹`
with derivative `O(Mσ^M)`, at the same explicit `σ = τ(e) < 1`.

`DominanceFTSupply.ftCoeff_re_sub_principal_eq_contour_re` puts the numerator on the
contour, where `PoleExpansion.hasDerivAt_ftContourRem_comp` differentiates it;
`hasDerivAt_cubicAmpNorm` differentiates the denominator `2‖W‖`; and
`QuotientDerivBound.abs_div_deriv_le_of_scaled` folds the quotient rule's two
terms into one, with the scale `s = (M+1)σ^M` out front so the constant is
visibly free of `M`.

**The single `(M+1)` comes from the `τ^{M+1}` prefactor and from nowhere else.**
Differentiating in the spectral parameter never touches `t^{-M-1}`, so
`ftContourRemDeriv` carries the same `R^{-M}` as the value — that is
`norm_ftContourRemDeriv_le`, and it is why the second term is `M`-free before the
scale is factored out. -/
theorem cubic_interior_cos_error_C1 {e a b : ℝ} (he : 0 < e) (he2 : e < π / 2)
    (hab : a ≤ b) (hsubR : Icc a b ⊆ cubicRetained) (hsube : Icc a b ⊆ Icc e (π - e)) :
    ∃ C ≥ (0 : ℝ), ∀ M : ℕ, ∃ ee de : ℝ → ℝ,
      (∀ θ ∈ Icc a b,
        ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
              * (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re
            / (2 * ftPrincipalAmp cubicQ witB 1
                (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ)
          = Real.cos (((M : ℝ) + 1) * θ - cubicPsi a θ) + ee θ) ∧
      (∀ θ ∈ Icc a b, |ee θ| ≤ C * cubicTau e ^ M) ∧
      (∀ θ ∈ Icc a b, HasDerivAt ee (de θ) θ) ∧
      (∀ θ ∈ Icc a b, |de θ| ≤ ((M : ℝ) + 1) * C * cubicTau e ^ M) := by
  classical
  have hpi := Real.pi_pos
  have hτe0 : 0 < cubicTau e := cubicTau_pos e
  have hτe1 : cubicTau e < 1 := cubicTau_lt_one ⟨he, by linarith⟩
  have hDlo := cubicDenFloor_pos he (by linarith)
  have harc : ∀ θ ∈ Icc a b, θ ∈ Ioo 0 π := fun θ hθ => (hsubR hθ).1
  have hCI : (0 : ℝ) ≤ cubicTau e * (4 / cubicDenFloor e) := by positivity
  have hQd0 : (0 : ℝ) ≤ 4 / (cubicDenFloor e / 2) ^ 2 := by positivity
  obtain ⟨A, hA, hfloor⟩ :=
    exists_amplitude_floor_on_subarc (Q := cubicQ) (B := witB) (r := 1)
      (z := fun θ' => cubicZ (cubicTau θ') θ') (τ := cubicTau) (a := a) (b := b)
      (fun θ hθ => (continuousAt_cubicAmp (hsubR hθ)).continuousWithinAt)
      (fun θ hθ => cubicAmp_ne_zero (hsubR hθ))
  obtain ⟨Wd, hWd0, hWd⟩ := exists_sup_on (f := fun s => ‖cubicAmpLogDeriv s * cubicAmp s‖)
    (a := a) (b := b) (fun θ hθ =>
      ((continuousAt_cubicAmpLogDeriv (hsubR hθ)).mul
        (continuousAt_cubicAmp (hsubR hθ))).norm.continuousWithinAt)
  obtain ⟨Zs, hZs0, hZs⟩ := exists_sup_on (f := cubicZbranchDeriv) (a := a) (b := b)
    (fun θ hθ => (continuousAt_cubicZbranchDeriv (harc θ hθ)).continuousWithinAt)
  obtain ⟨Ts, hTs0, hTs⟩ := exists_sup_on (f := cubicTauDeriv) (a := a) (b := b)
    (fun θ hθ => ContinuousAt.continuousWithinAt
      (continuousAt_cubicTauDeriv ⟨(harc θ hθ).1.le, (harc θ hθ).2.le⟩))
  set Cst : ℝ := max (cubicTau e * (4 / cubicDenFloor e) / (2 * A))
      ((2 * (cubicTau e * (4 / cubicDenFloor e)) * Ts
          + cubicTau e * Zs * (4 / (cubicDenFloor e / 2) ^ 2)) / (2 * A)
        + cubicTau e * (4 / cubicDenFloor e) * (2 * Wd) / (4 * A ^ 2)) with hCst
  have hC1 : cubicTau e * (4 / cubicDenFloor e) / (2 * A) ≤ Cst := by
    rw [hCst]; exact le_max_left _ _
  have hC2 : (2 * (cubicTau e * (4 / cubicDenFloor e)) * Ts
        + cubicTau e * Zs * (4 / (cubicDenFloor e / 2) ^ 2)) / (2 * A)
      + cubicTau e * (4 / cubicDenFloor e) * (2 * Wd) / (4 * A ^ 2) ≤ Cst := by
    rw [hCst]; exact le_max_right _ _
  have hCst0 : (0 : ℝ) ≤ Cst := le_trans (by positivity) hC1
  refine ⟨Cst, hCst0, fun M => ?_⟩
  have hkey : ∀ θ ∈ Icc a b, ∃ v : ℝ,
      HasDerivAt (fun s => ((((cubicTau s : ℝ) : ℂ)) ^ (M + 1)
          * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau s) s : ℝ) : ℂ)).re
        / (2 * ‖cubicAmp s‖)) v θ ∧
      |v| ≤ ((M : ℝ) + 1) * Cst * cubicTau e ^ M := by
    intro θ hθ
    have hτ0 : 0 < cubicTau θ := cubicTau_pos θ
    have hAle : A ≤ ‖cubicAmp θ‖ := by
      have h := hfloor θ hθ; rwa [ftPrincipalAmp_cubic_eq] at h
    have hWpos : 0 < ‖cubicAmp θ‖ := lt_of_lt_of_le hA hAle
    have h2W : (0 : ℝ) < 2 * ‖cubicAmp θ‖ := by linarith
    have hA2 : 2 * A ≤ 2 * ‖cubicAmp θ‖ := by linarith
    have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      have h : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    have hσn : (0 : ℝ) ≤ cubicTau e ^ M := by positivity
    have hτle : cubicTau θ ≤ cubicTau e := cubicTau_le_of_mem he he2 (hsube hθ)
    have hhalf : 1 / 2 ≤ cubicTau θ :=
      half_le_cubicTau ⟨(harc θ hθ).1.le, (harc θ hθ).2.le⟩
    -- the `C⁰` bound on the contour value
    have hb := cubic_interior_remainder_norm he he2 (harc θ hθ) (hsube hθ) M
    have hre := abs_re_scaled_ftContourRem_le he he2 (harc θ hθ) (hsube hθ) M
    -- the contour derivative
    have hCB : ∀ t ∈ Metric.sphere (0 : ℂ) 1, ‖witB.eval t‖ ≤ 4 :=
      fun t ht => norm_witB_eval_le (by simpa using Metric.mem_sphere.1 ht)
    have hDb := cubic_den_floor_nbhd he he2 (hsube hθ)
    have hCRd : ‖ftContourRemDeriv cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖
        ≤ 4 / (cubicDenFloor e / 2) ^ 2 := by
      refine le_trans (norm_ftContourRemDeriv_le one_pos
        (by linarith : (0:ℝ) < cubicDenFloor e / 2) hCB
        (hDb (cubicZ (cubicTau θ) θ) (by simp; linarith))) (le_of_eq ?_)
      rw [one_pow, one_pow, mul_one]
      norm_num
    have hCR := hasDerivAt_ftContourRem_comp (Q := cubicQ) (B := witB) (r := 1) (M := M)
      (R := 1) (CB := 4) (m := cubicDenFloor e / 2) (ε := cubicDenFloor e / 2)
      (z := fun s => cubicZ (cubicTau s) s) one_pos (by positivity) (by positivity)
      hCB hDb (hasDerivAt_cubicZbranch (harc θ hθ))
    have hpow := ((hasDerivAt_cubicTau (harc θ hθ)).ofReal_comp).pow (M + 1)
    have hD : HasDerivAt (fun s => 2 * ‖cubicAmp s‖) (2 * cubicAmpNormDeriv θ) θ :=
      (hasDerivAt_cubicAmpNorm (hsubR hθ)).const_mul 2
    refine ⟨_, (hpow.mul hCR).re.div hD h2W.ne', ?_⟩
    -- the numerator's value bound, in the scaled shape
    have hNs : |((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
        * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re|
        ≤ ((M : ℝ) + 1) * cubicTau e ^ M * (cubicTau e * (4 / cubicDenFloor e)) := by
      refine le_trans hre ?_
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hM1) hσn) hCI]
    -- the numerator's derivative bound: `(M+1)` from the prefactor alone
    have hN's : |(((M + 1 : ℕ) : ℂ) * ((cubicTau θ : ℝ) : ℂ) ^ (M + 1 - 1)
          * ((cubicTauDeriv θ : ℝ) : ℂ)
          * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
        + ((cubicTau θ : ℝ) : ℂ) ^ (M + 1)
          * (cubicZbranchDeriv θ • ftContourRemDeriv cubicQ witB 1 1 M
              ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).re|
        ≤ ((M : ℝ) + 1) * cubicTau e ^ M
            * (2 * (cubicTau e * (4 / cubicDenFloor e)) * Ts
              + cubicTau e * Zs * (4 / (cubicDenFloor e / 2) ^ 2)) := by
      refine le_trans (Complex.abs_re_le_norm _) (le_trans (norm_add_le _ _) ?_)
      rw [Nat.add_sub_cancel, norm_cast_pow_real_mul hτ0, norm_pow_real_mul_smul hτ0]
      have hpm : cubicTau θ ^ M * ‖ftContourRem cubicQ witB 1 1 M
          ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖
          ≤ 2 * (cubicTau e * (4 / cubicDenFloor e) * cubicTau e ^ M) :=
        pow_mul_le_two_of_half hhalf (norm_nonneg _) hb
      have hτp : cubicTau θ ^ (M + 1) ≤ cubicTau e * cubicTau e ^ M := by
        rw [← pow_succ']
        exact pow_le_pow_left₀ hτ0.le hτle (M + 1)
      have hmm : |cubicZbranchDeriv θ| * ‖ftContourRemDeriv cubicQ witB 1 1 M
          ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖
          ≤ Zs * (4 / (cubicDenFloor e / 2) ^ 2) :=
        mul_le_mul (hZs θ hθ) hCRd (norm_nonneg _) hZs0
      have ht1 : ((M + 1 : ℕ) : ℝ) * cubicTau θ ^ M * |cubicTauDeriv θ|
            * ‖ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖
          ≤ ((M : ℝ) + 1) * cubicTau e ^ M
              * (2 * (cubicTau e * (4 / cubicDenFloor e)) * Ts) := by
        have hnn : (0 : ℝ) ≤ cubicTau θ ^ M * ‖ftContourRem cubicQ witB 1 1 M
            ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖ := by positivity
        have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        calc ((M : ℝ) + 1) * cubicTau θ ^ M * |cubicTauDeriv θ|
              * ‖ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖
            = ((M : ℝ) + 1) * ((cubicTau θ ^ M
                * ‖ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖)
                  * |cubicTauDeriv θ|) := by ring
          _ ≤ ((M : ℝ) + 1) * ((2 * (cubicTau e * (4 / cubicDenFloor e)
                * cubicTau e ^ M)) * Ts) := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              exact mul_le_mul hpm (hTs θ hθ) (abs_nonneg _) (by positivity)
          _ = ((M : ℝ) + 1) * cubicTau e ^ M
                * (2 * (cubicTau e * (4 / cubicDenFloor e)) * Ts) := by ring
      have ht2 : cubicTau θ ^ (M + 1) * (|cubicZbranchDeriv θ|
            * ‖ftContourRemDeriv cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖)
          ≤ cubicTau e ^ M * (cubicTau e * Zs * (4 / (cubicDenFloor e / 2) ^ 2)) := by
        have hmm0 : (0 : ℝ) ≤ |cubicZbranchDeriv θ| * ‖ftContourRemDeriv cubicQ witB 1 1 M
            ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)‖ := by positivity
        nlinarith [mul_le_mul hτp hmm hmm0 (by positivity : (0:ℝ) ≤ cubicTau e * cubicTau e ^ M)]
      exact add_le_scaled hM1 hσn (by positivity) ht1 ht2
    have hDb' : |2 * cubicAmpNormDeriv θ| ≤ 2 * Wd := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have h1 := abs_cubicAmpNormDeriv_le (hsubR hθ)
      have h2 := hWd θ hθ
      rw [abs_of_nonneg (norm_nonneg _)] at h2
      linarith
    refine le_trans (abs_div_deriv_le_of_scaled (A := A) (bD' := 2 * Wd) hA hA2
      (by positivity) hNs hN's hDb') ?_
    have hprod : ((M : ℝ) + 1) * cubicTau e ^ M
        * ((2 * (cubicTau e * (4 / cubicDenFloor e)) * Ts
              + cubicTau e * Zs * (4 / (cubicDenFloor e / 2) ^ 2)) / (2 * A)
            + cubicTau e * (4 / cubicDenFloor e) * (2 * Wd) / (4 * A ^ 2))
        ≤ ((M : ℝ) + 1) * cubicTau e ^ M * Cst :=
      mul_le_mul_of_nonneg_left hC2 (by positivity)
    linarith [hprod]
  refine ⟨fun s => ((((cubicTau s : ℝ) : ℂ)) ^ (M + 1)
      * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau s) s : ℝ) : ℂ)).re
      / (2 * ‖cubicAmp s‖),
    deriv (fun s => ((((cubicTau s : ℝ) : ℂ)) ^ (M + 1)
      * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau s) s : ℝ) : ℂ)).re
      / (2 * ‖cubicAmp s‖)), ?_, ?_, ?_, ?_⟩
  · -- the decomposition: the numerator is the contour remainder, by `hcontour`
    intro θ hθ
    have hWpos : 0 < ‖cubicAmp θ‖ := norm_pos_iff.2 (cubicAmp_ne_zero (hsubR hθ))
    have h2W : (0 : ℝ) < 2 * ‖cubicAmp θ‖ := by linarith
    have hpa : ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ
        = ‖cubicAmp θ‖ := ftPrincipalAmp_cubic_eq θ
    have hpolar : ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
        (ftPrincipal cubicTau θ)
        = ((ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ')
            cubicTau θ : ℝ) : ℂ) * Complex.exp ((cubicPsi a θ : ℂ) * Complex.I) := by
      rw [hpa]; exact cubicAmp_eq_polar hab hsubR hθ
    have hcos := principal_term_cos (M := M)
      (z := fun θ' => cubicZ (cubicTau θ') θ') (cubicTau_pos θ) hpolar
    obtain ⟨hr, hs, hsm, hne, hpair⟩ := cubic_pole_data (harc θ hθ)
    have hcontour := ftCoeff_re_sub_principal_eq_contour_re (Q := cubicQ) (B := witB)
      hasRealCoeffs_cubicQ hasRealCoeffs_witB le_rfl (by simp [cubicQ])
      (z := fun θ' => cubicZ (cubicTau θ') θ') (τ := cubicTau)
      (cubicTau_pos θ) one_pos (cubicTau_lt_one (harc θ hθ)) hr hs hsm hne hpair M
    rw [hpa] at hcos
    have hne2 : (2 : ℝ) * ‖cubicAmp θ‖ ≠ 0 := h2W.ne'
    have key : ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
          * (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re
        = 2 * ‖cubicAmp θ‖ * Real.cos (((M : ℝ) + 1) * θ - cubicPsi a θ)
          + ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
              * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re := by
      linarith [hcontour, hcos]
    dsimp only
    rw [hpa, key, add_div, mul_div_cancel_left₀ _ hne2]
  · -- the value bound
    intro θ hθ
    have hAle : A ≤ ‖cubicAmp θ‖ := by
      have := hfloor θ hθ; rwa [ftPrincipalAmp_cubic_eq] at this
    have hWpos : 0 < ‖cubicAmp θ‖ := lt_of_lt_of_le hA hAle
    have h2W : (0 : ℝ) < 2 * ‖cubicAmp θ‖ := by linarith
    have hnum := abs_re_scaled_ftContourRem_le he he2 (harc θ hθ) (hsube hθ) M
    have hC1' : cubicTau e * (4 / cubicDenFloor e) ≤ Cst * (2 * A) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * A)] at hC1; exact hC1
    have hσn : (0:ℝ) ≤ cubicTau e ^ M := by positivity
    dsimp only
    rw [abs_div, abs_of_pos h2W, div_le_iff₀ h2W]
    calc |((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
            * ftContourRem cubicQ witB 1 1 M ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re|
        ≤ cubicTau e * (4 / cubicDenFloor e) * cubicTau e ^ M := hnum
      _ ≤ Cst * (2 * A) * cubicTau e ^ M := by nlinarith [hC1', hσn]
      _ = Cst * cubicTau e ^ M * (2 * A) := by ring
      _ ≤ Cst * cubicTau e ^ M * (2 * ‖cubicAmp θ‖) := by
          refine mul_le_mul_of_nonneg_left (by linarith) ?_
          exact mul_nonneg hCst0 hσn
  · -- the derivative exists
    intro θ hθ
    obtain ⟨v, hv, -⟩ := hkey θ hθ
    exact hv.deriv ▸ hv
  · -- and is bounded by `(M+1)Cσ^M`
    intro θ hθ
    obtain ⟨v, hv, hb⟩ := hkey θ hθ
    rw [hv.deriv]
    exact hb

/-! ### `prop:local-strong-clock` at the cubic pencil, with only the `C^1` input left -/

/-- **`eq:local-strong-clock` at the cubic pencil, `C^0` side closed.**  Every
binder of `cubic_local_strong_clock` except the *derivative* of the remainder is
discharged: the decomposition `hdec` and both value bounds `heb`, `hCeb` come
from `cubic_interior_cos_error`, and the threshold in `M` is where the
exponentially small error drops below `sin δ`.

What is still assumed is `eq:C1-interior-remainder` alone — that the error
function this theorem hands back is differentiable with a derivative bounded by
`Ce`, at a `Ce` under `(√2/2)(M - 1/2)`.  The error is produced here, so the
hypothesis is about a named object rather than about an unspecified one, and
`Consequences.exists_c1_interior_remainder_bound` is the shape that would
discharge it.

**Containment.**  The conclusion relates the coefficient polynomial to two of its
zero angles; no hypothesis of this theorem mentions the zero set at all, and the
inner implication's three hypotheses constrain only `ee` and its derivative. -/
theorem cubic_local_strong_clock_of_C1 {e a b δ : ℝ}
    (he : 0 < e) (he2 : e < π / 2)
    (hab : a ≤ b) (hsubR : Icc a b ⊆ cubicRetained) (hsube : Icc a b ⊆ Icc e (π - e))
    (hδ : 0 < δ) (hδ4 : δ ≤ π / 4) :
    ∃ C ≥ (0 : ℝ), ∃ κ₂ ≥ (0 : ℝ), ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∃ ee : ℝ → ℝ,
        (∀ θ ∈ Icc a b,
          ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
                * (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re
              / (2 * ftPrincipalAmp cubicQ witB 1
                  (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ)
            = Real.cos (((M : ℝ) + 1) * θ - cubicPsi a θ) + ee θ) ∧
        (∀ θ ∈ Icc a b, |ee θ| ≤ C * σ ^ M) ∧
        ∀ (de : ℝ → ℝ) (Ce : ℝ),
          (∀ θ ∈ Icc a b, HasDerivAt ee (de θ) θ) →
          (∀ θ ∈ Icc a b, |de θ| ≤ Ce) →
          Ce < Real.sqrt 2 / 2 * ((M : ℝ) - 1 / 2) →
          ∀ u₀ : ℝ, Real.cos u₀ = 0 →
          ((M : ℝ) + 1) * a - cubicPsi a a ≤ u₀ - δ →
          u₀ + π + δ ≤ ((M : ℝ) + 1) * b - cubicPsi a b →
          ∃ θk ∈ Icc a b, ∃ θk1 ∈ Icc a b, θk < θk1 ∧
            (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θk) θk : ℝ) : ℂ) = 0 ∧
            (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θk1) θk1 : ℝ) : ℂ) = 0 ∧
            θk1 - θk ≤ (π + 2 * (π / 2 * (C * σ ^ M))) / (((M : ℝ) + 1) - 3 / 2) ∧
              |(θk1 - θk) - π / ((M : ℝ) + 1)
                  - π * (cubicAmpLogDeriv θk * cubicAmp θk / cubicAmp θk).im
                      / ((M : ℝ) + 1) ^ 2|
                ≤ (2 * (π / 2 * (C * σ ^ M))
                      + κ₂ * ((π + 2 * (π / 2 * (C * σ ^ M)))
                          / (((M : ℝ) + 1) - 3 / 2)) ^ 2)
                    / (((M : ℝ) + 1) - 3 / 2)
                  + π * (3 / 2) ^ 2
                      / (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) - 3 / 2)) := by
  obtain ⟨C, hC, σ, hσ0, hσ1, hdecomp⟩ := cubic_interior_cos_error he he2 hab hsubR hsube
  obtain ⟨κ₂, hκ₂0, htay⟩ := exists_cubic_taylor_bound hsubR
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have htend : Filter.Tendsto (fun M : ℕ => C * σ ^ M) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hσ0.le hσ1).const_mul C
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.1 (htend.eventually_lt_const hsin)
  refine ⟨C, hC, κ₂, hκ₂0, σ, hσ0, hσ1, max M₁ 2, fun M hM => ?_⟩
  have hMe : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨ee, hdec, hbd⟩ := hdecomp M
  refine ⟨ee, hdec, hbd, fun de Ce hed hdeb hCe u₀ hcos hlo hhi => ?_⟩
  exact cubic_local_strong_clock hM2 hκ₂0 htay hab hsubR hcos hδ hδ4 hlo hhi hdec
    (fun θ hθ => lt_of_le_of_lt (hbd θ hθ) (hM₁ M hMe))
    (by positivity) hbd hed hdeb hCe


/-- **`prop:local-strong-clock` at the cubic pencil, with nothing assumed.**  Two
consecutive zeros of `F_M` in `z(𝒥)`, ordered, with `eq:local-strong-clock`'s
spacing law between their angles — every binder of `cubic_local_strong_clock`
discharged, the remainder's included.

**Three thresholds in `M`, and which binds was not the obvious one.**  The window
binders need `Φ` to turn by more than `2π + 2δ`; the `C⁰` half needs
`Cσ^M < sin δ`, so the error cannot reach the cosine's own scale; the `C¹` half
needs `(M+1)Cσ^M < (√2/2)(M - 1/2)`, so the error's derivative cannot overcome
the phase's.  The `(M+1)` on the left of the third looks like it must make it the
latest, and **it does not**: its right-hand side grows too, and by the time the
geometric decay has brought `Cσ^M` under `sin δ` that side is some fifty times
`sin δ`, which more than absorbs the factor.  Measured at this pencil on
`[1.75, 2.55]` with `δ = π/4`, the window binds at `M = 10` and the other two
**both** at `M = 54`.  `M₀` here is larger only because the proof takes the
conservative targets `sin δ/2` and `1/2`, which is slack chosen in the proof
rather than mathematics.  `scripts/check_cubic_strong_clock_threshold.py`
measures all three and exhibits a witness above the threshold. -/
theorem cubic_local_strong_clock_closed {e a b δ : ℝ}
    (he : 0 < e) (he2 : e < π / 2)
    (hab : a ≤ b) (hsubR : Icc a b ⊆ cubicRetained) (hsube : Icc a b ⊆ Icc e (π - e))
    (hδ : 0 < δ) (hδ4 : δ ≤ π / 4) :
    ∃ C ≥ (0 : ℝ), ∃ κ₂ ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ u₀ : ℝ, Real.cos u₀ = 0 →
      ((M : ℝ) + 1) * a - cubicPsi a a ≤ u₀ - δ →
      u₀ + π + δ ≤ ((M : ℝ) + 1) * b - cubicPsi a b →
      ∃ θk ∈ Icc a b, ∃ θk1 ∈ Icc a b, θk < θk1 ∧
        (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θk) θk : ℝ) : ℂ) = 0 ∧
        (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θk1) θk1 : ℝ) : ℂ) = 0 ∧
        θk1 - θk ≤ (π + 2 * (π / 2 * (C * cubicTau e ^ M))) / (((M : ℝ) + 1) - 3 / 2) ∧
          |(θk1 - θk) - π / ((M : ℝ) + 1)
              - π * (cubicAmpLogDeriv θk * cubicAmp θk / cubicAmp θk).im
                  / ((M : ℝ) + 1) ^ 2|
            ≤ (2 * (π / 2 * (C * cubicTau e ^ M))
                  + κ₂ * ((π + 2 * (π / 2 * (C * cubicTau e ^ M)))
                      / (((M : ℝ) + 1) - 3 / 2)) ^ 2)
                / (((M : ℝ) + 1) - 3 / 2)
              + π * (3 / 2) ^ 2 / (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) - 3 / 2)) := by
  have hpi := Real.pi_pos
  obtain ⟨C, hC0, hdata⟩ := cubic_interior_cos_error_C1 he he2 hab hsubR hsube
  obtain ⟨κ₂, hκ₂0, htay⟩ := exists_cubic_taylor_bound hsubR
  have hτe0 : 0 < cubicTau e := cubicTau_pos e
  have hτe1 : cubicTau e < 1 := cubicTau_lt_one ⟨he, by linarith⟩
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)
  obtain ⟨M₁, hM₁⟩ :=
    exists_succ_pow_mul_geometric_le hτe0.le hτe1 hC0 (half_pos hsin) 0
  obtain ⟨M₂, hM₂⟩ :=
    exists_succ_pow_mul_geometric_le hτe0.le hτe1 hC0 (by norm_num : (0:ℝ) < 1 / 2) 1
  refine ⟨C, hC0, κ₂, hκ₂0, max (max M₁ M₂) 2, fun M hM u₀ hcos hlo hhi => ?_⟩
  have hMa : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMb : M₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  obtain ⟨ee, de, hdec, hval, hed, hdeb⟩ := hdata M
  refine cubic_local_strong_clock hM2 hκ₂0 htay hab hsubR hcos hδ hδ4 hlo hhi hdec ?_
    (by positivity) hval hed hdeb ?_
  · -- the `C⁰` threshold: the error stays below the cosine's own scale
    intro θ hθ
    have h1 := hM₁ M hMa
    rw [pow_zero, one_mul] at h1
    linarith [hval θ hθ]
  · -- the `C¹` threshold: the error's derivative stays below the phase's
    have h2 := hM₂ M hMb
    rw [pow_one] at h2
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [h2, hsq, hnn, hMR, hC0]

end ForgacsTran
