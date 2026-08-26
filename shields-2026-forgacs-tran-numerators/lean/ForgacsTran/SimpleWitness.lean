/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.QuadraticWitness
import ForgacsTran.SimpleEndpoint

/-!
# A `ρ = 1` pencil carrying an amplitude divisor

`SimpleEndpoint` unblocked the shape of `thm:weighted-dominance` at a simple
smallest zero; this module carries a pencil through it.

The pencil is the Favard one, `Q = 1 - 4t + t^2` with `r = 1`, whose zeros
`2 ± √3` are positive and **distinct**, so `ρ = 1`.  What is new here is the
numerator: `B(t) = t^2 + 1` vanishes at `±i`, and the branch is the unit
semicircle, so `B` vanishes **on the arc** at `θ = π/2`.  That is what makes this
a test of `lem:amplitude-divisor` rather than a way around it -- the way `B = 1`
of `QuadraticWitness` is.

## Why this pencil, and what it settles

`τ ≡ 1` and `D = Q + zt` is quadratic, so the denominator has exactly the
principal pair and nothing else.  Three consequences, each of which the cubic
witness lacks:

* `n₀ = n₁ = 0` -- both endpoint clusters are empty, which is the shape
  `weighted_dominance_of_branch_any_multiplicity` needs at `ρ = 1`;
* both endpoints are collisions of the principal pair at points that are **not
  zeros of `Q`** (`quadDen_eq_sq_lower`, `quadDen_eq_sq_upper` give `D` as an
  exact square), so `k = 2` and `hk₀` is immediate;
* `σ = τ_max/R = 1/R` is **constant in the interior parameter**, because `τ` does
  not tend to `1` from below as the window opens.  So the fixed-window
  obstruction of BANK-37 does not arise here at all, and
  `eq:amplitude-deletion`'s window is exponentially small directly.

## The amplitude

`W(θ) = i cot(θ) e^{iθ}`, so `|W| = |cot θ|`: it vanishes on `(0,π)` exactly at
`θ = π/2` and blows up at both endpoints.  `B = 1` gives `|W| = 1/(2 sin θ)`
instead, with no zero at all.

## The case is covered

`fav_weighted_dominance` is `thm:weighted-dominance` at this pencil with an
**empty binder list**: `eq:dominance-bound` on `eq:retained-range`, off deleted
windows of half-width `2^{-M/2}`.  It is the first pencil in the tree carried
through `weighted_dominance_of_branch_any_multiplicity` at a **simple** smallest
zero, and the first whose deleted family shrinks with `M`.

The five hypotheses `SimpleEndpoint` conditioned on `0 < n₀` -- `hρ`, `hcB₀`,
`hcQ₀`, `hBp₀`, `hEp₀` -- are discharged vacuously here, `n₀` being `0`.  That is
the conditioning earning its keep: `hEp₀` is *false* at `ρ = 1`, and at a simple
smallest zero there is no cluster for it to be about.

## Main statements

* `ftAmp_fav_eq`, `ftPrincipalAmp_fav` — `W = i cot(θ)e^{iθ}`, `|W| = |cot θ|`.
* `ftAmp_favB_eq_zero_iff` — `lem:amplitude-divisor`: the divisor is `{π/2}`.
* `witQ_smallest_zero_simple`, `witQ_eval_one` — `ρ = 1`, and the collision point
  is not a zero of `Q`.
* `ftDen_witQ_factor`, `favRoots_uniq`, `favRoots_erase_card` — the pair is the
  whole denominator, so both endpoint clusters are empty.
* `ftDen_witQ_lower_sq`, `ftDen_witQ_upper_sq` — both endpoints are exact
  squares, so `k = 2`.
* `favTheta`, `favTheta_shrinks` — `eq:amplitude-deletion` at `σ = 1/2`,
  exponentially small in `M`.
* `favWitness_hinterior`, `favCbd`, `ftPrincipalAmp_fav_upper` — the interior
  group, the contour bound, the upper amplitude floor.
* `fav_weighted_dominance` — the composition.

## Tags

simple endpoint, Favard pencil, amplitude divisor, witness
-/

namespace ForgacsTran

open Polynomial Complex

/-! ### The numerator, and the pencil's `ρ` -/

/-- The witness numerator `B(t) = t² + 1`, whose zeros `±i` lie on the unit
circle, which is the branch. -/
noncomputable def favB : Polynomial ℂ := X ^ 2 + 1

@[simp] theorem favB_eval (t : ℂ) : favB.eval t = t ^ 2 + 1 := by
  simp [favB]

theorem favB_ne_zero : favB ≠ 0 := by
  intro h
  have h0 := favB_eval 0
  rw [h] at h0
  simp at h0

theorem hasRealCoeffs_favB : HasRealCoeffs favB := by
  have hmap : favB = ((X ^ 2 + 1 : Polynomial ℝ)).map (algebraMap ℝ ℂ) := by
    rw [favB, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  intro k
  rw [hmap, coeff_map]
  simp

theorem hasRealCoeffs_witQ : HasRealCoeffs witQ := by
  have hmap : witQ
      = ((Polynomial.C (1 : ℝ) + Polynomial.C (-4 : ℝ) * X
          + Polynomial.C (1 : ℝ) * X ^ 2).map (algebraMap ℝ ℂ)) := by
    rw [witQ, quadPoly]
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_pow, Complex.coe_algebraMap]
  intro k
  rw [hmap, coeff_map]
  simp only [Complex.coe_algebraMap, Complex.conj_ofReal]

theorem witQ_eval (t : ℂ) : witQ.eval t = 1 - 4 * t + t ^ 2 := by
  rw [witQ, quadPoly_eval]
  push_cast
  ring

theorem witQ_eval_zero_ne : witQ.eval 0 ≠ 0 := by
  rw [witQ_eval]; norm_num

/-- **`ρ = 1`.**  `Q = 1 - 4t + t²` factors as `(t - (2-√3))(t - (2+√3))` with
two distinct positive zeros, so its smallest zero is simple. -/
theorem witQ_factor (t : ℂ) :
    witQ.eval t = (t - ((2 - Real.sqrt 3 : ℝ) : ℂ)) * (t - ((2 + Real.sqrt 3 : ℝ) : ℂ)) := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  rw [witQ_eval]
  push_cast
  linear_combination h3

theorem witQ_smallest_zero_simple :
    (2 : ℝ) - Real.sqrt 3 < 2 + Real.sqrt 3 ∧ 0 < 2 - Real.sqrt 3 := by
  have h1 : Real.sqrt 3 < 2 := by
    have : Real.sqrt 3 < Real.sqrt 4 := by
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at this
  have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  constructor <;> linarith

/-! ### The branch, and the amplitude in closed form -/

theorem witTau_eq_one (θ : ℝ) : witTau θ = 1 := by
  rw [witTau, quadMod_one]

theorem ftPrincipal_witTau (θ : ℝ) :
    ftPrincipal witTau θ = Complex.exp ((θ : ℂ) * I) := by
  rw [ftPrincipal, witTau_eq_one]
  simp

theorem ftDen_witQ_eval_principal (θ : ℝ) :
    (ftDen witQ 1 ((witZ θ : ℝ) : ℂ)).eval (ftPrincipal witTau θ) = 0 := by
  have h := quadDen_eval_principal (q0 := 1) (q2 := 1) (q1 := -4) one_pos one_pos θ
  have hz : ((witZ θ : ℝ) : ℂ) = (((-(-4 : ℝ) - 2 * Real.sqrt (1 * 1) * Real.cos θ : ℝ)) : ℂ) := by
    rw [witZ, quadZ, quadHalf]
  have hpr : ftPrincipal witTau θ
      = ((Real.sqrt (1 / 1 : ℝ) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    rw [ftPrincipal, witTau, quadMod]
  rw [hz, hpr, witQ]
  exact h

/-- `∂_tD(t,z) = -4 + 2t + z` at this pencil. -/
theorem derivative_ftDen_witQ_eval (z t : ℂ) :
    (derivative (ftDen witQ 1 z)).eval t = -4 + 2 * t + z := by
  rw [ftDen, witQ, quadPoly]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, zero_mul, zero_add, mul_one, pow_one, Nat.cast_ofNat]
  push_cast
  ring

theorem witZ_eq' (θ : ℝ) : witZ θ = 4 - 2 * Real.cos θ := witZ_eq θ

/-- The cofactor along the branch: `∂_tD(γ(θ)) = 2i sin θ`. -/
theorem derivative_ftDen_witQ_principal (θ : ℝ) :
    (derivative (ftDen witQ 1 ((witZ θ : ℝ) : ℂ))).eval (ftPrincipal witTau θ)
      = 2 * I * ((Real.sin θ : ℝ) : ℂ) := by
  rw [derivative_ftDen_witQ_eval, ftPrincipal_witTau, witZ_eq', Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- The numerator along the branch: `B(γ(θ)) = 2cos θ · e^{iθ}`. -/
theorem favB_eval_principal (θ : ℝ) :
    favB.eval (ftPrincipal witTau θ)
      = 2 * ((Real.cos θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) := by
  rw [favB_eval, ftPrincipal_witTau, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  have hpy : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  linear_combination -hpy + ((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.I_sq

/-- **`eq:W-def` at this pencil.**  `W(θ) = i cot(θ) e^{iθ}`. -/
theorem ftAmp_fav_eq {θ : ℝ} (hsin : Real.sin θ ≠ 0) :
    ftAmp witQ favB 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ)
      = ((Real.cos θ / Real.sin θ : ℝ) : ℂ) * I * Complex.exp ((θ : ℂ) * I) := by
  have hsc : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsin
  rw [ftAmp_eq_neg_div_derivative (ftDen_witQ_eval_principal θ),
    derivative_ftDen_witQ_principal, favB_eval_principal]
  rw [Complex.ofReal_div]
  field_simp
  linear_combination (-((Real.cos θ : ℝ) : ℂ)) * Complex.I_sq

/-- **`|W| = |cot θ|`.**  The amplitude's modulus on the arc. -/
theorem ftPrincipalAmp_fav {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftPrincipalAmp witQ favB 1 witZ witTau θ = |Real.cos θ| / Real.sin θ := by
  rw [ftPrincipalAmp, ftAmp_fav_eq hsin.ne', norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_div, abs_of_pos hsin]
  ring

/-- **`lem:amplitude-divisor` at this pencil.**  The amplitude vanishes on the
open arc exactly at `θ = π/2`, so the divisor is a single interior angle -- the
feature `B = 1` has no way to exhibit. -/
theorem ftAmp_favB_eq_zero_iff {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ftAmp witQ favB 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ) = 0
      ↔ θ = Real.pi / 2 := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  constructor
  · intro h
    have hn : ftPrincipalAmp witQ favB 1 witZ witTau θ = 0 := by
      rw [ftPrincipalAmp, h, norm_zero]
    rw [ftPrincipalAmp_fav hsin, div_eq_zero_iff] at hn
    rcases hn with h1 | h1
    · have hc : Real.cos θ = 0 := abs_eq_zero.1 h1
      have hpi := Real.pi_pos
      refine Real.injOn_cos ⟨hθ.1.le, hθ.2.le⟩ ⟨by linarith, by linarith⟩ ?_
      rw [hc, Real.cos_pi_div_two]
    · exact absurd h1 hsin.ne'
  · rintro rfl
    rw [ftAmp_fav_eq (by rw [Real.sin_pi_div_two]; norm_num)]
    rw [Real.cos_pi_div_two]
    simp


/-! ### The denominator is the principal pair and nothing else

`D = Q + zt` is quadratic and monic, and its two roots on the arc are `γ` and
`γ̄`.  So the retained cluster is the principal pair at every angle, both endpoint
clusters are empty, and the separating radius may be any `R > 1` -- in
particular `σ = τ_max/R = 1/R` does **not** move with the interior parameter.
That is the structural difference from the cubic witness, where `τ(e) → 1` as the
window opens and forces the deleted window to a fixed width. -/

theorem conj_ftPrincipal_witTau (θ : ℝ) :
    ((witTau θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I) = Complex.exp (-(θ : ℂ) * I) := by
  rw [witTau_eq_one]; simp

/-- `D(·, z(θ)) = (X - γ)(X - γ̄)`: the pencil is monic and its roots are the pair. -/
theorem ftDen_witQ_factor (θ : ℝ) :
    ftDen witQ 1 ((witZ θ : ℝ) : ℂ)
      = (X - C (ftPrincipal witTau θ)) * (X - C (Complex.exp (-(θ : ℂ) * I))) := by
  refine Polynomial.funext fun t => ?_
  simp only [ftDen_eval, eval_mul, eval_sub, eval_X, eval_C, pow_one]
  rw [witQ_eval, ftPrincipal_witTau, witZ_eq']
  have hEE : Complex.exp ((θ : ℂ) * I) * Complex.exp (-(θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hsum : Complex.exp ((θ : ℂ) * I) + Complex.exp (-(θ : ℂ) * I)
      = 2 * ((Real.cos θ : ℝ) : ℂ) := by
    rw [Complex.exp_mul_I, show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination t * hsum - hEE

/-- Every root of the pencil inside any radius is one of the principal pair. -/
theorem ftDen_witQ_root_eq (θ : ℝ) {t : ℂ}
    (ht : (ftDen witQ 1 ((witZ θ : ℝ) : ℂ)).eval t = 0) :
    t = ftPrincipal witTau θ ∨ t = Complex.exp (-(θ : ℂ) * I) := by
  rw [ftDen_witQ_factor, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C,
    mul_eq_zero, sub_eq_zero, sub_eq_zero] at ht
  exact ht

/-- The cofactor at the conjugate root: `∂_tD(γ̄) = -2i sin θ`. -/
theorem derivative_ftDen_witQ_conj (θ : ℝ) :
    (derivative (ftDen witQ 1 ((witZ θ : ℝ) : ℂ))).eval (Complex.exp (-(θ : ℂ) * I))
      = -(2 * I * ((Real.sin θ : ℝ) : ℂ)) := by
  rw [derivative_ftDen_witQ_eval, witZ_eq',
    show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

theorem ftPrincipal_ne_conj {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ftPrincipal witTau θ ≠ ((witTau θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I) := by
  rw [conj_ftPrincipal_witTau, ftPrincipal_witTau]
  intro h
  have him := congrArg Complex.im h
  rw [Complex.exp_ofReal_mul_I_im,
    show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_im, Real.sin_neg] at him
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  linarith

/-- The branch has a nonvanishing derivative: `τ` is constant, so `γ' = ie^{iθ}`. -/
theorem hasDerivAt_ftPrincipal_witTau (θ : ℝ) :
    HasDerivAt (ftPrincipal witTau) (Complex.exp ((θ : ℂ) * I) * I) θ := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (((t : ℝ) : ℂ) * I))
      (Complex.exp (((θ : ℝ) : ℂ) * I) * I) θ := by
    have : HasDerivAt (fun w : ℂ => Complex.exp (w * I))
        (Complex.exp (((θ : ℝ) : ℂ) * I) * I) (((θ : ℝ) : ℂ)) := by
      simpa using ((hasDerivAt_id (((θ : ℝ) : ℂ))).mul_const I).cexp
    exact this.comp_ofReal
  refine hE.congr_of_eventuallyEq ?_
  filter_upwards with t
  exact ftPrincipal_witTau t

/-! ### The amplitude's divisor has multiplicity one -/

theorem ftPrincipal_witTau_pi_div_two : ftPrincipal witTau (Real.pi / 2) = I := by
  rw [ftPrincipal_witTau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem favB_rootMultiplicity_I : favB.rootMultiplicity I = 1 := by
  have hroot : favB.IsRoot I := by
    rw [Polynomial.IsRoot, favB_eval, Complex.I_sq]; ring
  have hpos : 0 < favB.rootMultiplicity I :=
    (Polynomial.rootMultiplicity_pos favB_ne_zero).2 hroot
  have hnot : ¬ (1 < favB.rootMultiplicity I) := by
    intro h
    have hd := ((Polynomial.one_lt_rootMultiplicity_iff_isRoot favB_ne_zero).1 h).2
    rw [Polynomial.IsRoot, favB, derivative_add, derivative_pow, derivative_X,
      derivative_one] at hd
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, add_zero, mul_one, Nat.cast_ofNat] at hd
    exact Complex.I_ne_zero (by linear_combination hd / 2)
  omega


/-! ### `hinterior`, with a window that actually shrinks

The deleted family is `eq:amplitude-deletion`'s, at `σ = 1/2`: half-width
`e^{-(log 2)M/2}`, exponentially small in `M`.  Nothing here is forced to a fixed
width, because `σ = τ_max/R = 1/2` does not depend on the interior parameter `e`
-- the failure recorded in BANK-37 is a property of pencils whose `τ` climbs to
`1` at the endpoint, not of the theorem. -/

/-- The deleted windows at this witness: `eq:amplitude-deletion` about the single
amplitude zero `π/2`, of half-width `2^{-M/2}`. -/
noncomputable def favTheta : ℕ → Set ℝ :=
  fun M => {θ : ℝ | |θ - Real.pi / 2| < Real.exp (-(Real.log 2 / 2 * M))}

theorem mem_favTheta {M : ℕ} {θ : ℝ} :
    θ ∈ favTheta M ↔ |θ - Real.pi / 2| < Real.exp (-(Real.log 2 / 2 * M)) := Iff.rfl

/-- The window is exponentially small, which is what `subsec:proof` asks of it
and what `cubicTheta` cannot be. -/
theorem favTheta_shrinks : ∀ ε > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ θ ∈ favTheta M, |θ - Real.pi / 2| < ε := by
  intro ε hε
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : ∀ M : ℕ, Real.exp (-(Real.log 2 / 2 * M))
      = Real.exp (-(Real.log 2 / 2)) ^ M := by
    intro M
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hlt1 : Real.exp (-(Real.log 2 / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hpos : 0 < Real.exp (-(Real.log 2 / 2)) := Real.exp_pos _
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt1).eventually_lt_const hε)
  refine ⟨M₀, fun M hM θ hθ => ?_⟩
  rw [mem_favTheta, hpow] at hθ
  exact lt_trans hθ (hM₀ M hM)

theorem favWitness_hinterior :
    ∀ e : ℝ, 0 < e →
      ∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
        0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → 0 < witTau θ) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → witTau θ ≤ τmi) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → witTau θ < Ri) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          (ftDen witQ 1 ((witZ θ : ℝ) : ℂ)).eval (ftPrincipal witTau θ) = 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          (derivative (ftDen witQ 1 ((witZ θ : ℝ) : ℂ))).eval (ftPrincipal witTau θ) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          (derivative (ftDen witQ 1 ((witZ θ : ℝ) : ℂ))).eval
            (((witTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          ftPrincipal witTau θ ≠ ((witTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → ∀ t : ℂ, ‖t‖ ≤ Ri →
          (ftDen witQ 1 ((witZ θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal witTau θ
            ∨ t = ((witTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (↑S ⊆ Set.Icc e (Real.pi - e)) ∧
        (∀ θj ∈ S, ftAmp witQ favB 1 ((witZ θj : ℝ) : ℂ) (ftPrincipal witTau θj) = 0) ∧
        (∀ θ ∈ Set.Icc e (Real.pi - e),
          ftAmp witQ favB 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ) = 0 → θ ∈ S) ∧
        (∀ θ ∈ Set.Icc e (Real.pi - e),
          ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal witTau) γ' θ) ∧
        (∀ θ ∈ Set.Icc e (Real.pi - e), ContinuousAt (fun θ' => ((witZ θ' : ℝ) : ℂ)) θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ favTheta M → ∀ θj ∈ S,
          Real.exp (-((-Real.log σi) / (2 * S.card) * M
            / (favB.rootMultiplicity (ftPrincipal witTau θj)))) ≤ |θ - θj|) := by
  classical
  intro e he
  have hπ := Real.pi_pos
  -- the objects, none of which moves with `e`
  have hIoo : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → θ ∈ Set.Ioo 0 Real.pi :=
    fun θ h1 h2 => ⟨lt_of_lt_of_le he h1, by linarith⟩
  have hsin : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → 0 < Real.sin θ := fun θ h1 h2 =>
    Real.sin_pos_of_pos_of_lt_pi (hIoo θ h1 h2).1 (hIoo θ h1 h2).2
  have hdp : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
      (derivative (ftDen witQ 1 ((witZ θ : ℝ) : ℂ))).eval (ftPrincipal witTau θ) ≠ 0 := by
    intro θ h1 h2
    rw [derivative_ftDen_witQ_principal]
    have hs : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (hsin θ h1 h2).ne'
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hs
  have hdc : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
      (derivative (ftDen witQ 1 ((witZ θ : ℝ) : ℂ))).eval
        (((witTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0 := by
    intro θ h1 h2
    rw [conj_ftPrincipal_witTau, derivative_ftDen_witQ_conj]
    have hs : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (hsin θ h1 h2).ne'
    exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hs)
  have huniq : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → ∀ t : ℂ, ‖t‖ ≤ 2 →
      (ftDen witQ 1 ((witZ θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal witTau θ
        ∨ t = ((witTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I) := by
    intro θ _ _ t _ ht
    rw [conj_ftPrincipal_witTau]
    exact ftDen_witQ_root_eq θ ht
  have hderiv : ∀ θ ∈ Set.Icc e (Real.pi - e),
      ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal witTau) γ' θ := by
    intro θ _
    exact ⟨Complex.exp ((θ : ℂ) * I) * I,
      mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero,
      hasDerivAt_ftPrincipal_witTau θ⟩
  have hzc : ∀ θ ∈ Set.Icc e (Real.pi - e),
      ContinuousAt (fun θ' => ((witZ θ' : ℝ) : ℂ)) θ := by
    intro θ _
    have hr : Continuous witZ := by
      have h : Continuous fun θ' : ℝ => (4 : ℝ) - 2 * Real.cos θ' := by fun_prop
      exact h.congr fun x => (witZ_eq' x).symm
    exact (Complex.continuous_ofReal.comp hr).continuousAt
  rcases le_or_gt e (Real.pi / 2) with hle | hgt
  · -- the window meets `π/2`, and the divisor is `{π/2}`
    have hhalf : Real.pi / 2 ∈ Set.Icc e (Real.pi - e) := ⟨hle, by linarith⟩
    refine ⟨2, 1, 1 / 2, {Real.pi / 2}, by norm_num, by norm_num, by norm_num, by norm_num,
      fun θ _ _ => by rw [witTau_eq_one]; norm_num,
      fun θ _ _ => by rw [witTau_eq_one],
      fun θ _ _ => by rw [witTau_eq_one]; norm_num,
      fun θ _ _ => ftDen_witQ_eval_principal θ, hdp, hdc,
      fun θ h1 h2 => ftPrincipal_ne_conj (hIoo θ h1 h2), huniq, ?_, ?_, ?_, hderiv, hzc, ?_⟩
    · simpa using hhalf
    · intro θj hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact (ftAmp_favB_eq_zero_iff ⟨by linarith, by linarith⟩).2 rfl
    · intro θ hθ hz0
      rw [Finset.mem_singleton]
      exact (ftAmp_favB_eq_zero_iff (hIoo θ hθ.1 hθ.2)).1 hz0
    · intro M θ hθ θj hj
      rw [Finset.mem_singleton] at hj
      subst hj
      rw [ftPrincipal_witTau_pi_div_two, favB_rootMultiplicity_I]
      rw [mem_favTheta, not_lt] at hθ
      refine le_trans (le_of_eq ?_) hθ
      congr 1
      rw [Finset.card_singleton]
      have h2 : -Real.log (1 / 2 : ℝ) = Real.log 2 := by
        rw [one_div, Real.log_inv, neg_neg]
      rw [h2]
      push_cast
      ring
  · -- the window misses `π/2`: the interval is empty and the divisor with it
    have hempty : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → False := by
      intro θ h1 h2; linarith
    refine ⟨2, 1, 1 / 2, ∅, by norm_num, by norm_num, by norm_num, by norm_num,
      fun θ h1 h2 => absurd (hempty θ h1 h2) not_false,
      fun θ h1 h2 => absurd (hempty θ h1 h2) not_false,
      fun θ h1 h2 => absurd (hempty θ h1 h2) not_false,
      fun θ _ _ => ftDen_witQ_eval_principal θ, hdp, hdc,
      fun θ h1 h2 => ftPrincipal_ne_conj (hIoo θ h1 h2), huniq, by simp, by simp,
      ?_, hderiv, hzc, by simp⟩
    intro θ hθ _
    exact absurd (hempty θ hθ.1 hθ.2) not_false


/-! ### The two endpoints are collisions away from the zeros of `Q`

This is the `ρ = 1` signature.  At both ends the pencil is an exact square, so
the principal pair collides and `lem:amplitude-divisor`'s `k = max{ρ,2}` is `2`;
and the collision point is **not** a zero of `Q`, so no cluster at a multiple
zero is involved and `SimpleEndpoint`'s exponent mismatch is exactly what would
have been asked for. -/

theorem witZ_zero : witZ 0 = 2 := by
  rw [witZ_eq', Real.cos_zero]; norm_num

theorem witZ_pi : witZ Real.pi = 6 := by
  rw [witZ_eq', Real.cos_pi]; norm_num

/-- **The lower endpoint is a double collision**: `D(·, z(0)) = (t-1)²`. -/
theorem ftDen_witQ_lower_sq :
    ftDen witQ 1 ((witZ 0 : ℝ) : ℂ) = C (1 : ℂ) * (X - C (1 : ℂ)) ^ 2 := by
  have h := quadDen_eq_sq_lower (q0 := 1) (q2 := 1) (q1 := -4) one_pos one_pos
  rw [witZ_zero, witQ]
  norm_num at h ⊢
  simpa using h

/-- **The upper endpoint is a double collision**: `D(·, z(π)) = (t+1)²`. -/
theorem ftDen_witQ_upper_sq :
    ftDen witQ 1 ((witZ Real.pi : ℝ) : ℂ) = C (1 : ℂ) * (X + C (1 : ℂ)) ^ 2 := by
  have h := quadDen_eq_sq_upper (q0 := 1) (q2 := 1) (q1 := -4) one_pos one_pos
  rw [witZ_pi, witQ]
  norm_num at h ⊢
  simpa using h

/-- **The collision point is not a zero of `Q`.**  `Q(1) = -2`.  At `ρ ≥ 2` the
lower endpoint sits at the multiple zero itself; here it does not, which is why
the cluster expansion about `x₁` cannot describe it. -/
theorem witQ_eval_one : witQ.eval 1 = -2 := by
  rw [witQ_eval]; norm_num

theorem witQ_eval_neg_one : witQ.eval (-1) = 6 := by
  rw [witQ_eval]; norm_num

/-- `hk₀`: the limiting principal root is a root of the endpoint pencil. -/
theorem rootMultiplicity_lower_pos :
    1 ≤ (ftDen witQ 1 ((witZ 0 : ℝ) : ℂ)).rootMultiplicity 1 := by
  have hne : ftDen witQ 1 ((witZ 0 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have h0 : (ftDen witQ 1 ((witZ 0 : ℝ) : ℂ)).eval 0 = 1 := by
      rw [ftDen_eval, witQ_eval]; norm_num
    rw [h] at h0
    simp at h0
  refine (Polynomial.rootMultiplicity_pos hne).2 ?_
  rw [Polynomial.IsRoot, ftDen_lower_eval_one]
where
  ftDen_lower_eval_one : (ftDen witQ 1 ((witZ 0 : ℝ) : ℂ)).eval 1 = 0 := by
    rw [ftDen_eval, witQ_eval, witZ_zero]; norm_num

/-! ### The amplitude floor at the upper endpoint

`|W| = |cot θ|` blows up at both ends, so the floor `A₁η^{p₁}` holds with
`p₁ = 0`: `cot η ≥ 1` on `(0, π/4]`. -/

theorem one_le_cot {η : ℝ} (hη : 0 < η) (hle : η ≤ Real.pi / 4) :
    Real.sin η ≤ Real.cos η := by
  have hpi := Real.pi_pos
  have h1 : Real.sin η ≤ Real.sin (Real.pi / 4) := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h]
    · exact (Real.strictMonoOn_sin ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ h).le
  have h2 : Real.cos (Real.pi / 4) ≤ Real.cos η := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h]
    · exact (Real.strictAntiOn_cos ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ h).le
  rw [Real.sin_pi_div_four] at h1
  rw [Real.cos_pi_div_four] at h2
  linarith

/-- **`hamp₁`.**  The amplitude floor at the upper endpoint, with `p₁ = 0` and
`A₁ = 1`: the amplitude does not vanish there, it diverges. -/
theorem ftPrincipalAmp_fav_upper {η : ℝ} (hη : 0 < η) (hle : η ≤ Real.pi / 4) :
    (1 : ℝ) * η ^ (0 : ℕ) ≤ ftPrincipalAmp witQ favB 1 witZ witTau (Real.pi - η) := by
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi - η) := by
    rw [Real.sin_pi_sub]
    exact Real.sin_pos_of_pos_of_lt_pi hη (by linarith)
  rw [ftPrincipalAmp_fav hsin, Real.sin_pi_sub, Real.cos_pi_sub, abs_neg,
    abs_of_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)]
  rw [pow_zero, one_mul, le_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi hη (by linarith))]
  linarith [one_le_cot hη hle]


/-! ### The retained cluster: the pair, and nothing to separate it from

`D` is quadratic, so `sfun δ = {e^{iδ}, e^{-iδ}}` is the whole root set at every
angle.  Both endpoint clusters are therefore empty (`n₀ = n₁ = 0`), and the
`Fin 0` groups of `weighted_dominance_of_branch_any_multiplicity` are discharged
by `Fin.elim0`. -/

/-- The root set of the pencil at angle `δ`. -/
noncomputable def favRoots (δ : ℝ) : Finset ℂ :=
  {Complex.exp ((δ : ℂ) * I), Complex.exp (-(δ : ℂ) * I)}

theorem mem_favRoots_iff {δ : ℝ} {t : ℂ} :
    t ∈ favRoots δ ↔ t = Complex.exp ((δ : ℂ) * I) ∨ t = Complex.exp (-(δ : ℂ) * I) := by
  simp [favRoots]

theorem favRoots_root {δ : ℝ} {a : ℂ} (ha : a ∈ favRoots δ) :
    (ftDen witQ 1 ((witZ δ : ℝ) : ℂ)).eval a = 0 := by
  rw [ftDen_witQ_factor, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C]
  rcases mem_favRoots_iff.1 ha with rfl | rfl
  · rw [ftPrincipal_witTau]; ring
  · rw [sub_self]; ring

theorem favRoots_simple {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 Real.pi) {a : ℂ}
    (ha : a ∈ favRoots δ) :
    (derivative (ftDen witQ 1 ((witZ δ : ℝ) : ℂ))).eval a ≠ 0 := by
  have hs : ((Real.sin δ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hδ.1 hδ.2).ne'
  have hne : (2 : ℂ) * I * ((Real.sin δ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hs
  rcases mem_favRoots_iff.1 ha with rfl | rfl
  · rw [← ftPrincipal_witTau, derivative_ftDen_witQ_principal]; exact hne
  · rw [derivative_ftDen_witQ_conj]; exact neg_ne_zero.2 hne

theorem favRoots_ne_zero {δ : ℝ} {a : ℂ} (ha : a ∈ favRoots δ) : a ≠ 0 := by
  rcases mem_favRoots_iff.1 ha with rfl | rfl <;> exact Complex.exp_ne_zero _

theorem favRoots_norm {δ : ℝ} {a : ℂ} (ha : a ∈ favRoots δ) : ‖a‖ = 1 := by
  rcases mem_favRoots_iff.1 ha with rfl | rfl
  · exact Complex.norm_exp_ofReal_mul_I δ
  · rw [show -(δ : ℂ) * I = ((-δ : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-δ)

theorem favRoots_norm_lt {δ : ℝ} {a : ℂ} (ha : a ∈ favRoots δ) : ‖a‖ < 2 := by
  rw [favRoots_norm ha]; norm_num

theorem favRoots_uniq {δ : ℝ} {t : ℂ}
    (ht : (ftDen witQ 1 ((witZ δ : ℝ) : ℂ)).eval t = 0) : t ∈ favRoots δ := by
  rw [mem_favRoots_iff]
  rcases ftDen_witQ_root_eq δ ht with h | h
  · exact Or.inl (by rw [h, ftPrincipal_witTau])
  · exact Or.inr h

/-- The twice-erased root set is empty: the cluster is the principal pair. -/
theorem favRoots_erase_card (δ : ℝ) :
    (((favRoots δ).erase (ftPrincipal witTau δ)).erase
      (((witTau δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hx1 := Finset.mem_of_mem_erase hx
  have hne2 := Finset.ne_of_mem_erase hx
  have hne1 := Finset.ne_of_mem_erase hx1
  rcases mem_favRoots_iff.1 (Finset.mem_of_mem_erase hx1) with rfl | rfl
  · exact hne1 (ftPrincipal_witTau δ).symm
  · exact hne2 (conj_ftPrincipal_witTau δ).symm

/-! ### The contour bound

On `‖t‖ = 2` the two roots are at distance at least `1`, so `‖D‖ ≥ 1`, while
`‖B‖ = ‖t²+1‖ ≤ 5`.  Measured maximum of `‖B/D‖` on that circle:
`4.9994` (`scripts/check_simple_witness.py`). -/

theorem favCbd {δ : ℝ} {t : ℂ} (ht : t ∈ Metric.sphere (0 : ℂ) 2) :
    ‖favB.eval t / (ftDen witQ 1 ((witZ δ : ℝ) : ℂ)).eval t‖ ≤ 5 := by
  have hnt : ‖t‖ = 2 := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
  have hden : (1 : ℝ) ≤ ‖(ftDen witQ 1 ((witZ δ : ℝ) : ℂ)).eval t‖ := by
    rw [ftDen_witQ_factor, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C, norm_mul]
    have h1 : (1 : ℝ) ≤ ‖t - ftPrincipal witTau δ‖ := by
      rw [ftPrincipal_witTau]
      have h := norm_sub_norm_le t (Complex.exp ((δ : ℂ) * I))
      rw [hnt, Complex.norm_exp_ofReal_mul_I] at h
      linarith
    have h2 : (1 : ℝ) ≤ ‖t - Complex.exp (-(δ : ℂ) * I)‖ := by
      rw [show -(δ : ℂ) * I = ((-δ : ℝ) : ℂ) * I by push_cast; ring]
      have h := norm_sub_norm_le t (Complex.exp (((-δ : ℝ) : ℂ) * I))
      rw [hnt, Complex.norm_exp_ofReal_mul_I] at h
      linarith
    nlinarith [norm_nonneg (t - ftPrincipal witTau δ),
      norm_nonneg (t - Complex.exp (-(δ : ℂ) * I))]
  have hnum : ‖favB.eval t‖ ≤ 5 := by
    rw [favB_eval]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_pow, hnt, norm_one]
    norm_num
  rw [norm_div]
  rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖(ftDen witQ 1 ((witZ δ : ℝ) : ℂ)).eval t‖)]
  nlinarith [hnum, hden]


/-! ### The composition

Every binder of `weighted_dominance_of_branch_any_multiplicity` at this pencil.
The lower-cluster group is empty (`n₀ = 0`), so `hρ`, `hcB₀`, `hcQ₀`, `hBp₀` and
`hEp₀` -- the five `SimpleEndpoint` conditioned on `0 < n₀`, one of which is
false at `ρ = 1` -- are discharged vacuously.  That is the whole point of the
conditioning: at a simple smallest zero the cluster does not exist, so the
hypotheses about its principal index have nothing to say. -/

theorem fav_hrootev : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    (ftDen witQ 1 ((witZ δ : ℝ) : ℂ)).eval (ftPrincipal witTau δ) = 0 :=
  Filter.Eventually.of_forall ftDen_witQ_eval_principal

theorem fav_hγ0 : ftPrincipal witTau 0 = 1 := by
  rw [ftPrincipal_witTau]
  simp

theorem fav_hγd : HasDerivWithinAt (fun δ => ftPrincipal witTau δ) I (Set.Ici (0 : ℝ)) 0 := by
  have h := hasDerivAt_ftPrincipal_witTau 0
  rw [show ((0 : ℝ) : ℂ) * I = 0 by simp, Complex.exp_zero, one_mul] at h
  exact h.hasDerivWithinAt

/-- **`thm:weighted-dominance` at a `ρ = 1` pencil with an amplitude divisor.**
`eq:dominance-bound` on `eq:retained-range`, off deleted windows of half-width
`2^{-M/2}` about the amplitude's zero at `θ = π/2`.

This is the first pencil in the tree carried through
`weighted_dominance_of_branch_any_multiplicity` at a **simple** smallest zero,
and the first whose deleted family shrinks with `M`. -/
theorem fav_weighted_dominance :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ Real.pi - h / M → θ ∉ favTheta M →
        ftRemainder witQ favB 1 witZ witTau M θ
          ≤ ftPrincipalAmp witQ favB 1 witZ witTau θ / 2 := by
  have hpi := Real.pi_pos
  have hs3 : Real.sqrt 3 < 2 := by
    have h : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h
  have hIoo : ∀ δ : ℝ, 0 < δ → δ ≤ Real.pi / 4 → δ ∈ Set.Ioo 0 Real.pi :=
    fun δ h1 h2 => ⟨h1, by linarith⟩
  have hIooU : ∀ δ : ℝ, 0 < δ → δ ≤ Real.pi / 4 → Real.pi - δ ∈ Set.Ioo 0 Real.pi :=
    fun δ h1 h2 => ⟨by linarith, by linarith⟩
  exact weighted_dominance_of_branch_any_multiplicity
    (Q := witQ) (B := favB) (r := 1) (b := Real.pi) (z := witZ) (τ := witTau)
    (Θ := favTheta) (n₀ := 0) (n₁ := 0)
    (g₀ := fun _ => Fin.elim0) (g₁ := fun _ => Fin.elim0)
    (sfun₀ := favRoots) (sfun₁ := fun δ => favRoots (Real.pi - δ))
    (x₁ := 2 - Real.sqrt 3) (ρ := 1) (te₀ := 1) (γe₀ := I)
    (idx₀ := Fin.elim0) (jp₀ := 0) (νB₀ := 0) (cB₀ := 1) (cQ₀ := 1)
    (R₀ := 2) (τmax₀ := 1) (σ₀ := 1 / 2) (e₀ := Real.pi / 4)
    (C₀ := 5) (Cexp₀ := 0) (p₁ := 0) (A₁ := 1)
    (idx₁ := Fin.elim0) (L₁ := Fin.elim0)
    (R₁ := 2) (τmax₁ := 1) (σ₁ := 1 / 2) (e₁ := Real.pi / 4)
    (C₁ := 5) (Cexp₁ := 0)
    (hQ := hasRealCoeffs_witQ) (hB := hasRealCoeffs_favB) (hB0 := favB_ne_zero)
    (hr := le_rfl) (hQ0 := witQ_eval_zero_ne)
    (hx₁ := by linarith) (hρ := fun h => absurd h (lt_irrefl 0))
    (hte₀ := one_ne_zero) (hγe₀ := Complex.I_ne_zero)
    (hγ0₀ := fav_hγ0) (hγd₀ := fav_hγd)
    (hk₀ := rootMultiplicity_lower_pos) (hrootev₀ := fav_hrootev)
    (hcB₀ := fun h => absurd h (lt_irrefl 0)) (hcQ₀ := fun h => absurd h (lt_irrefl 0))
    (hBj₀ := fun i => i.elim0) (hBp₀ := fun h => absurd h (lt_irrefl 0))
    (hEj₀ := fun i => i.elim0) (hEp₀ := fun h => absurd h (lt_irrefl 0))
    (hR₀ := by norm_num) (hσ₀ := by norm_num) (hσ₀1 := by norm_num)
    (he₀ := by linarith)
    (hτpos₀ := fun δ _ _ => by rw [witTau_eq_one]; norm_num)
    (hτle₀ := fun δ _ _ => by rw [witTau_eq_one])
    (hroot₀ := fun δ _ _ a ha => favRoots_root ha)
    (hsimple₀ := fun δ h1 h2 a ha => favRoots_simple (hIoo δ h1 h2) ha)
    (haR₀ := fun δ _ _ a ha => favRoots_norm_lt ha)
    (huniq₀ := fun δ _ _ t _ ht => favRoots_uniq ht)
    (hrootplus₀ := fun δ _ _ => ftDen_witQ_eval_principal δ)
    (hne₀ := fun δ h1 h2 => ftPrincipal_ne_conj (hIoo δ h1 h2))
    (hginj₀ := fun δ _ _ i => i.elim0)
    (hgmem₀ := fun δ _ _ i => i.elim0)
    (hgcard₀ := fun δ _ _ => favRoots_erase_card δ)
    (hC₀ := by norm_num) (hCbd₀ := fun δ _ _ t ht => favCbd ht)
    (hCexp₀ := le_rfl) (hωne₀ := fun i => i.elim0) (hωne'₀ := fun i => i.elim0)
    (hexp₀ := fun i => i.elim0)
    (hA₁ := one_pos)
    (hamp₁ := ⟨Real.pi / 4, by linarith, fun η h1 h2 => ftPrincipalAmp_fav_upper h1 h2⟩)
    (hn₁r := fun h => absurd h (lt_irrefl 0))
    (hL₁ := fun i => i.elim0) (hratio₁ := fun i => i.elim0)
    (hR₁ := by norm_num) (hσ₁ := by norm_num) (hσ₁1 := by norm_num)
    (he₁ := by linarith)
    (hτpos₁ := fun δ _ _ => by rw [witTau_eq_one]; norm_num)
    (hτle₁ := fun δ _ _ => by rw [witTau_eq_one])
    (hroot₁ := fun δ _ _ a ha => favRoots_root ha)
    (hsimple₁ := fun δ h1 h2 a ha => favRoots_simple (hIooU δ h1 h2) ha)
    (haR₁ := fun δ _ _ a ha => favRoots_norm_lt ha)
    (huniq₁ := fun δ _ _ t _ ht => favRoots_uniq ht)
    (hrootplus₁ := fun δ _ _ => ftDen_witQ_eval_principal (Real.pi - δ))
    (hne₁ := fun δ h1 h2 => ftPrincipal_ne_conj (hIooU δ h1 h2))
    (hginj₁ := fun δ _ _ i => i.elim0)
    (hgmem₁ := fun δ _ _ i => i.elim0)
    (hgcard₁ := fun δ _ _ => favRoots_erase_card (Real.pi - δ))
    (hC₁ := by norm_num) (hCbd₁ := fun δ _ _ t ht => favCbd ht)
    (hCexp₁ := le_rfl) (hωne₁ := fun i => i.elim0) (hωne'₁ := fun i => i.elim0)
    (hexp₁ := fun i => i.elim0)
    (hinterior := favWitness_hinterior)

end ForgacsTran
