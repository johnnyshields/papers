/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchEndpoint
import ForgacsTran.Amplitude
import ForgacsTran.ComplexPart

/-!
# The arc pencil's conjugate symmetry in the angle

`FTBranchEndpoint` defines `ftPencilIm P r τ θ`, the imaginary part whose vanishing
is the branch equation of `eq:ab-def`, and `ftPencilImDeriv`, its `θ`-derivative,
which at `θ = 0` is `-E(τ)`.  This module records that the first is **odd** in `θ`
and the second **even**.

The reason is the conjugate symmetry of a real pencil, read on the arc: `θ ↦ -θ`
conjugates the arc point, the real coefficients carry the conjugation through the
evaluation, and `e^{ir\theta}` is conjugated too, so the whole bracket is
conjugated and its imaginary part changes sign.

**What this is for.**  The branch satisfies `ftPencilIm P r (τ θ) θ = 0`, and
`ftPencilIm P r τ 0 = 0` for *every* `τ`, so Rolle gives
`ftPencilImDeriv P r (τ θ) ξ = 0` at some `ξ ∈ (0,θ)`.  Expanding at `ξ = 0`, where
the derivative is `-E(τ)`, turns that into `E(τ θ) = O(ξ) = O(θ)`, and with
`E'(t_a) ≠ 0` — `EndpointCollision.sum_div_sq_pos`, a sum of positive terms — it
bounds the radial slope `(τ θ - t_a)/θ`.  It does not make the slope vanish.

Evenness is what makes it vanish: an even function's `θ`-derivative at `0` is zero,
so the expansion improves to `E(τ θ) = o(θ)`.  At `2 ≤ ρ` the slope is genuinely
nonzero, so nothing here contradicts that — the difference is which point the
radius runs into, not the symmetry, which holds at every `ρ`.

**The Rolle step is the trap, and it is a trap because it is correct.**  It is a
true statement, it is provable, it is in exactly the shape the endpoint argument
wants, and it is one order short.  A reader who reconstructs it will find the
symmetry lemmas below redundant — the bound already follows without them — and the
`o` that the `ρ = 1` derivative binder actually needs will be gone with them.  The
parity is not decoration over a Rolle step; it is the entire difference between a
slope that is bounded and a slope that is zero.

## Main statements

* `ftArcPoint_neg` — `θ ↦ -θ` conjugates the arc point.
* `ftPencilIm_neg`, `ftPencilImDeriv_neg` — odd and even in `θ`.
* `eq_zero_of_hasDerivAt_of_even` — an even function differentiable at `0` has
  derivative `0` there.
* `eq_zero_of_hasDerivAt_ftPencilImDeriv` — those two together, on the whole line
  `θ = 0`, whatever `τ` and whatever the pencil.
* `ftPencilImDeriv2`, `hasDerivAt_ftPencilImDeriv` — the second `θ`-derivative in
  closed form, `e^{ir\theta}(rE(t) - tE'(t))`.
* `ftPencilImDeriv2_zero` — it vanishes on the whole line `θ = 0`, as an identity:
  the bracket there is real.  This is the parity fact again, obtained without
  differentiating anything, which is the form the uniform estimate consumes.
* `continuous_ftPencilImDeriv2` — jointly continuous, which is what turns that
  identity into a bound that is small near the endpoint rather than merely zero
  at it.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `eq:principal-pair`.

## Tags

arc pencil, conjugate symmetry, critical polynomial, branch equation
-/

namespace ForgacsTran

open Complex Filter Polynomial
open scoped Topology

/-- A real polynomial pushed into `ℂ` has real coefficients. -/
theorem hasRealCoeffs_map_ofReal (P : Polynomial ℝ) :
    HasRealCoeffs (P.map (algebraMap ℝ ℂ)) := by
  intro k
  rw [Polynomial.coeff_map]
  simp

/-- The arc point is conjugated by `θ ↦ -θ`. -/
theorem ftArcPoint_neg (τ θ : ℝ) :
    ftArcPoint τ (-θ) = (starRingEnd ℂ) (ftArcPoint τ θ) := by
  rw [ftArcPoint, ftArcPoint, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **`ftPencilIm` is odd in `θ`.**  This is the conjugate symmetry of a real
pencil, read on the arc: `θ ↦ -θ` conjugates the arc point, the real coefficients
carry the conjugation through the evaluation, and `e^{ir\theta}` is conjugated too,
so the bracket is conjugated and its imaginary part changes sign. -/
theorem ftPencilIm_neg (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) :
    ftPencilIm P r τ (-θ) = -ftPencilIm P r τ θ := by
  have hreal := hasRealCoeffs_map_ofReal P
  have hexp : Complex.exp ((((r : ℝ) * -θ : ℝ)) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp ((((r : ℝ) * θ : ℝ)) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  rw [ftPencilIm, ftPencilIm, hexp, ftArcPoint_neg, ← hreal.eval_conj, ← map_mul,
    Complex.conj_im]

/-- **`ftPencilImDeriv` is even in `θ`**, which is the previous statement
differentiated — proved here directly, by the same conjugation, so that it does
not depend on a differentiation step. -/
theorem ftPencilImDeriv_neg (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) :
    ftPencilImDeriv P r τ (-θ) = ftPencilImDeriv P r τ θ := by
  have hreal : HasRealCoeffs (ftCritical (P.map (algebraMap ℝ ℂ)) r) := by
    rw [ftCritical_map]
    exact hasRealCoeffs_map_ofReal _
  have hexp : Complex.exp ((((r : ℝ) * -θ : ℝ)) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp ((((r : ℝ) * θ : ℝ)) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  -- `-i·conj z` and `-i·z` have the same imaginary part, `-Re z`
  have key : ∀ z : ℂ, (-Complex.I * (starRingEnd ℂ) z).im = (-Complex.I * z).im := by
    intro z
    simp [Complex.mul_im]
  rw [ftPencilImDeriv, ftPencilImDeriv, hexp, ftArcPoint_neg, ← hreal.eval_conj]
  simp only [mul_assoc, ← map_mul]
  exact key _

/-- An even function differentiable at `0` has derivative `0` there. -/
theorem eq_zero_of_hasDerivAt_of_even {f : ℝ → ℝ} {d : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x) (h : HasDerivAt f d 0) : d = 0 := by
  -- the difference quotient at `0` is ODD, so its limit is its own negative
  rw [hasDerivAt_iff_tendsto_slope] at h
  have hmap : Filter.Tendsto (fun x : ℝ => -x) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have hodd : ∀ x : ℝ, slope f 0 (-x) = -slope f 0 x := by
    intro x
    rw [slope_def_field, slope_def_field, heven x, sub_zero, sub_zero, div_neg]
  have h2 : Filter.Tendsto (fun x : ℝ => -slope f 0 x) (𝓝[≠] (0 : ℝ)) (𝓝 d) := by
    refine (h.comp hmap).congr fun x => ?_
    simpa using hodd x
  exact by linarith [tendsto_nhds_unique h2 h.neg]

/-- **The `θ`-derivative of `ftPencilImDeriv` vanishes on the whole line `θ = 0`.**
Whatever `τ` is, and whatever the pencil is.  This is the fact that upgrades the
Rolle bound on the radial slope to a vanishing one, and it is the only place the
conjugate symmetry enters that argument. -/
theorem eq_zero_of_hasDerivAt_ftPencilImDeriv {P : Polynomial ℝ} {r : ℕ} {τ d : ℝ}
    (h : HasDerivAt (fun s : ℝ => ftPencilImDeriv P r τ s) d 0) : d = 0 :=
  eq_zero_of_hasDerivAt_of_even (fun x => ftPencilImDeriv_neg P r τ x) h

/-! ### The second `θ`-derivative, and why it vanishes on `θ = 0`

`ftPencilImDeriv_neg` already forces this: an even function's derivative at `0` is
zero.  It is proved below as an identity instead, because the identity is what the
uniform estimate needs — the bracket at `θ = 0` is a real expression in `τ`, so its
imaginary part is `0` for *every* `τ` at once, with no appeal to a derivative
existing.  The parity lemmas remain the reason to expect it.
-/

/-- The second `θ`-derivative of `ftPencilIm`, in closed form.  Differentiating
`-i e^{ir\theta}E(t)` once more turns the `-i` into the pencil's own weight:
`e^{ir\theta}(rE(t) - tE'(t))`. -/
noncomputable def ftPencilImDeriv2 (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) : ℝ :=
  (Complex.exp ((((r : ℝ) * θ : ℝ)) * Complex.I)
    * ((r : ℂ) * (ftCritical (P.map (algebraMap ℝ ℂ)) r).eval (ftArcPoint τ θ)
      - ftArcPoint τ θ
        * (derivative (ftCritical (P.map (algebraMap ℝ ℂ)) r)).eval (ftArcPoint τ θ))).im

theorem hasDerivAt_ftPencilImDeriv (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) :
    HasDerivAt (fun s => ftPencilImDeriv P r τ s) (ftPencilImDeriv2 P r τ θ) θ := by
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((((r : ℝ) * s : ℝ)) * Complex.I))
      (Complex.exp ((((r : ℝ) * θ : ℝ)) * Complex.I) * ((r : ℂ) * Complex.I)) θ := by
    have h1 : HasDerivAt (fun s : ℝ => (((r : ℝ) * s : ℝ) : ℂ)) ((r : ℂ)) θ := by
      have := ((hasDerivAt_id θ).const_mul ((r : ℝ))).ofReal_comp
      simpa using this
    have h0 : HasDerivAt (fun s : ℝ => (((r : ℝ) * s : ℝ) : ℂ) * Complex.I)
        ((r : ℂ) * Complex.I) θ := by simpa using h1.mul_const Complex.I
    exact h0.cexp
  have he := hexp.const_mul (-Complex.I)
  have hp : HasDerivAt
      (fun s : ℝ => (ftCritical (P.map (algebraMap ℝ ℂ)) r).eval (ftArcPoint τ s))
      ((derivative (ftCritical (P.map (algebraMap ℝ ℂ)) r)).eval (ftArcPoint τ θ)
        * (-Complex.I * ftArcPoint τ θ)) θ :=
    ((ftCritical (P.map (algebraMap ℝ ℂ)) r).hasDerivAt (ftArcPoint τ θ)).comp θ
      (hasDerivAt_ftArcPoint_theta τ θ)
  refine (he.mul hp).im.congr_deriv ?_
  rw [ftPencilImDeriv2]
  congr 1
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  set A : ℂ := Complex.exp ((((r : ℝ) * θ : ℝ)) * Complex.I) with hA
  set t : ℂ := ftArcPoint τ θ with ht
  set V : ℂ := (ftCritical (P.map (algebraMap ℝ ℂ)) r).eval t with hV
  set W : ℂ := (derivative (ftCritical (P.map (algebraMap ℝ ℂ)) r)).eval t with hW
  linear_combination (A * (t * W - (r : ℂ) * V)) * hI

/-- **The second `θ`-derivative vanishes on the whole line `θ = 0`.**  At `θ = 0`
the arc point is the real `τ`, and `E` and `E'` are real polynomials there, so the
bracket is real and its imaginary part is `0` — for every `τ` and every pencil, as
an identity rather than a limit.

This is what turns the Rolle bound of the module header into a vanishing one: the
second-order term it controls is not merely small at the endpoint, it is absent
along the entire line the endpoint sits on. -/
@[simp] theorem ftPencilImDeriv2_zero (P : Polynomial ℝ) (r : ℕ) (τ : ℝ) :
    ftPencilImDeriv2 P r τ 0 = 0 := by
  simp [ftPencilImDeriv2, ftCritical_map, Polynomial.derivative_map, aeval_ofReal]

theorem continuous_ftPencilImDeriv2 (P : Polynomial ℝ) (r : ℕ) :
    Continuous (fun p : ℝ × ℝ => ftPencilImDeriv2 P r p.1 p.2) := by
  have harc : Continuous (fun p : ℝ × ℝ => ftArcPoint p.1 p.2) := by
    simp only [ftArcPoint]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp continuous_snd).neg).mul
        continuous_const))
  have hexp : Continuous (fun p : ℝ × ℝ => Complex.exp ((((r : ℝ) * p.2 : ℝ)) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_snd)).mul
        continuous_const)
  exact Complex.continuous_im.comp (hexp.mul
    ((continuous_const.mul
        ((ftCritical (P.map (algebraMap ℝ ℂ)) r).continuous_aeval.comp harc)).sub
      (harc.mul
        ((derivative (ftCritical (P.map (algebraMap ℝ ℂ)) r)).continuous_aeval.comp harc))))

/-! ### The second-order bound the endpoint argument consumes

`ftPencilIm P r τ 0 = 0` and `ftPencilImDeriv P r τ 0 = -E(τ)`, so the first-order
expansion of `ftPencilIm` in `θ` is `-θE(τ)`.  The bound below is that expansion
with its remainder controlled by the second derivative on the segment — the mean
value inequality applied twice, once to `ftPencilImDeriv` and once to what is left.

The constant is `C` rather than `C/2`; the factor is not worth the Taylor
machinery, since `C` is going to be sent to `0` by `ftPencilImDeriv2_zero` and
continuity rather than compared against anything. -/

theorem abs_ftPencilIm_sub_linear_le {P : Polynomial ℝ} {r : ℕ} {τ θ C : ℝ}
    (hθ : 0 ≤ θ) (hC : ∀ ξ ∈ Set.Icc (0 : ℝ) θ, |ftPencilImDeriv2 P r τ ξ| ≤ C) :
    |ftPencilIm P r τ θ - θ * ftPencilImDeriv P r τ 0| ≤ C * θ ^ 2 := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) θ) := convex_Icc _ _
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) θ := ⟨le_rfl, hθ⟩
  have hθmem : θ ∈ Set.Icc (0 : ℝ) θ := ⟨hθ, le_rfl⟩
  -- the first derivative moves by at most `C·x` on the segment
  have hstep : ∀ x ∈ Set.Icc (0 : ℝ) θ,
      |ftPencilImDeriv P r τ x - ftPencilImDeriv P r τ 0| ≤ C * θ := by
    intro x hx
    have hbound := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => ftPencilImDeriv P r τ s) (f' := fun s => ftPencilImDeriv2 P r τ s)
      (fun y _ => (hasDerivAt_ftPencilImDeriv P r τ y).hasDerivWithinAt)
      (fun y hy => by simpa using hC y hy) h0mem hx
    have hxθ : |x - 0| ≤ θ := by
      rw [sub_zero, abs_of_nonneg hx.1]; exact hx.2
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 h0mem)
    calc |ftPencilImDeriv P r τ x - ftPencilImDeriv P r τ 0|
        ≤ C * |x - 0| := by simpa using hbound
      _ ≤ C * θ := by nlinarith [abs_nonneg (x - 0)]
  -- and the linear model then holds to second order
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) θ,
      HasDerivWithinAt (fun s => ftPencilIm P r τ s - s * ftPencilImDeriv P r τ 0)
        (ftPencilImDeriv P r τ x - ftPencilImDeriv P r τ 0) (Set.Icc (0 : ℝ) θ) x := by
    intro x _
    have h1 := (hasDerivAt_ftPencilIm P r τ x).hasDerivWithinAt (s := Set.Icc (0 : ℝ) θ)
    have h2 : HasDerivWithinAt (fun s : ℝ => s * ftPencilImDeriv P r τ 0)
        (ftPencilImDeriv P r τ 0) (Set.Icc (0 : ℝ) θ) x := by
      simpa using ((hasDerivAt_id x).mul_const
        (ftPencilImDeriv P r τ 0)).hasDerivWithinAt (s := Set.Icc (0 : ℝ) θ)
    exact h1.sub h2
  have hmain := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => ftPencilIm P r τ s - s * ftPencilImDeriv P r τ 0)
    (f' := fun s => ftPencilImDeriv P r τ s - ftPencilImDeriv P r τ 0)
    hderiv (fun y hy => by simpa using hstep y hy) h0mem hθmem
  have hz : ftPencilIm P r τ 0 - (0 : ℝ) * ftPencilImDeriv P r τ 0 = 0 := by
    rw [ftPencilIm_zero]; ring
  rw [hz, sub_zero] at hmain
  have : |ftPencilIm P r τ θ - θ * ftPencilImDeriv P r τ 0| ≤ C * θ * |θ - 0| := by
    simpa using hmain
  rw [sub_zero, abs_of_nonneg hθ] at this
  calc |ftPencilIm P r τ θ - θ * ftPencilImDeriv P r τ 0| ≤ C * θ * θ := this
    _ = C * θ ^ 2 := by ring

/-- **The radial slope vanishes at a nondegenerate endpoint.**  Any solution of the
branch equation running into a simple zero of `E` approaches it faster than
linearly.

The three inputs are exactly the three facts the endpoint has: the branch equation
along the approach, the limit itself, and `E'(t_a) ≠ 0` — which at the
Forgács–Tran branch is `EndpointCollision.sum_div_sq_pos` together with
`Q(t_a) ≠ 0`, a sum of positive terms times a nonzero value.

**Nothing here knows about `ρ`, and the criterion is right where `ρ` is already
known.**  At a zero of multiplicity `ρ ≥ 2` one has `E'(x_1) = x_1Q''(x_1)`, so
among those the derivative is nonzero exactly at `ρ = 2`; and
`EndpointBranch.tendsto_ftTau_blowup` gives the slope there independently as
`-x_1\cot(π/ρ)`, which vanishes exactly at `ρ = 2`.  The two routes therefore call
the slope zero on the same set, by different arguments.  `ρ = 3` is the negative
control: `Q''(x_1) = 0`, the hypothesis fails, and the approach really is linear
with slope `-x_1/\sqrt3`.

`scripts/check_endpoint_slope_dichotomy.py` measures all three at `r = 1` and
`r = 2`: exponent `2` wherever `E'(t_a) ≠ 0`, exponent `1` and the slope equal to
`x_1\cot(π/ρ)` to `1e-4` where it vanishes. -/
theorem tendsto_slope_of_ftPencilIm_eq_zero {P : Polynomial ℝ} {r : ℕ} {T : ℝ → ℝ}
    {ta : ℝ}
    (hzero : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftPencilIm P r (T θ) θ = 0)
    (hlim : Filter.Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 ta))
    (hE : (ftCriticalReal P r).eval ta = 0)
    (hE' : (derivative (ftCriticalReal P r)).eval ta ≠ 0) :
    Filter.Tendsto (fun θ => (T θ - ta) / θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  set E : Polynomial ℝ := ftCriticalReal P r with hEdef
  set D : ℝ := (derivative E).eval ta with hDdef
  have hD : 0 < |D| := abs_pos.2 hE'
  set K : ℝ := 2 / |D| with hKdef
  have hK : 0 < K := div_pos two_pos hD
  -- (i) `E` is invertible-Lipschitz at `ta`, from its nonzero derivative there
  have hlip : ∀ᶠ τ in 𝓝 ta, |τ - ta| ≤ K * |E.eval τ| := by
    rw [← nhdsNE_sup_pure ta, Filter.eventually_sup]
    refine ⟨?_, by simp [hE]⟩
    have hslope : Filter.Tendsto (slope (fun s => E.eval s) ta) (𝓝[≠] ta) (𝓝 D) :=
      hasDerivAt_iff_tendsto_slope.1 (E.hasDerivAt ta)
    have hbig : ∀ᶠ τ in 𝓝[≠] ta, |D| / 2 < |slope (fun s => E.eval s) ta τ| :=
      hslope.eventually ((isOpen_lt continuous_const continuous_abs).eventually_mem
        (by exact (by linarith : |D| / 2 < |D|)))
    filter_upwards [hbig, self_mem_nhdsWithin] with τ hτ hne
    have hsub : τ - ta ≠ 0 := sub_ne_zero.2 hne
    have habs : 0 < |τ - ta| := abs_pos.2 hsub
    rw [slope_def_field, hE, sub_zero, abs_div, lt_div_iff₀ habs] at hτ
    rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ hD]
    nlinarith [hτ, habs]
  -- (ii) the second derivative is small near `(ta, 0)`, because it is zero there
  have hcont0 : Filter.Tendsto (fun p : ℝ × ℝ => ftPencilImDeriv2 P r p.1 p.2)
      (𝓝 (ta, 0)) (𝓝 0) := by
    have h := (continuous_ftPencilImDeriv2 P r).continuousAt (x := (ta, 0))
    rw [ContinuousAt] at h
    simpa using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := ε / (2 * K) with hε'def
  have hε' : 0 < ε' := by positivity
  have hnb : ∀ᶠ p : ℝ × ℝ in 𝓝 (ta, 0), |ftPencilImDeriv2 P r p.1 p.2| ≤ ε' := by
    filter_upwards [Metric.tendsto_nhds.1 hcont0 ε' hε'] with p hp
    rw [Real.dist_eq, sub_zero] at hp
    exact hp.le
  rw [nhds_prod_eq] at hnb
  obtain ⟨pa, hpa, pb, hpb, hprod⟩ := Filter.eventually_prod_iff.1 hnb
  obtain ⟨η, hη, hηmem⟩ := Metric.eventually_nhds_iff.1 hpb
  -- (iii) the three together, along the branch
  filter_upwards [hzero, hlim.eventually hpa, hlim.eventually hlip,
    Ioo_mem_nhdsGT hη, self_mem_nhdsWithin] with θ hz hpaθ hlipθ hθη hθ0
  have hθ : (0 : ℝ) < θ := hθ0
  have hC : ∀ ξ ∈ Set.Icc (0 : ℝ) θ, |ftPencilImDeriv2 P r (T θ) ξ| ≤ ε' := by
    intro ξ hξ
    refine hprod hpaθ (hηmem ?_)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hξ.1]
    exact lt_of_le_of_lt hξ.2 hθη.2
  have htay := abs_ftPencilIm_sub_linear_le (P := P) (r := r) (τ := T θ) hθ.le hC
  rw [hz, ftPencilImDeriv_zero, ← hEdef] at htay
  have hrw : (0 : ℝ) - θ * -E.eval (T θ) = θ * E.eval (T θ) := by ring
  rw [hrw, abs_mul, abs_of_pos hθ] at htay
  have hEbound : |E.eval (T θ)| ≤ ε' * θ := by nlinarith [abs_nonneg (E.eval (T θ)), htay, hθ]
  have hTbound : |T θ - ta| ≤ K * (ε' * θ) :=
    le_trans hlipθ (mul_le_mul_of_nonneg_left hEbound hK.le)
  have hKe : K * (ε' * θ) = ε / 2 * θ := by
    rw [hε'def, hKdef]
    field_simp
  rw [hKe] at hTbound
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hθ, div_lt_iff₀ hθ]
  nlinarith [hTbound, hθ, hε]

end ForgacsTran
