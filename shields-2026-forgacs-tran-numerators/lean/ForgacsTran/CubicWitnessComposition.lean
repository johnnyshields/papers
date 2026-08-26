/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.CubicWitnessInterior
import ForgacsTran.CubicWitnessCluster

/-!
# `thm:weighted-dominance` at one pencil, with nothing assumed

Composes `weighted_dominance_of_branch` end to end at `Q(t) = (1-t)^3`, `r = 1`,
`B(t) = 3t^2 + 1`, so that its conclusion holds with no hypothesis left standing.
That is the question `CubicWitness`'s header opens with: the theorem carries a
hundred-odd binders and nothing instantiated them, so nothing ruled out their
being jointly unmeetable.  Per-binder checks cannot see a joint failure, and
three defects in this tree were binders unsatisfiable at the real objects.

## Why `r = 1`, and what it does not settle

`r = 1` is where `hEp₁` is coherent.  At `r > 1` the upper endpoint has
`τ ≍ δ → 0`, so `|∂_tD| ≍ 1/δ`, and divided by `δ^{ρ-1}` it blows up like
`δ^{-ρ}`; the binder is not indexed by `Fin n₁`, so an empty cluster does not
evade it.  Only at `r = 1` does the principal pair coalesce to multiplicity
exactly two and the quantity stay bounded.

The price is that **the upper cluster is empty here**, `n₁ = 0`, and the binders
quantified over `Fin n₁` are satisfied vacuously.  That is legitimate and it is
what `hn₁r : 0 < n₁ → 2 ≤ r` says -- the upper cluster has no nonprincipal member
below `r = 2`.  It is also a real limit on what this composition establishes:
**it says nothing about the upper cluster group.**  A later reader meeting an
empty block here should read it as the pencil's geometry, not as a gap; and
should not read the composition as evidence that `hexp₁` or `hratio₁` are
satisfiable, which they are not tested by.  `UpperClusterWitness` at `Q = 1 - t`,
`r = 3` is where those are witnessed non-vacuously.

**And no pencil can currently do better, which is the other half of that.**
`hγ0₁` pins `te₁ = γ(b)` and `hte₁` asks `te₁ ≠ 0`, so the two together need
`τ(b) ≠ 0` at the upper endpoint.  The upper cluster is
`{r-th roots of -1} \ {e^{±iπ/r}}`, which is empty at `r = 1` **and at `r = 2`**
-- there the two roots `±i` *are* the principal pair -- and first non-empty at
`r = 3`.  But at `r ≥ 2` the arc ends at `z → ∞` with the `r`-fold cluster
shrinking to the origin, so `τ(b) = 0` and `hte₁` fails.  Only `r = 1` ends at a
finite collision, where `τ(π) = 1/2`.

So the composition is available exactly where the upper cluster is vacuous, and
the upper cluster is non-vacuous exactly where the composition is blocked.  A
reader should not expect a later witness to fill the gap in; closing it needs
`hγ0₁`/`hte₁` restated so that a vanishing endpoint datum is admissible, which
is a change to `weighted_dominance_of_branch` rather than to a witness.

The endpoint behaviour is measured rather than argued -- over `deg Q < r`,
`= r` and `> r` at `r = 3` and `r = 4`, in
`../scripts/check_cubic_composition.py` (C7) -- so it is a statement about the
pencils swept.  The general claim would need the endpoint classification.

## The upper radius is `1`, not the retained block's `5`

`cubicWitness_upperRetainedSet_block` separates at `R₁ = 5`, which puts the third
denominator zero -- modulus `1/τ² → 4` as `θ → π` -- *inside* the contour.  Then
`hgcard₁` forces `n₁ = 1` and `hexp₁` demands `‖third/τ‖ → 1`, while the true
limit is `8`.  **That pairing is refuted, not merely awkward.**  Taking `R₁ = 1`
puts only the principal pair inside, which is what makes `n₁ = 0` correct rather
than convenient; `σ₁ = τ(π - e₁) < 1` still separates, and no zero sits on
`‖t‖ = 1` at any `δ ∈ [0, e₁]`, `δ = 0` included, where the zeros are `-1/2`
twice and `4`.

## Everything is elementary because the branch is closed-form

`cubicTau_closed_form` makes `τ(θ) = 1/(2cos((π-θ)/3))` on `[0,π]`, so the
endpoint derivatives, the cluster directions and the residue constants are trig
rather than asymptotics.  In particular the spectral parameter's rate is free:
`z = -(1-γ)³/γ` at a branch point, so `z/δ² = -((1-γ)/δ)³ · δ/γ → 0` with no
expansion of `z` at all.  `z ≍ δ³` is never proved because it is never needed.

## Tags

witness, cubic pencil, weighted dominance, non-vacuity
-/

namespace ForgacsTran

open Polynomial Complex

/-! ### The branch at the two endpoints

`cubicTau` matches its closed form on `[0,π]` and the closed form is smooth
across both endpoints, so each endpoint derivative is a `congr_of_eventuallyEq`
within `Set.Ici 0` -- the one-sided form `weighted_dominance_of_branch` asks for.
The implicit function theorem degenerates at the lower endpoint (differentiating
the branch equation at `(0,1)` gives `6τ' = 6τ'`), which is why the closed form
is the route. -/

theorem cubicTau_eventuallyEq_cf :
    cubicTau =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)]
      fun t : ℝ => 1 / (2 * Real.cos ((Real.pi - t) / 3)) := by
  have hpi := Real.pi_pos
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with t h1 h2
  exact cubicTau_closed_form ⟨h1, h2.le⟩

/-- `τ'(0) = -1/√3`, one-sided.  The rate the branch identity predicts by
comparing `θ²/2` against `3(1-τ)²/2`. -/
theorem hasDerivWithinAt_cubicTau_zero :
    HasDerivWithinAt cubicTau (-(1 / Real.sqrt 3)) (Set.Ici 0) 0 := by
  have hpi := Real.pi_pos
  have hcos : Real.cos ((Real.pi - 0) / 3) = 1 / 2 := by
    rw [sub_zero]
    simp
  have hsin : Real.sin ((Real.pi - 0) / 3) = Real.sqrt 3 / 2 := by
    rw [sub_zero]
    simp
  have hcf := hasDerivAt_cubicTauCF (θ := 0) (by rw [hcos]; norm_num)
  have hval : -Real.sin ((Real.pi - 0) / 3) / (6 * Real.cos ((Real.pi - 0) / 3) ^ 2)
      = -(1 / Real.sqrt 3) := by
    rw [hcos, hsin]
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hp : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    nlinarith [h3, hp]
  rw [hval] at hcf
  exact hcf.hasDerivWithinAt.congr_of_eventuallyEq cubicTau_eventuallyEq_cf
    (cubicTau_closed_form ⟨le_rfl, hpi.le⟩)

/-- On the upper chart the branch is `1/(2cos(δ/3))`, an even function of `δ`,
so its endpoint derivative is `0` -- the collision at `θ = π` is quadratic in the
angle from both sides. -/
theorem cubicTauUpper_eq {δ : ℝ} (hδ : δ ∈ Set.Icc 0 Real.pi) :
    cubicTau (Real.pi - δ) = 1 / (2 * Real.cos (δ / 3)) := by
  have hpi := Real.pi_pos
  have h := cubicTau_closed_form (θ := Real.pi - δ) ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
  rw [h, show Real.pi - (Real.pi - δ) = δ by ring]

theorem hasDerivWithinAt_cubicTauUpper_zero :
    HasDerivWithinAt (fun δ : ℝ => cubicTau (Real.pi - δ)) 0 (Set.Ici 0) 0 := by
  have hpi := Real.pi_pos
  have hcf : HasDerivAt (fun t : ℝ => 1 / (2 * Real.cos (t / 3)))
      (Real.sin (0 / 3) / (6 * Real.cos (0 / 3) ^ 2)) 0 := by
    have hu : HasDerivAt (fun t : ℝ => t / 3) (1 / 3 : ℝ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).div_const 3
    have hc : HasDerivAt (fun t : ℝ => Real.cos (t / 3))
        (-Real.sin (0 / 3) * (1 / 3)) 0 := hu.cos
    have hne : 2 * Real.cos (0 / 3) ≠ 0 := by norm_num
    have h2 : HasDerivAt (fun t : ℝ => 2 * Real.cos (t / 3))
        (2 * (-Real.sin (0 / 3) * (1 / 3))) 0 := hc.const_mul 2
    have h3 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div h2 hne
    have heq : (0 * (2 * Real.cos (0 / 3)) - 1 * (2 * (-Real.sin (0 / 3) * (1 / 3))))
          / (2 * Real.cos (0 / 3)) ^ 2
        = Real.sin (0 / 3) / (6 * Real.cos (0 / 3) ^ 2) := by
      norm_num
    exact heq ▸ h3
  have hval : Real.sin (0 / 3) / (6 * Real.cos (0 / 3) ^ 2) = 0 := by norm_num
  rw [hval] at hcf
  refine hcf.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with t h1 h2
    exact cubicTauUpper_eq ⟨h1, h2.le⟩
  · exact cubicTauUpper_eq ⟨le_rfl, hpi.le⟩

/-! ### The principal branch at the endpoints

`γ_e = -1/√3 + i` at the lower endpoint and `i/2` at the upper, both nonzero,
which is `hγe₀`/`hγe₁`.  At the lower endpoint the modulus falls at rate
`1/√3` while the angle turns at rate `1`; at the upper the modulus is stationary
and only the angle moves, which is the collision being quadratic there. -/

theorem hasDerivWithinAt_ftPrincipal_zero :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal cubicTau δ)
      (-((1 / Real.sqrt 3 : ℝ) : ℂ) + I) (Set.Ici 0) 0 := by
  have hτ : HasDerivWithinAt (fun δ : ℝ => ((cubicTau δ : ℝ) : ℂ))
      ((-(1 / Real.sqrt 3) : ℝ) : ℂ) (Set.Ici 0) 0 :=
    hasDerivWithinAt_cubicTau_zero.ofReal_comp
  have hE : HasDerivWithinAt (fun δ : ℝ => Complex.exp (((δ : ℝ) : ℂ) * I))
      (Complex.exp (((0 : ℝ) : ℂ) * I) * I) (Set.Ici 0) 0 := by
    have hc : HasDerivAt (fun w : ℂ => Complex.exp (w * I))
        (Complex.exp (((0 : ℝ) : ℂ) * I) * I) (((0 : ℝ) : ℂ)) := by
      simpa using ((hasDerivAt_id (((0 : ℝ) : ℂ))).mul_const I).cexp
    exact hc.comp_ofReal.hasDerivWithinAt
  have h := hτ.mul hE
  have hval : ((-(1 / Real.sqrt 3) : ℝ) : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * I)
      + ((cubicTau 0 : ℝ) : ℂ) * (Complex.exp (((0 : ℝ) : ℂ) * I) * I)
      = -((1 / Real.sqrt 3 : ℝ) : ℂ) + I := by
    rw [cubicTau_zero]
    push_cast
    simp
  rw [hval] at h
  exact h

theorem ftPrincipal_cubicTau_upper_zero :
    ftPrincipal cubicTau (Real.pi - 0) = -(1 / 2 : ℂ) := by
  rw [sub_zero, ftPrincipal, cubicTau_pi, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
  push_cast
  ring

theorem hasDerivWithinAt_ftPrincipal_upper_zero :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal cubicTau (Real.pi - δ))
      (I / 2) (Set.Ici 0) 0 := by
  have hτ : HasDerivWithinAt (fun δ : ℝ => ((cubicTau (Real.pi - δ) : ℝ) : ℂ))
      ((0 : ℝ) : ℂ) (Set.Ici 0) 0 :=
    hasDerivWithinAt_cubicTauUpper_zero.ofReal_comp
  have hE : HasDerivWithinAt (fun δ : ℝ => Complex.exp (((Real.pi - δ : ℝ) : ℂ) * I))
      (Complex.exp (((Real.pi : ℂ) - 0) * I) * (-1 * I)) (Set.Ici 0) 0 := by
    have hc : HasDerivAt (fun w : ℂ => Complex.exp (((Real.pi : ℂ) - w) * I))
        (Complex.exp (((Real.pi : ℂ) - 0) * I) * (-1 * I)) (0 : ℂ) :=
      ((((hasDerivAt_const (0 : ℂ) (Real.pi : ℂ)).sub (hasDerivAt_id (0 : ℂ))).congr_deriv
        (by ring)).mul_const I).cexp
    have hr := hc.comp_ofReal (z := (0 : ℝ))
    have hfe : (fun y : ℝ => Complex.exp (((Real.pi : ℂ) - ((y : ℝ) : ℂ)) * I))
        = fun δ : ℝ => Complex.exp (((Real.pi - δ : ℝ) : ℂ) * I) := by
      funext y
      push_cast
      ring_nf
    rw [hfe] at hr
    exact hr.hasDerivWithinAt
  have h := hτ.mul hE
  have hval : ((0 : ℝ) : ℂ) * Complex.exp (((Real.pi - 0 : ℝ) : ℂ) * I)
      + ((cubicTau (Real.pi - 0) : ℝ) : ℂ)
          * (Complex.exp (((Real.pi : ℂ) - 0) * I) * (-1 * I))
      = I / 2 := by
    rw [sub_zero, cubicTau_pi, sub_zero, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
    push_cast
    ring
  rw [hval] at h
  exact h

/-! ### The spectral parameter along the branch, as a ratio

`D(γ) = 0` is `(1-γ)³ + zγ = 0`, so `z = -(1-γ)³/γ`.  Every rate `z` needs later
comes out of this and the endpoint derivative, with no expansion of `z` itself. -/

theorem ftPrincipal_cubicTau_ne_zero (θ : ℝ) : ftPrincipal cubicTau θ ≠ 0 := by
  intro h
  have hn : ‖ftPrincipal cubicTau θ‖ = 0 := by rw [h, norm_zero]
  rw [norm_ftPrincipal_cubicTau] at hn
  exact (cubicTau_pos θ).ne' hn

theorem cubicZ_eq_neg_div (θ : ℝ) :
    ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
      = -(1 - ftPrincipal cubicTau θ) ^ 3 / ftPrincipal cubicTau θ := by
  have hγ := ftPrincipal_cubicTau_ne_zero θ
  have hroot := ftDen_cubicQ_eval_ftPrincipal θ
  rw [ftDen_eval, cubicQ_eval, pow_one] at hroot
  rw [eq_div_iff hγ]
  linear_combination hroot

private theorem Ici_zero_diff_singleton : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
  ext x
  simp [lt_iff_le_and_ne, ne_comm]

/-! ### The two cluster directions, as limits

`hEj₀` and `hEp₀` ask for `∂_tD` divided by `δ^{ρ-1} = δ²` along the
nonprincipal member and along the principal branch.  With
`∂_tD(t) = -3(1-t)² + z` both reduce to one slope and the `z`-rate, and the
`z`-rate is free from `z = -(1-γ)³/γ`. -/

theorem eval_derivative_ftDen_cubicQ (zz t : ℂ) :
    (derivative (ftDen cubicQ 1 zz)).eval t = -3 * (1 - t) ^ 2 + zz := by
  rw [eval_derivative_ftDen_formula, cubicQ]
  simp [derivative_pow]

theorem cubicThird_zero : cubicThird 0 = 1 := by
  rw [cubicThird, cubicTau_zero]
  norm_num

theorem hasDerivWithinAt_cubicThird_zero :
    HasDerivWithinAt cubicThird (2 / Real.sqrt 3) (Set.Ici 0) 0 := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hp : HasDerivWithinAt (fun δ : ℝ => cubicTau δ ^ 2)
      ((2 : ℝ) * cubicTau 0 ^ 1 * (-(1 / Real.sqrt 3))) (Set.Ici 0) 0 :=
    hasDerivWithinAt_cubicTau_zero.pow 2
  have hne : cubicTau 0 ^ 2 ≠ 0 := by rw [cubicTau_zero]; norm_num
  have h := (hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0:ℝ)) (1 : ℝ)).div hp hne
  have hval : ((0 : ℝ) * cubicTau 0 ^ 2 - 1 * ((2 : ℝ) * cubicTau 0 ^ 1 * (-(1 / Real.sqrt 3))))
      / (cubicTau 0 ^ 2) ^ 2 = 2 / Real.sqrt 3 := by
    rw [cubicTau_zero]
    field_simp
    ring
  rw [hval] at h
  exact h

theorem tendsto_one_sub_cubicThird_div :
    Filter.Tendsto (fun δ : ℝ => (1 - cubicThird δ) / δ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-(2 / Real.sqrt 3))) := by
  have hd := hasDerivWithinAt_cubicThird_zero
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_zero_diff_singleton] at hd
  refine (hd.neg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [slope_def_field, cubicThird_zero, sub_zero]
  ring

theorem tendsto_one_sub_ftPrincipal_div :
    Filter.Tendsto (fun δ : ℝ => (1 - ftPrincipal cubicTau δ) / (δ : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((1 / Real.sqrt 3 : ℝ) : ℂ) - I)) := by
  have hd := hasDerivWithinAt_ftPrincipal_zero
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_zero_diff_singleton] at hd
  have hlim : -(-((1 / Real.sqrt 3 : ℝ) : ℂ) + I) = ((1 / Real.sqrt 3 : ℝ) : ℂ) - I := by ring
  refine (hlim ▸ hd.neg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : (δ : ℂ) ≠ 0 := by
    simpa using ne_of_gt (Set.mem_Ioi.1 hδ)
  have h0 : ftPrincipal cubicTau 0 = 1 := ftPrincipal_cubicTau_zero
  rw [slope, h0, vsub_eq_sub, sub_zero, Complex.real_smul, Complex.ofReal_inv]
  field_simp
  ring

theorem ftPrincipal_cubicTau_zero' : ftPrincipal cubicTau 0 = 1 :=
  ftPrincipal_cubicTau_zero

theorem tendsto_ftPrincipal_one :
    Filter.Tendsto (fun δ : ℝ => ftPrincipal cubicTau δ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hc := hasDerivWithinAt_ftPrincipal_zero.continuousWithinAt
  rw [ContinuousWithinAt, ftPrincipal_cubicTau_zero'] at hc
  exact hc.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)

theorem tendsto_cubicZ_div_sq :
    Filter.Tendsto (fun δ : ℝ => ((cubicZ (cubicTau δ) δ : ℝ) : ℂ) / (δ : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hc := tendsto_one_sub_ftPrincipal_div
  have hδ : Filter.Tendsto (fun δ : ℝ => ((δ : ℝ) : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
    have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    simpa using this
  have hprod := ((hc.pow 3).neg.mul hδ).div tendsto_ftPrincipal_one one_ne_zero
  have hlimval : -(((1 / Real.sqrt 3 : ℝ) : ℂ) - I) ^ 3 * 0 / 1 = 0 := by simp
  rw [hlimval] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ'
  have hδ0 : (δ : ℂ) ≠ 0 := by simpa using ne_of_gt (Set.mem_Ioi.1 hδ')
  have hγ := ftPrincipal_cubicTau_ne_zero δ
  simp only [Pi.div_apply]
  rw [cubicZ_eq_neg_div]
  field_simp

/-! ### The residue constants

`x₁ = 1`, `ρ = 3`, and `B(1) = 4 ≠ 0`, so `ν_B = 0` and the `B`-legs are plain
continuity: neither carries a power of `δ`, and `jp₀` drops out of them.  The
`∂_tD`-legs carry `δ^{ρ-1} = δ²` and give `c_Q = -3` on both branches, which is
the check that the two legs see the same constant.

The nonprincipal direction is `α = clusterAlpha 1 3 2 = 2/√3`, fixed by
`clusterOmega 3 2 = -1`; the principal one is `clusterAlpha 1 3 0 = -1/√3 + i`,
which is `γ_e` itself.  That coincidence is what pins `jp₀ = 0` -- the index the
`clusterOmega` docstring calls the principal upper branch -- rather than leaving
it a fitted parameter. -/

theorem sin_pi_div_three_nat : Real.sin (Real.pi / ((3 : ℕ) : ℝ)) = Real.sqrt 3 / 2 := by
  norm_num

theorem clusterAlpha_one_three_two : clusterAlpha 1 3 2 = ((2 / Real.sqrt 3 : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by simp
  rw [clusterAlpha, clusterOmega_three_two, sin_pi_div_three_nat]
  push_cast
  field_simp

theorem clusterAlpha_one_three_zero :
    clusterAlpha 1 3 0 = -((1 / Real.sqrt 3 : ℝ) : ℂ) + I := by
  have hp : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hang : clusterAngle 3 0 = -(Real.pi / 3) := by
    rw [clusterAngle]
    push_cast
    ring
  have hom : clusterOmega 3 0 = ((1 / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
    rw [clusterOmega, hang]
    rw [show ((-(Real.pi / 3) : ℝ) : ℂ) * I = ((-(Real.pi / 3) : ℝ) : ℂ) * I from rfl]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show Real.cos (-(Real.pi / 3)) = 1 / 2 by rw [Real.cos_neg, Real.cos_pi_div_three]]
    rw [show Real.sin (-(Real.pi / 3)) = -(Real.sqrt 3 / 2) by
      rw [Real.sin_neg, Real.sin_pi_div_three]]
    push_cast
    ring
  rw [clusterAlpha, hom, sin_pi_div_three_nat]
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by simp
  push_cast
  field_simp
  ring

/-! ### The four residue limits -/

theorem tendsto_cubicThird_one :
    Filter.Tendsto cubicThird (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hc := hasDerivWithinAt_cubicThird_zero.continuousWithinAt
  rw [ContinuousWithinAt, cubicThird_zero] at hc
  exact hc.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)

theorem tendsto_witB_cubicThird :
    Filter.Tendsto (fun δ : ℝ => witB.eval ((cubicThird δ : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 4) := by
  have hc : Filter.Tendsto (fun δ : ℝ => ((cubicThird δ : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp tendsto_cubicThird_one
    simpa [Function.comp_def] using this
  have h := ((hc.pow 2).const_mul (3 : ℂ)).add_const (1 : ℂ)
  have h4 : (3 : ℂ) * 1 ^ 2 + 1 = 4 := by norm_num
  rw [h4] at h
  simpa using h

theorem tendsto_witB_ftPrincipal :
    Filter.Tendsto (fun δ : ℝ => witB.eval (ftPrincipal cubicTau δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 4) := by
  have h := ((tendsto_ftPrincipal_one.pow 2).const_mul (3 : ℂ)).add_const (1 : ℂ)
  have h4 : (3 : ℂ) * 1 ^ 2 + 1 = 4 := by norm_num
  rw [h4] at h
  simpa using h

theorem tendsto_one_sub_cubicThird_div_complex :
    Filter.Tendsto (fun δ : ℝ => (1 - ((cubicThird δ : ℝ) : ℂ)) / (δ : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
  have hr := (Complex.continuous_ofReal.tendsto (-(2 / Real.sqrt 3))).comp
    tendsto_one_sub_cubicThird_div
  refine (by simpa [Function.comp_def] using hr : Filter.Tendsto
    (fun δ : ℝ => (((1 - cubicThird δ) / δ : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-((2 / Real.sqrt 3 : ℝ) : ℂ)))).congr ?_
  intro δ
  push_cast
  ring

theorem tendsto_derivative_cubicThird :
    Filter.Tendsto (fun δ : ℝ =>
        (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ))).eval
          ((cubicThird δ : ℝ) : ℂ) / (δ : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-3 * ((2 / Real.sqrt 3 : ℝ) : ℂ) ^ 2)) := by
  have hsq := (tendsto_one_sub_cubicThird_div_complex.pow 2).const_mul (-3 : ℂ)
  have h := hsq.add tendsto_cubicZ_div_sq
  have hval : (-3 : ℂ) * (-((2 / Real.sqrt 3 : ℝ) : ℂ)) ^ 2 + 0
      = -3 * ((2 / Real.sqrt 3 : ℝ) : ℂ) ^ 2 := by ring
  rw [hval] at h
  refine h.congr ?_
  intro δ
  rw [eval_derivative_ftDen_cubicQ]
  by_cases hδ : (δ : ℂ) = 0
  · rw [hδ]
    simp
  · field_simp

theorem tendsto_derivative_ftPrincipal :
    Filter.Tendsto (fun δ : ℝ =>
        (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ))).eval
          (ftPrincipal cubicTau δ) / (δ : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-3 * (-((1 / Real.sqrt 3 : ℝ) : ℂ) + I) ^ 2)) := by
  have hsq := (tendsto_one_sub_ftPrincipal_div.pow 2).const_mul (-3 : ℂ)
  have h := hsq.add tendsto_cubicZ_div_sq
  have hval : (-3 : ℂ) * (((1 / Real.sqrt 3 : ℝ) : ℂ) - I) ^ 2 + 0
      = -3 * (-((1 / Real.sqrt 3 : ℝ) : ℂ) + I) ^ 2 := by ring
  rw [hval] at h
  refine h.congr ?_
  intro δ
  rw [eval_derivative_ftDen_cubicQ]
  by_cases hδ : (δ : ℂ) = 0
  · rw [hδ]
    simp
  · field_simp

/-! ### The upper retained set, at radius `1`

`cubicWitness_upperRetainedSet_block` separates at `R₁ = 5`, which encloses the
third zero and forces `n₁ = 1`; see the header for why that combination is
refuted rather than merely awkward.  Here the contour is the unit circle, which
encloses the principal pair and nothing else, so the upper cluster is empty. -/

open scoped Classical in
/-- The two denominator zeros inside `‖t‖ ≤ 1` near the upper endpoint. -/
noncomputable def cubicUpperPair (δ : ℝ) : Finset ℂ :=
  {ftPrincipal cubicTau (Real.pi - δ),
   ((cubicTau (Real.pi - δ) : ℝ) : ℂ) * Complex.exp (-((Real.pi - δ : ℝ) : ℂ) * I)}

theorem ftDen_cubicQ_pi_eval (t : ℂ) :
    (ftDen cubicQ 1 ((cubicZ (cubicTau Real.pi) Real.pi : ℝ) : ℂ)).eval t
      = -(t + 1 / 2) ^ 2 * (t - 4) := by
  rw [ftDen_eval, cubicQ_eval, pow_one, cubicZ, cubicTau_pi, Real.cos_pi]
  push_cast
  norm_num
  ring

theorem upperArc {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ Real.pi / 2) :
    Real.pi - δ ∈ Set.Ioo 0 Real.pi := by
  have hpi := Real.pi_pos
  exact ⟨by linarith, by linarith⟩

theorem mem_cubicUpperPair_iff {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ Real.pi / 2) {t : ℂ} :
    t ∈ cubicUpperPair δ ↔ t ∈ cubicRootSet (Real.pi - δ) ∧ ‖t‖ ≤ 1 := by
  classical
  have harc := upperArc hδ hδe
  have hτ1 : cubicTau (Real.pi - δ) < 1 := cubicTau_lt_one harc
  have hτ0 : 0 < cubicTau (Real.pi - δ) := cubicTau_pos _
  have hthird : 1 < cubicThird (Real.pi - δ) := by
    rw [cubicThird, lt_div_iff₀ (by positivity)]
    nlinarith
  have hconj : (starRingEnd ℂ) (ftPrincipal cubicTau (Real.pi - δ))
      = ((cubicTau (Real.pi - δ) : ℝ) : ℂ)
        * Complex.exp (-((Real.pi - δ : ℝ) : ℂ) * I) := conj_ftPrincipal cubicTau _
  have hnp : ‖ftPrincipal cubicTau (Real.pi - δ)‖ = cubicTau (Real.pi - δ) :=
    norm_ftPrincipal_cubicTau _
  constructor
  · intro ht
    simp only [cubicUpperPair, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · refine ⟨?_, by rw [hnp]; linarith⟩
      simp [cubicRootSet, ftPrincipal]
    · refine ⟨?_, ?_⟩
      · simp only [cubicRootSet, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl (by rw [← hconj, ftPrincipal]))
      · rw [← hconj, RCLike.norm_conj, hnp]; linarith
  · rintro ⟨ht, hn⟩
    simp only [cubicRootSet, Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [cubicUpperPair, Finset.mem_insert, Finset.mem_singleton]
    rcases ht with h | h | h
    · exact Or.inl (by rw [h, ftPrincipal])
    · exact Or.inr (by rw [h, ← hconj, ftPrincipal])
    · exfalso
      rw [h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_trans hτ0 (cubicTau_lt_cubicThird harc))] at hn
      linarith

theorem cubicUpper_root {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ Real.pi / 2) :
    ∀ a ∈ cubicUpperPair δ,
      (ftDen cubicQ 1 ((cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ) : ℝ) : ℂ)).eval a = 0 :=
  fun a ha => (mem_cubicRootSet_iff (upperArc hδ hδe)).1
    ((mem_cubicUpperPair_iff hδ hδe).1 ha).1

theorem cubicUpper_simple {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ Real.pi / 2) :
    ∀ a ∈ cubicUpperPair δ,
      (derivative (ftDen cubicQ 1
        ((cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ) : ℝ) : ℂ))).eval a ≠ 0 :=
  fun a ha => derivative_ftDen_cubicQ_ne_zero (upperArc hδ hδe)
    ((mem_cubicUpperPair_iff hδ hδe).1 ha).1

theorem cubicUpper_norm_lt {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ Real.pi / 2) :
    ∀ a ∈ cubicUpperPair δ, ‖a‖ < 1 := by
  classical
  intro a ha
  have hτ1 : cubicTau (Real.pi - δ) < 1 := cubicTau_lt_one (upperArc hδ hδe)
  have hnp : ‖ftPrincipal cubicTau (Real.pi - δ)‖ = cubicTau (Real.pi - δ) :=
    norm_ftPrincipal_cubicTau _
  have hconj : (starRingEnd ℂ) (ftPrincipal cubicTau (Real.pi - δ))
      = ((cubicTau (Real.pi - δ) : ℝ) : ℂ)
        * Complex.exp (-((Real.pi - δ : ℝ) : ℂ) * I) := conj_ftPrincipal cubicTau _
  simp only [cubicUpperPair, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · rw [hnp]; exact hτ1
  · rw [← hconj, RCLike.norm_conj, hnp]; exact hτ1

theorem cubicUpper_card {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ Real.pi / 2) :
    (((cubicUpperPair δ).erase (ftPrincipal cubicTau (Real.pi - δ))).erase
      (((cubicTau (Real.pi - δ) : ℝ) : ℂ)
        * Complex.exp (-((Real.pi - δ : ℝ) : ℂ) * I))).card = 0 := by
  classical
  rw [Finset.card_eq_zero]
  ext x
  simp only [cubicUpperPair, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, iff_false]
  tauto

/-! ### The two contours carry no zero

The theorem takes the contour bound **punctured** -- `hCbd₀`/`hCbd₁` quantify
over `0 < δ`, because `z` is unbounded at an upper endpoint and no closed-window
form can hold there.  These two lemmas are nonetheless stated on the **closed**
window, `δ = 0` included, and that is what makes the punctured binder
satisfiable here rather than merely stated: `exists_uniform_ftDiv_bound`
produces the constant by compactness on `Icc 0 e × sphere`, which is compact
only with the endpoint included, and needs the denominator nonvanishing there.

So the `δ = 0` case is doing work, and it costs a separate argument at each end,
because the retained set's own uniqueness clause is not available at the
endpoint.  At the lower one `z(0) = 0` and the denominator collapses to
`(1-t)^3`, whose only zero is `1`; at the upper it factors as
`-(t + 1/2)^2(t - 4)`, the principal pair having coalesced.  Neither meets its
contour.

A pencil whose denominator degenerated at `δ = 0` would meet the punctured
binder as stated and still need a different route to the constant. -/

theorem cubicLower_sphere {R₀ e₀ : ℝ} (hR₀ : 1 < R₀)
    (huniq : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ)).eval t = 0 → t ∈ cubicRootSet δ)
    (haR : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ cubicRootSet δ, ‖a‖ < R₀) :
    ∀ δ ∈ Set.Icc (0 : ℝ) e₀, ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ)).eval t ≠ 0 := by
  intro δ hδ t ht hev
  rw [Metric.mem_sphere, dist_zero_right] at ht
  rcases eq_or_lt_of_le hδ.1 with h | h
  · rw [← h, cubicZ_zero] at hev
    rw [ftDen_eval, cubicQ_eval, pow_one] at hev
    have h1 : t = 1 := by
      have : (1 - t) ^ 3 = 0 := by simpa using hev
      have := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this
      linear_combination -this
    rw [h1] at ht
    simp at ht
    linarith
  · have hmem := huniq δ h hδ.2 t (le_of_eq ht) hev
    have := haR δ h hδ.2 t hmem
    rw [ht] at this
    exact absurd this (lt_irrefl _)

theorem cubicUpper_sphere :
    ∀ δ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ t ∈ Metric.sphere (0 : ℂ) 1,
      (ftDen cubicQ 1
        ((cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ) : ℝ) : ℂ)).eval t ≠ 0 := by
  intro δ hδ t ht hev
  rw [Metric.mem_sphere, dist_zero_right] at ht
  rcases eq_or_lt_of_le hδ.1 with h | h
  · rw [← h, sub_zero, ftDen_cubicQ_pi_eval] at hev
    rcases mul_eq_zero.1 hev with h1 | h1
    · have h2 : t = -(1 / 2) := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (neg_eq_zero.1 h1)
        linear_combination this
      rw [h2] at ht
      rw [show (-(1 / 2) : ℂ) = ((-(1/2) : ℝ) : ℂ) by norm_num, Complex.norm_real] at ht
      rw [Real.norm_eq_abs] at ht
      norm_num at ht
    · have h2 : t = 4 := by linear_combination h1
      rw [h2] at ht
      norm_num at ht
  · have hmem := (mem_cubicUpperPair_iff h hδ.2).2
      ⟨(mem_cubicRootSet_iff (upperArc h hδ.2)).2 hev, le_of_eq ht⟩
    have := cubicUpper_norm_lt h hδ.2 t hmem
    rw [ht] at this
    exact absurd this (lt_irrefl _)

theorem tendsto_derivative_cubicThird_shape (i : Fin 1) :
    Filter.Tendsto (fun δ : ℝ =>
        (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ))).eval
          (cubicNonprincipal δ i) / ((δ : ℝ) : ℂ) ^ ((((3 : ℕ) - 1 : ℕ)) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((-3 : ℂ) * clusterAlpha 1 3 2 ^ ((3 : ℕ) - 1))) := by
  have h := tendsto_derivative_cubicThird
  rw [← clusterAlpha_one_three_two] at h
  exact h

theorem tendsto_derivative_ftPrincipal_shape :
    Filter.Tendsto (fun δ : ℝ =>
        (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ))).eval
          (ftPrincipal cubicTau δ) / ((δ : ℝ) : ℂ) ^ ((((3 : ℕ) - 1 : ℕ)) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((-3 : ℂ) * clusterAlpha 1 3 0 ^ ((3 : ℕ) - 1))) := by
  have h := tendsto_derivative_ftPrincipal
  rw [← clusterAlpha_one_three_zero] at h
  exact h

/-! ### The composition

Every binder of `weighted_dominance_of_branch` supplied at once, so its
conclusion holds with nothing left assumed.  What this settles is *joint*
satisfiability: a per-binder check cannot see a pair that cannot hold together,
and three defects in this tree were exactly that.

`n₁ = 0`: the upper cluster is empty at `r = 1`, so `hL₁`, `hratio₁`, `hωne₁`,
`hωne'₁` and `hexp₁` are discharged by `Fin.elim0`.  They are met, not tested. -/

theorem cubic_weighted_dominance :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ Real.pi - h / M → θ ∉ cubicTheta M →
        ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
          ≤ ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ')
              cubicTau θ / 2 := by
  classical
  have hpi := Real.pi_pos
  obtain ⟨R₀, τmax₀, eR, hR₀, hσR, heR, heRπ, hτposR, hτleR, hrootR, hsimpleR, haRR,
    huniqR, hrootplusR⟩ := cubicWitness_retainedSet_block
  obtain ⟨eC, Cexp₀, heC, heCπ, hCexp₀, hginjC, hgmemC, hgcardC, hexpC⟩ :=
    cubicWitness_cluster_block
  -- one window for both blocks
  set e₀ : ℝ := min eR eC with he₀def
  have he₀ : 0 < e₀ := lt_min heR heC
  have he₀R : e₀ ≤ eR := min_le_left _ _
  have he₀C : e₀ ≤ eC := min_le_right _ _
  have he₀π : e₀ < Real.pi := lt_of_le_of_lt he₀R heRπ
  -- the separating radius clears the unit circle, which is what `δ = 0` needs
  have hR₀1 : 1 < R₀ := by
    have hmem : ((cubicThird eR : ℝ) : ℂ) ∈ cubicRootSet eR := by simp [cubicRootSet]
    have h1 := haRR eR heR le_rfl _ hmem
    have hτ1 : cubicTau eR < 1 := cubicTau_lt_one ⟨heR, heRπ⟩
    have hτ0 : 0 < cubicTau eR := cubicTau_pos _
    have h3 : 1 < cubicThird eR := by
      rw [cubicThird, lt_div_iff₀ (by positivity)]
      nlinarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
    linarith
  have hsubIoo : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → δ ∈ Set.Ioo 0 Real.pi :=
    fun δ hδ hδe => ⟨hδ, lt_of_le_of_lt hδe he₀π⟩
  -- `r = 1`: the upper endpoint datum is nonzero, so the FINITE route applies.
  -- `weighted_dominance_of_branch` no longer chooses a route, so the endpoint
  -- group lives here, discharging the amplitude bound it always produced.
  obtain ⟨A₁, hA₁, hamp₁⟩ :=
    ftPrincipalAmp_lower_bound (Q := cubicQ) (B := witB) (r := 1)
      (z := fun θ => cubicZ (cubicTau θ) θ) (τ := cubicTau)
      (w := fun δ => Real.pi - δ) (te := ftPrincipal cubicTau (Real.pi - 0))
      (γe := I / 2) witB_ne_zero le_rfl
      (by rw [ftPrincipal_cubicTau_upper_zero]; norm_num)
      (by
        intro h
        have := congrArg Complex.im h
        simp at this)
      rfl hasDerivWithinAt_ftPrincipal_upper_zero
      (by
        intro h
        have := natDegree_ftDen_cubicQ
          ((cubicZ (cubicTau (Real.pi - 0)) (Real.pi - 0) : ℝ) : ℂ)
        rw [h] at this
        simp at this)
      (by
        have hne : ftDen cubicQ 1
            ((cubicZ (cubicTau (Real.pi - 0)) (Real.pi - 0) : ℝ) : ℂ) ≠ 0 := by
          intro h
          have := natDegree_ftDen_cubicQ
            ((cubicZ (cubicTau (Real.pi - 0)) (Real.pi - 0) : ℝ) : ℂ)
          rw [h] at this
          simp at this
        exact (rootMultiplicity_pos hne).2
          (ftDen_cubicQ_eval_ftPrincipal (Real.pi - 0)))
      (Filter.Eventually.of_forall fun δ =>
        ftDen_cubicQ_eval_ftPrincipal (Real.pi - δ))
  -- the contour constants: compactness on the closed window is how `r = 1` proves
  -- the punctured bound the theorem takes.
  obtain ⟨C₀, hC₀, hCbdI₀⟩ :=
    exists_uniform_ftDiv_bound (Q := cubicQ) (B := witB) (r := 1) (R₀ := R₀)
      (z := fun θ => cubicZ (cubicTau θ) θ) (a := 0) (b := e₀)
      (Complex.continuous_ofReal.comp continuous_cubicZ_branch).continuousOn
      (cubicLower_sphere hR₀1
        (fun δ hδ hδe => huniqR δ hδ (le_trans hδe he₀R))
        (fun δ hδ hδe => haRR δ hδ (le_trans hδe he₀R)))
  obtain ⟨C₁, hC₁, hCbdI₁⟩ :=
    exists_uniform_ftDiv_bound (Q := cubicQ) (B := witB) (r := 1) (R₀ := 1)
      (z := fun δ => cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ))
      (a := 0) (b := Real.pi / 2)
      (((Complex.continuous_ofReal.comp continuous_cubicZ_branch).comp
        (continuous_const.sub continuous_id)).continuousOn)
      cubicUpper_sphere
  have hCbd₀ := fun δ (hδ : 0 < δ) hδe t ht => hCbdI₀ δ ⟨hδ.le, hδe⟩ t ht
  have hCbd₁ := fun δ (hδ : 0 < δ) hδe t ht => hCbdI₁ δ ⟨hδ.le, hδe⟩ t ht
  exact weighted_dominance_of_branch
    (Q := cubicQ) (B := witB) (r := 1) (b := Real.pi)
    (z := fun θ => cubicZ (cubicTau θ) θ) (τ := cubicTau) (Θ := cubicTheta)
    (n₀ := 1) (n₁ := 0) (g₀ := cubicNonprincipal) (g₁ := fun _ => Fin.elim0)
    (sfun₀ := cubicRootSet) (sfun₁ := cubicUpperPair)
    (x₁ := 1) (ρ := 3)
    (te₀ := 1) (γe₀ := -((1 / Real.sqrt 3 : ℝ) : ℂ) + I)
    (idx₀ := fun _ => 2) (jp₀ := 0) (νB₀ := 0) (cB₀ := 4) (cQ₀ := -3)
    (R₀ := R₀) (τmax₀ := τmax₀) (σ₀ := τmax₀ / R₀) (e₀ := e₀) (Cexp₀ := Cexp₀)
    (idx₁ := Fin.elim0) (L₁ := Fin.elim0)
    (R₁ := 1) (τmax₁ := cubicTau (Real.pi / 2)) (σ₁ := cubicTau (Real.pi / 2))
    (e₁ := Real.pi / 2) (Cexp₁ := 0)
    (hQ := hasRealCoeffs_cubicQ) (hB := hasRealCoeffs_witB) (hB0 := witB_ne_zero)
    (hr := le_rfl) (hQ0 := cubicQ_eval_zero_ne)
    (hx₁ := one_pos) (hρ := by norm_num)
    (hte₀ := one_ne_zero)
    (hγe₀ := by
      intro h
      have him := congrArg Complex.im h
      simp at him)
    (hγ0₀ := ftPrincipal_cubicTau_zero')
    (hγd₀ := hasDerivWithinAt_ftPrincipal_zero)
    (hk₀ := by
      have hne : ftDen cubicQ 1 ((cubicZ (cubicTau 0) 0 : ℝ) : ℂ) ≠ 0 := by
        intro h
        have := natDegree_ftDen_cubicQ ((cubicZ (cubicTau 0) 0 : ℝ) : ℂ)
        rw [h] at this
        simp at this
      have hroot : (ftDen cubicQ 1 ((cubicZ (cubicTau 0) 0 : ℝ) : ℂ)).IsRoot 1 := by
        have := ftDen_cubicQ_eval_ftPrincipal 0
        rwa [ftPrincipal_cubicTau_zero'] at this
      exact (rootMultiplicity_pos hne).2 hroot)
    (hrootev₀ := Filter.Eventually.of_forall fun δ => ftDen_cubicQ_eval_ftPrincipal δ)
    (hcB₀ := by norm_num) (hcQ₀ := by norm_num)
    (hBj₀ := fun i => by simpa [cubicNonprincipal] using tendsto_witB_cubicThird)
    (hBp₀ := by simpa using tendsto_witB_ftPrincipal)
    (hEj₀ := tendsto_derivative_cubicThird_shape)
    (hEp₀ := tendsto_derivative_ftPrincipal_shape)
    (hR₀ := hR₀) (hσ₀ := le_rfl) (hσ₀1 := hσR) (he₀ := he₀)
    (hτpos₀ := fun δ hδ hδe => hτposR δ hδ (le_trans hδe he₀R))
    (hτle₀ := fun δ hδ hδe => hτleR δ hδ (le_trans hδe he₀R))
    (hroot₀ := fun δ hδ hδe => hrootR δ hδ (le_trans hδe he₀R))
    (hsimple₀ := fun δ hδ hδe => hsimpleR δ hδ (le_trans hδe he₀R))
    (haR₀ := fun δ hδ hδe => haRR δ hδ (le_trans hδe he₀R))
    (huniq₀ := fun δ hδ hδe => huniqR δ hδ (le_trans hδe he₀R))
    (hrootplus₀ := fun δ hδ hδe => ftDen_cubicQ_eval_ftPrincipal δ)
    (hne₀ := fun δ hδ hδe => by
      rw [← conj_ftPrincipal cubicTau δ]
      exact cubic_pair_ne (hsubIoo δ hδ hδe))
    (hginj₀ := fun δ hδ hδe => hginjC δ hδ (le_trans hδe he₀C))
    (hgmem₀ := fun δ hδ hδe i => by
      have := hgmemC δ hδ (le_trans hδe he₀C) i
      rwa [← conj_ftPrincipal cubicTau δ])
    (hgcard₀ := fun δ hδ hδe => by
      have := hgcardC δ hδ (le_trans hδe he₀C)
      rwa [← conj_ftPrincipal cubicTau δ])
    (hC₀ := hC₀) (hCbd₀ := hCbd₀)
    (hCexp₀ := hCexp₀)
    (hωne₀ := fun i => by
      rw [clusterOmega_three_two]
      intro h
      have := congrArg Complex.re h
      rw [Complex.exp_ofReal_mul_I_re] at this
      norm_num at this)
    (hωne'₀ := fun i => by
      rw [clusterOmega_three_two]
      intro h
      have := congrArg Complex.re h
      rw [Complex.exp_ofReal_mul_I_re] at this
      norm_num at this)
    (hexp₀ := fun i δ hδ hδe => hexpC i δ hδ (le_trans hδe he₀C))
    (hA₁ := hA₁) (hamp₁ := hamp₁)
    (hn₁r := fun h => absurd h (lt_irrefl 0))
    (hL₁ := fun i => i.elim0)
    (hratio₁ := fun i => i.elim0)
    (hR₁ := one_pos) (hσ₁ := by rw [div_one]) (hσ₁1 := cubicTau_lt_one ⟨by linarith, by linarith⟩)
    (he₁ := by linarith)
    (hτpos₁ := fun δ hδ hδe => cubicTau_pos _)
    (hτle₁ := fun δ hδ hδe => by
      rcases eq_or_lt_of_le hδe with h | h
      · rw [h, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
      · exact (cubicTau_strictAntiOn ⟨by linarith, by linarith⟩
          ⟨by linarith, by linarith⟩ (by linarith)).le)
    (hroot₁ := fun δ hδ hδe => cubicUpper_root hδ hδe)
    (hsimple₁ := fun δ hδ hδe => cubicUpper_simple hδ hδe)
    (haR₁ := fun δ hδ hδe => cubicUpper_norm_lt hδ hδe)
    (huniq₁ := fun δ hδ hδe t ht hev => (mem_cubicUpperPair_iff hδ hδe).2
      ⟨(mem_cubicRootSet_iff (upperArc hδ hδe)).2 hev, ht⟩)
    (hrootplus₁ := fun δ hδ hδe => ftDen_cubicQ_eval_ftPrincipal (Real.pi - δ))
    (hne₁ := fun δ hδ hδe => by
      rw [← conj_ftPrincipal cubicTau (Real.pi - δ)]
      exact cubic_pair_ne (upperArc hδ hδe))
    (hginj₁ := fun δ hδ hδe a => a.elim0)
    (hgmem₁ := fun δ hδ hδe i => i.elim0)
    (hgcard₁ := fun δ hδ hδe => cubicUpper_card hδ hδe)
    (hC₁ := hC₁) (hCbd₁ := hCbd₁)
    (hCexp₁ := le_rfl)
    (hωne₁ := fun i => i.elim0)
    (hωne'₁ := fun i => i.elim0)
    (hexp₁ := fun i => i.elim0)
    (hinterior := cubicWitness_hinterior)

end ForgacsTran
