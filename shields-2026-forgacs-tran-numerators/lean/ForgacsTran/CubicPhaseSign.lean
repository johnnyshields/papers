/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.CubicWitnessComposition
import ForgacsTran.ClauseThree
import ForgacsTran.ClauseThreeComposition

/-!
# The sign at a phase point, at the cubic pencil

`ClauseThree.exists_phaseZeros` counts the zeros of a real coefficient
polynomial on one component of `eq:Omega-M`, and takes the analytic supply as
one binder, `hsign`: at every point where the phase meets `πℤ`, the coefficient
carries the sign `eq:principal-decomposition` predicts.  Its own docstring says
that binder is *exactly* what `thm:weighted-dominance` delivers.

`cubic_weighted_dominance` now delivers it unconditionally at `Q = (1-t)^3`,
`r = 1`, `B = 3t^2 + 1`, so `hsign` is dischargeable there rather than assumed.
This module builds toward that.

## Why a real polynomial has to be produced

`hsign` is stated for `P : Polynomial ℝ`, while the coefficient this development
carries is `ftCoeffPoly : ℂ[X]`.  The two are the same object only because `Q`
and `B` have real coefficients, and `HasRealCoeffs` says that as a fixed-point
condition on `starRingEnd` rather than as a preimage.  So the first thing needed
is the descent: a `HasRealCoeffs` polynomial is the image of a real one.

`Amplitude` carries that descent and the closure it rests on:
`hasRealCoeffs_iff_mem_lifts` identifies `HasRealCoeffs` with membership in
`Polynomial.lifts (algebraMap ℝ ℂ)`, which is a `Subsemiring` and so closed under
sums, products and finite sums.  `ftCoeffPoly` is a strong recursion built from
exactly those, so what is consumed here is that closure.

## What is left, and what it costs

`ClauseThree.exists_phaseZeros` takes five binders, and **all five are
discharged at this pencil** -- `hsign` and `hz` here, the sign step in
`ClauseThreeComposition`, the dominance bound in `CubicWitnessComposition`, and
`hΦc`/`hΦm` in `CubicPhaseDerivative`.  `cubic_exists_phaseZeros` applies the
theorem with them, so the phase count holds here with no analytic hypothesis.

`hz` was elementary because `z` depends on `τ` alone; see `cubicZ_eq_cubicZofTau`.
The same turned out to be true of the phase derivative, which is why
`eq:phase-derivative-bound` came out as a constant rather than a subarc-dependent
estimate: `ψ = arg 𝒜` with `𝒜 = -B(γ)/∂_tD(γ)` and `γ = τe^{iθ}`, and eliminating
the angle through the branch relation leaves `Im(𝒜'/𝒜)` rational in `τ`.  That
uniformity is what the composition needs -- a bound that moved with the subarc
would have to be chosen after `M`, while the retained range shrinks with `M`.

## Three traps this module paid for

**The general sign step already existed**, as
`ClauseThreeComposition.sign_at_phase_point_of_ftDominance`.  A search for the
names it might carry finds nothing; what finds it is its conclusion shape,
`0 < stripSign k * P.eval`.

**`interior_cos_decomposition_on_subarc` is the wrong door.**  The wrapper asks
for a *geometric* remainder bound `|R_M| ≤ C·σ^M`, which is strictly more than
`thm:weighted-dominance` delivers; the primitive `interior_cos_decomposition`
bounds its error by `ftRemainder/(2·ftPrincipalAmp)`, which is exactly what the
dominance theorem proves.  A chain built through the wrapper acquires a
hypothesis nobody needs.

**`exists_real_ftCoeffPoly` is taken**, by a pencil-specific version in
`ClauseThreeQuadraticRay`.  The name clash is what revealed that a special case
existed and that the general form here subsumes it -- a build error answering a
question nobody had asked.

-/

namespace ForgacsTran

open Polynomial Complex

/-! ### The coefficient polynomials are real

`ftDenCoeff` is a constant plus `X` in one slot, and `ftCoeffPoly` is a strong
recursion over sums and products of those, so both descend from the closure
above -- the induction is `Nat.strong_induction_on` because the recursion reads
every earlier index. -/

theorem hasRealCoeffs_ftDenCoeff {Q : Polynomial ℂ} (hQ : HasRealCoeffs Q) (r j : ℕ) :
    HasRealCoeffs (ftDenCoeff Q r j) := by
  rw [ftDenCoeff]
  rcases eq_or_ne j r with rfl | hj
  · simpa using (hQ.C_coeff j).add hasRealCoeffs_X
  · simpa [hj] using hQ.C_coeff j

theorem hasRealCoeffs_ftCoeffPoly {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) (r : ℕ) : ∀ M : ℕ, HasRealCoeffs (ftCoeffPoly Q B r M) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rw [ftCoeffPoly_eq]
    refine (hQ.C_inv_coeff 0).mul ((hB.C_coeff M).sub (HasRealCoeffs.sum ?_))
    intro i hi
    exact (hasRealCoeffs_ftDenCoeff hQ r (M - i)).mul (ih i (Finset.mem_range.1 hi))

/-! ### The real polynomial `hsign` quantifies over

`ClauseThree.exists_phaseZeros` and the sign step that feeds it
(`ClauseThreeComposition.sign_at_phase_point_of_ftDominance`) are stated for a
`P : Polynomial ℝ` with `P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M`.  Every
site in this tree either takes that as a hypothesis or builds it **by hand at
one pencil** -- `ClauseThreeWitness.witPpow`, `ClauseThreeRayRemainder`'s
quadratic constructions.  Nothing produced it in general.

This does, for any `Q` and `B` with real coefficients, which is where the
`lifts` route pays: `ftCoeffPoly` is a strong recursion over products and finite
sums, and `lifts` is a `Subsemiring`, so the closure the equivalence gives is
exactly what the induction consumes.

`ClauseThreeQuadraticRay.exists_real_ftCoeffPoly` is the special case
`Q = quadPoly q₀ q₁ q₂`, `B = 1`, `r = 2`, built through an explicit range
argument; it is a candidate for retirement against this one. -/

theorem exists_real_ftCoeffPoly_of_real {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) (r M : ℕ) :
    ∃ P : Polynomial ℝ, P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M :=
  (hasRealCoeffs_ftCoeffPoly hQ hB r M).exists_real

/-- The family form, which is what `MainComposition`'s `hPmap` asks for: one
real polynomial per index, chosen together. -/
theorem exists_real_ftCoeffPoly_family_of_real {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) (r : ℕ) :
    ∃ Pr : ℕ → Polynomial ℝ, ∀ M, (Pr M).map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M :=
  ⟨fun M => (exists_real_ftCoeffPoly_of_real hQ hB r M).choose,
   fun M => (exists_real_ftCoeffPoly_of_real hQ hB r M).choose_spec⟩
/-! ### `hsign` at the cubic pencil

`ClauseThree.exists_phaseZeros`'s analytic binder, discharged rather than
assumed at `Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1`.

Two things make it go through, and both are the retained set doing work.
`cubic_weighted_dominance` bounds the remainder only off `cubicTheta M`, and
that same deletion is what keeps the amplitude away from its own zero: `B`
vanishes on the branch exactly at `θ = π/2`, and `cubicTheta M` deletes
`|θ - π/2| < 1` at every `M`.  So on the retained range the amplitude is
nonzero **for the same reason** the remainder is small, and neither has to be
assumed separately.

**Differs from the paper's route.**  `subsec:proof` keeps the amplitude's zero
set and the deletion apart -- the windows are sized by the remainder and the
divisor is handled by `lem:amplitude-divisor` -- while here one deletion serves
both, because the compatibility wrapper `weighted_dominance_of_branch` binds
`Θ` ahead of `hinterior`'s per-epsilon quantifier and so forces an
`M`-independent window wide enough to contain the divisor.  That is a
consequence of the wrapper's binder order, recorded in `CubicWitnessInterior`,
and not a simplification of the argument -- the `_at` forms bind `Θ` after `ε`
and would not force it.

**Searching by name is not searching.**  The general sign step this consumes
already existed as `ClauseThreeComposition.sign_at_phase_point_of_ftDominance`,
and a search for the names it would plausibly carry found nothing, because it
carries a different one.  What finds it is its **conclusion shape**,
`0 < stripSign k * P.eval`.  The house rule against name-searching Mathlib
applies to this tree with equal force: at 89 modules nobody holds the name space
in their head, and the second proof of a proved result costs a reader a decision
every time they meet both. -/

theorem cubic_hsign {u v : ℝ} (M : ℕ) {ψ : ℝ → ℝ}
    (hpolar : ∀ θ : ℝ, ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
        (ftPrincipal cubicTau θ)
      = ((ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ : ℝ) : ℂ)
        * Complex.exp ((ψ θ : ℂ) * Complex.I))
    {P : Polynomial ℝ} (hP : P.map (algebraMap ℝ ℂ) = ftCoeffPoly cubicQ witB 1 M)
    (harc : ∀ θ ∈ Set.Icc u v, θ ∈ Set.Ioo 0 Real.pi)
    (hoff : ∀ θ ∈ Set.Icc u v, θ ∉ cubicTheta M)
    (hdom : ∀ θ ∈ Set.Icc u v,
      ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
        ≤ ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ / 2) :
    ∀ θ ∈ Set.Icc u v, ∀ k : ℤ,
      ((M : ℝ) + 1) * θ - ψ θ = (k : ℝ) * Real.pi →
        0 < stripSign k * P.eval (cubicZ (cubicTau θ) θ) := by
  intro θ hθ k hphase
  -- the deleted window is what keeps the amplitude off its own zero
  have hne : θ ≠ Real.pi / 2 := by
    intro h
    refine hoff θ hθ ?_
    rw [mem_cubicTheta, h]
    simp
  have hWne : ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
      (ftPrincipal cubicTau θ) ≠ 0 := by
    intro h
    exact hne ((ftAmp_witB_eq_zero_iff (harc θ hθ)).1 h)
  exact sign_at_phase_point_of_ftDominance hP (cubicTau_pos θ) hWne (hpolar θ)
    (hdom θ hθ) hphase

/-! ### `hz`: the spectral parameter is strictly increasing along the arc

`exists_phaseZeros` asks for `z` strictly monotone on the subarc, and at this
pencil that reduces to one identity: **`z` is a function of `τ` alone.**  The
branch relation `2τ³cos θ = 3τ² - 1` eliminates `cos θ` from
`z = 3 - τ² - 2cos θ/τ`, leaving

`z = 3 - τ² - 3/τ² + 1/τ⁴`

with no `θ` in it.  Then `z` is strictly increasing in `θ` because `τ` is
strictly decreasing in `θ` and this is strictly decreasing in `τ`, and the second
is a factorization rather than an estimate:

`d/dτ = -2(τ² - 1)²(τ² + 2)/τ⁵`

which is negative on `(0,1)` and vanishes only at `τ = 1`, the lower endpoint,
where the branch meets `t_a`.

**The double factor is not a coincidence of the algebra.**  `(τ²-1)²` is the
same degeneracy `cubicTau_endpoint_identity` records -- the collision at
`θ = 0` is quadratic from both sides -- and it is why `z` leaves `0` at order
`θ³`.  So `ρ = 3`, the multiplicity of `Q`'s smallest zero, the stationary point
of `z(τ)` at `τ = 1`, and the cubic vanishing rate of `z` are **one fact seen
three ways**: `Q = (1-t)^3` forces the branch to reach `t_a = 1` with a double
contact, that contact is the vanishing of `dz/dτ`, and integrating it against
`τ = 1 - θ/√3 + O(θ²)` gives the cube.

That matters for reading the rest of this pencil.  A reader meeting `z ≍ θ³`
elsewhere -- in `tendsto_cubicZ_div_sq`, or in `hEj₀`'s `z/δ² → 0` -- should not
take it as an accident to be re-measured at each site; it is `ρ` showing through
in a different coordinate, and at a pencil with a different `ρ` the exponent
moves with it. -/

/-- The spectral parameter as a function of the branch modulus alone. -/
noncomputable def cubicZofTau (t : ℝ) : ℝ := 3 - t ^ 2 - 3 / t ^ 2 + 1 / t ^ 4

theorem cubicZ_eq_cubicZofTau (θ : ℝ) :
    cubicZ (cubicTau θ) θ = cubicZofTau (cubicTau θ) := by
  have hτ : 0 < cubicTau θ := cubicTau_pos θ
  have hbr := cubicTau_branch θ
  rw [cubicZ, cubicZofTau]
  field_simp
  nlinarith [hbr, hτ, sq_nonneg (cubicTau θ)]

theorem hasDerivAt_cubicZofTau {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt cubicZofTau (-2 * (t ^ 2 - 1) ^ 2 * (t ^ 2 + 2) / t ^ 5) t := by
  have h1 : HasDerivAt (fun x : ℝ => 3 - x ^ 2) (-(2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_sub 3)
  have h2 : HasDerivAt (fun x : ℝ => 3 / x ^ 2)
      ((0 * t ^ 2 - 3 * (2 * t ^ 1)) / (t ^ 2) ^ 2) t :=
    (hasDerivAt_const t 3).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht)
  have h3 : HasDerivAt (fun x : ℝ => 1 / x ^ 4)
      ((0 * t ^ 4 - 1 * (4 * t ^ 3)) / (t ^ 4) ^ 2) t :=
    (hasDerivAt_const t 1).div (hasDerivAt_pow 4 t) (pow_ne_zero 4 ht)
  have h := (h1.sub h2).add h3
  have hval : -(2 * t) - (0 * t ^ 2 - 3 * (2 * t ^ 1)) / (t ^ 2) ^ 2
      + (0 * t ^ 4 - 1 * (4 * t ^ 3)) / (t ^ 4) ^ 2
      = -2 * (t ^ 2 - 1) ^ 2 * (t ^ 2 + 2) / t ^ 5 := by
    field
  rw [hval] at h
  exact h

theorem cubicZofTau_strictAntiOn : StrictAntiOn cubicZofTau (Set.Ioc 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 1) ?_ ?_
  · refine ContinuousOn.sub (ContinuousOn.sub continuousOn_const
      (continuousOn_pow 2)) ?_ |>.add ?_
    · exact continuousOn_const.div (continuousOn_pow 2) fun x hx => pow_ne_zero 2 (ne_of_gt hx.1)
    · exact continuousOn_const.div (continuousOn_pow 4) fun x hx => pow_ne_zero 4 (ne_of_gt hx.1)
  · intro t ht
    rw [interior_Ioc] at ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    rw [(hasDerivAt_cubicZofTau (ne_of_gt ht0)).deriv]
    have hne : (t ^ 2 - 1) ^ 2 > 0 := by
      have h : t ^ 2 - 1 ≠ 0 := by nlinarith
      exact pow_two_pos_of_ne_zero h
    have h5 : 0 < t ^ 5 := by positivity
    have : 0 < 2 * (t ^ 2 - 1) ^ 2 * (t ^ 2 + 2) := by positivity
    rw [div_neg_iff]
    right
    constructor <;> nlinarith

/-- **`hz` at the witness.**  `z` is strictly increasing along the arc, being a
strictly decreasing function of a strictly decreasing one. -/
theorem cubicZ_strictMonoOn :
    StrictMonoOn (fun θ => cubicZ (cubicTau θ) θ) (Set.Icc 0 Real.pi) := by
  intro a ha b hb hab
  have hmem : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, cubicTau θ ∈ Set.Ioc 0 1 :=
    fun θ _ => ⟨cubicTau_pos θ, cubicTau_le_one θ⟩
  have hlt : cubicTau b < cubicTau a := cubicTau_strictAntiOn ha hb hab
  change cubicZ (cubicTau a) a < cubicZ (cubicTau b) b
  rw [cubicZ_eq_cubicZofTau, cubicZ_eq_cubicZofTau]
  exact cubicZofTau_strictAntiOn (hmem b hb) (hmem a ha) hlt

end ForgacsTran
