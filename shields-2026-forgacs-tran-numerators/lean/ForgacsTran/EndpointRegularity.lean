/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Geometry

/-!
# Endpoint regularity of the principal branch

**What is imported and what is proved.**  The *existence* of the principal branch
near an endpoint, and its analyticity there, are `Forgacs2017RationalDenominator`
Prop. 3, which the paper cites; every theorem below takes that as the explicit
hypothesis `HasDerivAt γ γ_e 0` together with `γ_e ≠ 0`.  What the paper extracts
for itself — and what is proved here — is the *order* statement: the exponent `k`
in `eq:z-endpoint-order` is the multiplicity of the endpoint collision, and the
leading coefficient is nonzero.

**The parameter is real and one-sided.**  `δ` is the angular distance to the
endpoint, a real variable, and the sign of `z - z_e` is carried by the complex
coefficient `c`.  There is deliberately no complex `v` with `v^k = z - z_e`
anywhere: at a finite upper endpoint that parameter is imaginary and `dt/dv`
comes out real for a nonreal branch, so a development built on it would typecheck
and say nothing about the branch.

## Main statements

* `endpoint_root_identity` — `(t - t_e)^k G(t) = -(z - z_e) t^r`, exact at any
  denominator zero.  Everything below is this identity plus continuity.
* `z_endpoint_order` — `eq:z-endpoint-order`.
* `exists_infiniteEndpoint_form` — `eq:principal-infinite-endpoint-regularity`,
  `γ = ηT(η)` with `T(0) ≠ 0`, in the form the amplitude module consumes.
* `finiteEndpoint_expansion` — `eq:principal-finite-endpoint-regularity`, with
  `γ_e ≠ 0` derived rather than assumed.  `Amplitude` imports this module and
  uses it to discharge that hypothesis.
* `infiniteEndpoint_z_asymptotic` — its quantitative content, `η^r z(η)` tending
  to a nonzero limit.

* the **derivative** takes `Set.Ici 0`, because the conclusion makes claims *at*
  the endpoint — a value, a nonvanishing, a continuity — which a derivative on
  the punctured side alone cannot supply;
* an **eventual condition** takes `nhdsWithin 0 (Set.Ioi 0)` when the endpoint
  value is supplied separately, and `nhdsWithin 0 (Set.Ici 0)` only when it must
  be *derived* — `rootMultiplicity_pos_of_branch` is the second kind, since it
  reads the multiplicity off the value at `0` itself.

## Implementation notes

**Endpoint binders are one-sided, and the two sides are not symmetric.**  Every
`δ` in this module is the *distance* to an endpoint, so `δ ≥ 0` and a two-sided
derivative at `0` does not exist — `τ` is even in the angle, so the two one-sided
difference quotients there are exact negatives and both nonzero.  A
`HasDerivAt _ _ 0` in an endpoint hypothesis is therefore a defect on sight
rather than a strengthening: it asks for the negation of the phenomenon it
describes, and no branch can satisfy it.

Which one-sided filter is not uniform, and the rule is what the conclusion needs:

Making them uniform in the strong direction is what left a downstream binder
unmeetable, and uniform in the weak direction loses the endpoint value.

**After a mechanical sweep over these filters, diff the statement lines against
`HEAD` — the build will not tell you.**  A sweep that widens a filter *weakens* a
conclusion, and a weakened conclusion still typechecks and still passes every
consumer, because weaker conclusions are harder to use rather than easier.
Nothing fires unless some existing consumer happened to need the strong part.
It is the inverse of every other failure here: those are false alarms that look
like findings, this is a false pass that looks like nothing.  Measured: one
regex pass over `{0}ᶜ` silently widened `infiniteEndpoint_z_asymptotic`'s
conclusion, compiled clean, and was caught only by the diff.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Forgács--Tran geometry
and endpoint separation» (`sec:geometry`, `subsec:FT-geometry`,
`lem:principal-endpoint-regularity`, `eq:principal-finite-endpoint-regularity`,
`eq:z-endpoint-order`, `eq:principal-infinite-endpoint-regularity`).

## Tags

endpoint regularity, principal branch, denominator collision
-/

namespace ForgacsTran

open Polynomial Metric

/-- The endpoint factorization `Q(t) + z_e t^r = (t - t_e)^k G(t)`, `G(t_e) ≠ 0`,
with `k` the multiplicity of the collision. -/
theorem exists_endpointFactor {Q : Polynomial ℂ} {r : ℕ} {ze te : ℂ}
    (hP : ftDen Q r ze ≠ 0) :
    ∃ G : Polynomial ℂ,
      ftDen Q r ze = (X - C te) ^ ((ftDen Q r ze).rootMultiplicity te) * G ∧
        G.eval te ≠ 0 :=
  ⟨_, (pow_mul_divByMonic_rootMultiplicity_eq _ te).symm,
    eval_divByMonic_pow_rootMultiplicity_ne_zero te hP⟩

/-- **The near-endpoint root equation.**  At any zero `t` of `D(·,z)`, the
endpoint factorization evaluates to `-(z - z_e)t^r`.  Exact algebra: the `t^r`
terms of the two pencils differ by exactly `(z - z_e)t^r`. -/
theorem endpoint_root_identity {Q : Polynomial ℂ} {r : ℕ} {ze z te t : ℂ} {k : ℕ}
    {G : Polynomial ℂ} (hfac : ftDen Q r ze = (X - C te) ^ k * G)
    (hroot : (ftDen Q r z).eval t = 0) :
    (t - te) ^ k * G.eval t = -(z - ze) * t ^ r := by
  have h1 : (ftDen Q r ze).eval t = -(z - ze) * t ^ r := by
    rw [ftDen_eval] at hroot ⊢
    linear_combination hroot
  rw [hfac] at h1
  simpa using h1

/-- **The `Λ` factor is nonvanishing.**  The base of the `k`-th root in the
branch construction is `-ε t_e^r/G(t_e)`; it is nonzero exactly because the
endpoint root is off the origin and the collision is exactly of order `k`.  Both
hypotheses are load-bearing and both appear in the type. -/
theorem lambdaBase_ne_zero {G : Polynomial ℂ} {te ε : ℂ} {r : ℕ} (hε : ε ≠ 0)
    (hte : te ≠ 0) (hG : G.eval te ≠ 0) :
    -ε * te ^ r / G.eval te ≠ 0 :=
  div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hε) (pow_ne_zero _ hte)) hG

/-- **`eq:z-endpoint-order`.**  `z(δ) - z_e = c_e δ^k (1 + O(δ))` with `c_e ≠ 0`,
where `k` is the multiplicity of the endpoint collision — stated with the
`(1 + O(δ))` carried by continuity of `c` at `0`, so `c 0 = c_e`.

Only the branch's differentiability and `γ_e ≠ 0` are taken from
`Forgacs2017RationalDenominator` Prop. 3; the exponent and the nonvanishing of
`c_e` are read off `endpoint_root_identity`.  Explicitly
`c_e = -γ_e^k G(t_e)/t_e^r`.
**Differs from the paper's route.**  In the paper the order is immediate because the parameter is
*defined* by `z - z_e = ±y^k`.  Here `δ` is the angular distance, an independent
variable, so the order is derived: substituting the linear factorization of `γ`
into `endpoint_root_identity` exhibits `z - z_e` as `δ^k` times a continuous
nonvanishing factor.
-/
theorem z_endpoint_order {Q : Polynomial ℂ} {r : ℕ} {ze te : ℂ} (hte : te ≠ 0)
    (hP : ftDen Q r ze ≠ 0) {γ zf : ℝ → ℂ} {γe : ℂ} (hγe : γe ≠ 0) (hγ0 : γ 0 = te)
    (hγ : HasDerivWithinAt γ γe (Set.Ici (0 : ℝ)) 0)
    (hroot : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    ∃ c : ℝ → ℂ, ContinuousWithinAt c (Set.Ici (0 : ℝ)) 0 ∧ c 0 ≠ 0 ∧
      ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        zf δ - ze = (δ : ℂ) ^ ((ftDen Q r ze).rootMultiplicity te) * c δ := by
  classical
  set k := (ftDen Q r ze).rootMultiplicity te with hkdef
  obtain ⟨G, hfac, hG⟩ := exists_endpointFactor (Q := Q) (r := r) (ze := ze) (te := te) hP
  obtain ⟨h, hhc, hh0, hhmul⟩ := exists_linearFactor_within hγ
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
      ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  have hγc : ContinuousWithinAt γ (Set.Ici (0 : ℝ)) 0 := hγ.continuousWithinAt
  have hGc : ContinuousWithinAt (fun δ => G.eval (γ δ)) (Set.Ici (0 : ℝ)) 0 :=
    ((Polynomial.continuous G).continuousAt).comp_continuousWithinAt hγc
  have hGne : G.eval (γ 0) ≠ 0 := by rwa [hγ0]
  have hγne0 : γ 0 ≠ 0 := by rwa [hγ0]
  refine ⟨fun δ => -((h δ) ^ k * G.eval (γ δ)) / (γ δ) ^ r, ?_, ?_, ?_⟩
  · exact (((hhc.pow k).mul hGc).neg).div (hγc.pow r) (pow_ne_zero _ hγne0)
  · change -((h 0) ^ k * G.eval (γ 0)) / (γ 0) ^ r ≠ 0
    rw [hh0, hγ0]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hγe) hG))
      (pow_ne_zero _ hte)
  · filter_upwards [hroot, hmono (Filter.Tendsto.eventually_ne hγc hγne0)] with δ hr0 hγd
    have hid := endpoint_root_identity (te := te) (k := k) (G := G) hfac hr0
    have hlin : γ δ - te = (δ : ℂ) * h δ := by
      have := hhmul δ
      rwa [hγ0, Complex.ofReal_zero, sub_zero] at this
    rw [hlin, mul_pow] at hid
    have hmain : (zf δ - ze) * (γ δ) ^ r
        = (δ : ℂ) ^ k * (-((h δ) ^ k * G.eval (γ δ))) := by linear_combination hid
    field_simp
    linear_combination hmain

/-- **`eq:principal-infinite-endpoint-regularity`.**  At the unbounded upper
endpoint the branch runs into the origin, and `γ = ηT(η)` with `T(0) ≠ 0` is
exactly differentiability at `0` with `γ(0) = 0` and nonzero derivative.  This is
the form `Amplitude.amplitude_endpoint_form_origin` consumes, so a caller with
the branch data need not produce `T` by hand. -/
theorem exists_infiniteEndpoint_form {γ : ℝ → ℂ} {γe : ℂ} (hγ0 : γ 0 = 0)
    (hγ : HasDerivWithinAt γ γe (Set.Ici (0 : ℝ)) 0) (hγe : γe ≠ 0) :
    ∃ T : ℝ → ℂ, ContinuousWithinAt T (Set.Ici (0 : ℝ)) 0 ∧ T 0 ≠ 0 ∧
      ∀ η : ℝ, γ η = (η : ℂ) * T η := by
  obtain ⟨T, hTc, hT0, hTmul⟩ := exists_linearFactor_within hγ
  refine ⟨T, hTc, by rw [hT0]; exact hγe, fun η => ?_⟩
  have := hTmul η
  rwa [hγ0, Complex.ofReal_zero, sub_zero, sub_zero] at this

/-- **The quantitative content of `eq:principal-infinite-endpoint-regularity`.**
With `γ = ηT(η)`, the spectral parameter blows up at exactly the rate `η^{-r}`:
`η^r z(η) → -Q(0)/T(0)^r ≠ 0`.  This is what makes `w = z^{-1/r}` comparable to
`η`, which is the substance of the paper's change of parameter.
**Differs from the paper's route.**  The paper passes to `w = z^{-1/r}` and applies the implicit
function
theorem.  Here the same content is stated as a limit of `η^r z(η)`, obtained by
solving the root equation for `z` directly, so neither `w` nor an
implicit-function step appears.
-/
theorem infiniteEndpoint_z_asymptotic {Q : Polynomial ℂ} {r : ℕ} (_hr : 1 ≤ r)
    (_hQ0 : Q.eval 0 ≠ 0) {γ zf T : ℝ → ℂ}
    (hT : ContinuousWithinAt T (Set.Ici (0 : ℝ)) 0) (hT0 : T 0 ≠ 0)
    (hγ : ∀ η : ℝ, γ η = (η : ℂ) * T η)
    (hroot : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (ftDen Q r (zf η)).eval (γ η) = 0) :
    Filter.Tendsto (fun η : ℝ => (η : ℂ) ^ r * zf η) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (-(Q.eval 0) / T 0 ^ r)) := by
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
      ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  have hγ0 : γ 0 = 0 := by simp [hγ]
  have hγc : ContinuousWithinAt γ (Set.Ici (0 : ℝ)) 0 := by
    have hfun : γ = fun η : ℝ => (η : ℂ) * T η := funext hγ
    rw [hfun]
    exact (Complex.continuous_ofReal.continuousAt).continuousWithinAt.mul hT
  have hlim : Filter.Tendsto (fun η : ℝ => -(Q.eval (γ η)) / T η ^ r)
      (nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))) (nhds (-(Q.eval 0) / T 0 ^ r)) := by
    have hQt : Filter.Tendsto (fun x : ℝ => Q.eval (γ x))
        (nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))) (nhds (Q.eval 0)) := by
      have h : Filter.Tendsto (fun x : ℝ => Q.eval (γ x))
          (nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))) (nhds (Q.eval (γ 0))) :=
        ((Polynomial.continuous Q).continuousAt).comp_continuousWithinAt hγc
      rwa [hγ0] at h
    exact Filter.Tendsto.div hQt.neg (hT.pow r) (pow_ne_zero _ hT0)
  refine (hlim.mono_left hmono).congr' ?_
  filter_upwards [hroot, hmono (Filter.Tendsto.eventually_ne hT hT0),
    self_mem_nhdsWithin] with η hr0 hTne hη0
  have hηne : ((η : ℂ)) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using ne_of_gt hη0
  have hγη : γ η = (η : ℂ) * T η := hγ η
  rw [ftDen_eval, hγη] at hr0
  rw [hγη]
  field_simp
  linear_combination -hr0


/-! ### `eq:principal-finite-endpoint-regularity` -/

/-- **The leading coefficient is forced, and nonzero.**  Dividing
`endpoint_root_identity` by `δ^k` turns it into
`((γ(δ)-t_e)/δ)^k = -c(δ)γ(δ)^r/G(γ(δ))`, and both sides have limits at `δ = 0`:
the left is `γ_e^k` and the right is the `Λ`-base `-c_e t_e^r/G(t_e)`, which is
nonzero by `lambdaBase_ne_zero`.  So `γ_e ≠ 0` is *derived* from the order
statement rather than assumed — which is what
`eq:principal-finite-endpoint-regularity` asserts beyond differentiability.

Note the shape of `hz`: the parameter is the real one-sided `δ` and the sign of
`z - z_e` sits in the complex `c`, so `c 0` plays the role of `ε` and no `k`-th
root of a complex parameter is ever taken.
**Differs from the paper's route.**  `lem:principal-endpoint-regularity` builds the branch from a
real
one-sided `y ≥ 0` with `z - z_e = ε y^k` and an analytic `k`-th root
`Λ = (-ε t^r/G(t))^{1/k}`, and reads `γ ≠ 0` off that construction.  Here the
branch is taken as given and the identity is used in the other direction:
dividing `endpoint_root_identity` by `δ^k` and passing to the limit forces
`γ_e^k` to equal the `Λ`-base, which `lambdaBase_ne_zero` shows is nonzero.  No
`k`-th root is constructed.
-/
theorem finiteEndpoint_leadingCoeff_pow {Q : Polynomial ℂ} {r k : ℕ} {ze te : ℂ}
    {G : Polynomial ℂ} (hte : te ≠ 0) (hG : G.eval te ≠ 0) (hk : 1 ≤ k)
    (hfac : ftDen Q r ze = (X - C te) ^ k * G)
    {γ zf c : ℝ → ℂ} {γe : ℂ} (hγ0 : γ 0 = te)
    (hγ : HasDerivWithinAt γ γe (Set.Ici (0 : ℝ)) 0)
    (hc : ContinuousWithinAt c (Set.Ici (0 : ℝ)) 0) (hc0 : c 0 ≠ 0)
    (hroot : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), (ftDen Q r (zf δ)).eval (γ δ) = 0)
    (hz : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), zf δ - ze = (δ : ℂ) ^ k * c δ) :
    γe ^ k = -c 0 * te ^ r / G.eval te ∧ γe ≠ 0 := by
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
      ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  have hγc : ContinuousWithinAt γ (Set.Ici (0 : ℝ)) 0 := hγ.continuousWithinAt
  have hγne0 : γ 0 ≠ 0 := by rwa [hγ0]
  have hGne : G.eval (γ 0) ≠ 0 := by rwa [hγ0]
  have hGc : ContinuousWithinAt (fun δ => G.eval (γ δ)) (Set.Ici (0 : ℝ)) 0 :=
    ((Polynomial.continuous G).continuousAt).comp_continuousWithinAt hγc
  -- the slope tends to the derivative
  have hslope : Filter.Tendsto (fun δ : ℝ => (γ δ - te) / ((δ : ℂ)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds γe) := by
    have hγ' : HasDerivWithinAt γ γe (Set.Ioi (0 : ℝ)) 0 :=
      hγ.mono Set.Ioi_subset_Ici_self
    refine ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hγ').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : ¬ (δ = 0) := ne_of_gt hδ
    simp only [slope_def_module, Complex.real_smul, Complex.ofReal_inv,
      sub_zero, div_eq_inv_mul, hγ0]
  -- and the right-hand side tends to the `Λ`-base
  have hrhs : Filter.Tendsto (fun δ : ℝ => -c δ * (γ δ) ^ r / G.eval (γ δ))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (-c 0 * te ^ r / G.eval te)) := by
    have h : Filter.Tendsto (fun δ : ℝ => -c δ * (γ δ) ^ r / G.eval (γ δ))
        (nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)))
        (nhds (-c 0 * (γ 0) ^ r / G.eval (γ 0))) :=
      Filter.Tendsto.div (hc.neg.mul (hγc.pow r)) hGc hGne
    rw [hγ0] at h
    exact h.mono_left hmono
  -- the two agree off the origin
  have hcongr : (fun δ : ℝ => ((γ δ - te) / ((δ : ℂ))) ^ k)
      =ᶠ[nhdsWithin 0 (Set.Ioi (0 : ℝ))] fun δ : ℝ => -c δ * (γ δ) ^ r / G.eval (γ δ) := by
    filter_upwards [hroot, hz,
      hmono (Filter.Tendsto.eventually_ne hGc hGne), self_mem_nhdsWithin]
      with δ hr0 hzδ hGδ hδ0
    have hδne : ((δ : ℂ)) ≠ 0 := by
      simpa [Complex.ofReal_eq_zero] using ne_of_gt hδ0
    have hid := endpoint_root_identity (te := te) (k := k) (G := G) hfac hr0
    rw [hzδ] at hid
    rw [div_pow]
    field_simp
    linear_combination hid
  have hlim := (hslope.pow k).congr' hcongr
  have heq : γe ^ k = -c 0 * te ^ r / G.eval te := tendsto_nhds_unique hlim hrhs
  refine ⟨heq, ?_⟩
  intro hz0
  rw [hz0, zero_pow (by omega : k ≠ 0)] at heq
  exact (lambdaBase_ne_zero (ε := c 0) (te := te) (r := r) (G := G) hc0 hte hG) heq.symm

/-- **`eq:principal-finite-endpoint-regularity`.**  The branch enters a finite
endpoint linearly with nonvanishing leading coefficient:
`γ(δ) - t_e = γ_e δ(1 + O(δ))` with `γ_e ≠ 0`, the `O(δ)` carried by continuity
of `h` at `0` and `h 0 = γ_e`.  This is the form
`Amplitude.amplitude_endpoint_form` consumes. -/
theorem finiteEndpoint_expansion {Q : Polynomial ℂ} {r k : ℕ} {ze te : ℂ}
    {G : Polynomial ℂ} (hte : te ≠ 0) (hG : G.eval te ≠ 0) (hk : 1 ≤ k)
    (hfac : ftDen Q r ze = (X - C te) ^ k * G)
    {γ zf c : ℝ → ℂ} {γe : ℂ} (hγ0 : γ 0 = te)
    (hγ : HasDerivWithinAt γ γe (Set.Ici (0 : ℝ)) 0)
    (hc : ContinuousWithinAt c (Set.Ici (0 : ℝ)) 0) (hc0 : c 0 ≠ 0)
    (hroot : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), (ftDen Q r (zf δ)).eval (γ δ) = 0)
    (hz : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), zf δ - ze = (δ : ℂ) ^ k * c δ) :
    ∃ h : ℝ → ℂ, ContinuousWithinAt h (Set.Ici (0 : ℝ)) 0 ∧ h 0 = γe ∧ γe ≠ 0 ∧
      ∀ δ : ℝ, γ δ - te = (δ : ℂ) * h δ := by
  obtain ⟨-, hγe⟩ := finiteEndpoint_leadingCoeff_pow hte hG hk hfac hγ0 hγ hc hc0 hroot hz
  obtain ⟨h, hhc, hh0, hhmul⟩ := exists_linearFactor_within hγ
  refine ⟨h, hhc, hh0, hγe, fun δ => ?_⟩
  have := hhmul δ
  rwa [hγ0, Complex.ofReal_zero, sub_zero] at this

/-- **The `k` leading coefficients are the `ω Λ(t_e)`, `ω^k = 1`, and distinct.**
Two branches into the same endpoint have leading coefficients differing by a
`k`-th root of unity, and distinct roots of unity give distinct coefficients
because the `Λ`-base is nonzero — which is what lets an angular parameter single
out one branch rather than the whole collision. -/
theorem leadingCoeff_ratio_pow_eq_one {k : ℕ} (hk : 1 ≤ k) {γ₁ γ₂ w : ℂ} (hw : w ≠ 0)
    (h1 : γ₁ ^ k = w) (h2 : γ₂ ^ k = w) :
    γ₂ ≠ 0 ∧ (γ₁ / γ₂) ^ k = 1 := by
  have h2ne : γ₂ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : k ≠ 0)] at h2
    exact hw h2.symm
  exact ⟨h2ne, by rw [div_pow, h1, h2, div_self hw]⟩


/-! ### What the endpoint data discharges for the amplitude module -/

/-- **`hk` is not an independent hypothesis.**  If the branch passes through
`t_e` at the endpoint parameter, `t_e` is a zero of the limiting denominator, so
the collision multiplicity is at least one. -/
theorem rootMultiplicity_pos_of_branch {Q : Polynomial ℂ} {r : ℕ} {te : ℂ} {γ zf : ℝ → ℂ}
    (hP : ftDen Q r (zf 0) ≠ 0) (hγ0 : γ 0 = te)
    (hroot : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)),
      (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    1 ≤ (ftDen Q r (zf 0)).rootMultiplicity te := by
  have h0 : (ftDen Q r (zf 0)).eval (γ 0) = 0 :=
    hroot.self_of_nhdsWithin (Set.mem_Ici.mpr le_rfl)
  rw [hγ0] at h0
  exact (Polynomial.rootMultiplicity_pos hP).2 h0

/-- **`γ_e ≠ 0` is independent of the remaining endpoint hypotheses, so it cannot
simply be dropped.**  Every other binder of `Amplitude.amplitude_endpoint_form`
is satisfied by `Q = X - 1`, `r = 1`, `t_e = 1`, the constant branch `γ ≡ 1` and
the constant parameter `zf ≡ 0` — for which `γ_e = 0`.  What rules this out is
the endpoint *order*, which a constant `zf` fails; that is why
`amplitude_endpoint_form_of_order` exchanges `γ_e ≠ 0` for `eq:z-endpoint-order`
rather than discharging it outright. -/
theorem leadingCoeff_ne_zero_independent :
    ∃ (Q : Polynomial ℂ) (r : ℕ) (te : ℂ) (γ zf : ℝ → ℂ),
      1 ≤ r ∧ te ≠ 0 ∧ γ 0 = te ∧ HasDerivAt γ 0 0 ∧ ftDen Q r (zf 0) ≠ 0 ∧
        1 ≤ (ftDen Q r (zf 0)).rootMultiplicity te ∧
        (∀ᶠ δ in nhds (0 : ℝ), (ftDen Q r (zf δ)).eval (γ δ) = 0) := by
  refine ⟨X - C 1, 1, 1, fun _ => 1, fun _ => 0, le_refl 1, one_ne_zero, rfl,
    hasDerivAt_const 0 1, ?_, ?_, ?_⟩
  · simpa [ftDen] using X_sub_C_ne_zero (1 : ℂ)
  · refine (Polynomial.rootMultiplicity_pos ?_).2 ?_
    · simpa [ftDen] using X_sub_C_ne_zero (1 : ℂ)
    · simp [ftDen, IsRoot]
  · filter_upwards with δ
    simp [ftDen]

end ForgacsTran
