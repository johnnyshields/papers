/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperGeneralN

/-!
# The `ρ = 1` lower endpoint: the extension `hk₀` needs

At `2 ≤ ρ` the lower endpoint of the viewing arc is the smallest root `x₁`, the
branch radius runs into it, and the spectral parameter runs into
`g(x₁) = -Q(x₁)/x₁^r = 0` because `x₁` is a zero of `Q`.  `EndpointPackage`
extends both to the closed interval on that basis.

At `ρ = 1` neither endpoint value is the same.  The radius runs into the critical
point `t_a`, which is strictly inside `(x₁, x₂)` and is NOT a zero of `Q`, and the
parameter runs into `a_end = -Q(t_a)/t_a^r`, which is not `0`.

**The two extensions are not symmetric, and that is the defect.**
`ftTauLower a r l x₁` takes its endpoint value as an ARGUMENT — the name `x₁` is
what the `2 ≤ ρ` caller supplies, not part of the definition — so a `ρ = 1`
caller may pass `t_a` and get the right function.  `ftBranchZLower a c r l`
hardcodes `0`.  So at `ρ = 1` the extended parameter is wrong at the single point
`θ = 0`, and `thm:weighted-dominance`'s

  `hk₀ : 1 ≤ (ftDen Q r (z 0)).rootMultiplicity te₀`

becomes the claim `Q(t_a) = 0`, which is FALSE — `t_a` is a critical point of `g`,
not a root of `Q`.  Measured at three pencils in `scripts/`: `Q(t_a)` is `-0.613`,
`-0.375`, `-0.966`.

This is a FALSE BINDER rather than a missing lemma, so nothing in the tree fails:
a `ρ = 1` composition would typecheck against a hypothesis nobody can discharge.

This module supplies the parameterized extension without touching
`EndpointPackage`, and shows the existing one is its `0` case, so no consumer of
`ftBranchZLower` sees any change.

## Main statements

* `ftBranchZLowerAt` — the extension with the endpoint value as an argument.
* `ftBranchZLower_eq_ftBranchZLowerAt` — the existing definition is the `a = 0`
  case, which is why this is additive rather than a change.
* `eval_ftDen_branch_value` — at any nonzero `s₀`, the pencil at that point's own
  branch value vanishes there.  This is what makes `hk₀` true once the endpoint
  value is right, and at `2 ≤ ρ` it degenerates to `Q(x₁) = 0`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:ab-def`.

## Tags

lower endpoint, rho = 1, endpoint extension, false binder
-/

namespace ForgacsTran

open Polynomial

/-- The spectral parameter extended to the closed endpoint interval, with the
endpoint value supplied rather than assumed.  `EndpointPackage.ftBranchZLower` is
this at `a = 0`, which is the `2 ≤ ρ` value `g(x₁) = 0`. -/
noncomputable def ftBranchZLowerAt {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ)
    (aEnd : ℝ) : ℝ → ℝ :=
  fun θ => if 0 < θ then ftBranchZ a c r l θ else aEnd

theorem ftBranchZLowerAt_agree {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) (aEnd : ℝ)
    {θ : ℝ} (hθ : 0 < θ) : ftBranchZLowerAt a c r l aEnd θ = ftBranchZ a c r l θ := by
  rw [ftBranchZLowerAt, if_pos hθ]

@[simp] theorem ftBranchZLowerAt_zero {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ)
    (aEnd : ℝ) : ftBranchZLowerAt a c r l aEnd 0 = aEnd := by
  rw [ftBranchZLowerAt, if_neg (lt_irrefl 0)]

/-- **The existing extension is the `a = 0` case.**  Nothing consuming
`ftBranchZLower` is affected by the parameterized form existing. -/
theorem ftBranchZLower_eq_ftBranchZLowerAt {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) :
    ftBranchZLower a c r l = ftBranchZLowerAt a c r l 0 := rfl

/-- **The pencil at a point's own branch value vanishes there.**  With
`z = -Q(s₀)/s₀^r`, `D(·,z)` has `s₀` as a root, for any `s₀ ≠ 0` and any `r`.

This is what makes `hk₀` true once the endpoint value is the branch's own.  At
`2 ≤ ρ` it degenerates: `s₀ = x₁` is a zero of `Q`, so the branch value is `0` and
the statement reduces to `Q(x₁) = 0` — which is why the hardcoded `0` is invisible
there and false at `ρ = 1`. -/
theorem eval_ftDen_branch_value {Q : Polynomial ℂ} {r : ℕ} {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    (ftDen Q r (-(Q.eval s₀) / s₀ ^ r)).eval s₀ = 0 := by
  rw [ftDen_eval]
  field_simp
  ring

/-! ### The fiber map of `eq:ab-def`

Nothing below has a consumer, and each says which of the two reasons that is.
`hγd₀` at this endpoint is discharged by
`RhoOneEndpointFactorization.hasDerivWithinAt_ftPrincipal_ftTauLower_of_simple_endpoint`
through the oddness of `ftPencilIm`, so the analytic route these were built for
is not the one the tree takes.  A zero consumer count is not a verdict, and an
`AxiomCheck` guard is not a consumer, so the reason is recorded per declaration
rather than left to be re-derived.

`t_a ≠ 0` is what makes `wʳ` invertible near it, and it is also what makes this
endpoint different from `2 ≤ ρ`, where the collision sits at `x₁` and `f` has a
pole. -/

/-- The fiber map `f(w) = -Q(w)/wʳ` of `eq:ab-def`.

Paper step: `eq:ab-def` defines the spectral parameter as this map's value, so the
map is the paper's object rather than a helper introduced to state something
else. -/
noncomputable def ftFiber (Q : Polynomial ℂ) (r : ℕ) : ℂ → ℂ :=
  fun w => -(Q.eval w) / w ^ r

/-- Superseded but correct: the defining equation, unfolded.  Kept with
`ftFiber` rather than separately. -/
theorem ftFiber_apply (Q : Polynomial ℂ) (r : ℕ) (w : ℂ) :
    ftFiber Q r w = -(Q.eval w) / w ^ r := rfl

/-- **The fiber map is analytic off the origin.**  Superseded but correct: this
was the analytic route's first input, and the tree reaches `hγd₀` by parity
instead.  The statement is true of `eq:ab-def` independently of which route
consumes it.  A polynomial evaluation over an invertible power — `AnalyticOnNhd.eval_polynomial` for the numerator, so no
punctured-neighborhood argument is needed anywhere. -/
theorem analyticAt_ftFiber (Q : Polynomial ℂ) (r : ℕ) {w : ℂ} (hw : w ≠ 0) :
    AnalyticAt ℂ (ftFiber Q r) w := by
  have hQ : AnalyticAt ℂ (fun z : ℂ => Polynomial.eval z Q) w :=
    AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) Q w (Set.mem_univ w)
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ r) w := (analyticAt_id (z := w)).pow r
  exact hQ.neg.div hpow (pow_ne_zero r hw)

/-- **The product identity the derivative is read off.**  Superseded but correct,
and consumed by `deriv_ftFiber_eq_zero` below rather than by anything outside this
file.  `wʳ f(w) = -Q(w)` off the origin.  Differentiating THIS rather than the quotient is what keeps `r = 0` from
being a special case: nothing is divided. -/
theorem pow_mul_ftFiber (Q : Polynomial ℂ) (r : ℕ) {w : ℂ} (hw : w ≠ 0) :
    w ^ r * ftFiber Q r w = -(Q.eval w) := by
  rw [ftFiber_apply, mul_div_cancel₀ _ (pow_ne_zero r hw)]

/-- **`f'` vanishes at a zero of `E`.**

Paper step, not scaffolding: this says the spectral fiber has a critical point
exactly at a zero of `E`, which is `eq:ab-def`'s own content and is what makes
`t_a` a critical point rather than merely a root of something.  It was reached as
an analytic route's second input and it outlives that route.

`E(t) = tQ'(t) - rQ(t)` is `eq:Dprime-identity`, so `t_a` being a critical point of
the fiber map and a zero of `E` are the same statement — which is why
`exists_ftSigmaReal_eq_zero_between`, which produces `t_a` as a zero of `Σ`,
produces a critical point for free. -/
theorem deriv_ftFiber_eq_zero (Q : Polynomial ℂ) {r : ℕ} (hr : 1 ≤ r) {w : ℂ}
    (hw : w ≠ 0) (hE : (ftCritical Q r).eval w = 0) : deriv (ftFiber Q r) w = 0 := by
  have hana := analyticAt_ftFiber Q r hw
  have hfd : HasDerivAt (ftFiber Q r) (deriv (ftFiber Q r) w) w :=
    hana.differentiableAt.hasDerivAt
  have hnb : (fun z : ℂ => z ^ r * ftFiber Q r z) =ᶠ[nhds w] fun z : ℂ => -(Q.eval z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hw)] with z hz
    exact pow_mul_ftFiber Q r (by simpa using hz)
  have hrhs : HasDerivAt (fun z : ℂ => -(Q.eval z)) (-((derivative Q).eval w)) w :=
    (Q.hasDerivAt w).neg
  have hlhs : HasDerivAt (fun z : ℂ => z ^ r * ftFiber Q r z)
      ((r : ℂ) * w ^ (r - 1) * ftFiber Q r w + w ^ r * deriv (ftFiber Q r) w) w :=
    (hasDerivAt_pow r w).fun_mul hfd
  have heq := hlhs.unique (hrhs.congr_of_eventuallyEq hnb)
  rw [ftFiber_apply] at heq
  rw [eval_ftCritical] at hE
  have hpne : (w : ℂ) ^ r ≠ 0 := pow_ne_zero r hw
  have hsplit : (w : ℂ) ^ r = w ^ (r - 1) * w := by
    rw [← pow_succ]; congr 1; omega
  -- multiply through by `w`: the first term collapses to `-r Q(w)` and `E(w)` appears
  have h1 : (r : ℂ) * w ^ (r - 1) * (-(Q.eval w) / w ^ r) * w = -((r : ℂ) * Q.eval w) := by
    rw [hsplit]
    field_simp
  have h2 := congrArg (fun x : ℂ => x * w) heq
  simp only [add_mul] at h2
  rw [h1] at h2
  have hfin : w ^ r * deriv (ftFiber Q r) w * w = 0 := by linear_combination h2 - hE
  rcases mul_eq_zero.1 hfin with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hpne
    · exact h'
  · exact absurd h hw

end ForgacsTran
