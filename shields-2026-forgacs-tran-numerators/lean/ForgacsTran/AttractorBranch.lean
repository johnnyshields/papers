/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# The dominant root branch

`prop:isolated-dominant-cancellation` opens by taking the implicit function
theorem for `D(t,z) = Q(t) + z t^r` at a simple denominator zero.  Off `t = 0`
the denominator equation is solved for `z` outright — `D(t,z) = 0` iff
`z = g(t) = -Q(t)/t^r` — so the branch `t(z)` is not a genuine two-variable
implicit function but the **local inverse of the single function `g`**, and the
whole step is Mathlib's `AnalyticAt.analyticAt_localInverse`.

## Main statements

* `ftDenomFn_eq_zero_iff` — the denominator equation solved for `z`.
* `deriv_ftBranch` — `rem:cancellation-meaning`'s
  `g'(t₀) = -∂_t D(t₀, z₀)/t₀^r`, so `g'(t₀) ≠ 0` is exactly simplicity of the
  zero.
* `exists_root_branch` — the holomorphic branch `t(z)` with `t(z₀) = t₀`,
  `D(t(z), z) = 0` near `z₀`, and the derivative `eq:dominant-root-derivative`
  `t'(z₀) = -t₀^r/∂_t D(t₀,z₀)`.

## Implementation notes

Stated for an arbitrary `Q` analytic at `t₀`; the paper's `Q ∈ ℝ[t]` is a case.
Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`,
`prop:isolated-dominant-cancellation`, `eq:dominant-root-derivative`,
`rem:cancellation-meaning`).

## Tags

dominant root, branch, zero attractor
-/

namespace ForgacsTran

open Complex

/-- Paper `prop:isolated-dominant-cancellation` — the denominator
`D(t,z) = Q(t) + z t^r`. -/
def ftDenomFn (Q : ℂ → ℂ) (r : ℕ) (z t : ℂ) : ℂ := Q t + z * t ^ r

/-- Paper `rem:cancellation-meaning` — the fiber map `g(t) = -Q(t)/t^r`, whose
graph is the denominator curve off `t = 0`. -/
noncomputable def ftBranch (Q : ℂ → ℂ) (r : ℕ) (t : ℂ) : ℂ := -Q t / t ^ r

/-- Paper `rem:cancellation-meaning` — `∂_t D(t,z) = Q'(t) + z r t^{r-1}`,
evaluated along the fiber map. -/
noncomputable def ftDenomFnDeriv (Q : ℂ → ℂ) (r : ℕ) (t : ℂ) : ℂ :=
  deriv Q t + ftBranch Q r t * r * t ^ (r - 1)

/-- **The denominator equation, solved for `z`.**  Off the origin, `D(t,z) = 0`
says exactly that `z` is the fiber value `g(t)`. -/
theorem ftDenomFn_eq_zero_iff (Q : ℂ → ℂ) (r : ℕ) {z t : ℂ} (ht : t ≠ 0) :
    ftDenomFn Q r z t = 0 ↔ z = ftBranch Q r t := by
  have htr : t ^ r ≠ 0 := pow_ne_zero _ ht
  simp only [ftDenomFn, ftBranch]
  rw [eq_div_iff htr]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Paper `rem:cancellation-meaning`.**  `g'(t₀) = -∂_t D(t₀, z₀)/t₀^r` at
`z₀ = g(t₀)`, so the fiber map has nonvanishing derivative exactly where `t₀` is
a simple zero of `D(·, z₀)`. -/
theorem deriv_ftBranch {Q : ℂ → ℂ} {r : ℕ} {t₀ : ℂ} (hQ : AnalyticAt ℂ Q t₀)
    (ht₀ : t₀ ≠ 0) :
    HasDerivAt (ftBranch Q r) (-ftDenomFnDeriv Q r t₀ / t₀ ^ r) t₀ := by
  have htr : t₀ ^ r ≠ 0 := pow_ne_zero _ ht₀
  have hQd : HasDerivAt Q (deriv Q t₀) t₀ := hQ.differentiableAt.hasDerivAt
  have hden : HasDerivAt (fun t : ℂ => t ^ r) ((r : ℂ) * t₀ ^ (r - 1)) t₀ :=
    hasDerivAt_pow r t₀
  have hdiv := hQd.neg.div hden htr
  have hval : (-deriv Q t₀ * t₀ ^ r - -Q t₀ * ((r : ℂ) * t₀ ^ (r - 1))) / (t₀ ^ r) ^ 2
      = -ftDenomFnDeriv Q r t₀ / t₀ ^ r := by
    simp only [ftDenomFnDeriv, ftBranch]
    field
  rw [← hval]
  exact hdiv

/-- **Paper `prop:isolated-dominant-cancellation` — the root branch.**  At a
simple nonzero zero `t₀` of `D(·, z₀)` there is a holomorphic `T` near
`z₀ = g(t₀)` with `T(z₀) = t₀` and `D(T(z), z) = 0` near `z₀`, and its derivative
is `eq:dominant-root-derivative`, `t'(z₀) = -t₀^r/∂_t D(t₀, z₀)`.

The proof is the local inverse of the fiber map `g`, which
`ftDenomFn_eq_zero_iff` shows is the same thing as the implicit branch. -/
theorem exists_root_branch {Q : ℂ → ℂ} {r : ℕ} {t₀ : ℂ} (hQ : AnalyticAt ℂ Q t₀)
    (ht₀ : t₀ ≠ 0) (hsimple : ftDenomFnDeriv Q r t₀ ≠ 0) :
    ∃ T : ℂ → ℂ, AnalyticAt ℂ T (ftBranch Q r t₀) ∧ T (ftBranch Q r t₀) = t₀ ∧
      (∀ᶠ z in nhds (ftBranch Q r t₀), ftDenomFn Q r z (T z) = 0) ∧
      HasDerivAt T (-t₀ ^ r / ftDenomFnDeriv Q r t₀) (ftBranch Q r t₀) := by
  have htr : t₀ ^ r ≠ 0 := pow_ne_zero _ ht₀
  have hg : HasDerivAt (ftBranch Q r) (-ftDenomFnDeriv Q r t₀ / t₀ ^ r) t₀ :=
    deriv_ftBranch hQ ht₀
  have hgan : AnalyticAt ℂ (ftBranch Q r) t₀ := by
    have hpow : AnalyticAt ℂ (fun t : ℂ => t ^ r) t₀ := analyticAt_id.pow r
    exact (hQ.neg).div hpow htr
  have hd0 : deriv (ftBranch Q r) t₀ ≠ 0 := by
    rw [hg.deriv]
    exact div_ne_zero (neg_ne_zero.mpr hsimple) htr
  have hstrict := hgan.hasStrictDerivAt
  refine ⟨hstrict.localInverse _ _ _ hd0, hgan.analyticAt_localInverse hd0,
    HasStrictFDerivAt.localInverse_apply_image .., ?_, ?_⟩
  · have hinv := hstrict.eventually_right_inverse (f' := deriv (ftBranch Q r) t₀) (hf' := hd0)
    have himg : hstrict.localInverse _ _ _ hd0 (ftBranch Q r t₀) = t₀ :=
      HasStrictFDerivAt.localInverse_apply_image ..
    have hcont : ContinuousAt (hstrict.localInverse _ _ _ hd0) (ftBranch Q r t₀) :=
      (hgan.analyticAt_localInverse hd0).continuousAt
    have hne : ∀ᶠ z in nhds (ftBranch Q r t₀),
        hstrict.localInverse _ _ _ hd0 z ≠ 0 :=
      hcont.eventually_ne (by rw [himg]; exact ht₀)
    filter_upwards [hinv, hne] with z hz hz0
    exact (ftDenomFn_eq_zero_iff Q r hz0).mpr hz.symm
  · have h := hstrict.to_localInverse (hf' := hd0)
    have hval : (deriv (ftBranch Q r) t₀)⁻¹ = -t₀ ^ r / ftDenomFnDeriv Q r t₀ := by
      rw [hg.deriv]
      field_simp
    rw [← hval]
    exact h.hasDerivAt

end ForgacsTran
