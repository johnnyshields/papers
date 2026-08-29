/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Geometry

/-!
# The spectral fiber map

`eq:ab-def` sends a point `w` of the denominator to the spectral parameter that
puts a root there,

  `f(w) = -Q(w)/w^r`,

so the map is the paper's own object rather than a helper introduced to state
something else.  This module carries `f` and what is true of it away from the
origin: that it is analytic there, that `w^r f(w) = -Q(w)`, and that `f'`
vanishes exactly at a zero of `E(t) = tQ'(t) - rQ(t)`.

`w ≠ 0` is the standing hypothesis and it is what makes `w^r` invertible.  Where
the fiber map is used at an endpoint, that hypothesis is the difference between
the two endpoints of the viewing arc: at `ρ = 1` the collision sits at the
critical point `t_a ≠ 0` and `f` is analytic there, while at `2 ≤ ρ` it sits at
`x₁` and `f` has a pole.

Nothing here mentions the endpoint, the branch, or the multiplicity.

## Main statements

* `ftFiber` — the map of `eq:ab-def`.
* `analyticAt_ftFiber` — analytic off the origin.
* `deriv_ftFiber_eq_zero` — `f'` vanishes at a zero of `E`, so a zero of `E` and
  a critical point of the fiber map are the same thing.

## References

* `shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `eq:Dprime-identity`.

## Tags

spectral fiber, critical point, analytic
-/

namespace ForgacsTran

open Polynomial

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

/-- **The fiber map is analytic off the origin.**  This is what
`LowerEndpointTangent.exists_morse_endpoint` takes its Morse square
from.  A polynomial evaluation over an invertible power —
`AnalyticOnNhd.eval_polynomial` for the numerator — so no punctured-neighborhood
argument is needed anywhere. -/
theorem analyticAt_ftFiber (Q : Polynomial ℂ) (r : ℕ) {w : ℂ} (hw : w ≠ 0) :
    AnalyticAt ℂ (ftFiber Q r) w := by
  have hQ : AnalyticAt ℂ (fun z : ℂ => Polynomial.eval z Q) w :=
    AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) Q w (Set.mem_univ w)
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ r) w := (analyticAt_id (z := w)).pow r
  exact hQ.neg.div hpow (pow_ne_zero r hw)

/-- **The product identity the derivative is read off.**  Superseded but correct,
and consumed by `deriv_ftFiber_eq_zero` below rather than by anything outside this
file.  `wʳ f(w) = -Q(w)` off the origin.  Differentiating THIS rather than the
quotient is what keeps `r = 0` from being a special case: nothing is divided. -/
theorem pow_mul_ftFiber (Q : Polynomial ℂ) (r : ℕ) {w : ℂ} (hw : w ≠ 0) :
    w ^ r * ftFiber Q r w = -(Q.eval w) := by
  rw [ftFiber_apply, mul_div_cancel₀ _ (pow_ne_zero r hw)]

/-- **`f'` vanishes at a zero of `E`.**

Paper step, not scaffolding: this says the spectral fiber has a critical point
exactly at a zero of `E`, which is `eq:ab-def`'s own content and is what makes
the critical point of `g` a critical point rather than merely a root of
something.

`E(t) = tQ'(t) - rQ(t)` is `eq:Dprime-identity`, so a point being a critical point
of the fiber map and a zero of `E` are the same statement — which is why
`exists_ftSigmaReal_eq_zero_between`, which produces the critical point as a zero
of `Σ`, produces a critical point of `f` for free. -/
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
