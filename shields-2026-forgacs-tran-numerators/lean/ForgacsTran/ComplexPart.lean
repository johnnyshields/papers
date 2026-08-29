/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.Basic

/-!
# Derivatives of the real and imaginary parts of a complex-valued curve

Every phase and every modulus in this tree is a real or an imaginary part of a curve
`ℝ → ℂ` — the branch phase `ψ = Im log W` of `eq:phase-derivative-bound`, the viewing
angle of `eq:viewing-angle-bound`, the modulus `‖W‖` through `√(re² + im²)` — so one
step recurs wherever any of them is differentiated: `Re` and `Im` are continuous and
`ℝ`-linear, and therefore carry a derivative through unchanged.

Mathlib supplies each ingredient separately — the two linear maps `Complex.reCLM` and
`Complex.imCLM`, the composition rule `HasFDerivAt.comp_hasDerivAt`, and the
`Differentiable` and `AnalyticAt` forms of the conclusion — but not the `HasDerivAt`
form.  The upstream name closest to it states something else: `HasDerivAt.real_of_complex`
starts from a function `ℂ → ℂ` differentiable **over `ℂ`** at a real point, a hypothesis
none of the curves here satisfies.

Both are stated in the `HasDerivAt` namespace so that `h.re` and `h.im` apply to a
derivative hypothesis directly, on the pattern of `Measurable.re` and `Integrable.im`.

## Main statements

* `HasDerivAt.re`, `HasDerivAt.im` — a derivative `f'` of `f : ℝ → ℂ` at `x` is a
  derivative of the real and of the imaginary part of `f` at `x`, with value the
  corresponding part of `f'`.

Sorry-free.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:phase-derivative-bound` and
  `eq:viewing-angle-bound`, whose phases are the imaginary parts this differentiates.

## Tags

real part, imaginary part, derivative, continuous linear map
-/

/-- The real part of a complex-valued curve has the real part of the derivative as its
derivative, `Complex.re` being continuous and `ℝ`-linear. -/
theorem HasDerivAt.re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The imaginary part of a complex-valued curve has the imaginary part of the derivative
as its derivative, `Complex.im` being continuous and `ℝ`-linear. -/
theorem HasDerivAt.im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
