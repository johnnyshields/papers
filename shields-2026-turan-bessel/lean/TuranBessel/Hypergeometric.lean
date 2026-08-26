/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Zseries
import Vendor.MathlibPR.PR42760.Bessel

/-!
# `Z` as a regularized hypergeometric function

Identifies the `Z` of `shields-2026-turan-bessel.tex`, «Reciprocal-gamma
formulation and positivity phase diagram» (`sec:main`, `eq:Zdef`) with Mathlib's regularized `₀F₁`,
and records the
`J`-side of `eq:I-Z`.

`Z(a,λ) = ∑_k λ^k/(k! Γ(a+k)) = ₀F₁(;a;λ)/Γ(a)` is by definition the *regularized*
`₀F₁`, so `Zfun` is not a private construction: it is `regularizedHGFun 0 {a}`
transported along `ℝ → ℂ`.  `ofReal_Zfun` proves that, and needs no hypothesis —
both sides are `tsum`s, so termwise equality suffices whether or not the series
converges.

`besselJ_eq_Zfun` is the Bessel-side consequence.  Upstream's
`besselJ ν x = (x/2)^ν · ₀F̃₁(;ν+1; -(x/2)²)` puts the hypergeometric factor at
index `ν+1`, so it is `J_{a-1}`, not `J_a`, whose factor is `Z(a,·)`:
```
  J_{a-1}(x) = (x/2)^{a-1} Z(a, -(x/2)²).
```
At `x = 2√λ` that is `eq:I-Z` with the sign of the argument flipped, which is the
only difference between `I_ν` and `J_ν` in this normalization.  The modified `I_ν`
itself is not in Mathlib and is deliberately deferred by the vendored PR, so the
curvature functionals `G_ν`, `P_ν` and `H_ν` are not built here; `BesselI`,
`BesselDict` and `BesselDictPH` build them.  What this removes is the need to
*define* the series side of that dictionary here.

Both results are stated against `Vendor.MathlibPR.PR42760`, whose audit header
records the source PR and every adaptation to the pinned Mathlib.

Sorry-free, and axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace TuranBessel

open Complex

/-- `Z(a,λ)` is the regularized `₀F₁`, `eq:Zdef`.  No hypothesis: both sides are
`tsum`s, so termwise agreement gives the identity outright. -/
theorem ofReal_Zfun (a lam : ℝ) :
    ((Zfun a lam : ℝ) : ℂ) = regularizedHGFun 0 {(a : ℂ)} (lam : ℂ) := by
  rw [Zfun, Complex.ofReal_tsum, regularizedHGFun, FormalMultilinearSeries.sum,
    regularizedHGFunSeries]
  refine tsum_congr fun k => ?_
  rw [FormalMultilinearSeries.ofScalars_apply_eq, regularizedHGFunCoeff, zterm]
  push_cast [← Complex.Gamma_ofReal]
  simp [smul_eq_mul, div_eq_mul_inv]
  ring

/-- The `J`-side of `eq:I-Z`: `J_{a-1}(x) = (x/2)^{a-1} Z(a, -(x/2)²)`.  The index
drops by one because upstream's `besselJ ν` carries `₀F̃₁(;ν+1;·)`. -/
theorem besselJ_eq_Zfun (a x : ℝ) :
    besselJ ((a : ℂ) - 1) (x : ℂ)
      = ((x : ℂ) / 2) ^ ((a : ℂ) - 1) * ((Zfun a (-(x / 2) ^ 2) : ℝ) : ℂ) := by
  rw [ofReal_Zfun, besselJ]
  push_cast
  ring_nf

end TuranBessel
