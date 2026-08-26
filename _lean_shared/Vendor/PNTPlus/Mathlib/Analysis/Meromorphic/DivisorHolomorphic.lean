/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-
VENDORED FROM AN EXTERNAL LEAN PROJECT -- see `Vendor/PNTPlus.lean` for the full
quality audit, the licence, and the retirement condition.

* Project: PrimeNumberTheoremAnd (PNT+), <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>
* Upstream path: `PrimeNumberTheoremAnd/Mathlib/Analysis/Meromorphic/DivisorHolomorphic.lean`
* Revision: `7715064f690d0689f30889846f4e2c5e7ec0c47e`
* Licence: Apache 2.0.  The copyright and `Authors:` line above are upstream's.

Copied verbatim apart from the `PrimeNumberTheoremAnd.` import prefix, which becomes
`Vendor.PNTPlus.`.  Any other change is marked inline as adapted to the pin.
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Divisors of holomorphic functions

Holomorphic functions on `ℂ` have non-negative divisors, since zeros contribute non-negative
multiplicity and poles cannot occur.

## Main results

* `Differentiable.divisor_nonneg` : the divisor of an entire function is non-negative
-/

@[expose] public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The divisor of an entire function is non-negative. -/
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
