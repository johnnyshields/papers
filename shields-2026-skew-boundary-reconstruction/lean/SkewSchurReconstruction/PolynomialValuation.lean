/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.WeightedPolynomials
import Mathlib.RingTheory.Valuation.Basic

/-!
# The polynomial weight as a standard additive valuation

Connects «Convex valuations» (`subsec:valuations`, `lem:valuation-laws`) to
«An abstract Strict-Monge cofactor principle» (`subsec:abstract`) in
`shields-2026-skew-boundary-reconstruction.tex`.  All valuation laws are supplied
by the finite-support polynomial proofs.  Sorry-free.
-/

namespace SkewSchurReconstruction

variable {σ R : Type*} [CommRing R] [IsDomain R]

@[simp]
theorem monomialValuation_one (w : σ → ℝ) :
    monomialValuation w (1 : MvPolynomial σ R) = 0 := by
  simp [monomialValuation]

/-- The actual finite-support weight valuation, packaged in Mathlib's standard type. -/
noncomputable def polynomialAddValuation (w : σ → ℝ) :
    AddValuation (MvPolynomial σ R) (WithTop ℝ) :=
  AddValuation.of (monomialValuation w) (monomialValuation_zero w)
    (monomialValuation_one w) (monomialValuation_add_ge w) (monomialValuation_mul w)

@[simp]
theorem polynomialAddValuation_apply (w : σ → ℝ) (p : MvPolynomial σ R) :
    polynomialAddValuation w p = monomialValuation w p := rfl

/-- Nonzero polynomials have finite valuation; there is no undisclosed valuation kernel. -/
theorem polynomialAddValuation_finite {w : σ → ℝ} {p : MvPolynomial σ R}
    (hp : p ≠ 0) : polynomialAddValuation w p ≠ ⊤ := by
  change monomialValuation w p ≠ ⊤
  intro h
  exact hp ((monomialValuation_eq_top_iff w p).mp h)

end SkewSchurReconstruction
