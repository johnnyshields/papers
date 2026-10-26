/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.ValuedMonge
import SkewSchurReconstruction.PolynomialValuation
import SkewSchurReconstruction.GeneratorProducts
import SkewSchurReconstruction.MongeMinors

/-!
# The Jacobi--Trudi instance of the abstract valued family

The specialization in «An abstract Strict-Monge cofactor principle»
(`subsec:abstract`, `thm:abstract-monge`) of
`shields-2026-skew-boundary-reconstruction.tex`.
All family fields are supplied by the actual complete generators and their proved valuation.
Sorry-free.
-/

namespace SkewSchurReconstruction

/-- A concrete inhabited valued Monge family, including negative row parameters. -/
noncomputable def convexMongeFamily (w : ConvexWeight) :
    ValuedMongeFamily CompleteRing ℝ ℤ ℤ where
  valuation := polynomialAddValuation w.generatorWeight
  finite _ hp := polynomialAddValuation_finite hp
  entry A d := complete (d - A)
  support_mono := by
    intro A A' d d' hA hd hs
    apply (complete_ne_zero_iff (d - A)).mpr
    have h := (complete_ne_zero_iff (d' - A')).mp hs
    omega
  strict_monge := by
    intro A A' d d' hA hd h1 h2 h3 h4
    have hs1 := (complete_ne_zero_iff (d - A)).mp h1
    have hs2 := (complete_ne_zero_iff (d' - A')).mp h2
    have hs3 := (complete_ne_zero_iff (d' - A)).mp h3
    have hs4 := (complete_ne_zero_iff (d - A')).mp h4
    simp only [polynomialAddValuation_apply,
      complete_monomialValuation w (d - A) hs1,
      complete_monomialValuation w (d' - A') hs2,
      complete_monomialValuation w (d' - A) hs3,
      complete_monomialValuation w (d - A') hs4, WithTop.untopD_coe]
    exact w.strict_monge_int hA hd (by omega)

/-- The generic board is exactly the free-generator staircase, not a surrogate. -/
theorem convexMongeFamily_board (w : ConvexWeight) {n : ℕ} (A d : Fin n → ℤ) :
    (convexMongeFamily w).board A d = staircaseMatrix A d := rfl

end SkewSchurReconstruction
