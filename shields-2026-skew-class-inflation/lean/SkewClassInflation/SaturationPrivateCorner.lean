/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationWeights
import SkewClassInflation.PrivateCornerBounds

/-!
# Actual triangular corner data for general repeated powers

The complete expansion `eq:private-saturation-corner` in
`shields-2026-skew-class-inflation.tex`.  The leading generator has its
actual affine index, its signed cofactor is produced, and every residual
generator has a strictly smaller index.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- The actual power has its exact signed private-generator expansion and lower-index residual. -/
theorem power_corner_expansion (m : ℕ) (hm : 0 < m) :
    (A.power m hm).toBetaDiagram.schur =
      (-1 : CompleteRing) ^ (m * A.k) * complete A.c ^ (m * A.k) *
        complete ((m : ℤ) * A.spanIncrement + A.d) +
          (A.power m hm).toBetaDiagram.cornerResidual ∧
      ∀ j ∈ (A.power m hm).toBetaDiagram.cornerResidual.vars,
        (j.val : ℤ) < (m : ℤ) * A.spanIncrement + A.d := by
  constructor
  · let D := (A.power m hm).toBetaDiagram
    let j : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    have hc : complete D.largestLabel = (MvPolynomial.X j : CompleteRing) :=
      complete_of_pos D.largestLabel_pos
    have he := D.schur_corner_split
    change D.schur = D.cornerCoefficient * MvPolynomial.X j + D.cornerResidual at he
    rw [← hc] at he
    change (A.power m hm).toBetaDiagram.schur =
      (A.power m hm).toBetaDiagram.cornerCoefficient *
        complete (A.power m hm).toBetaDiagram.largestLabel +
          (A.power m hm).toBetaDiagram.cornerResidual at he
    rw [A.power_largest_label, BetaDiagram.cornerCoefficient, A.power_cofactor] at he
    exact he
  · intro j hj
    have he := (A.power m hm).toBetaDiagram.cornerResidual_vars_lt j hj
    rw [A.power_largest_label] at he
    exact he

end SkewClassInflation.SaturationInner
