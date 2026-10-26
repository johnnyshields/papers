/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.ConnectedIrreducibility
import SkewCofactorIndependence.OrdinaryReadings

/-!
# Row degree, proper corners and irreducibility

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Row degree, proper corners, and independent
coordinates» (`sec:coframe-coordinates`, `sc:row-degree`) at physical normalization: the
positive row degree of a skew diagram is its number of rows; for a connected diagram the largest
generator is its span, its coefficient is the nonzero signed proper corner, and the polynomial
is irreducible, hence primitive-prime to that corner.  The coherent homogenization over
`ℚ(ϑ)` is not formalized here.  Sorry-free.
-/

namespace SkewCoframeRigidity

open SkewCofactorIndependence MvPolynomial

namespace BetaDiagram

variable {n : ℕ}

/-- The positive row degree of a skew diagram is its number of rows (`sc:row-degree`). -/
theorem rowDegree (D : BetaDiagram n) : D.schur.totalDegree = n :=
  SkewCofactorIndependence.BetaDiagram.schur_totalDegree D

/-- For a connected diagram, the largest generator occurring is its span `M = X₁ - Y_r`, and its
coefficient is the nonzero signed proper corner `(-1)^{r-1} det T`. -/
theorem largestGenerator (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∈ D.schur.vars ∧
      (∀ j ∈ D.schur.vars, (j.val : ℤ) ≤ D.largestLabel) ∧
      pderiv (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) D.schur =
        D.cornerCoefficient ∧ D.cornerCoefficient ≠ 0 := by
  refine ⟨D.largest_mem_vars hD, fun j hj => D.vars_le_largestLabel j hj,
    D.pderiv_schur_largest, ?_⟩
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (D.cornerPolynomial_ne_zero hD)

/-- A connected skew Schur polynomial is irreducible, and so is coprime to its proper corner
unless it divides it (`sc:row-degree`, the corrected irreducibility input). -/
theorem connected_irreducible (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    Irreducible D.schur := D.schur_irreducible hD

end BetaDiagram

end SkewCoframeRigidity
