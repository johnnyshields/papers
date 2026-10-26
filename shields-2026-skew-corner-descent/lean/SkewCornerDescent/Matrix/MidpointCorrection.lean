/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.UnitVertexResponse
import SkewCornerDescent.Matrix.OriginalNormalDerivative

/-!
# The protected square coefficient of a midpoint unit correction

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). The
product correction of two effective monic vertex coefficients has square coefficient
minus one in its genuine original surviving generator. Its lower corrections may
be rational functions of all smaller surviving coordinates. The insertion geometry
and its endpoint coefficient producers are separate inputs to this algebraic step.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open Polynomial

/-- The univariate representative of the unit-vertex correction at its original
midpoint generator, over the full actual strictly lower coefficient field. -/
noncomputable def midpointCorrectionPolynomial (N J : ℕ+) (a b : residueLowerField N J) :
    Polynomial (residueLowerField N J) := -((Polynomial.X + Polynomial.C a) *
      (Polynomial.X + Polynomial.C b))

/-- The exact protected square coefficient is minus one, regardless of the
lower rational corrections. -/
theorem midpointCorrectionPolynomial_coeff_two (N J : ℕ+) (a b : residueLowerField N J) :
    (midpointCorrectionPolynomial N J a b).coeff 2 = -1 := by
  unfold midpointCorrectionPolynomial
  simp only [Polynomial.coeff_neg, add_mul, mul_add]
  simp

/-- Evaluating the correction retains both actual lower corrections and their
shared original higher generator; no independent response variables are inserted. -/
theorem midpointCorrectionPolynomial_aeval (N J : ℕ+) (hJ : N < J)
    (a b : residueLowerField N J) :
    Polynomial.aeval (residueGenerator N ⟨J, ne_of_gt hJ⟩)
      (midpointCorrectionPolynomial N J a b) =
        -((residueGenerator N ⟨J, ne_of_gt hJ⟩ + (a : OtherField N)) *
          (residueGenerator N ⟨J, ne_of_gt hJ⟩ + (b : OtherField N))) := by
  simp only [midpointCorrectionPolynomial, map_neg, map_mul, map_add,
    Polynomial.aeval_X, Polynomial.aeval_C, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply]

/-- A midpoint correction cannot vanish on the original selected chart when its
midpoint generator lies strictly above the selected span. -/
theorem midpoint_correction_ne_zero (N J : ℕ+) (hJ : N < J)
    (a b : OtherField N) (ha : a ∈ residueLowerField N J) (hb : b ∈ residueLowerField N J) :
    -((residueGenerator N ⟨J, ne_of_gt hJ⟩ + a) *
      (residueGenerator N ⟨J, ne_of_gt hJ⟩ + b)) ≠ 0 := by
  have hleft : residueGenerator N ⟨J, ne_of_gt hJ⟩ + a ≠ 0 := by
    intro hz
    have h := congrArg (residueGeneratorDeriv N ⟨J, ne_of_gt hJ⟩) hz
    rw [map_add, residueGeneratorDeriv_generator, ite_eq_left rfl,
      residueGeneratorDeriv_lower N ⟨J, ne_of_gt hJ⟩ ha, add_zero, map_zero] at h
    exact one_ne_zero h
  have hright : residueGenerator N ⟨J, ne_of_gt hJ⟩ + b ≠ 0 := by
    intro hz
    have h := congrArg (residueGeneratorDeriv N ⟨J, ne_of_gt hJ⟩) hz
    rw [map_add, residueGeneratorDeriv_generator, ite_eq_left rfl,
      residueGeneratorDeriv_lower N ⟨J, ne_of_gt hJ⟩ hb, add_zero, map_zero] at h
    exact one_ne_zero h
  exact neg_ne_zero.mpr (mul_ne_zero hleft hright)

end SkewCornerDescent.Matrix
