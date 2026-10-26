/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueGeneratorCoefficientField
import SkewCornerDescent.SimpleExtensionAffine

/-!
# Unique ordinary affine coefficients of actual residue fractions

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The standard coefficient field contains every other original surviving
generator. Vanishing of the actual second partial derivative produces the
unique affine polynomial and its ordinary linear coefficient. This lemma
does not assume or assert affinity of any particular comparison. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open Polynomial

/-- A vanishing actual second partial derivative gives the unique ordinary
polynomial in the distinguished original generator over all other surviving
generators. Its linear coefficient is the original first partial derivative. -/
theorem residueGenerator_affine_polynomial (N : ℕ+) (j : {j : ℕ+ // j ≠ N})
    (f : OtherField N) (hδδ : residueGeneratorDeriv N j (residueGeneratorDeriv N j f) = 0) :
    ∃ p : Polynomial (residueGeneratorCoefficientField N j), p.natDegree ≤ 1 ∧
      Polynomial.aeval (residueGenerator N j) p = f ∧
      ((p.coeff 1 : residueGeneratorCoefficientField N j) : OtherField N) =
        residueGeneratorDeriv N j f ∧
      ∀ q : Polynomial (residueGeneratorCoefficientField N j),
        Polynomial.aeval (residueGenerator N j) q = f → q = p := by
  obtain ⟨p, hp, he, hc⟩ := simple_extension_affine_polynomial
    (residueGeneratorDeriv N j) (residueGeneratorCoefficientField N j)
    (residueGeneratorCoefficientField_fixed N j) (residueGenerator N j) (by simp)
    (residueGeneratorCoefficientField_adjoin N j) f hδδ
  refine ⟨p, hp, he, hc, ?_⟩
  intro q hq
  exact (transcendental_iff_injective.mp
    (residueGeneratorCoefficientField_transcendental N j)) (hq.trans he.symm)

end SkewCornerDescent.Matrix
