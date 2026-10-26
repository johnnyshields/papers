/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.Algebraic.Basic

/-!
# Unique rational representations at a transcendental coordinate

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`). Equality
of polynomial quotients at a transcendental coordinate is exactly equality of
cross-products. Nonzero denominators are proved nonzero after evaluation.
Sorry-free.
-/

namespace SkewCornerDescent

/-- Evaluation at a transcendental coordinate distinguishes rational functions,
without requiring a particular reduced numerator/denominator presentation. -/
theorem transcendental_rational_representation_unique {k E : Type*} [Field k] [Field E]
    [Algebra k E] {u : E} (hu : Transcendental k u)
    (p₁ q₁ p₂ q₂ : Polynomial k) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (heq : Polynomial.aeval u p₁ / Polynomial.aeval u q₁ =
      Polynomial.aeval u p₂ / Polynomial.aeval u q₂) :
    p₁ * q₂ = p₂ * q₁ := by
  have hi := transcendental_iff_injective.mp hu
  have hd₁ : Polynomial.aeval u q₁ ≠ 0 := by
    intro hz
    exact hq₁ (hi (hz.trans (map_zero _).symm))
  have hd₂ : Polynomial.aeval u q₂ ≠ 0 := by
    intro hz
    exact hq₂ (hi (hz.trans (map_zero _).symm))
  apply hi
  simpa only [map_mul] using (div_eq_div_iff hd₁ hd₂).mp heq

end SkewCornerDescent
