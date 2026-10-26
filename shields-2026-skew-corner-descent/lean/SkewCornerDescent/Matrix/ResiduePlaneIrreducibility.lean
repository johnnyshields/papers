/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueRationalLabels
import SkewCornerDescent.TranscendentalPolynomialFactors

/-!
# Constant-plane irreducibility over the actual lower residue field

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). The no-new-algebraic-constants producer
is applied to every coefficient of a monic factor. No rationality of factor coefficients
or preserved irreducibility is assumed.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

noncomputable local instance planeIrreducibilityRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Algebraic elements of the actual lower coefficient field come from rational constants. -/
theorem residueLowerField_algebraic_constants (N K : ℕ+)
    (z : residueLowerField N K) (hz : IsAlgebraic ℚ z) :
    ∃ c : ℚ, algebraMap ℚ (residueLowerField N K) c = z := by
  let f : residueLowerField N K →ₐ[ℚ] OtherField N :=
    IsScalarTower.toAlgHom ℚ (residueLowerField N K) (OtherField N)
  have hi : IsIntegral ℚ (z : OtherField N) := IsIntegral.map f hz.isIntegral
  obtain ⟨c, hc⟩ := residueLowerField_algebraic_constant N K z.prop hi.isAlgebraic
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply ℚ (residueLowerField N K) (OtherField N) c).symm.trans
    ((map_ratCast (algebraMap ℚ (OtherField N)) c).trans hc)

/-- An irreducible monic rational polynomial stays irreducible in the actual lower field. -/
theorem residueLowerField_irreducible_map (N K : ℕ+) {p : Polynomial ℚ}
    (hp : p.Monic) (hirr : Irreducible p) :
    Irreducible (p.map (algebraMap ℚ (residueLowerField N K))) :=
  irreducible_map_of_algebraic_constants (residueLowerField_algebraic_constants N K) hp hirr

end SkewCornerDescent.Matrix
