/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.SpliceIdentity

/-!
# The left coframe over the raw field

The complete left coframe `C_K` of a cap `K` in `shields-2026-skew-coframe-rigidity.tex`
(«Rigidity with the same literal cap»), over the raw field of rational functions in the coherent
letters.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial

variable {k : ℕ}

/-- The complete left coframe `C_K` of a cap over the raw field of rational functions in the
coherent letters. -/
noncomputable def leftCoframe (K : BetaDiagram (k + 1)) : CohField[X] :=
  leftCoframeOf cohLetters K

end SkewCoframeRigidity.FixedCap
