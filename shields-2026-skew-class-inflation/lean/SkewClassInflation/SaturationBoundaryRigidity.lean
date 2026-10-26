/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationFullClass
import SkewClassInflation.SaturationBoundaryExamples

/-!
# Full classes of the strict-seam ambiguity examples

The rotation-rigidity assertions in `rem:saturation-boundaries` of
`shields-2026-skew-class-inflation.tex`.  Each strictly separated parent
has its entire unrestricted rotation class, although its one-copy inner
has a genuine nonrotation mate.  Sorry-free.
-/

namespace SkewClassInflation

/-- The first strict-seam parent has exactly its two literal global orientations as all mates. -/
theorem ambiguous_zero_parent_full_class :
    ConnectedProfile.schurClass (ambiguousInnerZero.diagram (Composition.ones 2) (by decide)) =
      {ambiguousInnerZero.diagram (Composition.ones 2) (by decide),
        ConnectedProfile.rotate (ambiguousInnerZero.diagram (Composition.ones 2) (by decide))} :=
  ambiguousInnerZero.full_class_ones 2 (by decide)

/-- The second strict-seam parent also has its entire rotation-only unrestricted class. -/
theorem ambiguous_one_parent_full_class :
    ConnectedProfile.schurClass (ambiguousInnerOne.diagram (Composition.ones 2) (by decide)) =
      {ambiguousInnerOne.diagram (Composition.ones 2) (by decide),
        ConnectedProfile.rotate (ambiguousInnerOne.diagram (Composition.ones 2) (by decide))} :=
  ambiguousInnerOne.full_class_ones 2 (by decide)

end SkewClassInflation
