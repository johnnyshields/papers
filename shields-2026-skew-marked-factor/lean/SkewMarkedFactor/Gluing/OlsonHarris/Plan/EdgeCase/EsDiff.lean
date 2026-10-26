/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/EsDiff.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EsDiff.Induction

/-!
# Removing the key ribbons of a downset from a composite (case (a))

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.4.3, iterated over the cells
of a downset, and the exponent count of Lemma 5.4.6 (`OlsonHarris2024HopfApplications`).

`cellSchur_copies_sdiff_liftRibbon_proof` proves the statement `cellSchur_copies_sdiff_liftRibbon`
of `EdgeCase.Geometry`.

## Route

* `EsDiff.Coords`, `EsDiff.Local`, `EsDiff.LocalEmpty`: one copy of `E` is the disjoint union of
  the key ribbon and the pieces `W₊`, `\overline W + e`, `\overline O + e` (`EdgeLocal`), in
  diagonal coordinates `(a, r)` read off the merged `Local` development.
* `EsDiff.Neighbors`, `EsDiff.Relative`, `EsDiff.Step`: for a cell `b` of a skew diagram with no
  cell to its northwest, the key ribbon of the copy at `b` meets no other copy, and the rest of the
  copy at `b` is the union of the pieces of the missing east, south, southeast neighbors, which are
  not adjacent to any other copy.
* `EsDiff.Induction`: the cells of the downset are removed one at a time in the northwest order.

**Differs from the paper's route.** The thesis argues with pictures of overlapping copies; here
the overlaps are computed from the first and last rows of the diagonals of `E`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

open scoped Classical

/-- **Removing the key ribbons of a downset leaves the composite of the rest, together with copies
of `W`, `\overline W` and `\overline O`** (thesis Lemma 5.4.3 for one box, iterated; Lemma 5.4.6):
the statement `cellSchur_copies_sdiff_liftRibbon`. -/
theorem cellSchur_copies_sdiff_liftRibbon_proof {ω : MarkedInner} (hω : ω.IsLegal)
    (hc : ω.case = .a) {X : Diagram} (hX : IsSkew X) {A : Diagram} (hA : IsDownsetIn X A) :
    cellSchur (MarkedInner.copies ω X \ liftRibbon ω X A) =
      cellSchur (MarkedInner.copies ω (X \ A)) *
        cellSchur ω.W ^ (A.filter fun x => x + (0, 1) ∉ X).card *
        cellSchur (hatMarkFin ω) ^ (A.filter fun x => x + (1, 0) ∉ X).card *
        cellSchur (hatMiddleFin ω) ^ (A.filter fun x => x + eCell ∉ X).card :=
  EsDiff.cellSchur_copies_sdiff_lift hω hc hX hA

end Plan

end SkewMarkedFactor.Gluing
