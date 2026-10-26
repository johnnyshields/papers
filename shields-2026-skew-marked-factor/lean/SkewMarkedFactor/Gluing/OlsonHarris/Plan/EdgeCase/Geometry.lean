/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/Geometry.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.TFun
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Ribbons
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EdgeRibbon
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EsDiff

/-!
# The geometry of the composite of a legal mark of case (a)

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis §5.3.3 and §5.4
(`OlsonHarris2024HopfApplications`), Thm. 5.4.1 and Lemmas 5.4.2–5.4.5.

Cell-level statements about the union of copies `copies ω X` for a legal mark of case (a), about
`keyRibbon ω` and `liftRibbon ω X A` of `Plan.Defs`: `keyRibbon ω` is the top key ribbon `K↑(E)`
(the cells of the northwest border of `E` whose contents lie in the `q` contents ending at the
greatest content of the middle), and `liftRibbon ω X A` is the union of the copies of `K↑(E)` at
the cells of `A`, so for a ribbon `A` removable on the left from `X` it is `A ∘ K↑(E)`.

`leftRibbons_copies` is proved in `EdgeCase.EdgeRibbon` and `cellSchur_copies_sdiff_liftRibbon`
in `EdgeCase.EsDiff`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

open scoped Classical

/-- **The ribbons of size `m q` removable on the left from a composite** (thesis Lemma 5.4.5 (1)
with Lemma 5.2.9): they are the lifts `A ∘ K↑(E)` of the ribbons `A` of size `m` removable on the
left from the outer diagram, the lift is injective, and `ht (A ∘ K↑(E)) = m h(E) + ht A` with
`h(E) ≡ |v₁|`.
  The proof, from the border word of the composite, is in
`SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EdgeRibbon`. -/
theorem leftRibbons_copies {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .a) {C : Diagram}
    (hC : IsConnectedSkew C) {m : ℕ} (hm : 0 < m) :
    leftRibbons (MarkedInner.copies ω C) (m * ω.period.toNat) =
        (leftRibbons C m).image (liftRibbon ω C) ∧
      Set.InjOn (liftRibbon ω C) (leftRibbons C m : Set Diagram) ∧
      ∀ A ∈ leftRibbons C m,
        ribbonSign (liftRibbon ω C A) = (-1) ^ (m * ω.v.1.natAbs) * ribbonSign A :=
  leftRibbons_copies_proof hω hc hC hm

/-- **Removing the key ribbons of a downset leaves the composite of the rest, together with copies
of `W`, `\overline W` and `\overline O`** (thesis Lemma 5.4.3 for one box, iterated; Lemma 5.4.6):
for a skew diagram `X` and a downset `A` of `X`, `copies ω X \ A ∘ K↑(E)` is the edge-disjoint
union of `copies ω (X \ A)` and, for each `b ∈ A`, a copy of `W` if `b` has no box to its east in
`X`, a copy of `\overline W` if `b` has no box to its south, a copy of `\overline O` if `b` has no
box to its southeast.
  The proof (the single-box statement and the induction over the downset) is in
`SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EsDiff`. -/
theorem cellSchur_copies_sdiff_liftRibbon {ω : MarkedInner} (hω : ω.IsLegal)
    (hc : ω.case = .a) {X : Diagram} (hX : IsSkew X) {A : Diagram} (hA : IsDownsetIn X A) :
    cellSchur (MarkedInner.copies ω X \ liftRibbon ω X A) =
      cellSchur (MarkedInner.copies ω (X \ A)) *
        cellSchur ω.W ^ (A.filter fun x => x + (0, 1) ∉ X).card *
        cellSchur (hatMarkFin ω) ^ (A.filter fun x => x + (1, 0) ∉ X).card *
        cellSchur (hatMiddleFin ω) ^ (A.filter fun x => x + eCell ∉ X).card :=
  cellSchur_copies_sdiff_liftRibbon_proof hω hc hX hA

end Plan

end SkewMarkedFactor.Gluing
