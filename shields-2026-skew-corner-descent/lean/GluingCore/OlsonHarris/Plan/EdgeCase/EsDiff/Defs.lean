-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/EsDiff/Defs.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.TFun
import GluingCore.OlsonHarris.Plan.EdgeCase.HatShapes

/-!
# The three pieces of a copy

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis §5.3.3 and §5.4
(`OlsonHarris2024HopfApplications`), Lemma 5.4.3.

The pieces `pieceE`, `pieceS`, `pieceSE` of a copy of `E` are the
translates of `W`, `\overline W`, `\overline O` that remain of the copy after removing the key
ribbon and the cells shared with the copies at the neighboring cells.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

namespace EsDiff

open scoped Classical

/-- The piece of a copy of `E` that is shared with the copy at the cell to the east: `W₊`. -/
def pieceE (ω : MarkedInner) : Diagram := translate ω.v ω.W

/-- The piece of a copy of `E` that is shared with the copy at the cell to the south, a
translate of `\overline W`. -/
def pieceS (ω : MarkedInner) : Diagram := translate eCell (hatMarkFin ω)

/-- The piece of a copy of `E` that is shared with the copy at the cell to the southeast, a
translate of `\overline O`. -/
def pieceSE (ω : MarkedInner) : Diagram := translate eCell (hatMiddleFin ω)

theorem mem_nwBorder {E : Diagram} {z : ℤ × ℤ} : z ∈ nwBorder E ↔ z ∈ E ∧ z - eCell ∉ E := by
  unfold nwBorder
  rw [Finset.mem_filter]

theorem mem_keyRibbon {ω : MarkedInner} {z : ℤ × ℤ} :
    z ∈ keyRibbon ω ↔ (z ∈ ω.E ∧ z - eCell ∉ ω.E) ∧
      maxContent ω.middle - ω.period < content z ∧ content z ≤ maxContent ω.middle := by
  unfold keyRibbon
  rw [Finset.mem_filter, mem_nwBorder]

theorem mem_liftRibbon {ω : MarkedInner} {X A : Diagram} {z : ℤ × ℤ} :
    z ∈ liftRibbon ω X A ↔ ∃ b ∈ A, z ∈ translate (ω.origin X b) (keyRibbon ω) := by
  unfold liftRibbon
  rw [Finset.mem_biUnion]

theorem mem_pieceE {ω : MarkedInner} {z : ℤ × ℤ} : z ∈ pieceE ω ↔ z - ω.v ∈ ω.W := by
  unfold pieceE
  rw [mem_translate]

theorem mem_pieceS {ω : MarkedInner} {z : ℤ × ℤ} : z ∈ pieceS ω ↔ z - eCell ∈ hatMarkFin ω := by
  unfold pieceS
  rw [mem_translate]

theorem mem_pieceSE {ω : MarkedInner} {z : ℤ × ℤ} :
    z ∈ pieceSE ω ↔ z - eCell ∈ hatMiddleFin ω := by
  unfold pieceSE
  rw [mem_translate]

/-! ### Checks on the worked marks -/

/-- On the chart-figure mark, `E` is the key ribbon `{(-2, 1), (-1, 0), (-1, 1)}`, the domino `W₊`
and the cell `(0, 0)`, a translate of `\overline W`; `\overline O` is empty. -/
example : keyRibbon chartFigureInner = {(-2, 1), (-1, 0), (-1, 1)} := by decide +kernel
example : pieceE chartFigureInner = {(-2, 2), (-1, 2)} := by decide +kernel
example : pieceS chartFigureInner = {(0, 0)} := by decide +kernel
example : pieceSE chartFigureInner = ∅ := by decide +kernel

/-- On `gaugeInnerA`, `E` is the disjoint union of the key ribbon and the three pieces. -/
example : keyRibbon gaugeInnerA ∪ pieceE gaugeInnerA ∪ pieceS gaugeInnerA ∪ pieceSE gaugeInnerA =
    gaugeInnerA.E := by decide +kernel
example : (keyRibbon gaugeInnerA).card + (pieceE gaugeInnerA).card + (pieceS gaugeInnerA).card +
    (pieceSE gaugeInnerA).card = gaugeInnerA.E.card := by decide +kernel

end EsDiff

end Plan

end GluingCore
