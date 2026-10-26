import SkewGluing.Mark
import SkewGluing.Composition

/-!
# The two ordinary marks on `(4, 4, 2) / (2)`: the facts stated beside the key

Formalizes `shields-2026-skew-gluing.tex`, «Component keys» (`eq:component-key`, the
example `E = (4, 4, 2) / (2)` showing that the involution cannot be omitted from the key).

The paper asserts of the two legal width-two, period-four ordinary marks `ω_a`, `ω_b` on `E`
(`gaugeInnerA`, `gaugeInnerB`): each lower copy is its end intersection `E ∩ (E - v)`, the middle
is a ribbon, and each end copy has exactly two cells adjacent to the middle.  Legality of the two
marks, the identity `(2) ∘_{ω_a} E = (1, 1) ∘_{ω_b} E` and `h₂ ≠ e₂` are in
`SkewGluing.Mark`, `SkewGluing.Composition` and `SkewGluing.MinimalFibers.Key`.

Sorry-free.
-/

namespace SkewGluing

namespace GaugeExample

/-- A ribbon: a connected skew diagram that contains no `2 × 2` block of cells. -/
def IsRibbon (R : Diagram) : Prop :=
  IsConnectedSkew R ∧ ∀ x ∈ R, ¬ (x + (0, 1) ∈ R ∧ x + (1, 0) ∈ R ∧ x + (1, 1) ∈ R)

instance (R : Diagram) : Decidable (IsRibbon R) := by
  unfold IsRibbon; infer_instance

/-- The cells of `W` that share an edge with a cell of the diagram `O`. -/
def adjacentCells (W O : Diagram) : Diagram :=
  W.filter fun x => ∃ y ∈ O, |x.1 - y.1| + |x.2 - y.2| = 1

instance (W O : Diagram) : DecidablePred (· ∈ adjacentCells W O) := by
  unfold adjacentCells; infer_instance

/-- The lower copy of each mark is the end intersection `E ∩ (E - v)`. -/
example : gaugeInnerA.W = gaugeInnerA.fullIntersection ∧
    gaugeInnerB.W = gaugeInnerB.fullIntersection := by decide +kernel

/-- The middle of each mark is a ribbon. -/
example : IsRibbon gaugeInnerA.middle ∧ IsRibbon gaugeInnerB.middle := by decide +kernel

/-- Each end copy has two cells adjacent to the middle.  The paper reads this as a violation of
Hypothesis V of McNamara–van Willigenburg, which is not defined there and not formalized. -/
example : (adjacentCells gaugeInnerA.W gaugeInnerA.middle).card = 2 ∧
    (adjacentCells gaugeInnerA.upper gaugeInnerA.middle).card = 2 ∧
    (adjacentCells gaugeInnerB.W gaugeInnerB.middle).card = 2 ∧
    (adjacentCells gaugeInnerB.upper gaugeInnerB.middle).card = 2 := by decide +kernel

end GaugeExample

end SkewGluing
