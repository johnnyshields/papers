/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinFullClass
import SkewClassInflation.RibbonDeterminants

/-!
# Two exact threshold examples

The two-row examples in `sec:examples` and
`eq:first-boundary-example` of `shields-2026-skew-class-inflation.tex`.
The original two distinct outer orders are equal; threshold one and
threshold two give distinct survival regimes.  Sorry-free.
-/

namespace SkewClassInflation

/-- The outer composition with its shorter part first. -/
def outerOneTwo : Composition 3 := ⟨[1, 2], by simp, rfl⟩

/-- The reversed, literally distinct outer composition. -/
def outerTwoOne : Composition 3 := ⟨[2, 1], by simp, rfl⟩

/-- The two outer ribbons have the same actual independent-generator polynomial. -/
theorem outer_one_two_ribbon_eq :
    ribbonWord outerOneTwo.blocks = ribbonWord outerTwoOne.blocks := by
  simp only [outerOneTwo, outerTwoOne, ribbonWord, ribbonTail]
  rw [mul_comm]

/-- The parameter pair whose first inflation is already at the boundary. -/
def thresholdOne : ThinParameters := ⟨2, 3, 1, by decide, by decide, by decide⟩

/-- The parameter pair for which one positive inflation still precedes the boundary. -/
def thresholdTwo : ThinParameters := ⟨3, 4, 1, by decide, by decide, by decide⟩

/-- Both outer orders are genuine original mates, for every admissible thin inner. -/
theorem original_two_order_equality (B : ThinParameters) :
    (B.diagram outerOneTwo (by decide)).schur =
      (B.diagram outerTwoOne (by decide)).schur := by
  have he := (B.diagram_schur_eq_iff outerOneTwo outerTwoOne (by decide)).mpr
    outer_one_two_ribbon_eq
  simpa only [ConnectedProfile.schur, profileSchur_eq_inherited,
    SkewJacobiNegative.Gluing.Profile.toBetaDiagram_schur] using he

/-- These original equal functions are attached to different literal diagrams. -/
theorem original_two_orders_distinct (B : ThinParameters) :
    B.diagram outerOneTwo (by decide) ≠ B.diagram outerTwoOne (by decide) := by
  intro he
  have hh := B.diagram_injective (by decide) he
  have hn : outerOneTwo ≠ outerTwoOne := by decide
  exact hn hh

/-- At threshold one the two distinct original mates separate immediately. -/
theorem threshold_one_separation :
    (ConnectedProfile.inflate 1 (thresholdOne.diagram outerOneTwo (by decide))).schur ≠
      (ConnectedProfile.inflate 1 (thresholdOne.diagram outerTwoOne (by decide))).schur :=
  thresholdOne.superthreshold_functions_ne outerOneTwo outerTwoOne (by decide)
    (by decide) 1 (by decide)

/-- At threshold two the same nonrotation equality survives the first positive inflation. -/
theorem threshold_two_survival :
    (ConnectedProfile.inflate 1 (thresholdTwo.diagram outerOneTwo (by decide))).schur =
      (ConnectedProfile.inflate 1 (thresholdTwo.diagram outerTwoOne (by decide))).schur := by
  have hmem : thresholdTwo.diagram outerTwoOne (by decide) ∈
      ConnectedProfile.schurClass (thresholdTwo.diagram outerOneTwo (by decide)) :=
    (original_two_order_equality thresholdTwo).symm
  have hi : ConnectedProfile.inflate 1 (thresholdTwo.diagram outerTwoOne (by decide)) ∈
      ConnectedProfile.inflate 1 ''
        ConnectedProfile.schurClass (thresholdTwo.diagram outerOneTwo (by decide)) :=
    ⟨_, hmem, rfl⟩
  rw [← thresholdTwo.subthreshold_full_class outerOneTwo (by decide) 1 (by decide)] at hi
  exact hi.symm

/-- The surviving equality disappears exactly at the second inflation. -/
theorem threshold_two_separation :
    (ConnectedProfile.inflate 2 (thresholdTwo.diagram outerOneTwo (by decide))).schur ≠
      (ConnectedProfile.inflate 2 (thresholdTwo.diagram outerTwoOne (by decide))).schur :=
  thresholdTwo.superthreshold_functions_ne outerOneTwo outerTwoOne (by decide)
    (by decide) 2 (by decide)

end SkewClassInflation
