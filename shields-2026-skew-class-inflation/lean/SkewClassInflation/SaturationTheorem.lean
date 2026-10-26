/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationClassCounts
import SkewClassInflation.SaturationCompositionCells

/-!
# Complete repeated-block saturation theorem

Formalizes `thm:repeated-block-saturation` of
`shields-2026-skew-class-inflation.tex`.  Full arbitrary-mate recovery,
both exact cardinalities, the original chart's legality, unique actual
attachments, and the literal marked presentation are composed here with
only the paper's given parameters and standing domain.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewGluing

variable (A : SaturationInner)

/-- Every actual full mate has the fixed legal marked presentation after at most one rotation. -/
theorem every_mate_legal_presentation {M : ℕ} (α : Composition M) (hM : 2 ≤ M)
    (H : ConnectedProfile) (hH : H ∈ ConnectedProfile.schurClass (A.diagram α (by omega))) :
    ∃ β : Composition M, β ∈ ribbonClass α ∧
      (H = A.diagram β (by omega) ∨ H = ConnectedProfile.rotate (A.diagram β (by omega))) ∧
      A.markedInner.IsLegal ∧
      (attachmentCells A.markedInner.W A.markedInner.middle).card = 1 ∧
      (attachmentCells A.markedInner.upper A.markedInner.middle).card = 1 ∧
      A.markedInner.compose (profileCells (outerRibbon β (by omega)).2) =
        translate (((1 - (M : ℤ)) * A.k), -(M : ℤ) * A.k)
          (profileCells (A.diagram β (by omega)).2) := by
  rw [A.full_class α hM] at hH
  rcases hH with ⟨β, hβ, he⟩ | ⟨β, hβ, he⟩
  · exact ⟨β, hβ, Or.inl he.symm, A.markedInner_legal,
      A.markedInner_hypothesisV.1, A.markedInner_hypothesisV.2,
      A.diagram_compose_eq_source β (by omega)⟩
  · exact ⟨β, hβ, Or.inr he.symm, A.markedInner_legal,
      A.markedInner_hypothesisV.1, A.markedInner_hypothesisV.2,
      A.diagram_compose_eq_source β (by omega)⟩

open scoped Classical in
/-- The full unrestricted class, exact symmetry-dependent count, and actual legal chart compose. -/
theorem repeated_block_saturation {M : ℕ} (α : Composition M) (hM : 2 ≤ M) :
    ConnectedProfile.schurClass (A.diagram α (by omega)) =
        (fun β : Composition M => A.diagram β (by omega)) '' ribbonClass α ∪
          (fun β : Composition M => ConnectedProfile.rotate (A.diagram β (by omega))) ''
            ribbonClass α ∧
      (ConnectedProfile.schurClass (A.diagram α (by omega))).ncard =
        (if A.profile.rotate = A.profile then (ribbonClass α).ncard
          else 2 * (ribbonClass α).ncard) ∧
      A.markedInner.IsLegal ∧
      (attachmentCells A.markedInner.W A.markedInner.middle).card = 1 ∧
      (attachmentCells A.markedInner.upper A.markedInner.middle).card = 1 ∧
      ∀ β ∈ ribbonClass α,
        A.markedInner.compose (profileCells (outerRibbon β (by omega)).2) =
          translate (((1 - (M : ℤ)) * A.k), -(M : ℤ) * A.k)
            (profileCells (A.diagram β (by omega)).2) := by
  obtain ⟨_, _, _, hlegal, hlower, hupper, _⟩ := A.literal_legal_chart α (by omega)
  refine ⟨A.full_class α hM, A.full_class_card α hM, hlegal, hlower, hupper, ?_⟩
  intro β _
  exact (A.literal_legal_chart β (by omega)).2.2.2.2.2.2

end SkewClassInflation.SaturationInner
