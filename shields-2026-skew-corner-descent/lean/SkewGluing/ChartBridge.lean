/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.SchurAssociates
import SkewCornerDescent.SourceMinimal

/-!
# Actual chart geometry in the two Schur APIs

Supports `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `thm:descent`).  The reverse conversion preserves legality,
period, width, and every composed cell set, so the source-minimal chart and cofactor
APIs can be used together without a mathematical assumption at their seam.

Sorry-free.
-/

namespace GluingCore

def AttachCase.toCorner : AttachCase → SkewGluing.AttachCase
  | .a => .a
  | .b => .b
  | .c => .c
  | .d => .d

/-- The same actual cells, displacement, and attachment reading in the cofactor API. -/
def MarkedInner.toCorner (ω : MarkedInner) : SkewGluing.MarkedInner :=
  ⟨ω.E, ω.W, ω.v, ω.case.toCorner⟩

theorem MarkedInner.toCorner_toGluing (ω : MarkedInner) : ω.toCorner.toGluing = ω := by
  cases ω with
  | mk E W v ac => cases ac <;> rfl

theorem MarkedInner.IsLegal.toCorner {ω : MarkedInner} (h : ω.IsLegal) :
    ω.toCorner.IsLegal := by
  have hi : ω.toCorner.IsLegal ↔ ω.IsLegal := by
    cases ω with
    | mk E W v ac =>
      cases ac <;>
        simp [SkewGluing.MarkedInner.IsLegal, MarkedInner.IsLegal,
          SkewGluing.MarkedInner.IsWellFormed, MarkedInner.IsWellFormed,
          SkewGluing.MarkedInner.IsEmptyMark, MarkedInner.IsEmptyMark,
          SkewGluing.MarkedInner.IsNonemptyMark, MarkedInner.IsNonemptyMark,
          SkewGluing.MarkedInner.AttachmentMatches, MarkedInner.AttachmentMatches,
          MarkedInner.toCorner, AttachCase.toCorner] <;> rfl
  exact hi.mpr h

theorem MarkedInner.toCorner_compose (ω : MarkedInner) (D : Diagram) :
    ω.toCorner.compose D = ω.compose D := by
  cases ω with
  | mk E W v ac => cases ac <;> rfl

theorem MarkedInner.toCorner_period (ω : MarkedInner) : ω.toCorner.period = ω.period := rfl

theorem MarkedInner.toCorner_width (ω : MarkedInner) : ω.toCorner.width = ω.width := rfl

end GluingCore
