/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/RotateRoot.lean`. -/
import GluingCore.SmallOverlap.RootFacts

/-!
# Rotation of a proper root

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the reduction of case (c) to case (d) by rotation.

`Chart.IsProperRoot.rotate`: a proper root of period `p` of `F` rotates to a proper root of the
same period of the rotated diagram, with the same width and the rotated attachment case.

Sorry-free.
-/

namespace GluingCore

open MarkedInner

theorem Chart.IsProperRoot.rotate {χ : Chart} {F : Diagram} {p : ℕ} (h : χ.IsProperRoot F p) :
    χ.rotate.IsProperRoot (GluingCore.rotate F) p := by
  obtain ⟨hp, ⟨t, ht⟩, hq⟩ := h
  refine ⟨hp.rotate, ⟨-t, ?_⟩, hq⟩
  rw [Chart.parent_rotate hp, ht, rotate_translate_eq]

theorem Chart.rotate_ω (χ : Chart) : χ.rotate.ω = χ.ω.rotate := rfl

theorem Chart.rotate_width (χ : Chart) : χ.rotate.ω.width = χ.ω.width := width_rotate _

end GluingCore
