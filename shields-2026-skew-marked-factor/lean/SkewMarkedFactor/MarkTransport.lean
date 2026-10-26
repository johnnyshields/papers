/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MarkAtlas

/-!
# Transport of the full readout mark domain

The translation and transported rotation used in `thm:transport` of
`shields-2026-skew-marked-factor.tex`.
Rotation uses the upper copy as the new lower mark, and both empty readings
are preserved by the actual corner-displacement formulas.
-/

namespace SkewMarkedFactor
open Gluing

namespace Gluing.MarkedInner

/-- The vertical empty datum translates with the inner, keeping its displacement. -/
theorem emptyMarkV_translate {E : Diagram} (hE : E.Nonempty) (t : ℤ × ℤ) :
    (emptyMarkV E).translate t = emptyMarkV (Gluing.translate t E) := by
  have hv : vV (Gluing.translate t E) = vV E := by
    unfold vV
    rw [ne_translate hE, sw_translate hE]
    abel
  have hempty : Gluing.translate t ∅ = ∅ := Finset.image_empty _
  simp only [MarkedInner.translate, emptyMarkV, hempty, hv]

/-- Rotation keeps the actual vertical displacement, while moving the lower copy correctly. -/
theorem emptyMarkV_rotate {E : Diagram} (hE : IsConnectedSkew E) :
    (emptyMarkV E).rotate = emptyMarkV (Gluing.rotate E) := by
  have hv : vV (Gluing.rotate E) = vV E := by
    unfold vV
    rw [ne_rotate hE, sw_rotate hE]
    abel
  have ht : Gluing.translate (vV E) ∅ = ∅ := Finset.image_empty _
  have hr : Gluing.rotate ∅ = ∅ := Finset.image_empty _
  simp only [MarkedInner.rotate, emptyMarkV, MarkedInner.upper,
    ht, hr, AttachCase.rotate, hv]

/-- Readout legality, including the vertical empty mark, survives translation. -/
theorem IsReadoutLegal.translate {η : MarkedInner} (hη : η.IsReadoutLegal)
    (t : ℤ × ℤ) : (η.translate t).IsReadoutLegal := by
  rcases hη with hη | ⟨hE, he⟩
  · exact (isLegal_translate t hη).readoutLegal
  · right
    refine ⟨isConnectedSkew_translate t hE, ?_⟩
    rw [he, emptyMarkV_translate hE.2.1]
    rfl

/-- Full legality is invariant under translation in both directions. -/
theorem readoutLegal_translate_iff (η : MarkedInner) (t : ℤ × ℤ) :
    (η.translate t).IsReadoutLegal ↔ η.IsReadoutLegal := by
  refine ⟨fun h => ?_, fun h => h.translate t⟩
  simpa only [MarkedInner.translate_neg_translate] using h.translate (-t)

/-- Transported rotation preserves the full readout legal domain. -/
theorem IsReadoutLegal.rotate {η : MarkedInner} (hη : η.IsReadoutLegal) :
    η.rotate.IsReadoutLegal := by
  rcases hη with hη | ⟨hE, he⟩
  · exact (isLegal_rotate hη).readoutLegal
  · right
    refine ⟨isConnectedSkew_rotate hE, ?_⟩
    rw [he, emptyMarkV_rotate hE]
    rfl

/-- Full legality is invariant under transported rotation in both directions. -/
theorem readoutLegal_rotate_iff (η : MarkedInner) :
    η.rotate.IsReadoutLegal ↔ η.IsReadoutLegal := by
  refine ⟨fun h => ?_, IsReadoutLegal.rotate⟩
  simpa only [MarkedInner.rotate_rotate] using h.rotate

/-- Ordinary attachment is exactly one of the two unmixed cases. -/
theorem IsOrdinary.cases {η : MarkedInner} (hη : η.IsOrdinary) :
    η.case = .a ∨ η.case = .b := by
  cases hc : η.case <;> simp_all [IsOrdinary, AttachCase.IsMixed]

/-- Transport preserves ordinary attachment, without relabeling the mark. -/
theorem IsOrdinary.rotate {η : MarkedInner} (hη : η.IsOrdinary) :
    η.rotate.IsOrdinary := by
  rcases hη.cases with hc | hc <;>
    simp [IsOrdinary, MarkedInner.rotate, hc, AttachCase.rotate, AttachCase.IsMixed]

end Gluing.MarkedInner

/-- The actual inner translation preserves its number of cells. -/
theorem diagram_card_translate (E : Diagram) (t : ℤ × ℤ) :
    (translate t E).card = E.card :=
  Finset.card_image_of_injective _ (add_left_injective t)

/-- Negation preserves the number of cells, including the empty diagram. -/
theorem diagram_card_rotate (E : Diagram) : (rotate E).card = E.card :=
  Finset.card_image_of_injective _ neg_injective

namespace Gluing.Chart

/-- Moving only the inner preserves every properness bound and the supplied period. -/
theorem IsProperReadoutLegal.translate_inner {χ : Chart} (hχ : χ.IsProperReadoutLegal)
    (t : ℤ × ℤ) : ({χ with ω := χ.ω.translate t} : Chart).IsProperReadoutLegal := by
  refine ⟨hχ.1, hχ.2.1, ?_, hχ.2.2.2.translate t⟩
  simpa only [MarkedInner.translate_E, diagram_card_translate] using hχ.2.2.1

/-- Rotating both actual diagrams preserves every properness bound. -/
theorem IsProperReadoutLegal.rotate {χ : Chart} (hχ : χ.IsProperReadoutLegal) :
    ({D := Gluing.rotate χ.D, ω := χ.ω.rotate} : Chart).IsProperReadoutLegal := by
  refine ⟨isConnectedSkew_rotate hχ.1, ?_, ?_, hχ.2.2.2.rotate⟩
  · simpa only [diagram_card_rotate] using hχ.2.1
  · simpa only [MarkedInner.rotate_E, diagram_card_rotate] using hχ.2.2.1

end Gluing.Chart

/-- A marked fiber already includes its transported rotation, with the same outer function. -/
theorem fiberClass_rotate {R : Type*} (s : Diagram → R) (η : MarkedInner) (Q : R) :
    fiberClass s η.rotate Q = fiberClass s η Q := by
  have hf : fiber s η.rotate Q = fiber s η Q := by
    ext F
    simp only [fiber, MarkedInner.rotate_rotate, or_comm]
  unfold fiberClass
  rw [hf]

end SkewMarkedFactor
