import SkewGluing.Composition
import SkewGluing.CellSchur

/-!
# Each fiber is a clique

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`, and the paragraph on the fiber `𝓕(ω, Q)`): two distinct members
of a fiber `𝓕(ω, Q)` have a common final factor.

The outer functions of the two charts are both `Q` by definition of the fiber, and the marked
inners are `ω` or `ω*`, so the charts are proper and legal with the same marked inner up to
transported rotation.  That the members lie in one Schur class, so that this is an edge of one
common-factor graph, is `fiber_cellSchur_eq` (`SkewGluing.OlsonHarris`).

This part does not use `OlsonHarrisComposition`.

Sorry-free.
-/

namespace SkewGluing

theorem MarkedInner.equivTranslate_refl (ω : MarkedInner) : ω.EquivTranslate ω := by
  refine ⟨0, ?_⟩
  cases ω
  simp [MarkedInner.translateBy, translate_zero]

/-- **Each fiber is a clique.**  For a legal marked inner `ω` with `|E| ≥ 2`, two members of
`𝓕(ω, Q)` that are not translates of one another have a common final factor
(`HasCommonFinalFactor`). -/
theorem fiber_hasCommonFinalFactor {ω : MarkedInner} (hω : ω.IsLegal) (hE : 2 ≤ ω.E.card)
    {Q : Lambda} {F F' : Diagram} (hF : F ∈ fiber cellSchur ω Q)
    (hF' : F' ∈ fiber cellSchur ω Q) (hne : ¬ ∃ t, F' = translate t F) :
    HasCommonFinalFactor cellSchur F F' := by
  have hωr : ω.rotate.IsLegal := MarkedInner.isLegal_rotate hω
  have hEr : 2 ≤ ω.rotate.E.card := by
    change 2 ≤ (Finset.image (fun x : ℤ × ℤ => -x) ω.E).card
    rwa [Finset.card_image_of_injective _ neg_injective]
  refine ⟨hne, ?_⟩
  obtain ⟨A, hA, hA2, hAQ, hFA⟩ := hF
  obtain ⟨A', hA', hA'2, hA'Q, hFA'⟩ := hF'
  have hs : cellSchur A = cellSchur A' := by rw [hAQ, hA'Q]
  have hchart : ∀ (ω₀ : MarkedInner) (B : Diagram), (Chart.mk B ω₀).IsChartOf (ω₀.compose B) :=
    fun ω₀ B => ⟨0, by simp [Chart.parent, translate_zero]⟩
  rcases hFA with rfl | rfl <;> rcases hFA' with rfl | rfl
  · exact ⟨⟨A, ω⟩, ⟨A', ω⟩, ⟨hA, hA2, hE, hω⟩, ⟨hA', hA'2, hE, hω⟩, hchart _ _, hchart _ _,
      Or.inl (MarkedInner.equivTranslate_refl ω), hs⟩
  · exact ⟨⟨A, ω⟩, ⟨A', ω.rotate⟩, ⟨hA, hA2, hE, hω⟩, ⟨hA', hA'2, hEr, hωr⟩, hchart _ _,
      hchart _ _, Or.inr (MarkedInner.equivTranslate_refl _), hs⟩
  · refine ⟨⟨A, ω.rotate⟩, ⟨A', ω⟩, ⟨hA, hA2, hEr, hωr⟩, ⟨hA', hA'2, hE, hω⟩, hchart _ _,
      hchart _ _, Or.inr ?_, hs⟩
    simpa [MarkedInner.rotate_rotate] using MarkedInner.equivTranslate_refl ω
  · exact ⟨⟨A, ω.rotate⟩, ⟨A', ω.rotate⟩, ⟨hA, hA2, hEr, hωr⟩, ⟨hA', hA'2, hEr, hωr⟩,
      hchart _ _, hchart _ _, Or.inl (MarkedInner.equivTranslate_refl _), hs⟩

end SkewGluing
