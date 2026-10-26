import SkewGluing.EqualPeriods
import SkewGluing.CommonFactorGraph
import SkewGluing.OlsonHarris.Deductions

/-!
# An edge of the common-factor graph is a fiber membership

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`def:gluing-graph`) and «Completion of the gluing proof» (`thm:gluing`, the normalization of the
two incident witnesses as proper roots of the middle diagram).

* `Chart.IsProperLegal.mem_fiberClass_parent`: a diagram with a proper chart `χ` lies in the fiber
  `𝓕(ω, s_D)` of that chart.
* `HasCommonFinalFactor.exists_chart_fiber`: if `X` and `Y` have a common final factor then `Y` has
  a proper chart `χ` such that `X` lies in the fiber `𝓕(χ.ω, s_{χ.D})`.  This is the normalization
  of an incident witness as a proper root of the middle diagram, "transporting the full marked
  inner whenever it is rotated".
* `olsonHarris_pair`: the form of the Olson-Harris composition and reversal theorems used by
  `MarkedInner.divisible`, derived from `OlsonHarrisComposition`.

Sorry-free.
-/

namespace SkewGluing

namespace Chart

/-- A diagram with a proper chart `χ` lies in the fiber of that chart: `F` is the parent of
`(χ.D, χ.ω)` up to translation, and `|χ.D| ≥ 2` with `χ.D` connected. -/
theorem IsProperLegal.mem_fiberClass_parent {χ : Chart} (hχ : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) : F ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  obtain ⟨t, rfl⟩ := hF
  exact ⟨χ.parent, ⟨χ.D, hχ.1, hχ.2.1, rfl, Or.inl rfl⟩, t, rfl⟩

end Chart

/-- A diagram `translate t (ω.compose A)` lies in the fiber `𝓕(ω, s_A)` when `A` is connected
with at least two cells. -/
theorem mem_fiberClass_compose {ω : MarkedInner} {A : Diagram} (hA : IsConnectedSkew A)
    (hc : 2 ≤ A.card) (t : ℤ × ℤ) :
    translate t (ω.compose A) ∈ fiberClass cellSchur ω (cellSchur A) :=
  ⟨ω.compose A, ⟨A, hA, hc, rfl, Or.inl rfl⟩, t, rfl⟩

/-- Likewise for the rotated marked inner. -/
theorem mem_fiberClass_rotate_compose {ω : MarkedInner} {A : Diagram} (hA : IsConnectedSkew A)
    (hc : 2 ≤ A.card) (t : ℤ × ℤ) :
    translate t (ω.rotate.compose A) ∈ fiberClass cellSchur ω (cellSchur A) :=
  ⟨ω.rotate.compose A, ⟨A, hA, hc, rfl, Or.inr rfl⟩, t, rfl⟩

/-- **Normalizing a witness of an edge as a proper root of the middle diagram.**  If `X` and `Y`
have a common final factor, then `Y` has a proper chart `χ` such that `X` lies in the fiber
`𝓕(χ.ω, s_{χ.D})` of `χ`: the witness `χ₂` of `Y` is that chart, and the witness `χ₁` of `X`
has the same marked inner up to translation or transported rotation and the same outer function. -/
theorem HasCommonFinalFactor.exists_chart_fiber {X Y : Diagram}
    (h : HasCommonFinalFactor cellSchur X Y) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf Y ∧
      X ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  obtain ⟨-, χ₁, χ₂, p₁, p₂, ⟨t, ht⟩, c₂, hω, hs⟩ := h
  refine ⟨χ₂, p₂, c₂, ?_⟩
  have hA := p₁.1
  have hc := p₁.2.1
  rw [← hs]
  have hX : X = translate t (χ₁.ω.compose χ₁.D) := ht
  rcases hω with ⟨u, hu⟩ | ⟨u, hu⟩
  · have hu' : χ₂.ω = χ₁.ω.translate u := hu
    have e : χ₁.ω.compose χ₁.D = translate (-u) (χ₂.ω.compose χ₁.D) := by
      rw [hu', MarkedInner.compose_translate, translate_translate, neg_add_cancel,
        translate_zero]
    rw [hX, e, translate_translate]
    exact mem_fiberClass_compose hA hc _
  · have hu' : χ₂.ω = χ₁.ω.rotate.translate u := hu
    have e : χ₁.ω.compose χ₁.D = translate u (χ₂.ω.rotate.compose χ₁.D) := by
      have h1 : χ₂.ω.rotate = χ₁.ω.translate (-u) := by
        rw [hu', MarkedInner.rotate_translate, MarkedInner.rotate_rotate]
      rw [h1, MarkedInner.compose_translate, translate_translate, add_neg_cancel, translate_zero]
    rw [hX, e, translate_translate]
    exact mem_fiberClass_rotate_compose hA hc _

/-- The Olson-Harris composition and reversal theorems (Thms. 5.3.9 and 5.3.10), in the exact
form consumed by `MarkedInner.divisible`, derived from the composition theorem
`OlsonHarrisComposition`. -/
theorem olsonHarris_pair (hOH : OlsonHarrisComposition) :
    ∀ (ω : MarkedInner), ω.IsLegal → ∀ D D' : Diagram, IsConnectedSkew D → IsConnectedSkew D' →
      cellSchur D = cellSchur D' →
      cellSchur (ω.compose D) = cellSchur (ω.compose D') ∧
      cellSchur (ω.rotate.compose D) = cellSchur (ω.compose D') := by
  intro ω hω D D' hD hD' h
  exact ⟨hOH ω hω D D' hD hD' h,
    (hOH.compose_eq_rotate_compose hω hD' hD h.symm).symm⟩

end SkewGluing
