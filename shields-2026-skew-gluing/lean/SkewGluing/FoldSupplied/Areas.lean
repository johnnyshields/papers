import SkewGluing.FoldSupplied.Lift
import SkewGluing.CommonFactorGraph
import SkewGluing.Decoder

/-!
# The inner of a proper chart has strictly smaller occupied area

Formalizes `shields-2026-skew-gluing.tex`, «Recovery from the generic words» (`ge:decoder`,
the area clause) for the inner factor: the inner of a proper legal chart of `F` has fewer cells than
`F`, because its translate is a proper subset of the composite (the composite has more diagonals).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

/-- The inner of a proper legal chart has strictly fewer cells than its parent. -/
theorem Chart.IsProperLegal.inner_card_lt {χ : Chart} (hχ : χ.IsProperLegal) :
    χ.ω.E.card < χ.parent.card := by
  obtain ⟨hD, hDc, hEc, hω⟩ := hχ
  obtain ⟨d, hd⟩ := hD.2.1
  have hsub : SkewGluing.translate (χ.ω.origin χ.D d) χ.ω.E ⊆ χ.parent := by
    intro x hx
    change x ∈ χ.ω.compose χ.D
    rw [mem_compose ⟨d, hd⟩]
    exact Or.inl ⟨d, hd, hx⟩
  have hne : SkewGluing.translate (χ.ω.origin χ.D d) χ.ω.E ≠ χ.parent := by
    intro heq
    have hsp : (span χ.parent : ℤ) = (span χ.D : ℤ) * χ.ω.period + χ.ω.width :=
      span_compose hD hω
    have hE := hω.1.span_eq
    have h1 : span (SkewGluing.translate (χ.ω.origin χ.D d) χ.ω.E) = span χ.ω.E :=
      span_translate _
    have h2 : span χ.parent = span (SkewGluing.translate (χ.ω.origin χ.D d) χ.ω.E) := by
      rw [heq]
    have h4 : span χ.parent = span χ.ω.E := by rw [h2, h1]
    have h3 : 2 ≤ span χ.D := two_le_span_of_two_le_card hD hDc
    have hq := hω.period_pos
    have h5 : (span χ.D : ℤ) * χ.ω.period ≥ 2 * χ.ω.period := by
      have : (2 : ℤ) ≤ span χ.D := by exact_mod_cast h3
      nlinarith
    have h6 : (span χ.parent : ℤ) = span χ.ω.E := by rw [h4]
    omega
  have hss : SkewGluing.translate (χ.ω.origin χ.D d) χ.ω.E ⊂ χ.parent :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  have := Finset.card_lt_card hss
  rw [SkewGluing.translate, Finset.card_image_of_injective _ (add_left_injective _)] at this
  exact this

theorem Chart.IsProperLegal.inner_card_lt_of_chartOf {χ : Chart} {F : Diagram}
    (hχ : χ.IsProperLegal) (hF : χ.IsChartOf F) : χ.ω.E.card < F.card := by
  obtain ⟨t, rfl⟩ := hF
  have := hχ.inner_card_lt
  rwa [SkewGluing.translate, Finset.card_image_of_injective _ (add_left_injective _)]

/-- Both factors of a proper legal chart have strictly fewer cells than its parent
(`ge:decoder`, area clause): the outer through the sampled private heights. -/
theorem Chart.IsProperLegal.outer_card_lt {χ : Chart} (hχ : χ.IsProperLegal) :
    χ.D.card < χ.parent.card := by
  obtain ⟨hD, hDc, hEc, hω⟩ := hχ
  have hEs := two_le_span_of_two_le_card hω.1.1 hEc
  have hspE := hω.1.span_eq
  have hwq := hω.2.2.1.2
  have hf : 2 ≤ χ.ω.period := by
    have : (2 : ℤ) ≤ span χ.ω.E := by exact_mod_cast hEs
    omega
  have hP := hω.isConnectedSkew_compose hD
  have hm := two_le_span_of_two_le_card hD hDc
  have := MarkedInner.decoder_sizes (ω := χ.ω) hω hf hD (P := χ.ω.compose χ.D) hP (u := 0)
    (by rw [SkewGluing.translate_zero])
    (fun j hj0 hj => (hω.hwd_compose_private hf hD hj0 hj).1.symm) hm
  exact this.2.2.1

theorem Chart.IsProperLegal.outer_card_lt_of_chartOf {χ : Chart} {F : Diagram}
    (hχ : χ.IsProperLegal) (hF : χ.IsChartOf F) : χ.D.card < F.card := by
  obtain ⟨t, rfl⟩ := hF
  have := hχ.outer_card_lt
  rwa [SkewGluing.translate, Finset.card_image_of_injective _ (add_left_injective _)]

end SkewGluing
