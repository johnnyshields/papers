/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MarkedCharts
import SkewMarkedFactor.Gluing.EqualPeriods

/-!
# Ordinary mark atlas

«Equal functions at a common period» (`sec:transport`, `lem:mark-atlas`,
`eq:gauge`) of `shields-2026-skew-marked-factor.tex`.
The comparison uses the inner diagram and the period alone.  No equality of
literal parent diagrams is assumed.  Both empty-edge readings are included.
-/

namespace SkewMarkedFactor
open Gluing

namespace MarkAtlas

/-- Marked-inner equality is equality of its four actual data fields. -/
private theorem ext {η θ : MarkedInner} (hE : η.E = θ.E) (hW : η.W = θ.W)
    (hv : η.v = θ.v) (hc : η.case = θ.case) : η = θ := by
  cases η
  cases θ
  simp_all

/-- The inner of every admitted mark is a genuine connected skew diagram. -/
theorem inner_connected {η : MarkedInner} (h : η.IsReadoutLegal) : IsConnectedSkew η.E := by
  rcases h with h | ⟨h, _⟩
  · exact h.1.1
  · exact h

/-- The two empty displacements have exactly the same period. -/
theorem empty_period_eq (E : Diagram) : (emptyMarkV E).period = (emptyMarkH E).period := by
  change content (vV E) = content (vH E)
  rw [vH_eq_vV_add_eCell, content_add]
  simp [content, eCell]

/-- The span law is valid in the paper's broader mark domain. -/
theorem span_eq {η : MarkedInner} (h : η.IsReadoutLegal) :
    (span η.E : ℤ) = η.period + η.width := by
  rcases h with h | ⟨hE, he⟩
  · exact h.1.span_eq
  · have hh := (emptyMarkH_isLegal hE).1.span_eq
    have hp := empty_period_eq η.E
    have hW : η.W = ∅ := by simpa only [emptyMarkV] using congrArg MarkedInner.W he
    have hper : η.period = (emptyMarkV η.E).period := congrArg MarkedInner.period he
    simpa only [hper, hp, hW, MarkedInner.width, emptyMarkH, span, contents,
      Finset.image_empty, Finset.card_empty, Nat.cast_zero, add_zero] using hh

/-- Equal supplied periods on a fixed inner have equal mark widths. -/
theorem width_eq {η θ : MarkedInner} (hη : η.IsReadoutLegal) (hθ : θ.IsReadoutLegal)
    (hE : θ.E = η.E) (hp : θ.period = η.period) : θ.width = η.width := by
  have h1 := span_eq hη
  have h2 := span_eq hθ
  rw [hE, hp] at h2
  have he : (θ.width : ℤ) = (η.width : ℤ) := by omega
  exact_mod_cast he

/-- The horizontal/vertical alternatives are the literal empty-edge data. -/
theorem empty_cases {η : MarkedInner} (h : η.IsReadoutLegal) (hW : η.W = ∅) :
    η = emptyMarkH η.E ∨ η = emptyMarkV η.E := by
  rcases h with h | ⟨_, he⟩
  · rcases h.1.2 with hh | hn
    · exact Or.inl (ext rfl hh.1 hh.2.1 hh.2.2)
    · exact False.elim (hn.1.ne_empty hW)
  · exact Or.inr he

/-- Positive width is equivalent to nonemptiness of the actual lower mark. -/
theorem width_pos {η : MarkedInner} (hW : η.W.Nonempty) : 0 < η.width := by
  exact Finset.card_pos.mpr (hW.image content)

/-- Equal widths transfer actual nonemptiness without a geometric certificate. -/
theorem nonempty_of_width_eq {η θ : MarkedInner} (hw : θ.width = η.width)
    (hη : η.W.Nonempty) : θ.W.Nonempty := by
  have hp : 0 < θ.width := by rw [hw]; exact width_pos hη
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hp
  obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hc
  exact ⟨x, hx⟩

end MarkAtlas

/-- At a fixed inner and period there is at most one legal mark of each attachment type. -/
theorem ordinary_mark_unique {η θ : MarkedInner}
    (hη : η.IsReadoutLegal) (hθ : θ.IsReadoutLegal)
    (hE : θ.E = η.E) (hp : θ.period = η.period) (hc : θ.case = η.case) : θ = η := by
  classical
  have hw := MarkAtlas.width_eq hη hθ hE hp
  by_cases hW : η.W.Nonempty
  · have hWθ := MarkAtlas.nonempty_of_width_eq hw hW
    have hlη := (MarkedInner.readoutLegal_iff_of_nonempty hW).mp hη
    have hlθ := (MarkedInner.readoutLegal_iff_of_nonempty hWθ).mp hθ
    rcases hlη.displacement_adjacent hlθ hW hWθ hE hw with hv | hv | hv
    · exact hlη.eq_of_displacement hlθ hW hWθ hE hv
    · obtain ⟨hηb, hθa⟩ := hlη.double_cases hlθ hW hWθ hE hw hv
      simp [hηb, hθa] at hc
    · obtain ⟨hθb, hηa⟩ := hlθ.double_cases hlη hWθ hW hE.symm hw.symm hv
      simp [hθb, hηa] at hc
  · have heη : η.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    have heθ : θ.W = ∅ := by
      by_contra hn
      have hpθ := MarkAtlas.width_pos (Finset.nonempty_iff_ne_empty.mpr hn)
      rw [hw] at hpθ
      simp [MarkedInner.width, heη, span, contents] at hpθ
    rcases MarkAtlas.empty_cases hη heη with hηH | hηV <;>
      rcases MarkAtlas.empty_cases hθ heθ with hθH | hθV
    · rw [hθH, hE, ← hηH]
    · have hηa : η.case = .a := by simpa only [emptyMarkH] using congrArg MarkedInner.case hηH
      have hθb : θ.case = .b := by simpa only [emptyMarkV] using congrArg MarkedInner.case hθV
      simp [hηa, hθb] at hc
    · have hηb : η.case = .b := by simpa only [emptyMarkV] using congrArg MarkedInner.case hηV
      have hθa : θ.case = .a := by simpa only [emptyMarkH] using congrArg MarkedInner.case hθH
      simp [hηb, hθa] at hc
    · rw [hθV, hE, ← hηV]

/-- The two ordinary alternatives differ by exactly the stated diagonal displacement. -/
theorem ordinary_mark_displacement {ηa ηb : MarkedInner}
    (ha : ηa.IsReadoutLegal) (hb : ηb.IsReadoutLegal)
    (hE : ηb.E = ηa.E) (hp : ηb.period = ηa.period)
    (hca : ηa.case = .a) (hcb : ηb.case = .b) : ηa.v = ηb.v + eCell := by
  classical
  have hw := MarkAtlas.width_eq ha hb hE hp
  by_cases hW : ηa.W.Nonempty
  · have hWb := MarkAtlas.nonempty_of_width_eq hw hW
    have hla := (MarkedInner.readoutLegal_iff_of_nonempty hW).mp ha
    have hlb := (MarkedInner.readoutLegal_iff_of_nonempty hWb).mp hb
    rcases hla.displacement_adjacent hlb hW hWb hE hw with he | he | he
    · have heq := hla.eq_of_displacement hlb hW hWb hE he
      have hc := congrArg MarkedInner.case heq
      simp [hca, hcb] at hc
    · have hc := (hla.double_cases hlb hW hWb hE hw he).1
      simp [hca] at hc
    · exact he
  · have heWa : ηa.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    have heWb : ηb.W = ∅ := by
      by_contra hn
      have hpw := MarkAtlas.width_pos (Finset.nonempty_iff_ne_empty.mpr hn)
      rw [hw] at hpw
      simp [MarkedInner.width, heWa, span, contents] at hpw
    rcases MarkAtlas.empty_cases ha heWa with heHa | heVa
    · rcases MarkAtlas.empty_cases hb heWb with heHb | heVb
      · have hc := congrArg MarkedInner.case heHb
        simp [emptyMarkH, hcb] at hc
      · have hva := congrArg MarkedInner.v heHa
        have hvb := congrArg MarkedInner.v heVb
        simp only [emptyMarkH, emptyMarkV] at hva hvb
        rw [hva, hvb, hE]
        exact vH_eq_vV_add_eCell _
    · have hc := congrArg MarkedInner.case heVa
      simp [emptyMarkV, hca] at hc

/-- The actual ordinary gauge uses antitransposition of the outer, not transposition. -/
theorem ordinary_mark_gauge {ηa ηb : MarkedInner}
    (ha : ηa.IsReadoutLegal) (hb : ηb.IsReadoutLegal)
    (hE : ηb.E = ηa.E) (hp : ηb.period = ηa.period)
    (hca : ηa.case = .a) (hcb : ηb.case = .b)
    {D : Diagram} (hD : D.Nonempty) :
    ηa.compose D = ηb.compose (antitranspose D) :=
  MarkedInner.compose_antitranspose_gauge hD hE.symm hca hcb
    (ordinary_mark_displacement ha hb hE hp hca hcb)

/-- The span identity includes the vertical empty-edge reading of `eq:span`. -/
theorem readout_span_compose {η : MarkedInner} (hη : η.IsReadoutLegal)
    {D : Diagram} (hD : IsConnectedSkew D) :
    (span (η.compose D) : ℤ) = (span D : ℤ) * η.period + η.width := by
  rcases hη with hl | ⟨hE, he⟩
  · exact MarkedInner.span_compose hD hl
  · have hg := ordinary_mark_gauge
      (MarkedInner.emptyMarkH_readoutLegal hE)
      (MarkedInner.emptyMarkV_readoutLegal hE) rfl (MarkAtlas.empty_period_eq η.E)
      rfl rfl (isConnectedSkew_antitranspose hD).2.1
    rw [antitranspose_antitranspose] at hg
    have hs := MarkedInner.span_compose (isConnectedSkew_antitranspose hD)
      (emptyMarkH_isLegal hE)
    rw [hg, span_antitranspose] at hs
    have hw : η.width = (emptyMarkH η.E).width := by
      rw [he]
      rfl
    have hp : η.period = (emptyMarkH η.E).period := by
      rw [he]
      exact MarkAtlas.empty_period_eq _
    simpa only [← he, ← hp, ← hw] using hs

end SkewMarkedFactor
