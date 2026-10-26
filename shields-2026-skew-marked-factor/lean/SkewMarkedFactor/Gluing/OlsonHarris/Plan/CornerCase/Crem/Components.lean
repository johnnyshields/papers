/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/Components.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem.Glue
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem.Ranges
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Disconnected
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Bookkeeping

/-!
# The composite of a disconnected outer is the union of the composites of its components

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), "`(D ⊔ D') ∘_W E = (D ∘_W E) ⊔ (D' ∘_W E)`", for a legal mark
of case (c) and a skew outer `X`.

* `compose_eq_biUnion`: `X ∘_ω E` is the union of the composites of the components of `X`;
* `sep_compose_components`: the composites of two components lie on separated diagonals;
* `cellSchur_Fp`: `s_{X ∘_ω E} = ∏_C s_{C ∘_ω E}`, i.e. `compSchur ω X`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner} {X C : Diagram}

theorem diagLo_component (hX : IsSkew X) (hC : C ∈ edgeComponents X) {j : ℤ}
    (hj : j ∈ contents C) : diagLo C j = diagLo X j := by
  have hjX : j ∈ contents X := by
    obtain ⟨i, hi⟩ := mem_contents_iff.mp hj
    exact mem_contents_iff.mpr ⟨i, component_subset hC hi⟩
  obtain ⟨i0, hi0⟩ := mem_contents_iff.mp hj
  refine diagLo_eq_of (l := diagLo X j) ?_ ?_
  · have hy := diagLo_mem hjX
    have hlo := diagLo_le (component_subset hC hi0) (by ring : i0 + j - i0 = j)
    exact (mem_component_iff_of_le hX hC (component_subset hC hi0) hy
      (by simpa using hlo) (by simpa using hlo)).mp hi0
  · intro i hi
    exact diagLo_le (component_subset hC hi) (by ring)

theorem origin_component (hc : ω.case = .c) (hX : IsSkew X) (hC : C ∈ edgeComponents X)
    {d : ℤ × ℤ} (hd : d ∈ C) : ω.origin C d = ω.origin X d := by
  have := diagLo_component hX hC (content_mem_contents hd)
  unfold MarkedInner.origin
  rw [hc]
  simp only [this]

theorem sameRibbon_component_iff (hc : ω.case = .c) (hX : IsSkew X) (hC : C ∈ edgeComponents X)
    {d : ℤ × ℤ} (hd : d ∈ C) : ω.SameRibbon C d ↔ ω.SameRibbon X d := by
  have e : content (d.1 - 1, d.2) = content d + 1 := by simp [content]; ring
  unfold MarkedInner.SameRibbon
  rw [hc]
  simp only
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨component_subset hC h1, ?_⟩
    have hm : content d + 1 ∈ contents C := by
      have := content_mem_contents h1
      rwa [e] at this
    rw [← diagLo_component hX hC (content_mem_contents hd), ← diagLo_component hX hC hm]
    exact h2
  · rintro ⟨h1, h2⟩
    have hn : (d.1 - 1, d.2) ∈ C := by
      refine mem_component_of_reach hC hd (Relation.ReflTransGen.single ⟨component_subset hC hd,
        h1, ?_⟩)
      rw [cellAdj_iff]; simp
    refine ⟨hn, ?_⟩
    have hm : content d + 1 ∈ contents C := by
      have := content_mem_contents hn
      rwa [e] at this
    rw [diagLo_component hX hC (content_mem_contents hd), diagLo_component hX hC hm]
    exact h2

theorem compose_eq_biUnion (hc : ω.case = .c) (hX : IsSkew X) (hXne : X.Nonempty) :
    ω.compose X = (edgeComponents X).biUnion fun C => ω.compose C := by
  ext x
  rw [Finset.mem_biUnion, mem_compose hXne]
  constructor
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hsr, hx⟩)
    · have hC : (X.filter fun y => DiagReach X d y) ∈ edgeComponents X :=
        mem_edgeComponents.mpr ⟨d, hd, rfl⟩
      have hdC : d ∈ X.filter fun y => DiagReach X d y :=
        Finset.mem_filter.mpr ⟨hd, Relation.ReflTransGen.refl⟩
      refine ⟨_, hC, ?_⟩
      rw [mem_compose ⟨d, hdC⟩]
      left
      exact ⟨d, hdC, by rw [origin_component hc hX hC hdC]; exact hx⟩
    · have hC : (X.filter fun y => DiagReach X d y) ∈ edgeComponents X :=
        mem_edgeComponents.mpr ⟨d, hd, rfl⟩
      have hdC : d ∈ X.filter fun y => DiagReach X d y :=
        Finset.mem_filter.mpr ⟨hd, Relation.ReflTransGen.refl⟩
      refine ⟨_, hC, ?_⟩
      rw [mem_compose ⟨d, hdC⟩]
      right
      exact ⟨d, hdC, (sameRibbon_component_iff hc hX hC hdC).mpr hsr,
        by rw [origin_component hc hX hC hdC]; exact hx⟩
  · rintro ⟨C, hC, hx⟩
    rw [mem_compose (component_nonempty hC)] at hx
    rcases hx with ⟨d, hd, hx⟩ | ⟨d, hd, hsr, hx⟩
    · left
      exact ⟨d, component_subset hC hd, by rw [← origin_component hc hX hC hd]; exact hx⟩
    · right
      exact ⟨d, component_subset hC hd, (sameRibbon_component_iff hc hX hC hd).mp hsr,
        by rw [← origin_component hc hX hC hd]; exact hx⟩

theorem comp_diag_sep (hX : IsSkew X) {C C' : Diagram} (hC : C ∈ edgeComponents X)
    (hC' : C' ∈ edgeComponents X) (hne : C ≠ C') {j j' : ℤ} (hj : j ∈ contents C)
    (hj' : j' ∈ contents C') : j + 1 < j' ∨ j' + 1 < j := by
  by_contra hcon
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hj
  obtain ⟨i', hi'⟩ := mem_contents_iff.mp hj'
  have hxX := component_subset hC hi
  have hyX := component_subset hC' hi'
  have hcmp : (i ≤ i' ∧ i + j ≤ i' + j') ∨ (i' ≤ i ∧ i' + j' ≤ i + j) := by omega
  have hsame : (i, i + j) ∈ C' := by
    rcases hcmp with h | h
    · exact (mem_component_iff_of_le hX hC' hyX hxX (x := (i', i' + j')) (y := (i, i + j))
        h.1 h.2).mp hi'
    · exact (mem_component_iff_of_le hX hC' hxX hyX (x := (i, i + j)) (y := (i', i' + j'))
        h.1 h.2).mpr hi'
  exact hne (by
    have := edgeComponents_disjoint hC hC' hne
    exact absurd hsame (fun h => Finset.disjoint_left.mp this hi h))

theorem sep_compose_components (h : ω.IsLegalNonempty) (hX : IsSkew X) {C C' : Diagram}
    (hC : C ∈ edgeComponents X) (hC' : C' ∈ edgeComponents X) (hne : C ≠ C') :
    Sep (ω.compose C) (ω.compose C') := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hq0 : 0 < ω.period := by omega
  intro x hx y hy
  obtain ⟨j, hj, h1, h2⟩ := content_compose_block h (component_nonempty hC) hx
  obtain ⟨j', hj', h3, h4⟩ := content_compose_block h (component_nonempty hC') hy
  obtain ⟨f1, f2, f3, f4⟩ := far_facts hq0 j j'
  rcases comp_diag_sep hX hC hC' hne hj hj' with h5 | h5
  · have := f4 h5
    rw [abs_of_nonpos (by omega)]; omega
  · have := f3 h5
    rw [abs_of_nonneg (by omega)]; omega

theorem cellSchur_Fp (h : ω.IsLegalNonempty) (hc : ω.case = .c) (hX : IsSkew X) :
    cellSchur (Fp ω X) = compSchur ω X := by
  unfold Fp compSchur
  by_cases hXe : X = ∅
  · subst hXe
    simp [edgeComponents_empty]
  · simp only [hXe, ↓reduceIte]
    rw [compose_eq_biUnion hc hX (Finset.nonempty_iff_ne_empty.mpr hXe),
      cellSchur_biUnion_sep _ _ (fun C hC C' hC' hne => sep_compose_components h hX hC hC' hne)]

end Rem

end Corner

end Plan

end SkewMarkedFactor.Gluing
