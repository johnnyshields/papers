/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.PrivateDiagonals
import SkewGluing.InteriorBounds

/-!
# Finite end caps

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`sec:marks`, `eq:caps`, `eq:local-properties`).

Missing private diagonals separate the southeast interior into finite skew caps and the
middle interior. Content thresholds are relative to the least content, so no normalization
of the diagram is required.

Sorry-free.
-/

namespace SkewGluing

/-- Cutting below an unoccupied diagonal preserves skewness. An arbitrary content cut does not. -/
theorem IsSkew.filter_content_lt_of_gap {D : Diagram} (hD : IsSkew D) (k : ℤ)
    (hgap : ∀ x ∈ D, content x ≠ k) : IsSkew (D.filter fun x => content x < k) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxD, hxk⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyD, _⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hD x hxD y hyD h1 h2 i hi j hj, ?_⟩
  by_contra hnot
  have hcell : (i, i + k) ∈ D := hD x hxD y hyD h1 h2 i hi (i + k) (by
    rw [Finset.mem_Icc] at hi hj ⊢
    simp only [content] at hxk hnot
    omega)
  exact hgap _ hcell (by simp [content])

/-- Cutting above an unoccupied diagonal preserves skewness. -/
theorem IsSkew.filter_content_gt_of_gap {D : Diagram} (hD : IsSkew D) (k : ℤ)
    (hgap : ∀ x ∈ D, content x ≠ k) : IsSkew (D.filter fun x => k < content x) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxD, _⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyD, hyk⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hD x hxD y hyD h1 h2 i hi j hj, ?_⟩
  by_contra hnot
  have hcell : (i, i + k) ∈ D := hD x hxD y hyD h1 h2 i hi (i + k) (by
    rw [Finset.mem_Icc] at hi hj ⊢
    simp only [content] at hyk hnot
    omega)
  exact hgap _ hcell (by simp [content])

namespace MarkedInner
/-- A diagram supported in an open content interval has at most its interval's length in span. -/
theorem span_le_of_content_Ioo {D : Diagram} (a b : ℤ)
    (hb : ∀ x ∈ D, a < content x ∧ content x < b) :
    (span D : ℤ) ≤ max 0 (b - a - 1) := by
  have hsub : contents D ⊆ Finset.Ioo a b := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Ioo.mpr (hb x hx)
  have hc := Finset.card_le_card hsub
  rw [Int.card_Ioo] at hc
  change span D ≤ _ at hc
  omega


/-- The finite lower cap, at contents strictly below the first private diagonal. -/
def lowerCap (ω : MarkedInner) : Diagram :=
  (diagramInterior ω.E).filter fun x => content x < minContent ω.E + ω.width

/-- The finite upper cap, at contents strictly above the last private diagonal. -/
def upperCap (ω : MarkedInner) : Diagram :=
  (diagramInterior ω.E).filter fun x => minContent ω.E + ω.period - 1 < content x

variable {ω : MarkedInner}

/-- Southeast erosion removes both private singleton diagonals. -/
theorem IsLegal.interior_private_gaps (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {x : ℤ × ℤ} (hx : x ∈ diagramInterior ω.E) :
    content x ≠ minContent ω.E + ω.width ∧
      content x ≠ minContent ω.E + ω.period - 1 := by
  obtain ⟨hxE, hxeE⟩ := Finset.mem_filter.mp hx
  constructor
  · intro hc
    have he := h.private_lower_subsingleton hW hxE hxeE hc (content_eCell_add x)
    have := congrArg Prod.fst he
    simp only [eCell, Prod.fst_add] at this
    omega
  · intro hc
    have he := h.private_upper_subsingleton hW hxE hxeE hc (content_eCell_add x)
    have := congrArg Prod.fst he
    simp only [eCell, Prod.fst_add] at this
    omega

/-- Legality, rather than an arbitrary band restriction, makes the finite lower cap skew. -/
theorem IsLegal.isSkew_lowerCap (h : ω.IsLegal) (hW : ω.W.Nonempty) : IsSkew ω.lowerCap :=
  h.1.1.1.interior.filter_content_lt_of_gap _
    (fun _ hx => (h.interior_private_gaps hW hx).1)

/-- The upper cap is skew by the missing last private diagonal. -/
theorem IsLegal.isSkew_upperCap (h : ω.IsLegal) (hW : ω.W.Nonempty) : IsSkew ω.upperCap :=
  h.1.1.1.interior.filter_content_gt_of_gap _
    (fun _ hx => (h.interior_private_gaps hW hx).2)

/-- The middle interior avoids the marked bands and the two private singleton diagonals. -/
theorem IsLegal.middleInterior_content (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {x : ℤ × ℤ} (hx : x ∈ diagramInterior ω.middle) :
    minContent ω.E + ω.width < content x ∧
      content x < minContent ω.E + ω.period - 1 := by
  obtain ⟨hxO, hxeO⟩ := Finset.mem_filter.mp hx
  have hxE := (mem_middle.mp hxO).1
  have hxeE := (mem_middle.mp hxeO).1
  have hxI : x ∈ diagramInterior ω.E := Finset.mem_filter.mpr ⟨hxE, hxeE⟩
  have hgap := h.interior_private_gaps hW hxI
  have hthin : ¬(content x ≤ minContent ω.E + ω.width - 1 ∨
      minContent ω.E + ω.period ≤ content x) := by
    intro hc
    have he := h.middle_subsingleton hW hxO hxeO (content_eCell_add x).symm hc
    have := congrArg Prod.fst he
    simp only [eCell, Prod.fst_add] at this
    omega
  omega

/-- The interior splits into the two finite caps and the middle interior. -/
theorem IsLegal.interior_eq_caps (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    diagramInterior ω.E = ω.lowerCap ∪ diagramInterior ω.middle ∪ ω.upperCap := by
  ext x
  simp only [Finset.mem_union]
  constructor
  · intro hx
    have hg := h.interior_private_gaps hW hx
    by_cases hlo : content x < minContent ω.E + ω.width
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hx, hlo⟩))
    by_cases hhi : minContent ω.E + ω.period - 1 < content x
    · exact Or.inr (Finset.mem_filter.mpr ⟨hx, hhi⟩)
    have hn := h.isNonemptyMark hW
    have hnot : ∀ z, content z = content x → z ∈ ω.E → z ∈ ω.middle := by
      intro z hz hzE
      refine mem_middle.mpr ⟨hzE, ?_, ?_⟩
      · intro hzW
        have := (hn.content_W h.1.1 hzW).2
        omega
      · intro hzU
        have := (hn.content_upper h.1.1 hzU).1
        omega
    obtain ⟨hxE, hxeE⟩ := Finset.mem_filter.mp hx
    exact Or.inl (Or.inr (Finset.mem_filter.mpr
      ⟨hnot x rfl hxE, hnot _ (content_eCell_add x) hxeE⟩))
  · rintro ((hx | hx) | hx)
    · exact (Finset.mem_filter.mp hx).1
    · obtain ⟨hxO, hxeO⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(mem_middle.mp hxO).1, (mem_middle.mp hxeO).1⟩
    · exact (Finset.mem_filter.mp hx).1

/-- Each finite lower cap occupies at most `w - 1` consecutive contents. -/
theorem IsLegal.lowerCap_span_le (h : ω.IsLegal) :
    (span ω.lowerCap : ℤ) ≤ max 0 ((ω.width : ℤ) - 1) := by
  have hb := span_le_of_content_Ioo (D := ω.lowerCap)
    (minContent ω.E) (minContent ω.E + ω.width) (fun x hx => by
      obtain ⟨hxI, hxk⟩ := Finset.mem_filter.mp hx
      exact ⟨(interior_content_strict h.1.1 hxI).1, hxk⟩)
  simpa only [add_sub_cancel_left] using hb

/-- Each finite upper cap occupies at most `w - 1` consecutive contents. -/
theorem IsLegal.upperCap_span_le (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    (span ω.upperCap : ℤ) ≤ max 0 ((ω.width : ℤ) - 1) := by
  have hm := (h.isNonemptyMark hW).maxContent_E h.1.1
  have hb := span_le_of_content_Ioo (D := ω.upperCap)
    (minContent ω.E + ω.period - 1) (minContent ω.E + ω.period + ω.width - 1)
    (fun x hx => by
      obtain ⟨hxI, hxk⟩ := Finset.mem_filter.mp hx
      exact ⟨hxk, by have := (interior_content_strict h.1.1 hxI).2; omega⟩)
  convert hb using 1
  congr 1
  ring

/-- The middle interior occupies at most `p - w - 2` consecutive contents. -/
theorem IsLegal.middleInterior_span_le (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    (span (diagramInterior ω.middle) : ℤ) ≤ max 0 (ω.period - ω.width - 2) := by
  have hb := span_le_of_content_Ioo (D := diagramInterior ω.middle)
    (minContent ω.E + ω.width) (minContent ω.E + ω.period - 1)
    (fun _ hx => h.middleInterior_content hW hx)
  convert hb using 1
  congr 1
  ring

end MarkedInner

end SkewGluing
