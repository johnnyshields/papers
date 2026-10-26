/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.Interior
import SkewGluing.SkewComponents

/-!
# Summed-component bounds for the southeast interior

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `lem:interior-bounds`, `eq:outer-statistics`).  The southeast interior is skew;
its components occupy disjoint rows, columns, and contents.  Neither the last row nor the last
column survives, and the two extreme contents do not survive.

Sorry-free.
-/

namespace SkewGluing

/-- Southeast erosion preserves skew convexity, even when it disconnects the diagram. -/
theorem IsSkew.interior {D : Diagram} (hs : IsSkew D) : IsSkew (diagramInterior D) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxD, hxE⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyD, hyE⟩ := Finset.mem_filter.mp hy
  apply Finset.mem_filter.mpr
  refine ⟨hs x hxD y hyD h1 h2 i hi j hj, ?_⟩
  have h := hs (x + eCell) hxE (y + eCell) hyE
    (by simpa [eCell] using h1) (by simpa [eCell] using h2) (i + 1)
    (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hi).1; simpa [eCell],
      by have := (Finset.mem_Icc.mp hi).2; simpa [eCell]⟩) (j + 1)
    (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hj).1; simpa [eCell],
      by have := (Finset.mem_Icc.mp hj).2; simpa [eCell]⟩)
  simpa [eCell] using h

/-- A coordinate increasing by one on southeast steps loses its maximum under erosion. -/
theorem interior_image_card_add_one_le {D : Diagram} (hD : D.Nonempty)
    (f : ℤ × ℤ → ℤ) (hstep : ∀ x, f (x + eCell) = f x + 1) :
    ((diagramInterior D).image f).card + 1 ≤ (D.image f).card := by
  let S := D.image f
  have hS : S.Nonempty := Finset.image_nonempty.mpr hD
  have hmax : S.max' hS ∈ S := Finset.max'_mem S hS
  have hsub : (diagramInterior D).image f ⊆ S.erase (S.max' hS) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hxD, hxE⟩ := Finset.mem_filter.mp hx
    have hnext : f x + 1 ∈ S := by
      rw [← hstep]
      exact Finset.mem_image_of_mem f hxE
    have hbound := Finset.le_max' S _ hnext
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_image_of_mem f hxD⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmax] at hcard
  have hpos := Finset.card_pos.mpr hS
  change ((diagramInterior D).image f).card + 1 ≤ S.card
  omega

/-- Sum of the row counts of the actual interior components is at most `r(D) - 1`. -/
theorem interior_component_rows_le {D : Diagram} (hD : IsConnectedSkew D) :
    (∑ C ∈ edgeComponents (diagramInterior D), (C.image Prod.fst).card) + 1 ≤
      (D.image Prod.fst).card := by
  rw [sum_component_rows hD.1.interior]
  exact interior_image_card_add_one_le hD.2.1 Prod.fst (by intro x; simp [eCell])

/-- Sum of the column counts of the actual interior components is at most `c(D) - 1`. -/
theorem interior_component_cols_le {D : Diagram} (hD : IsConnectedSkew D) :
    (∑ C ∈ edgeComponents (diagramInterior D), (C.image Prod.snd).card) + 1 ≤
      (D.image Prod.snd).card := by
  rw [sum_component_cols hD.1.interior]
  exact interior_image_card_add_one_le hD.2.1 Prod.snd (by intro x; simp [eCell])

/-- Sum of the content spans of the actual interior components is at most `N_D - 2`. -/
theorem interior_component_spans_le {D : Diagram} (hD : IsConnectedSkew D)
    (hcard : 2 ≤ D.card) :
    (∑ C ∈ edgeComponents (diagramInterior D), span C) + 2 ≤ span D := by
  rw [sum_component_spans hD.1.interior]
  have h := interior_span_le_of_two_le_card hD hcard
  omega

/-- The three component inequalities of the paper's interior-bounds lemma. -/
theorem interior_component_bounds {D : Diagram} (hD : IsConnectedSkew D)
    (hcard : 2 ≤ D.card) :
    (∑ C ∈ edgeComponents (diagramInterior D), (C.image Prod.fst).card) + 1 ≤
        (D.image Prod.fst).card ∧
    (∑ C ∈ edgeComponents (diagramInterior D), (C.image Prod.snd).card) + 1 ≤
        (D.image Prod.snd).card ∧
    (∑ C ∈ edgeComponents (diagramInterior D), span C) + 2 ≤ span D :=
  ⟨interior_component_rows_le hD, interior_component_cols_le hD,
    interior_component_spans_le hD hcard⟩

end SkewGluing
