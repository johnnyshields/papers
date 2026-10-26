/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.MarkLocality
import SkewGluing.Interior

/-!
# Erosion of overlapping diagonal intervals

Formalizes the integer-interval step in `shields-2026-skew-corner-descent.tex`,
«Marked inners and finite end caps» (`sec:marks`, `eq:erosion-union`, `eq:cap-hat`).

A consecutive diagonal pair in a union of overlapping intervals belongs to one interval.
Thus southeast erosion commutes with a union of skew windows whose common diagonals overlap.

Sorry-free.
-/

namespace SkewGluing

private theorem pair_in_one_window {A B : Diagram} (hA : IsSkew A) (hB : IsSkew B)
    {x z : ℤ × ℤ} (hxA : x ∈ A) (hxeB : x + eCell ∈ B)
    (hzA : z ∈ A) (hzB : z ∈ B) (hc : content z = content x) :
    (x ∈ A ∧ x + eCell ∈ A) ∨ (x ∈ B ∧ x + eCell ∈ B) := by
  by_cases hz : z.1 ≤ x.1
  · refine Or.inr ⟨?_, hxeB⟩
    have hm : (x.1, x.2) ∈ B := hB.mem hzB hxeB
      (by simp only [eCell]; omega)
      (by simp only [content] at hc; simp only [eCell]; omega)
      (by omega) (by simp only [eCell]; omega)
      (by simp only [content] at hc; omega)
      (by simp only [eCell]; omega)
    exact hm
  · refine Or.inl ⟨hxA, ?_⟩
    have hm : (x.1 + 1, x.2 + 1) ∈ A := hA.mem hxA hzA (by omega)
      (by simp only [content] at hc; omega)
      (by omega) (by omega) (by omega) (by simp only [content] at hc; omega)
    convert hm using 1
    ext <;> simp [eCell]

/-- Southeast erosion commutes with a union when every common diagonal has a common cell. -/
theorem interior_union_of_overlap {A B : Diagram} (hA : IsSkew A) (hB : IsSkew B)
    (hover : ∀ k, k ∈ contents A → k ∈ contents B → k ∈ contents (A ∩ B)) :
    diagramInterior (A ∪ B) = diagramInterior A ∪ diagramInterior B := by
  ext x
  simp only [diagramInterior, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hxA | hxB, hxeA | hxeB⟩
    · exact Or.inl ⟨hxA, hxeA⟩
    · have hkA := content_mem_contents hxA
      have hkB : content x ∈ contents B := by
        simpa only [MarkedInner.content_eCell_add] using content_mem_contents hxeB
      obtain ⟨z, hz, hcz⟩ := exists_cell_of_mem_contents (hover _ hkA hkB)
      obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
      exact pair_in_one_window hA hB hxA hxeB hzA hzB hcz
    · have hkB := content_mem_contents hxB
      have hkA : content x ∈ contents A := by
        simpa only [MarkedInner.content_eCell_add] using content_mem_contents hxeA
      obtain ⟨z, hz, hcz⟩ := exists_cell_of_mem_contents (hover _ hkA hkB)
      obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
      exact (pair_in_one_window hB hA hxB hxeA hzB hzA hcz).symm
    · exact Or.inr ⟨hxB, hxeB⟩
  · rintro (⟨hx, hxe⟩ | ⟨hx, hxe⟩)
    · exact ⟨Or.inl hx, Or.inl hxe⟩
    · exact ⟨Or.inr hx, Or.inr hxe⟩

/-- Southeast erosion commutes with a finite family of pairwise overlapping diagonal windows. -/
theorem interior_biUnion_of_overlap {ι : Type*} (s : Finset ι)
    (D : ι → Diagram) (hskew : ∀ i ∈ s, IsSkew (D i))
    (hover : ∀ i ∈ s, ∀ j ∈ s, ∀ k, k ∈ contents (D i) → k ∈ contents (D j) →
      k ∈ contents (D i ∩ D j)) :
    diagramInterior (s.biUnion D) = s.biUnion (fun i => diagramInterior (D i)) := by
  classical
  ext x
  simp only [diagramInterior, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, hi, hx⟩, ⟨j, hj, hxe⟩⟩
    have hk : content x ∈ contents (D j) := by
      simpa only [MarkedInner.content_eCell_add] using content_mem_contents hxe
    obtain ⟨z, hz, hcz⟩ :=
      exists_cell_of_mem_contents (hover i hi j hj _ (content_mem_contents hx) hk)
    obtain ⟨hzI, hzJ⟩ := Finset.mem_inter.mp hz
    rcases pair_in_one_window (hskew i hi) (hskew j hj) hx hxe hzI hzJ hcz with hp | hp
    · exact ⟨i, hi, hp⟩
    · exact ⟨j, hj, hp⟩
  · rintro ⟨i, hi, hx, hxe⟩
    exact ⟨⟨i, hi, hx⟩, ⟨i, hi, hxe⟩⟩

end SkewGluing
