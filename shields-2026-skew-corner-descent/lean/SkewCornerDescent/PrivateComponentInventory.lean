/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.InteriorWindowPeriod
import SkewGluing.DisconnectedTableau

/-!
# Whole-component inventories at private cuts

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`).

A missing content diagonal splits the actual component inventory without cutting any
component. Complete equal windows identify these inventories by literal translation.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Restriction at an unoccupied diagonal retains exactly the wholly lower components. -/
theorem edgeComponents_prefix_of_gap {D : Diagram} {k : ℤ}
    (hgap : ∀ x ∈ D, content x ≠ k) :
    edgeComponents (D.filter fun x => content x < k) =
      (edgeComponents D).filter fun C => ∀ x ∈ C, content x < k := by
  classical
  let A := D.filter fun x => content x < k
  let B := D.filter fun x => k < content x
  have hsplit : D = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      have hk := hgap x hx
      by_cases h : content x < k
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, by omega⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hadj : ∀ x ∈ A, ∀ y ∈ B, ¬ CellAdj x y := by
    intro x hx y hy hxy
    have hxk := (Finset.mem_filter.mp hx).2
    have hyk := (Finset.mem_filter.mp hy).2
    have hstep := content_adj hxy
    omega
  have hcomponents : edgeComponents D = edgeComponents A ∪ edgeComponents B := by
    rw [hsplit, edgeComponents_union hadj]
  change edgeComponents A = _
  ext C
  rw [Finset.mem_filter]
  constructor
  · intro hC
    refine ⟨by rw [hcomponents]; exact Finset.mem_union_left _ hC, ?_⟩
    intro x hx
    exact (Finset.mem_filter.mp (component_subset hC hx)).2
  · rintro ⟨hC, hlow⟩
    rw [hcomponents] at hC
    rcases Finset.mem_union.mp hC with hA | hB
    · exact hA
    · obtain ⟨x, hx⟩ := (isEdgeConnected_component hB).1
      have hxk := (Finset.mem_filter.mp (component_subset hB hx)).2
      have hxl := hlow x hx
      omega

/-- A private singleton cut restricts the full actual interior component inventory. -/
theorem privateDiagonal_component_inventory {D : Diagram} {k : ℤ}
    (hsingle : diagLo D k = diagHi D k) :
    edgeComponents (diagramInterior (D.filter fun x => content x < k)) =
      (edgeComponents (diagramInterior D)).filter fun C => ∀ x ∈ C, content x < k := by
  rw [interior_content_filter D (fun c => c < k)]
  exact edgeComponents_prefix_of_gap (fun _ hx => privateDiagonal_avoids_interior hsingle hx)

/-- Complete equal windows identify all literal component occurrences, not just their functions. -/
theorem literalWindow_component_inventory {D : Diagram} {L q : ℤ} {v : ℤ × ℤ}
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q)) :
    edgeComponents ((diagramInterior D).filter (fun x => q ≤ content x ∧ content x < L)) =
      (edgeComponents ((diagramInterior D).filter fun x =>
        0 ≤ content x ∧ content x < L - q)).image (SkewGluing.translate v) := by
  rw [literalWindow_interior hwindow, edgeComponents_translate]

end SkewCornerDescent
