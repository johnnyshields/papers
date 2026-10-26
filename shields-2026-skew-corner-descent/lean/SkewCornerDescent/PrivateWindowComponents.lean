/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.PrivateComponentInventory
import SkewCornerDescent.Matrix.OriginalSelectedInventory

/-!
# Whole component occurrences in private content windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
Two private cuts retain exactly the complete source components inside the content window.
Selected occurrences retain their literal diagrams, not only their function classes.
Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- A restriction with no adjacency across its boundary cannot split a component. -/
theorem edgeComponents_filter_of_no_cross_adj {D : Diagram} (p : ℤ × ℤ → Prop)
    [DecidablePred p]
    (hadj : ∀ x ∈ D, ∀ y ∈ D, p x → ¬ p y → ¬ CellAdj x y) :
    edgeComponents (D.filter p) = (edgeComponents D).filter fun C => ∀ x ∈ C, p x := by
  classical
  let A := D.filter p
  let B := D.filter fun x => ¬ p x
  have hsplit : D = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    tauto
  have hcomponents : edgeComponents D = edgeComponents A ∪ edgeComponents B := by
    rw [hsplit]
    apply edgeComponents_union
    intro x hx y hy
    exact hadj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
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
      exact False.elim ((Finset.mem_filter.mp (component_subset hB hx)).2 (hlow x hx))

/-- Both unoccupied boundary diagonals preserve all complete interval components. -/
theorem edgeComponents_interval_of_gaps {D : Diagram} (lo hi : ℤ)
    (hlo : ∀ x ∈ D, content x ≠ lo) (hhi : ∀ x ∈ D, content x ≠ hi) :
    edgeComponents (D.filter fun x => lo ≤ content x ∧ content x < hi) =
      (edgeComponents D).filter fun C => ∀ x ∈ C, lo ≤ content x ∧ content x < hi := by
  classical
  apply edgeComponents_filter_of_no_cross_adj
  intro x hx y hy hxp hyp hxy
  have hxl := hlo x hx
  have hyl := hlo y hy
  have hyh := hhi y hy
  have hstep := content_adj hxy
  omega

namespace Matrix.SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Missing interior boundary diagonals select complete source components inside a window. -/
theorem selectedComponentInventory_interval_of_gaps (X : Diagram) (lo hi : ℤ)
    (hlo : ∀ x ∈ diagramInterior X, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior X, content x ≠ hi) :
    selectedComponentInventory (hD := hD)
        (X.filter fun x => lo ≤ content x ∧ content x < hi) =
      (selectedComponentInventory (hD := hD) X).filter fun C =>
        ∀ x ∈ C, lo ≤ content x ∧ content x < hi := by
  classical
  unfold selectedComponentInventory
  rw [interior_content_filter X (fun k => lo ≤ k ∧ k < hi),
    edgeComponents_interval_of_gaps lo hi hlo hhi]
  ext C
  simp only [Finset.mem_filter]
  tauto

/-- A complete window bounded by private cuts selects exactly the whole source occurrences. -/
theorem selectedComponentInventory_private_interval (X : Diagram) (lo hi : ℤ)
    (hlo : diagLo X lo = diagHi X lo) (hhi : diagLo X hi = diagHi X hi) :
    selectedComponentInventory (hD := hD)
        (X.filter fun x => lo ≤ content x ∧ content x < hi) =
      (selectedComponentInventory (hD := hD) X).filter fun C =>
        ∀ x ∈ C, lo ≤ content x ∧ content x < hi := by
  exact selectedComponentInventory_interval_of_gaps X lo hi
    (fun _ hx => privateDiagonal_avoids_interior hlo hx)
    (fun _ hx => privateDiagonal_avoids_interior hhi hx)

/-- Equal literal windows translate the whole selected overlap inventory, with all repeated
occurrences retained as different diagrams. Boundary gaps prevent partial components. -/
theorem selectedComponentInventory_literal_windows (X : Diagram) (lo hi q : ℤ) (v : ℤ × ℤ)
    (hprefix : IsSkew (X.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hwindow : X.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (X.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior X, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior X, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior X, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior X, content x ≠ hi) :
    ((selectedComponentInventory (hD := hD) X).filter fun C =>
      ∀ x ∈ C, lo + q ≤ content x ∧ content x < hi) =
      ((selectedComponentInventory (hD := hD) X).filter fun C =>
        ∀ x ∈ C, lo ≤ content x ∧ content x < hi - q).image (SkewGluing.translate v) := by
  classical
  rw [← selectedComponentInventory_interval_of_gaps X (lo + q) hi hloq hhi, hwindow,
    selectedComponentInventory_translate _ hprefix v,
    selectedComponentInventory_interval_of_gaps X lo (hi - q) hlo hhiq]

end Matrix.SelectedCoordinate

end SkewCornerDescent
