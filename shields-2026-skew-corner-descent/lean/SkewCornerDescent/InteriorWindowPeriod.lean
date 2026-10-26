/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LiteralWindowBands
import SkewGluing.Interior

/-!
# Complete interior windows and private component cuts

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`).

Content filtering commutes with the southeast interior. Complete translated cell windows
therefore identify their full interiors. A private singleton diagonal is absent from the
interior, so every edge-connected interior subdiagram lies wholly on one side of it.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- A content cut retains both cells of every southeast pair or neither of them. -/
theorem interior_content_filter (D : Diagram) (p : ℤ → Prop) [DecidablePred p] :
    diagramInterior (D.filter fun x => p (content x)) =
      (diagramInterior D).filter fun x => p (content x) := by
  ext x
  have hc : content (x + eCell) = content x := by
    simp only [content, eCell, Prod.fst_add, Prod.snd_add]
    omega
  simp only [diagramInterior, Finset.mem_filter, hc]
  tauto

/-- Translation identifies actual southeast pairs, hence the complete interior. -/
theorem interior_translate (D : Diagram) (v : ℤ × ℤ) :
    diagramInterior (translate v D) = translate v (diagramInterior D) := by
  ext x
  have he : (x + eCell) - v = (x - v) + eCell := by abel
  simp only [diagramInterior, Finset.mem_filter, mem_translate, he]

/-- Equal complete windows identify all their interior cells with the same displacement. -/
theorem literalWindow_interior {D : Diagram} {L q : ℤ} {v : ℤ × ℤ}
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q)) :
    (diagramInterior D).filter (fun x => q ≤ content x ∧ content x < L) =
      translate v ((diagramInterior D).filter fun x =>
        0 ≤ content x ∧ content x < L - q) := by
  have he := congrArg diagramInterior hwindow
  rw [interior_translate, interior_content_filter D (fun k => q ≤ k ∧ k < L),
    interior_content_filter D (fun k => 0 ≤ k ∧ k < L - q)] at he
  exact he

/-- No southeast pair can occupy a singleton diagonal of its parent. -/
theorem privateDiagonal_avoids_interior {D : Diagram} {k : ℤ}
    (hsingle : diagLo D k = diagHi D k) {x : ℤ × ℤ}
    (hx : x ∈ diagramInterior D) : content x ≠ k := by
  intro hc
  obtain ⟨hxD, hxe⟩ := Finset.mem_filter.mp hx
  have hlo := diagLo_le (D := D) (k := k) hxD (by simpa only [content] using hc)
  have hhi := le_diagHi (D := D) (k := k) hxe (by
    simpa only [content, eCell, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd,
      add_sub_add_right_eq_sub] using hc)
  simp only [eCell] at hhi
  omega

/-- An edge-connected subdiagram cannot cross a missing content diagonal. -/
theorem connected_subdiagram_gap {D C : Diagram} {k : ℤ}
    (hC : IsEdgeConnected C) (hCD : C ⊆ D)
    (hgap : ∀ x ∈ D, content x ≠ k) :
    (∀ x ∈ C, content x < k) ∨ (∀ x ∈ C, k < content x) := by
  obtain ⟨x, hx⟩ := hC.1
  have hxk := hgap x (hCD hx)
  by_cases hlow : content x < k
  · left
    intro y hy
    by_contra hnot
    have hk := contents_interval_of_edgeConnected hC x hx y hy k
      (Finset.mem_Icc.mpr (by omega))
    obtain ⟨z, hz, hzk⟩ := Finset.mem_image.mp hk
    exact hgap z (hCD hz) hzk
  · right
    intro y hy
    by_contra hnot
    have hk := contents_interval_of_edgeConnected hC y hy x hx k
      (Finset.mem_Icc.mpr (by omega))
    obtain ⟨z, hz, hzk⟩ := Finset.mem_image.mp hk
    exact hgap z (hCD hz) hzk

/-- A private cut places every whole actual interior component on exactly one side. -/
theorem privateDiagonal_component_side {D C : Diagram} {k : ℤ}
    (hC : IsEdgeConnected C) (hCD : C ⊆ diagramInterior D)
    (hsingle : diagLo D k = diagHi D k) :
    (∀ x ∈ C, content x < k) ∨ (∀ x ∈ C, k < content x) :=
  connected_subdiagram_gap hC hCD (fun _ hx => privateDiagonal_avoids_interior hsingle hx)

/-- An actual private prefix includes a whole component or excludes it entirely. -/
theorem privateDiagonal_component_prefix {D C : Diagram} {k : ℤ}
    (hC : IsEdgeConnected C) (hCD : C ⊆ diagramInterior D)
    (hsingle : diagLo D k = diagHi D k) :
    C ⊆ (diagramInterior D).filter (fun x => content x < k) ∨
      Disjoint C ((diagramInterior D).filter fun x => content x < k) := by
  rcases privateDiagonal_component_side hC hCD hsingle with hlow | hhigh
  · left
    exact fun x hx => Finset.mem_filter.mpr ⟨hCD hx, hlow x hx⟩
  · right
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hyk := (Finset.mem_filter.mp hy).2
    have hxk := hhigh x hx
    omega

end SkewCornerDescent
