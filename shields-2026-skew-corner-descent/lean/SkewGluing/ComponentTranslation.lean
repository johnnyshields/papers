/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.CellComponents

/-!
# Translation of component partitions

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:corner-factors`).

TODO-COPIED: adapted from the adjacency-preserving map argument in
`skew-factor-gluing/lean/SkewGluing/CellSchur.lean`.

Sorry-free.
-/

namespace SkewGluing
attribute [local instance 10] Classical.propDecidable

section Maps
variable (g : (ℤ × ℤ) ≃ (ℤ × ℤ))
variable (hg : ∀ a b, CellAdj (g a) (g b) ↔ CellAdj a b)
include hg

theorem diagReach_image_of {D : Diagram} {x y : ℤ × ℤ} (h : DiagReach D x y) :
    DiagReach (D.image g) (g x) (g y) := by
  refine Relation.ReflTransGen.lift g
    (p := fun a b => a ∈ D.image g ∧ b ∈ D.image g ∧ CellAdj a b) ?_ x y h
  intro a b hab
  exact ⟨Finset.mem_image_of_mem _ hab.1, Finset.mem_image_of_mem _ hab.2.1,
    (hg a b).mpr hab.2.2⟩

theorem diagReach_image_iff {D : Diagram} {x y : ℤ × ℤ} :
    DiagReach (D.image g) (g x) (g y) ↔ DiagReach D x y := by
  refine ⟨fun h => ?_, diagReach_image_of g hg⟩
  have hg' : ∀ a b, CellAdj (g.symm a) (g.symm b) ↔ CellAdj a b := fun a b => by
    rw [← hg (g.symm a) (g.symm b)]; simp
  have hr := diagReach_image_of g.symm hg' h
  have he : (D.image g).image g.symm = D := by
    have hi : (g.symm ∘ g) = id := by funext x; simp
    rw [Finset.image_image, hi, Finset.image_id]
  simpa [he] using hr

/-- Adjacency-preserving bijections carry components to components. -/
theorem edgeComponents_image (D : Diagram) :
    edgeComponents (D.image g) = (edgeComponents D).image (Finset.image g) := by
  unfold edgeComponents
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun x hx => ?_
  ext w
  simp only [Function.comp, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hr⟩
    obtain ⟨y, hy, rfl⟩ := hw
    exact ⟨y, ⟨hy, (diagReach_image_iff g hg).mp hr⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hxy⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, (diagReach_image_iff g hg).mpr hxy⟩

end Maps

/-- The components of a translate are exactly the translated components. -/
theorem edgeComponents_translate (v : ℤ × ℤ) (D : Diagram) :
    edgeComponents (translate v D) = (edgeComponents D).image (translate v) := by
  apply edgeComponents_image (Equiv.addRight v)
  intro a b
  simp only [Equiv.coe_addRight, cellAdj_iff, Prod.fst_add, Prod.snd_add]
  omega

end SkewGluing
