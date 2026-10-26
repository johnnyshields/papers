/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/

import Mathlib.Data.Int.Notation
import Mathlib.Tactic.Common
import SkewGluing.Diagram

/-!
# Edge-connected components of finite cell diagrams

Formalizes a component partition used in `shields-2026-skew-corner-descent.tex`, «Corner
cofactors and common cores» (`sec:corner`, `lem:interior-bounds`, `eq:corner-factors`).

TODO-COPIED: component partition machinery adapted from
`skew-factor-gluing/lean/SkewGluing/CellSchur.lean`.
-/

namespace SkewGluing
attribute [local instance 10] Classical.propDecidable

/-- Cells joined by a chain of edge-adjacent cells contained in `D`. -/
abbrev DiagReach (D : Diagram) : ℤ × ℤ → ℤ × ℤ → Prop :=
  Relation.ReflTransGen fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b

theorem DiagReach.symm {D : Diagram} {x y : ℤ × ℤ} (h : DiagReach D x y) :
    DiagReach D y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact Relation.ReflTransGen.head ⟨hab.2.1, hab.1, hab.2.2.symm'⟩ ih

theorem DiagReach.trans {D : Diagram} {x y z : ℤ × ℤ} (h : DiagReach D x y)
    (h' : DiagReach D y z) : DiagReach D x z :=
  Relation.ReflTransGen.trans h h'

/-- The edge-connected components of a finite diagram. -/
noncomputable def edgeComponents (D : Diagram) : Finset Diagram :=
  D.image fun x => D.filter fun y => DiagReach D x y

theorem mem_edgeComponents {D C : Diagram} :
    C ∈ edgeComponents D ↔ ∃ x ∈ D, C = D.filter fun y => DiagReach D x y := by
  simp only [edgeComponents, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem component_subset {D C : Diagram} (hC : C ∈ edgeComponents D) : C ⊆ D := by
  obtain ⟨x, hx, rfl⟩ := mem_edgeComponents.mp hC
  exact Finset.filter_subset _ _

theorem component_reach {D : Diagram} {x y : ℤ × ℤ} (h : DiagReach D x y) :
    DiagReach (D.filter fun z => DiagReach D x z) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxb hbc ih =>
    refine Relation.ReflTransGen.tail ih ⟨?_, ?_, hbc.2.2⟩
    · exact Finset.mem_filter.mpr ⟨hbc.1, hxb⟩
    · exact Finset.mem_filter.mpr ⟨hbc.2.1, hxb.tail hbc⟩

theorem isEdgeConnected_component {D C : Diagram} (hC : C ∈ edgeComponents D) :
    IsEdgeConnected C := by
  obtain ⟨x, hx, rfl⟩ := mem_edgeComponents.mp hC
  have hxm : x ∈ D.filter fun z => DiagReach D x z :=
    Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
  refine ⟨⟨x, hxm⟩, fun y hy z hz => ?_⟩
  exact (component_reach (Finset.mem_filter.mp hy).2).symm.trans
    (component_reach (Finset.mem_filter.mp hz).2)

theorem component_eq_of_mem {D C : Diagram} (hC : C ∈ edgeComponents D)
    {z : ℤ × ℤ} (hz : z ∈ C) : C = D.filter fun y => DiagReach D z y := by
  obtain ⟨x, hx, rfl⟩ := mem_edgeComponents.mp hC
  obtain ⟨hzD, hxz⟩ := Finset.mem_filter.mp hz
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hxy⟩
    exact ⟨hy, hxz.symm.trans hxy⟩
  · rintro ⟨hy, hzy⟩
    exact ⟨hy, hxz.trans hzy⟩

theorem edgeComponents_disjoint {D C C' : Diagram} (hC : C ∈ edgeComponents D)
    (hC' : C' ∈ edgeComponents D) (hne : C ≠ C') : Disjoint C C' := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hne ((component_eq_of_mem hC hz).trans (component_eq_of_mem hC' hz').symm)

/-- Components partition every finite diagram, including the empty diagram. -/
theorem biUnion_edgeComponents (D : Diagram) : (edgeComponents D).biUnion id = D := by
  ext z
  simp only [Finset.mem_biUnion, id]
  constructor
  · rintro ⟨C, hC, hz⟩
    exact component_subset hC hz
  · intro hz
    refine ⟨D.filter fun y => DiagReach D z y,
      mem_edgeComponents.mpr ⟨z, hz, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hz, Relation.ReflTransGen.refl⟩

theorem card_eq_sum_edgeComponents (D : Diagram) :
    D.card = ∑ C ∈ edgeComponents D, C.card := by
  conv_lhs => rw [← biUnion_edgeComponents D]
  rw [Finset.card_biUnion]
  · rfl
  · intro C hC C' hC' hne
    exact edgeComponents_disjoint hC hC' hne

end SkewGluing
