/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.CellComponents

/-!
# Coordinate separation of skew components

Formalizes the component-separation argument of `shields-2026-skew-corner-descent.tex`,
«Corner cofactors and common cores» (`sec:corner`, `lem:interior-bounds`).  Distinct components
share no row, column, or content.  Their coordinate counts therefore add without multiplicity.

Sorry-free.
-/

namespace SkewGluing
attribute [local instance 10] Classical.propDecidable

/-- Comparable cells of a skew diagram are joined inside their rectangle. -/
theorem IsSkew.reach_of_le {D : Diagram} (hs : IsSkew D) {x y : ℤ × ℤ}
    (hx : x ∈ D) (hy : y ∈ D) (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) :
    DiagReach D x y := by
  have key : ∀ n : ℕ, ∀ x y : ℤ × ℤ, x ∈ D → y ∈ D →
      x.1 ≤ y.1 → x.2 ≤ y.2 → y.1 - x.1 + (y.2 - x.2) = n → DiagReach D x y := by
    intro n
    induction n with
    | zero =>
      intro x y hx hy h1 h2 hn
      have hxy : x = y := Prod.ext (by omega) (by omega)
      subst y
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      intro x y hx hy h1 h2 hn
      by_cases hlt : x.1 < y.1
      · let z : ℤ × ℤ := (x.1 + 1, x.2)
        have hz : z ∈ D := hs x hx y hy h1 h2 _
          (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) _ (Finset.mem_Icc.mpr ⟨le_rfl, h2⟩)
        have hadj : CellAdj x z := cellAdj_iff.mpr (Or.inr ⟨rfl, Or.inr rfl⟩)
        exact Relation.ReflTransGen.head ⟨hx, hz, hadj⟩
          (ih z y hz hy (by dsimp [z]; omega) h2 (by dsimp [z]; omega))
      · let z : ℤ × ℤ := (x.1, x.2 + 1)
        have hz : z ∈ D := hs x hx y hy h1 h2 _
          (Finset.mem_Icc.mpr ⟨le_rfl, h1⟩) _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hadj : CellAdj x z := cellAdj_iff.mpr (Or.inl ⟨rfl, Or.inr rfl⟩)
        exact Relation.ReflTransGen.head ⟨hx, hz, hadj⟩
          (ih z y hz hy h1 (by dsimp [z]; omega) (by dsimp [z]; omega))
  exact key _ x y hx hy h1 h2 (Int.toNat_of_nonneg (by omega)).symm

/-- A skew diagram's components are themselves skew diagrams. -/
theorem isSkew_component {D C : Diagram} (hs : IsSkew D) (hC : C ∈ edgeComponents D) :
    IsSkew C := by
  intro x hx y hy h1 h2 i hi j hj
  have hxD := component_subset hC hx
  have hyD := component_subset hC hy
  have hzD := hs x hxD y hyD h1 h2 i hi j hj
  rw [component_eq_of_mem hC hx, Finset.mem_filter]
  exact ⟨hzD, hs.reach_of_le hxD hzD (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1⟩

theorem isConnectedSkew_component {D C : Diagram} (hs : IsSkew D)
    (hC : C ∈ edgeComponents D) : IsConnectedSkew C :=
  ⟨isSkew_component hs hC, isEdgeConnected_component hC⟩

theorem component_eq_of_reach {D C C' : Diagram} (hC : C ∈ edgeComponents D)
    (hC' : C' ∈ edgeComponents D) {x y : ℤ × ℤ} (hx : x ∈ C) (hy : y ∈ C')
    (hxy : DiagReach D x y) : C = C' := by
  have hyC : y ∈ C := by
    rw [component_eq_of_mem hC hx, Finset.mem_filter]
    exact ⟨component_subset hC' hy, hxy⟩
  exact (component_eq_of_mem hC hyC).trans (component_eq_of_mem hC' hy).symm

/-- Sharing a row forces two skew components to coincide. -/
theorem component_eq_of_row {D C C' : Diagram} (hs : IsSkew D)
    (hC : C ∈ edgeComponents D) (hC' : C' ∈ edgeComponents D)
    {x y : ℤ × ℤ} (hx : x ∈ C) (hy : y ∈ C') (hrow : x.1 = y.1) : C = C' := by
  have hxD := component_subset hC hx
  have hyD := component_subset hC' hy
  rcases le_total x.2 y.2 with h | h
  · exact component_eq_of_reach hC hC' hx hy (hs.reach_of_le hxD hyD (by omega) h)
  · exact (component_eq_of_reach hC' hC hy hx (hs.reach_of_le hyD hxD (by omega) h)).symm

/-- Sharing a column forces two skew components to coincide. -/
theorem component_eq_of_col {D C C' : Diagram} (hs : IsSkew D)
    (hC : C ∈ edgeComponents D) (hC' : C' ∈ edgeComponents D)
    {x y : ℤ × ℤ} (hx : x ∈ C) (hy : y ∈ C') (hcol : x.2 = y.2) : C = C' := by
  have hxD := component_subset hC hx
  have hyD := component_subset hC' hy
  rcases le_total x.1 y.1 with h | h
  · exact component_eq_of_reach hC hC' hx hy (hs.reach_of_le hxD hyD h (by omega))
  · exact (component_eq_of_reach hC' hC hy hx (hs.reach_of_le hyD hxD h (by omega))).symm

/-- Sharing a content forces two skew components to coincide. -/
theorem component_eq_of_content {D C C' : Diagram} (hs : IsSkew D)
    (hC : C ∈ edgeComponents D) (hC' : C' ∈ edgeComponents D)
    {x y : ℤ × ℤ} (hx : x ∈ C) (hy : y ∈ C') (hc : content x = content y) : C = C' := by
  have hxD := component_subset hC hx
  have hyD := component_subset hC' hy
  simp only [content] at hc
  rcases le_total x.1 y.1 with h | h
  · exact component_eq_of_reach hC hC' hx hy (hs.reach_of_le hxD hyD h (by omega))
  · exact (component_eq_of_reach hC' hC hy hx (hs.reach_of_le hyD hxD h (by omega))).symm

/-- An injective-on-components coordinate has additive coordinate counts. -/
theorem sum_component_image_card {D : Diagram} (f : ℤ × ℤ → ℤ)
    (hsep : ∀ C ∈ edgeComponents D, ∀ C' ∈ edgeComponents D,
      ∀ x ∈ C, ∀ y ∈ C', f x = f y → C = C') :
    (∑ C ∈ edgeComponents D, (C.image f).card) = (D.image f).card := by
  have hu : (edgeComponents D).biUnion (fun C => C.image f) = D.image f := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨C, hC, x, hx, rfl⟩
      exact ⟨x, component_subset hC hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hm : x ∈ (edgeComponents D).biUnion id := by rw [biUnion_edgeComponents]; exact hx
      obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hm
      exact ⟨C, hC, x, hxC, rfl⟩
  rw [← hu, Finset.card_biUnion]
  intro C hC C' hC' hne
  change Disjoint (C.image f) (C'.image f)
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hz
  obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp hz'
  exact hne (hsep C hC C' hC' x hx y hy (hfx.trans hfy.symm))

theorem sum_component_rows {D : Diagram} (hs : IsSkew D) :
    (∑ C ∈ edgeComponents D, (C.image Prod.fst).card) = (D.image Prod.fst).card :=
  sum_component_image_card Prod.fst fun _ hC _ hC' _ hx _ hy h =>
    component_eq_of_row hs hC hC' hx hy h

theorem sum_component_cols {D : Diagram} (hs : IsSkew D) :
    (∑ C ∈ edgeComponents D, (C.image Prod.snd).card) = (D.image Prod.snd).card :=
  sum_component_image_card Prod.snd fun _ hC _ hC' _ hx _ hy h =>
    component_eq_of_col hs hC hC' hx hy h

theorem sum_component_spans {D : Diagram} (hs : IsSkew D) :
    (∑ C ∈ edgeComponents D, span C) = span D :=
  sum_component_image_card content fun _ hC _ hC' _ hx _ hy h =>
    component_eq_of_content hs hC hC' hx hy h

end SkewGluing
