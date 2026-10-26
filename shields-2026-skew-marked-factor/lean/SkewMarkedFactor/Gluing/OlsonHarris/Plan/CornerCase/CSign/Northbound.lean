/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/CSign/Northbound.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Bookkeeping
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.CSign.Height

/-!
# The northbound count as a count of cells

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the northbound count `ξ` of thesis Lemmas 5.5.10 and 5.5.11
(`OlsonHarris2024HopfApplications`), for a legal mark of case (c).

`nwNorth X d` says that the cell north of `d` lies in `X` and on the same northwest ribbon of `X`
(this is `MarkedInner.SameRibbon` for case (c)), and `seNorth X d` that it lies on the same
southeast ribbon.  For a skew diagram `X`, the sum `northboundSum ω X` of the northbound counts
of its components is the number of cells of `X` with `nwNorth X` (`northboundSum_eq_card`),
because two cells of a skew diagram on one diagonal lie in one component.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

namespace CSign

/-- The cell north of `d` lies in `X` and on the same northwest ribbon: the ranks of the two cells
in the northwest decomposition, `i - ℓ`, agree. -/
def nwNorth (X : Diagram) (d : ℤ × ℤ) : Prop :=
  (d.1 - 1, d.2) ∈ X ∧ d.1 - diagLo X (content d) = (d.1 - 1) - diagLo X (content d + 1)

/-- The cell north of `d` lies in `X` and on the same southeast ribbon: the ranks of the two cells
in the southeast decomposition, `h - i`, agree. -/
def seNorth (X : Diagram) (d : ℤ × ℤ) : Prop :=
  (d.1 - 1, d.2) ∈ X ∧ diagHi X (content d) - d.1 = diagHi X (content d + 1) - (d.1 - 1)

instance (X : Diagram) (d : ℤ × ℤ) : Decidable (nwNorth X d) := by
  unfold nwNorth; infer_instance

instance (X : Diagram) (d : ℤ × ℤ) : Decidable (seNorth X d) := by
  unfold seNorth; infer_instance

theorem sameRibbon_c_iff {ω : MarkedInner} (hc : ω.case = .c) (X : Diagram) (d : ℤ × ℤ) :
    ω.SameRibbon X d ↔ nwNorth X d := by
  simp only [MarkedInner.SameRibbon, hc, nwNorth]

theorem northbound_eq_card {ω : MarkedInner} (hc : ω.case = .c) (C : Diagram) :
    northbound ω C = (C.filter (nwNorth C)).card := by
  unfold northbound
  congr 1
  exact Finset.filter_congr fun d _ => sameRibbon_c_iff hc C d

theorem content_north (d : ℤ × ℤ) : content (d.1 - 1, d.2) = content d + 1 := by
  simp only [content]; ring

/-- Two cells of a skew diagram on one diagonal are joined by a chain. -/
theorem reach_of_content_eq {X : Diagram} (hX : IsSkew X) {x y : ℤ × ℤ} (hx : x ∈ X)
    (hy : y ∈ X) (h : content x = content y) : DiagReach X x y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [content] at h
  rcases le_total a c with hac | hac
  · exact hX.reach_rect hx hy hac (by omega) (i := c) (j := d) hac le_rfl (by omega) le_rfl
  · exact (hX.reach_rect hy hx hac (by omega) (i := a) (j := b) hac le_rfl (by omega)
      le_rfl).symm

variable {X C : Diagram}

theorem diagLo_component (hX : IsSkew X) (hC : C ∈ edgeComponents X) {d : ℤ × ℤ} (hd : d ∈ C) :
    diagLo C (content d) = diagLo X (content d) := by
  have hdX := component_subset hC hd
  have hk := content_mem_contents hdX
  have hmem := diagLo_mem hk
  have hreach : DiagReach X d (diagLo X (content d), diagLo X (content d) + content d) :=
    reach_of_content_eq hX hdX hmem (by simp [content])
  have hmemC := mem_component_of_reach hC hd hreach
  exact diagLo_eq_of hmemC fun i hi => diagLo_le (component_subset hC hi) (by ring)

theorem diagHi_component (hX : IsSkew X) (hC : C ∈ edgeComponents X) {d : ℤ × ℤ} (hd : d ∈ C) :
    diagHi C (content d) = diagHi X (content d) := by
  have hdX := component_subset hC hd
  have hk := content_mem_contents hdX
  have hmem := diagHi_mem hk
  have hreach : DiagReach X d (diagHi X (content d), diagHi X (content d) + content d) :=
    reach_of_content_eq hX hdX hmem (by simp [content])
  have hmemC := mem_component_of_reach hC hd hreach
  exact diagHi_eq_of hmemC fun i hi => le_diagHi (component_subset hC hi) (by ring)

theorem north_mem_component (hC : C ∈ edgeComponents X) {d : ℤ × ℤ} (hd : d ∈ C)
    (hn : (d.1 - 1, d.2) ∈ X) : (d.1 - 1, d.2) ∈ C := by
  have hdX := component_subset hC hd
  refine mem_component_of_reach hC hd (Relation.ReflTransGen.single ⟨hdX, hn, ?_⟩)
  rw [cellAdj_iff]; simp

theorem nwNorth_component_iff (hX : IsSkew X) (hC : C ∈ edgeComponents X) {d : ℤ × ℤ}
    (hd : d ∈ C) : nwNorth C d ↔ nwNorth X d := by
  unfold nwNorth
  constructor
  · rintro ⟨hn, hr⟩
    refine ⟨component_subset hC hn, ?_⟩
    have h1 := diagLo_component hX hC hd
    have h2 := diagLo_component hX hC hn
    rw [content_north] at h2
    rw [← h1, ← h2]; exact hr
  · rintro ⟨hn, hr⟩
    have hnC := north_mem_component hC hd hn
    refine ⟨hnC, ?_⟩
    have h1 := diagLo_component hX hC hd
    have h2 := diagLo_component hX hC hnC
    rw [content_north] at h2
    rw [h1, h2]; exact hr

theorem seNorth_component_iff (hX : IsSkew X) (hC : C ∈ edgeComponents X) {d : ℤ × ℤ}
    (hd : d ∈ C) : seNorth C d ↔ seNorth X d := by
  unfold seNorth
  constructor
  · rintro ⟨hn, hr⟩
    refine ⟨component_subset hC hn, ?_⟩
    have h1 := diagHi_component hX hC hd
    have h2 := diagHi_component hX hC hn
    rw [content_north] at h2
    rw [← h1, ← h2]; exact hr
  · rintro ⟨hn, hr⟩
    have hnC := north_mem_component hC hd hn
    refine ⟨hnC, ?_⟩
    have h1 := diagHi_component hX hC hd
    have h2 := diagHi_component hX hC hnC
    rw [content_north] at h2
    rw [h1, h2]; exact hr

attribute [local instance 10] Classical.propDecidable

/-- The sum over the components of the number of cells of the component satisfying a predicate
that does not distinguish `C` from `X` is the number of cells of `X` satisfying it. -/
theorem sum_components_card_filter {P : Diagram → ℤ × ℤ → Prop} [∀ Y d, Decidable (P Y d)]
    (hP : ∀ C ∈ edgeComponents X, ∀ d ∈ C, P C d ↔ P X d) :
    ∑ C ∈ edgeComponents X, (C.filter (P C)).card = (X.filter (P X)).card := by
  have hU : X.filter (P X) = (edgeComponents X).biUnion fun C => C.filter (P C) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hd, hp⟩
      obtain ⟨C, hC, hdC⟩ : ∃ C ∈ edgeComponents X, d ∈ C :=
        ⟨_, mem_edgeComponents.mpr ⟨d, hd, rfl⟩,
          Finset.mem_filter.mpr ⟨hd, Relation.ReflTransGen.refl⟩⟩
      exact ⟨C, hC, hdC, (hP C hC d hdC).mpr hp⟩
    · rintro ⟨C, hC, hdC, hp⟩
      exact ⟨component_subset hC hdC, (hP C hC d hdC).mp hp⟩
  rw [hU, Finset.card_biUnion]
  intro C hC C' hC' hne
  rw [Function.onFun]
  exact Finset.disjoint_filter_filter (edgeComponents_disjoint hC hC' hne)

theorem northboundSum_eq_card {ω : MarkedInner} (hc : ω.case = .c) (hX : IsSkew X) :
    northboundSum ω X = (X.filter (nwNorth X)).card := by
  unfold northboundSum
  simp only [northbound_eq_card hc]
  exact sum_components_card_filter (P := nwNorth) fun C hC d hd =>
    nwNorth_component_iff hX hC hd

end CSign

end Corner

end Plan

end SkewMarkedFactor.Gluing
