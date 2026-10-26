import SkewGluing.OlsonHarris.Plan.Defs

/-!
# Edge-disjoint unions of diagrams

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): bookkeeping for thesis §5.4 (`OlsonHarris2024HopfApplications`),
Lemma 5.4.3 and Lemma 5.4.6.

For diagrams with no two cells of different parts sharing an edge, the edge components of the union
are the edge components of the parts, so `cellSchur` is multiplicative (`cellSchur_union`).  Two
cells of a skew diagram whose contents differ by at most one are related by the northwest order
and hence lie in one edge component (`diagReach_of_content_le_one`); the cell counts of a skew
diagram (`countE`, `countS`, `countSE`) are its size minus its numbers of rows, columns and
diagonals.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewGluing

namespace Plan

open scoped Classical

/-- No cell of `A` shares an edge with a cell of `B`. -/
def NonAdjacent (A B : Diagram) : Prop := ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b

theorem NonAdjacent.symm {A B : Diagram} (h : NonAdjacent A B) : NonAdjacent B A :=
  fun b hb a ha hba => h a ha b hb hba.symm'

theorem NonAdjacent.mono {A A' B B' : Diagram} (h : NonAdjacent A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    NonAdjacent A' B' := fun a ha b hb => h a (hA ha) b (hB hb)

theorem nonAdjacent_union_left {A A' B : Diagram} (h : NonAdjacent A B) (h' : NonAdjacent A' B) :
    NonAdjacent (A ∪ A') B := by
  intro a ha b hb
  rcases Finset.mem_union.mp ha with ha | ha
  · exact h a ha b hb
  · exact h' a ha b hb

theorem nonAdjacent_union_right {A B B' : Diagram} (h : NonAdjacent A B) (h' : NonAdjacent A B') :
    NonAdjacent A (B ∪ B') :=
  (nonAdjacent_union_left h.symm h'.symm).symm

theorem diagReach_union_left {A B : Diagram} (h : NonAdjacent A B) {x y : ℤ × ℤ} (hx : x ∈ A)
    (hxy : DiagReach (A ∪ B) x y) : y ∈ A ∧ DiagReach A x y := by
  induction hxy with
  | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hbA, hxb⟩ := ih
    have hc := Finset.mem_union.mp hbc.2.1
    rcases hc with hc | hc
    · exact ⟨hc, hxb.tail ⟨hbA, hc, hbc.2.2⟩⟩
    · exact absurd hbc.2.2 (h b hbA c hc)

/-- The component, in `A ∪ B`, of a cell of `A` is its component in `A`. -/
theorem filter_reach_union_left {A B : Diagram} (h : NonAdjacent A B) {x : ℤ × ℤ} (hx : x ∈ A) :
    (A ∪ B).filter (fun y => DiagReach (A ∪ B) x y) = A.filter (fun y => DiagReach A x y) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨-, hy⟩
    have := diagReach_union_left h hx hy
    exact ⟨this.1, this.2⟩
  · rintro ⟨hy, hxy⟩
    exact ⟨Or.inl hy, DiagReach.mono Finset.subset_union_left hxy⟩

theorem edgeComponents_union {A B : Diagram} (h : NonAdjacent A B) :
    edgeComponents (A ∪ B) = edgeComponents A ∪ edgeComponents B := by
  ext C
  rw [Finset.mem_union, mem_edgeComponents, mem_edgeComponents, mem_edgeComponents]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · left
      exact ⟨x, hx, filter_reach_union_left h hx⟩
    · right
      refine ⟨x, hx, ?_⟩
      rw [Finset.union_comm]
      exact filter_reach_union_left h.symm hx
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Finset.mem_union_left _ hx, (filter_reach_union_left h hx).symm⟩
    · refine ⟨x, Finset.mem_union_right _ hx, ?_⟩
      rw [Finset.union_comm]
      exact (filter_reach_union_left h.symm hx).symm

theorem disjoint_edgeComponents {A B : Diagram} (hAB : Disjoint A B) :
    Disjoint (edgeComponents A) (edgeComponents B) := by
  rw [Finset.disjoint_left]
  intro C hCA hCB
  obtain ⟨x, hx⟩ := component_nonempty hCA
  exact Finset.disjoint_left.mp hAB (component_subset hCA hx) (component_subset hCB hx)

/-- **`cellSchur` of an edge-disjoint union is the product.** -/
theorem cellSchur_union {A B : Diagram} (hAB : Disjoint A B) (h : NonAdjacent A B) :
    cellSchur (A ∪ B) = cellSchur A * cellSchur B := by
  unfold cellSchur
  rw [edgeComponents_union h, Finset.prod_union (disjoint_edgeComponents hAB)]

theorem nonAdjacent_empty_left (B : Diagram) : NonAdjacent ∅ B := by
  intro a ha; simp at ha

theorem cellSchur_biUnion {ι : Type*} (s : Finset ι) (f : ι → Diagram)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j))
    (hn : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → NonAdjacent (f i) (f j)) :
    cellSchur (s.biUnion f) = ∏ i ∈ s, cellSchur (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [cellSchur_empty]
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert ha]
    have hd' : Disjoint (f a) (s.biUnion f) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hd a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))
    have hn' : NonAdjacent (f a) (s.biUnion f) := by
      intro x hx y hy
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hy
      exact hn a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj)) x hx y hyj
    rw [cellSchur_union hd' hn', ih]
    · intro i hi j hj hij
      exact hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · intro i hi j hj hij
      exact hn i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij

/-! ### Cells of a skew diagram with nearby contents -/

theorem diagReach_of_le {X : Diagram} (hX : IsSkew X) {x y : ℤ × ℤ} (hx : x ∈ X) (hy : y ∈ X)
    (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) : DiagReach X x y := by
  have := hX.reach_rect hx hy h1 h2 (i := y.1) (j := y.2) h1 le_rfl h2 le_rfl
  simpa using this

/-- Two cells of a skew diagram whose contents differ by at most one are in the same edge
component. -/
theorem diagReach_of_content_le_one {X : Diagram} (hX : IsSkew X) {x y : ℤ × ℤ} (hx : x ∈ X)
    (hy : y ∈ X) (h : content y ≤ content x + 1) (h' : content x ≤ content y + 1) :
    DiagReach X x y := by
  simp only [content] at h h'
  by_cases h1 : x.1 ≤ y.1
  · by_cases h2 : x.2 ≤ y.2
    · exact diagReach_of_le hX hx hy h1 h2
    · exact (diagReach_of_le hX hy hx (by omega) (by omega)).symm
  · exact (diagReach_of_le hX hy hx (by omega) (by omega)).symm

/-- Cells in different components of a skew diagram have contents differing by at least two. -/
theorem two_le_content_of_components {X : Diagram} (hX : IsSkew X) {C C' : Diagram}
    (hC : C ∈ edgeComponents X) (hC' : C' ∈ edgeComponents X) (hne : C ≠ C') {x y : ℤ × ℤ}
    (hx : x ∈ C) (hy : y ∈ C') : content x + 2 ≤ content y ∨ content y + 2 ≤ content x := by
  by_contra hcon
  push Not at hcon
  have hreach := diagReach_of_content_le_one hX (component_subset hC hx)
    (component_subset hC' hy) (by omega) (by omega)
  apply hne
  rw [component_eq_of_mem hC hx, component_eq_of_mem hC' hy]
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hxz⟩
    exact ⟨hz, hreach.symm.trans hxz⟩
  · rintro ⟨hz, hyz⟩
    exact ⟨hz, hreach.trans hyz⟩

end Plan

end SkewGluing
