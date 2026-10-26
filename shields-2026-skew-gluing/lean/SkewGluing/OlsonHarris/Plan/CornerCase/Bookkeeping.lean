import SkewGluing.CellSchurTableau
import SkewGluing.OlsonHarris.Plan.Defs

/-!
# Rows, columns, diagonals and the northbound count over the components of a skew diagram

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the bookkeeping in the proof of thesis Lemma 5.5.12
(`OlsonHarris2024HopfApplications`), "where the exponents come from counting boxes as in the proof
of Lemma 5.4.6": the numbers of rows, of columns and of diagonals, and the northbound count `ξ`,
are additive over the edge components of a skew diagram, so the corner modified composition of a
skew diagram `X` is `(-1)^{ξ(X)} s_W^{|X| - row X} s_{\overline W}^{|X| - col X}
s_{\overline O}^{|X| - dia X}` times the product `compSchur` of the functions `s_{C ∘_ω E}` of its
components.

* `numRows_eq_sum`, `numCols_eq_sum`, `span_eq_sum`: additivity over the components;
* `modCompC_eq`: the displayed formula for `modCompC ω X`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

attribute [local instance 10] Classical.propDecidable

/-- The number of northbound boxes of a skew diagram: the sum over its components. -/
noncomputable def northboundSum (ω : MarkedInner) (X : Diagram) : ℕ :=
  ∑ C ∈ edgeComponents X, northbound ω C

/-- The product of the functions `s_{C ∘_ω E}` over the components `C` of `X`. -/
noncomputable def compSchur (ω : MarkedInner) (X : Diagram) : Lambda :=
  ∏ C ∈ edgeComponents X, cellSchur (ω.compose C)

/-- A statistic `f` of the cells of a skew diagram `X` that is constant on the components counts
additively over them: `|f(X)| = Σ_C |f(C)|`. -/
theorem card_image_eq_sum_components {X : Diagram} {f : ℤ × ℤ → ℤ}
    (hf : ∀ x ∈ X, ∀ y ∈ X, f x = f y → DiagReach X x y) :
    (X.image f).card = ∑ C ∈ edgeComponents X, (C.image f).card := by
  have hU : X.image f = (edgeComponents X).biUnion fun C => C.image f := by
    ext k
    simp only [Finset.mem_image, Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨_, mem_edgeComponents.mpr ⟨x, hx, rfl⟩, x, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
    · rintro ⟨C, hC, x, hx, rfl⟩
      exact ⟨x, component_subset hC hx, rfl⟩
  rw [hU, Finset.card_biUnion]
  intro C hC C' hC' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro k hk hk'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hk'
  have hC1 : C ∈ edgeComponents X := Finset.mem_coe.mp hC
  have hC2 : C' ∈ edgeComponents X := Finset.mem_coe.mp hC'
  have hr := hf y (component_subset hC2 hy) x (component_subset hC1 hx) hxy
  exact Finset.disjoint_left.mp (edgeComponents_disjoint hC1 hC2 hne) hx
    (mem_component_of_reach hC2 hy hr)

/-- The number of rows is additive over the components of a skew diagram. -/
theorem numRows_eq_sum {X : Diagram} (hX : IsSkew X) :
    numRows X = ∑ C ∈ edgeComponents X, numRows C := by
  unfold numRows rowSet
  refine card_image_eq_sum_components fun x hx y hy h => ?_
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at h
  subst h
  exact hX.reach_row hx hy

/-- The number of columns is additive over the components of a skew diagram. -/
theorem numCols_eq_sum {X : Diagram} (hX : IsSkew X) :
    numCols X = ∑ C ∈ edgeComponents X, numCols C := by
  simp only [numCols_eq_card_image_snd]
  refine card_image_eq_sum_components fun x hx y hy h => ?_
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at h
  subst h
  exact hX.reach_col hx hy

/-- The number of diagonals is additive over the components of a skew diagram. -/
theorem span_eq_sum {X : Diagram} (hX : IsSkew X) :
    span X = ∑ C ∈ edgeComponents X, span C := by
  unfold span contents
  refine card_image_eq_sum_components fun x hx y hy h => ?_
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [content] at h
  rcases le_total a c with hac | hac
  · have := hX.reach_rect hx hy hac (by omega) (i := c) (j := d) hac le_rfl (by omega) le_rfl
    exact this
  · have := hX.reach_rect hy hx hac (by omega) (i := a) (j := b) hac le_rfl (by omega) le_rfl
    exact this.symm

theorem numRows_le_card (X : Diagram) : numRows X ≤ X.card := Finset.card_image_le

theorem numCols_le_card (X : Diagram) : numCols X ≤ X.card := by
  rw [numCols_eq_card_image_snd]; exact Finset.card_image_le

theorem span_le_card (X : Diagram) : span X ≤ X.card := Finset.card_image_le

theorem numRows_mono {X Y : Diagram} (h : X ⊆ Y) : numRows X ≤ numRows Y :=
  Finset.card_le_card (Finset.image_subset_image h)

theorem numCols_mono {X Y : Diagram} (h : X ⊆ Y) : numCols X ≤ numCols Y := by
  rw [numCols_eq_card_image_snd, numCols_eq_card_image_snd]
  exact Finset.card_le_card (Finset.image_subset_image h)

theorem span_mono {X Y : Diagram} (h : X ⊆ Y) : span X ≤ span Y :=
  Finset.card_le_card (Finset.image_subset_image h)

/-- **The corner modified composition of a skew diagram** is the sign `(-1)^{ξ(X)}` times the
powers of the three factors times the product of the functions of the composites of the
components (thesis (5.14), extended multiplicatively). -/
theorem modCompC_eq (ω : MarkedInner) {X : Diagram} (hX : IsSkew X) :
    modCompC ω X = (-1 : Lambda) ^ northboundSum ω X * cellSchur ω.W ^ (X.card - numRows X) *
      cellSchur (hatMarkFin ω) ^ (X.card - numCols X) *
        cellSchur (hatMiddleFin ω) ^ (X.card - span X) * compSchur ω X := by
  have hcard := card_eq_sum_edgeComponents (D := X)
  have s1 : ∑ C ∈ edgeComponents X, (C.card - numRows C) = X.card - numRows X := by
    rw [Finset.sum_tsub_distrib _ fun C _ => numRows_le_card C, ← hcard, ← numRows_eq_sum hX]
  have s2 : ∑ C ∈ edgeComponents X, (C.card - numCols C) = X.card - numCols X := by
    rw [Finset.sum_tsub_distrib _ fun C _ => numCols_le_card C, ← hcard, ← numCols_eq_sum hX]
  have s3 : ∑ C ∈ edgeComponents X, (C.card - span C) = X.card - span X := by
    rw [Finset.sum_tsub_distrib _ fun C _ => span_le_card C, ← hcard, ← span_eq_sum hX]
  unfold modCompC compSchur northboundSum
  simp only [componentTc, componentT]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, s1, s2, s3]
  ring

/-- Removing an upset (a ribbon removable on the right) from a skew diagram leaves a skew
diagram. -/
theorem isSkew_sdiff_of_isUpsetIn {X Y : Diagram} (hX : IsSkew X) (hY : IsUpsetIn X Y) :
    IsSkew (X \ Y) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyX, hyY⟩ := Finset.mem_sdiff.mp hy
  simp only [Finset.mem_Icc] at hi hj
  have hz : (i, j) ∈ X := hX.mem (a := x.1) (b := x.2) (c := y.1) (d := y.2) hxX hyX h1 h2
    hi.1 hi.2 hj.1 hj.2
  refine Finset.mem_sdiff.mpr ⟨hz, fun hzY => hyY ?_⟩
  exact hY.2 y hyX (i, j) hzY hi.2 hj.2

/-- Removing a downset (a ribbon removable on the left) from a skew diagram leaves a skew
diagram. -/
theorem isSkew_sdiff_of_isDownsetIn {X Y : Diagram} (hX : IsSkew X) (hY : IsDownsetIn X Y) :
    IsSkew (X \ Y) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyX, hyY⟩ := Finset.mem_sdiff.mp hy
  simp only [Finset.mem_Icc] at hi hj
  have hz : (i, j) ∈ X := hX.mem (a := x.1) (b := x.2) (c := y.1) (d := y.2) hxX hyX h1 h2
    hi.1 hi.2 hj.1 hj.2
  refine Finset.mem_sdiff.mpr ⟨hz, fun hzY => hxY ?_⟩
  exact hY.2 x hxX (i, j) hzY hi.1 hj.1

end Corner

end Plan

end SkewGluing
