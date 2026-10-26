-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Disconnected.lean
import GluingCore.CellSchurTableau
import GluingCore.OlsonHarris.Plan.Defs

/-!
# From connected diagrams to all skew diagrams: the Leibniz step for `CornerEq`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the reduction in the proof of thesis Lemma 5.5.7 ("it is
sufficient to prove these in the case that `D` is connected; the result follows for disconnected
shapes by applying it to each component separately") and of Lemma 5.5.12 (the derivation
`p_{mq}^⊥` and the two ribbon sums are compatible with the product over components).

* `modCompC_union`: `modCompC` is multiplicative over a disjoint union without adjacent cells;
* `rightRibbons_split`, `leftRibbons_split`: the ribbons removable from `X` are the ribbons
  removable from a component `C` and those removable from `X \ C`;
* `cornerEq_of_connected`: `CornerEq ω C m` for every connected skew `C` implies it for every
  skew `X`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

attribute [local instance 10] Classical.propDecidable

/-! ### Components of a skew diagram -/

section Split

variable {X C : Diagram}

/-- In a skew diagram, two cells comparable in the northwest order lie in the same component. -/
theorem mem_component_iff_of_le (hX : IsSkew X) (hC : C ∈ edgeComponents X) {x y : ℤ × ℤ}
    (hx : x ∈ X) (hy : y ∈ X) (h1 : y.1 ≤ x.1) (h2 : y.2 ≤ x.2) : x ∈ C ↔ y ∈ C := by
  have hr : DiagReach X y x := by
    have := hX.reach_rect hy hx h1 h2 (i := x.1) (j := x.2) h1 le_rfl h2 le_rfl
    simpa using this
  exact ⟨fun h => mem_component_of_reach hC h hr.symm, fun h => mem_component_of_reach hC h hr⟩

/-- Cells of a component and of its complement are never adjacent. -/
theorem not_cellAdj_component (hC : C ∈ edgeComponents X) {a b : ℤ × ℤ} (ha : a ∈ C)
    (hb : b ∈ X \ C) : ¬ CellAdj a b := by
  intro hadj
  obtain ⟨hbX, hbC⟩ := Finset.mem_sdiff.mp hb
  refine hbC (mem_component_of_reach hC ha ?_)
  exact Relation.ReflTransGen.single ⟨component_subset hC ha, hbX, hadj⟩

/-- An edge-connected subset of `X` lies inside a component or misses it. -/
theorem subset_component_or_disjoint {Y : Diagram} (hYX : Y ⊆ X) (hY : IsEdgeConnected Y)
    (hC : C ∈ edgeComponents X) : Y ⊆ C ∨ Disjoint Y C := by
  obtain ⟨y0, hy0⟩ := hY.1
  have key : ∀ y ∈ Y, y ∈ C ↔ y0 ∈ C := by
    intro y hy
    have hr : DiagReach X y0 y := DiagReach.mono hYX (hY.2 y0 hy0 y hy)
    exact ⟨fun h => mem_component_of_reach hC h hr.symm, fun h => mem_component_of_reach hC h hr⟩
  by_cases h0 : y0 ∈ C
  · exact Or.inl fun y hy => (key y hy).mpr h0
  · refine Or.inr (Finset.disjoint_left.mpr fun y hy hyC => h0 ((key y hy).mp hyC))

/-- Ribbons removable on the right: a ribbon of `X` of size `m > 0` is removable from one
component or from the complement of that component, and conversely. -/
theorem rightRibbons_split (hX : IsSkew X) (hC : C ∈ edgeComponents X) {m : ℕ} (hm : 0 < m) :
    rightRibbons X m = rightRibbons C m ∪ rightRibbons (X \ C) m := by
  ext Y
  simp only [Finset.mem_union, mem_rightRibbons]
  constructor
  · rintro ⟨hYX, hcard, hrib, hup⟩
    have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
    rcases subset_component_or_disjoint hYX hrib.1.2 hC with hs | hd
    · refine Or.inl ⟨hs, hcard, hrib, hs, fun x hx y hy h1 h2 => ?_⟩
      exact hup.2 x (component_subset hC hx) y hy h1 h2
    · refine Or.inr ⟨fun y hy => Finset.mem_sdiff.mpr ⟨hYX hy, Finset.disjoint_left.mp hd hy⟩,
        hcard, hrib, fun y hy => Finset.mem_sdiff.mpr
          ⟨hYX hy, Finset.disjoint_left.mp hd hy⟩, fun x hx y hy h1 h2 => ?_⟩
      exact hup.2 x (Finset.mem_sdiff.mp hx).1 y hy h1 h2
  · rintro (⟨hYC, hcard, hrib, -, hup⟩ | ⟨hYC, hcard, hrib, -, hup⟩)
    · refine ⟨hYC.trans (component_subset hC), hcard, hrib, hYC.trans (component_subset hC),
        fun x hx y hy h1 h2 => ?_⟩
      have hyC : y ∈ C := hYC hy
      have hxC : x ∈ C :=
        (mem_component_iff_of_le hX hC hx (component_subset hC hyC) h1 h2).mpr hyC
      exact hup x hxC y hy h1 h2
    · refine ⟨hYC.trans Finset.sdiff_subset, hcard, hrib, hYC.trans Finset.sdiff_subset,
        fun x hx y hy h1 h2 => ?_⟩
      have hyC : y ∈ X \ C := hYC hy
      have hxC : x ∈ X \ C := by
        refine Finset.mem_sdiff.mpr ⟨hx, fun hxC => ?_⟩
        have := (mem_component_iff_of_le hX hC hx (Finset.mem_sdiff.mp hyC).1 h1 h2).mp hxC
        exact (Finset.mem_sdiff.mp hyC).2 this
      exact hup x hxC y hy h1 h2

/-- Ribbons removable on the left: as `rightRibbons_split`. -/
theorem leftRibbons_split (hX : IsSkew X) (hC : C ∈ edgeComponents X) {m : ℕ} (hm : 0 < m) :
    leftRibbons X m = leftRibbons C m ∪ leftRibbons (X \ C) m := by
  ext Y
  simp only [Finset.mem_union, mem_leftRibbons]
  constructor
  · rintro ⟨hYX, hcard, hrib, hup⟩
    have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
    rcases subset_component_or_disjoint hYX hrib.1.2 hC with hs | hd
    · refine Or.inl ⟨hs, hcard, hrib, hs, fun x hx y hy h1 h2 => ?_⟩
      exact hup.2 x (component_subset hC hx) y hy h1 h2
    · refine Or.inr ⟨fun y hy => Finset.mem_sdiff.mpr ⟨hYX hy, Finset.disjoint_left.mp hd hy⟩,
        hcard, hrib, fun y hy => Finset.mem_sdiff.mpr
          ⟨hYX hy, Finset.disjoint_left.mp hd hy⟩, fun x hx y hy h1 h2 => ?_⟩
      exact hup.2 x (Finset.mem_sdiff.mp hx).1 y hy h1 h2
  · rintro (⟨hYC, hcard, hrib, -, hup⟩ | ⟨hYC, hcard, hrib, -, hup⟩)
    · refine ⟨hYC.trans (component_subset hC), hcard, hrib, hYC.trans (component_subset hC),
        fun x hx y hy h1 h2 => ?_⟩
      have hyC : y ∈ C := hYC hy
      have hxC : x ∈ C :=
        (mem_component_iff_of_le hX hC (component_subset hC hyC) hx h1 h2).mp hyC
      exact hup x hxC y hy h1 h2
    · refine ⟨hYC.trans Finset.sdiff_subset, hcard, hrib, hYC.trans Finset.sdiff_subset,
        fun x hx y hy h1 h2 => ?_⟩
      have hyC : y ∈ X \ C := hYC hy
      have hxC : x ∈ X \ C := by
        refine Finset.mem_sdiff.mpr ⟨hx, fun hxC => ?_⟩
        have := (mem_component_iff_of_le hX hC (Finset.mem_sdiff.mp hyC).1 hx h1 h2).mpr hxC
        exact (Finset.mem_sdiff.mp hyC).2 this
      exact hup x hxC y hy h1 h2

theorem disjoint_rightRibbons_split {m : ℕ} (hm : 0 < m) :
    Disjoint (rightRibbons C m) (rightRibbons (X \ C) m) := by
  rw [Finset.disjoint_left]
  intro Y h1 h2
  rw [mem_rightRibbons] at h1 h2
  have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy⟩ := hne
  exact (Finset.mem_sdiff.mp (h2.1 hy)).2 (h1.1 hy)

theorem disjoint_leftRibbons_split {m : ℕ} (hm : 0 < m) :
    Disjoint (leftRibbons C m) (leftRibbons (X \ C) m) := by
  rw [Finset.disjoint_left]
  intro Y h1 h2
  rw [mem_leftRibbons] at h1 h2
  have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy⟩ := hne
  exact (Finset.mem_sdiff.mp (h2.1 hy)).2 (h1.1 hy)

end Split

/-! ### Multiplicativity of the corner modified composition -/

/-- `modCompC` is multiplicative over a disjoint union without adjacent cells. -/
theorem modCompC_union {ω : MarkedInner} {A B : Diagram} (hdisj : Disjoint A B)
    (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) :
    modCompC ω (A ∪ B) = modCompC ω A * modCompC ω B := by
  unfold modCompC
  rw [edgeComponents_union hadj, Finset.prod_union]
  rw [Finset.disjoint_left]
  intro C hCA hCB
  obtain ⟨z, hz⟩ := component_nonempty hCA
  exact Finset.disjoint_left.mp hdisj (component_subset hCA hz) (component_subset hCB hz)

section Reduction

variable {ω : MarkedInner} {X C : Diagram}

theorem modCompC_split (hC : C ∈ edgeComponents X) :
    modCompC ω X = modCompC ω C * modCompC ω (X \ C) := by
  have h : C ∪ (X \ C) = X := Finset.union_sdiff_of_subset (component_subset hC)
  rw [← modCompC_union Finset.disjoint_sdiff fun a ha b hb => not_cellAdj_component hC ha hb, h]

theorem ribbonSumRight_split (hX : IsSkew X) (hC : C ∈ edgeComponents X) {m : ℕ} (hm : 0 < m) :
    ribbonSumRight (modCompC ω) X m =
      ribbonSumRight (modCompC ω) C m * modCompC ω (X \ C) +
        modCompC ω C * ribbonSumRight (modCompC ω) (X \ C) m := by
  unfold ribbonSumRight
  rw [rightRibbons_split hX hC hm,
    Finset.sum_union (disjoint_rightRibbons_split (X := X) (C := C) hm),
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun Y hY => ?_
    rw [mem_rightRibbons] at hY
    have e : X \ Y = (C \ Y) ∪ (X \ C) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hz, hzY⟩
        by_cases hzC : z ∈ C
        · exact Or.inl ⟨hzC, hzY⟩
        · exact Or.inr ⟨hz, hzC⟩
      · rintro (⟨hzC, hzY⟩ | ⟨hz, hzC⟩)
        · exact ⟨component_subset hC hzC, hzY⟩
        · exact ⟨hz, fun hzY => hzC (hY.1 hzY)⟩
    rw [e, modCompC_union (Finset.disjoint_left.mpr fun z hz hz' =>
      (Finset.mem_sdiff.mp hz').2 (Finset.mem_sdiff.mp hz).1)
      (fun a ha b hb => not_cellAdj_component hC (Finset.mem_sdiff.mp ha).1 hb)]
    ring
  · refine Finset.sum_congr rfl fun Y hY => ?_
    rw [mem_rightRibbons] at hY
    have e : X \ Y = C ∪ ((X \ C) \ Y) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hz, hzY⟩
        by_cases hzC : z ∈ C
        · exact Or.inl hzC
        · exact Or.inr ⟨⟨hz, hzC⟩, hzY⟩
      · rintro (hzC | ⟨⟨hz, hzC⟩, hzY⟩)
        · exact ⟨component_subset hC hzC, fun hzY => (Finset.mem_sdiff.mp (hY.1 hzY)).2 hzC⟩
        · exact ⟨hz, hzY⟩
    rw [e, modCompC_union (Finset.disjoint_left.mpr fun z hz hz' =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz').1).2 hz)
      (fun a ha b hb => not_cellAdj_component hC ha
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).1,
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).2⟩))]
    ring

theorem ribbonSumLeft_split (hX : IsSkew X) (hC : C ∈ edgeComponents X) {m : ℕ} (hm : 0 < m) :
    ribbonSumLeft (modCompC ω) X m =
      ribbonSumLeft (modCompC ω) C m * modCompC ω (X \ C) +
        modCompC ω C * ribbonSumLeft (modCompC ω) (X \ C) m := by
  unfold ribbonSumLeft
  rw [leftRibbons_split hX hC hm,
    Finset.sum_union (disjoint_leftRibbons_split (X := X) (C := C) hm),
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun Y hY => ?_
    rw [mem_leftRibbons] at hY
    have e : X \ Y = (C \ Y) ∪ (X \ C) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hz, hzY⟩
        by_cases hzC : z ∈ C
        · exact Or.inl ⟨hzC, hzY⟩
        · exact Or.inr ⟨hz, hzC⟩
      · rintro (⟨hzC, hzY⟩ | ⟨hz, hzC⟩)
        · exact ⟨component_subset hC hzC, hzY⟩
        · exact ⟨hz, fun hzY => hzC (hY.1 hzY)⟩
    rw [e, modCompC_union (Finset.disjoint_left.mpr fun z hz hz' =>
      (Finset.mem_sdiff.mp hz').2 (Finset.mem_sdiff.mp hz).1)
      (fun a ha b hb => not_cellAdj_component hC (Finset.mem_sdiff.mp ha).1 hb)]
    ring
  · refine Finset.sum_congr rfl fun Y hY => ?_
    rw [mem_leftRibbons] at hY
    have e : X \ Y = C ∪ ((X \ C) \ Y) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hz, hzY⟩
        by_cases hzC : z ∈ C
        · exact Or.inl hzC
        · exact Or.inr ⟨⟨hz, hzC⟩, hzY⟩
      · rintro (hzC | ⟨⟨hz, hzC⟩, hzY⟩)
        · exact ⟨component_subset hC hzC, fun hzY => (Finset.mem_sdiff.mp (hY.1 hzY)).2 hzC⟩
        · exact ⟨hz, hzY⟩
    rw [e, modCompC_union (Finset.disjoint_left.mpr fun z hz hz' =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz').1).2 hz)
      (fun a ha b hb => not_cellAdj_component hC ha
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).1,
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).2⟩))]
    ring

/-- The corner equations at the empty diagram. -/
theorem cornerEq_empty (m : ℕ) (hm : 0 < m) : CornerEq ω ∅ m := by
  have h1 : modCompC ω ∅ = 1 := by simp [modCompC, edgeComponents_empty]
  have hr : ∀ s : Finset Diagram, (∀ Y ∈ s, Y ⊆ (∅ : Diagram) ∧ Y.card = m) → s = ∅ := by
    intro s hs
    refine Finset.eq_empty_of_forall_notMem fun Y hY => ?_
    obtain ⟨h1, h2⟩ := hs Y hY
    have : Y = ∅ := Finset.subset_empty.mp h1
    subst this
    simp at h2
    omega
  refine ⟨?_, ?_⟩
  · rw [h1]; exact (pDeriv _).map_one_eq_zero
  · have hR : rightRibbons (∅ : Diagram) m = ∅ :=
      hr _ fun Y hY => ⟨(mem_rightRibbons.mp hY).1, (mem_rightRibbons.mp hY).2.1⟩
    have hL : leftRibbons (∅ : Diagram) m = ∅ :=
      hr _ fun Y hY => ⟨(mem_leftRibbons.mp hY).1, (mem_leftRibbons.mp hY).2.1⟩
    simp [ribbonSumRight, ribbonSumLeft, hR, hL]

/-- **The Leibniz step.**  If the corner equations hold at every connected skew diagram, they
hold at every skew diagram: the product over components is differentiated by the Leibniz rule,
and the ribbon sums are compatible with the splitting off of one component. -/
theorem cornerEq_of_connected
    (h : ∀ C : Diagram, IsConnectedSkew C → ∀ m : ℕ, 0 < m → CornerEq ω C m) :
    ∀ (n : ℕ) (X : Diagram), X.card = n → IsSkew X → ∀ m : ℕ, 0 < m → CornerEq ω X m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hX m hm
  by_cases hemp : X = ∅
  · subst hemp; exact cornerEq_empty m hm
  by_cases hconn : IsEdgeConnected X
  · exact h X ⟨hX, hconn⟩ m hm
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
  set C : Diagram := X.filter (DiagReach X x) with hCdef
  have hC : C ∈ edgeComponents X := mem_edgeComponents.mpr ⟨x, hx, rfl⟩
  have hxC : x ∈ C := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
  have hCsub : C ⊆ X := component_subset hC
  have hCne : C ≠ X := fun h => hconn (h ▸ isEdgeConnected_component hC)
  have hcardC : C.card < n := hn ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hCsub, hCne⟩)
  have hcardX' : (X \ C).card < n := hn ▸ Finset.card_lt_card (by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => ?_⟩
    have : x ∈ X \ C := by rw [h]; exact hx
    exact (Finset.mem_sdiff.mp this).2 hxC)
  have e1 := ih _ hcardC C rfl (isSkew_component hX hC) m hm
  have e2 := ih _ hcardX' (X \ C) rfl (isSkew_sdiff_component hX hC) m hm
  obtain ⟨a1, b1⟩ := e1
  obtain ⟨a2, b2⟩ := e2
  refine ⟨?_, ?_⟩
  · rw [modCompC_split hC, Derivation.leibniz, a1, a2]
    simp
  · rw [ribbonSumRight_split hX hC hm, ribbonSumLeft_split hX hC hm, b1, b2]

end Reduction


end Corner

end Plan

end GluingCore
