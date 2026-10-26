-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/Reduction.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.Counts
import GluingCore.CellSchurTableau

/-!
# Reduction of the edge equations to connected diagrams

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis Lemma 5.4.7 and Thm. 5.4.8
(`OlsonHarris2024HopfApplications`), for diagrams that are not connected.

`EdgeEqL ω X m` is the left half of `EdgeEq`.  A ribbon is connected, so lies in one component of
a skew diagram `X`, and is removable on the left from `X` exactly when it is removable from that
component; the modified composition is multiplicative over components.  Hence the left equation
for a skew diagram follows, by the Leibniz rule and induction on the number of cells, from the left
equation for connected diagrams (`edgeEqL_of_connected`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

open scoped Classical

/-- The left half of `EdgeEq`. -/
def EdgeEqL (ω : MarkedInner) (X : Diagram) (m : ℕ) : Prop :=
  pDeriv (m * ω.period.toNat) (modComp ω X) =
    (edgeSign ω m : Lambda) * hatFactor ω ^ m * ribbonSumLeft (modComp ω) X m

/-- The right half of `EdgeEq`. -/
def EdgeEqR (ω : MarkedInner) (X : Diagram) (m : ℕ) : Prop :=
  pDeriv (m * ω.period.toNat) (modComp ω X) =
    (edgeSign ω m : Lambda) * hatFactor ω ^ m * ribbonSumRight (modComp ω) X m

theorem edgeEq_iff (ω : MarkedInner) (X : Diagram) (m : ℕ) :
    EdgeEq ω X m ↔ EdgeEqL ω X m ∧ EdgeEqR ω X m := Iff.rfl

/-! ### Components of a skew diagram -/

theorem nonAdjacent_component_sdiff {X C : Diagram} (hC : C ∈ edgeComponents X) :
    NonAdjacent C (X \ C) := by
  intro x hx y hy hxy
  obtain ⟨hyX, hyC⟩ := Finset.mem_sdiff.mp hy
  apply hyC
  exact mem_component_of_reach hC hx
    (Relation.ReflTransGen.single ⟨component_subset hC hx, hyX, hxy⟩)

theorem disjoint_component_sdiff (X C : Diagram) : Disjoint C (X \ C) :=
  Finset.disjoint_sdiff

theorem union_component_sdiff {X C : Diagram} (hC : C ∈ edgeComponents X) : C ∪ (X \ C) = X :=
  Finset.union_sdiff_of_subset (component_subset hC)

theorem modComp_union {ω : MarkedInner} {A B : Diagram} (hd : Disjoint A B)
    (hn : NonAdjacent A B) : modComp ω (A ∪ B) = modComp ω A * modComp ω B := by
  unfold modComp
  rw [edgeComponents_union hn, Finset.prod_union (disjoint_edgeComponents hd)]

theorem modComp_empty (ω : MarkedInner) : modComp ω ∅ = 1 := by
  simp [modComp, edgeComponents_empty]

/-- A connected subdiagram lies in a single component. -/
theorem subset_component_or_sdiff {X C Y : Diagram} (hC : C ∈ edgeComponents X) (hY : Y ⊆ X)
    (hYc : IsEdgeConnected Y) : Y ⊆ C ∨ Y ⊆ X \ C := by
  obtain ⟨y0, hy0⟩ := hYc.1
  by_cases h0 : y0 ∈ C
  · left
    intro y hy
    have hr := hYc.2 y0 hy0 y hy
    exact mem_component_of_reach hC h0 (DiagReach.mono hY hr)
  · right
    intro y hy
    refine Finset.mem_sdiff.mpr ⟨hY hy, fun hyC => h0 ?_⟩
    have hr := (hYc.2 y0 hy0 y hy)
    exact mem_component_of_reach hC hyC (DiagReach.mono hY hr).symm

theorem comparable_mem_component {X C : Diagram} (hX : IsSkew X) (hC : C ∈ edgeComponents X)
    {x y : ℤ × ℤ} (hx : x ∈ X) (hy : y ∈ C) (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) : x ∈ C :=
  mem_component_of_reach hC hy (diagReach_of_le hX hx (component_subset hC hy) h1 h2).symm

theorem comparable_not_mem_component {X C : Diagram} (hX : IsSkew X) (hC : C ∈ edgeComponents X)
    {x y : ℤ × ℤ} (hx : x ∈ C) (hy : y ∈ X \ C) (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) : False := by
  obtain ⟨hyX, hyC⟩ := Finset.mem_sdiff.mp hy
  exact hyC (mem_component_of_reach hC hx
    (diagReach_of_le hX (component_subset hC hx) hyX h1 h2))

theorem comparable_not_mem_component' {X C : Diagram} (hX : IsSkew X) (hC : C ∈ edgeComponents X)
    {x y : ℤ × ℤ} (hx : x ∈ X \ C) (hy : y ∈ C) (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) : False := by
  obtain ⟨hxX, hxC⟩ := Finset.mem_sdiff.mp hx
  exact hxC (comparable_mem_component hX hC hxX hy h1 h2)

theorem leftRibbons_eq_union {X C : Diagram} (hX : IsSkew X) (hC : C ∈ edgeComponents X) {m : ℕ} :
    leftRibbons X m = leftRibbons C m ∪ leftRibbons (X \ C) m := by
  ext Y
  rw [Finset.mem_union, mem_leftRibbons, mem_leftRibbons, mem_leftRibbons]
  constructor
  · rintro ⟨hYX, hcard, hrib, hdown⟩
    rcases subset_component_or_sdiff hC hYX hrib.1.2 with h | h
    · left
      exact ⟨h, hcard, hrib, h, fun x hx y hy h1 h2 =>
        hdown.2 x (component_subset hC hx) y hy h1 h2⟩
    · right
      exact ⟨h, hcard, hrib, h, fun x hx y hy h1 h2 =>
        hdown.2 x (Finset.mem_sdiff.mp hx).1 y hy h1 h2⟩
  · rintro (⟨hYC, hcard, hrib, hdown⟩ | ⟨hYC, hcard, hrib, hdown⟩)
    · refine ⟨hYC.trans (component_subset hC), hcard, hrib, hYC.trans (component_subset hC), ?_⟩
      intro x hx y hy h1 h2
      have hyC : y ∈ C := hYC hy
      exact hdown.2 x (comparable_mem_component hX hC hx hyC h1 h2) y hy h1 h2
    · refine ⟨hYC.trans Finset.sdiff_subset, hcard, hrib, hYC.trans Finset.sdiff_subset, ?_⟩
      intro x hx y hy h1 h2
      have hxR : x ∈ X \ C := by
        refine Finset.mem_sdiff.mpr ⟨hx, fun hxC => ?_⟩
        exact comparable_not_mem_component hX hC hxC (hYC hy) h1 h2
      exact hdown.2 x hxR y hy h1 h2

theorem disjoint_leftRibbons_component {X C : Diagram} {m : ℕ} (hm : 0 < m) :
    Disjoint (leftRibbons C m) (leftRibbons (X \ C) m) := by
  rw [Finset.disjoint_left]
  intro Y hY1 hY2
  rw [mem_leftRibbons] at hY1 hY2
  have hne : Y.Nonempty := by
    rw [← Finset.card_pos, hY1.2.1]; exact hm
  obtain ⟨y, hy⟩ := hne
  exact (Finset.mem_sdiff.mp (hY2.1 hy)).2 (hY1.1 hy)

theorem ribbonSumLeft_union {ω : MarkedInner} {X C : Diagram} (hX : IsSkew X)
    (hC : C ∈ edgeComponents X) {m : ℕ} (hm : 0 < m) :
    ribbonSumLeft (modComp ω) X m =
      ribbonSumLeft (modComp ω) C m * modComp ω (X \ C) +
        modComp ω C * ribbonSumLeft (modComp ω) (X \ C) m := by
  unfold ribbonSumLeft
  rw [leftRibbons_eq_union hX hC, Finset.sum_union (disjoint_leftRibbons_component hm),
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
    rw [e, modComp_union ?_ ?_]
    · ring
    · rw [Finset.disjoint_left]
      intro z hz hz'
      exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_sdiff.mp hz).1
    · exact (nonAdjacent_component_sdiff hC).mono Finset.sdiff_subset subset_rfl
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
        · refine ⟨component_subset hC hzC, fun hzY => ?_⟩
          exact (Finset.mem_sdiff.mp (hY.1 hzY)).2 hzC
        · exact ⟨hz, hzY⟩
    rw [e, modComp_union ?_ ?_]
    · ring
    · rw [Finset.disjoint_left]
      intro z hz hz'
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz').1).2 hz
    · exact (nonAdjacent_component_sdiff hC).mono subset_rfl Finset.sdiff_subset

/-- **The left equation for connected diagrams implies it for all skew diagrams**
(thesis Lemma 5.4.7 for a disconnected diagram: the Leibniz rule). -/
theorem edgeEqL_of_connected {ω : MarkedInner}
    (hcore : ∀ C : Diagram, IsConnectedSkew C → ∀ m : ℕ, 0 < m → EdgeEqL ω C m) :
    ∀ n : ℕ, ∀ X : Diagram, X.card = n → IsSkew X → ∀ m : ℕ, 0 < m → EdgeEqL ω X m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hn hX m hm
    by_cases hXe : X = ∅
    · subst hXe
      unfold EdgeEqL ribbonSumLeft
      have : leftRibbons ∅ m = ∅ := by
        ext Y
        rw [mem_leftRibbons]
        simp only [Finset.notMem_empty, iff_false]
        rintro ⟨hY, hc, -⟩
        have := Finset.subset_empty.mp hY
        subst this
        simp at hc
        omega
      rw [this, modComp_empty]
      simp
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hXe
      set C := X.filter (fun y => DiagReach X x y) with hCdef
      have hC : C ∈ edgeComponents X := mem_edgeComponents.mpr ⟨x, hx, rfl⟩
      have hCconn := isConnectedSkew_component hX hC
      have hRskew := isSkew_sdiff_component hX hC
      have hcard : (X \ C).card < n := by
        have h1 := Finset.card_sdiff_add_card_eq_card (component_subset hC)
        have h2 : 0 < C.card := Finset.card_pos.mpr (component_nonempty hC)
        omega
      have hIH := ih _ hcard (X \ C) rfl hRskew m hm
      have hCore := hcore C hCconn m hm
      unfold EdgeEqL at hIH hCore ⊢
      have hmod : modComp ω X = modComp ω C * modComp ω (X \ C) := by
        conv_lhs => rw [← union_component_sdiff hC]
        exact modComp_union (disjoint_component_sdiff X C) (nonAdjacent_component_sdiff hC)
      rw [ribbonSumLeft_union (ω := ω) hX hC hm, hmod, Derivation.leibniz, hIH, hCore]
      simp only [smul_eq_mul]
      ring

end Plan

end GluingCore
