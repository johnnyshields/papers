-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/TFun.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.Reduction
import GluingCore.Local.Final

/-!
# The modified composition of a skew diagram, in terms of cell counts

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis (5.13)
(`OlsonHarris2024HopfApplications`), `[D] □_W E = [W]^{|D|-row D} [\bar W]^{|D|-col D}
[\bar O]^{|D|-dia D} [D ∘_W E]`, for a skew diagram `D` that need not be connected.

For an ordinary legal mark the copies of `E` placed at cells of different components of `D` have
contents differing by at least two, so the composite of `D` is the edge-disjoint union of the
composites of its components and `cellSchur` is multiplicative over them
(`modComp_eq_tFun`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

open scoped Classical

namespace MarkedInner

open GluingCore.MarkedInner

theorem origin_ordinary {ω : MarkedInner} (h : ¬ ω.case.IsMixed) (D D' : Diagram) (d : ℤ × ℤ) :
    ω.origin D d = ω.origin D' d := by
  unfold GluingCore.MarkedInner.origin
  unfold AttachCase.IsMixed at h
  cases hc : ω.case <;> simp_all

/-- The union of the copies `E + L_ω(d)`, `d ∈ D`, of the ordinary composition (without the
convention for the empty outer). -/
def copies (ω : MarkedInner) (D : Diagram) : Diagram :=
  D.biUnion fun d => translate (ω.origin D d) ω.E

theorem mem_copies {ω : MarkedInner} {D : Diagram} {z : ℤ × ℤ} :
    z ∈ copies ω D ↔ ∃ d ∈ D, z ∈ translate (ω.origin D d) ω.E := by
  unfold copies
  rw [Finset.mem_biUnion]

theorem copies_empty (ω : MarkedInner) : copies ω ∅ = ∅ := by
  simp [copies]

theorem compose_eq_copies {ω : MarkedInner} (h : ¬ ω.case.IsMixed) {D : Diagram}
    (hD : D.Nonempty) : ω.compose D = copies ω D := by
  ext x
  rw [compose_of_ordinary hD h, mem_copies]

theorem copies_union {ω : MarkedInner} (h : ¬ ω.case.IsMixed) (A B : Diagram) :
    copies ω (A ∪ B) = copies ω A ∪ copies ω B := by
  ext x
  rw [Finset.mem_union, mem_copies, mem_copies, mem_copies]
  constructor
  · rintro ⟨d, hd, hx⟩
    rcases Finset.mem_union.mp hd with hd | hd
    · left; exact ⟨d, hd, by rwa [origin_ordinary h A (A ∪ B)]⟩
    · right; exact ⟨d, hd, by rwa [origin_ordinary h B (A ∪ B)]⟩
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hx⟩)
    · exact ⟨d, Finset.mem_union_left _ hd, by rwa [origin_ordinary h (A ∪ B) A]⟩
    · exact ⟨d, Finset.mem_union_right _ hd, by rwa [origin_ordinary h (A ∪ B) B]⟩

theorem content_of_mem_copies {ω : MarkedInner} (hω : ω.IsLegal) {D : Diagram} {z : ℤ × ℤ}
    (hz : z ∈ copies ω D) :
    ∃ d ∈ D, minContent ω.E + content d * ω.period ≤ content z ∧
      content z ≤ minContent ω.E + content d * ω.period + ω.period + ω.width - 1 := by
  obtain ⟨d, hd, hzd⟩ := mem_copies.mp hz
  refine ⟨d, hd, ?_⟩
  have h1 := hω.copy_content (mem_translate.mp hzd)
  rw [content_sub, content_origin] at h1
  constructor <;> omega

/-- Contents of cells of different components of a skew diagram, for a cell of a component
and a cell of the rest of the diagram. -/
theorem two_le_content_sdiff {X C : Diagram} (hX : IsSkew X) (hC : C ∈ edgeComponents X)
    {x y : ℤ × ℤ} (hx : x ∈ C) (hy : y ∈ X \ C) :
    content x + 2 ≤ content y ∨ content y + 2 ≤ content x := by
  obtain ⟨hyX, hyC⟩ := Finset.mem_sdiff.mp hy
  by_contra hcon
  push Not at hcon
  have hreach := diagReach_of_content_le_one hX (component_subset hC hx) hyX (by omega)
    (by omega)
  exact hyC (mem_component_of_reach hC hx hreach)

/-- The contents of the cells of `A` and `B` differ by at least two. -/
def ContentSep (A B : Diagram) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, content x + 2 ≤ content y ∨ content y + 2 ≤ content x

theorem ContentSep.disjoint {A B : Diagram} (h : ContentSep A B) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  rcases h x hxA x hxB with h | h <;> omega

theorem ContentSep.nonAdjacent {A B : Diagram} (h : ContentSep A B) : NonAdjacent A B := by
  intro x hx y hy hadj
  have := content_adj hadj
  rcases h x hx y hy with h | h <;> omega

theorem copies_separated {ω : MarkedInner} (hω : ω.IsLegal) {A B : Diagram}
    (hsep : ContentSep A B) :
    ContentSep (copies ω A) (copies ω B) := by
  have hq : 0 < ω.period := hω.period_pos
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  intro z hz z' hz'
  obtain ⟨d, hd, h1, h2⟩ := content_of_mem_copies hω hz
  obtain ⟨d', hd', h1', h2'⟩ := content_of_mem_copies hω hz'
  rcases hsep d hd d' hd' with hs | hs
  · left
    have : (content d + 2) * ω.period ≤ content d' * ω.period :=
      mul_le_mul_of_nonneg_right hs hq.le
    nlinarith
  · right
    have : (content d' + 2) * ω.period ≤ content d * ω.period :=
      mul_le_mul_of_nonneg_right hs hq.le
    nlinarith

theorem card_filter_union_sep {A B : Diagram} (hsep : ContentSep A B) (u : ℤ × ℤ)
    (hu : -1 ≤ content u ∧ content u ≤ 1) :
    ((A ∪ B).filter fun x => x + u ∈ A ∪ B).card =
      (A.filter fun x => x + u ∈ A).card + (B.filter fun x => x + u ∈ B).card := by
  have hAB : ∀ x ∈ A, (x + u ∈ A ∪ B ↔ x + u ∈ A) := by
    intro x hx
    rw [Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact h
      · have := hsep x hx _ h
        rw [content_add] at this
        omega
    · exact Or.inl
  have hBA : ∀ x ∈ B, (x + u ∈ A ∪ B ↔ x + u ∈ B) := by
    intro x hx
    rw [Finset.mem_union]
    constructor
    · rintro (h | h)
      · have := hsep _ h x hx
        rw [content_add] at this
        omega
      · exact h
    · exact Or.inr
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  · congr 1
    · exact congrArg Finset.card (Finset.filter_congr hAB)
    · exact congrArg Finset.card (Finset.filter_congr hBA)
  · exact Finset.disjoint_filter_filter hsep.disjoint

theorem countE_union {A B : Diagram} (h : ContentSep A B) :
    countE (A ∪ B) = countE A + countE B :=
  card_filter_union_sep h (0, 1) (by simp [content])

theorem countS_union {A B : Diagram} (h : ContentSep A B) :
    countS (A ∪ B) = countS A + countS B :=
  card_filter_union_sep h (1, 0) (by simp [content])

theorem countSE_union {A B : Diagram} (h : ContentSep A B) :
    countSE (A ∪ B) = countSE A + countSE B :=
  card_filter_union_sep h eCell (by simp [content, eCell])

end MarkedInner

/-- The modified composition of a skew diagram `X`, in terms of the cell counts and the union of
the copies. -/
noncomputable def tFun (ω : MarkedInner) (X : Diagram) : Lambda :=
  cellSchur ω.W ^ countE X * cellSchur (hatMarkFin ω) ^ countS X *
    cellSchur (hatMiddleFin ω) ^ countSE X * cellSchur (MarkedInner.copies ω X)

theorem modComp_connected_eq_tFun {ω : MarkedInner} (hord : ¬ ω.case.IsMixed) {C : Diagram}
    (hC : IsConnectedSkew C) : modComp ω C = tFun ω C := by
  unfold modComp tFun
  rw [edgeComponents_eq_singleton hC.2, Finset.prod_singleton]
  unfold componentT
  have h1 := card_eq_numRows_add_countE hC.1
  have h2 := card_eq_numCols_add_countS hC.1
  have h3 := card_eq_span_add_countSE hC.1
  have e1 : C.card - numRows C = countE C := by omega
  have e2 : C.card - numCols C = countS C := by omega
  have e3 : C.card - span C = countSE C := by omega
  rw [MarkedInner.compose_eq_copies hord hC.2.1, e1, e2, e3]

/-- **`modComp` of a skew diagram** (thesis (5.13) for a diagram that is not connected): the
product over the components, for an ordinary legal mark, is the formula (5.13) applied to the
whole diagram. -/
theorem modComp_eq_tFun {ω : MarkedInner} (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) :
    ∀ n : ℕ, ∀ X : Diagram, X.card = n → IsSkew X → modComp ω X = tFun ω X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hn hX
    by_cases hXe : X = ∅
    · subst hXe
      simp [modComp_empty, tFun, countE, countS, countSE, MarkedInner.copies_empty,
        cellSchur_empty]
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hXe
      set C := X.filter (fun y => DiagReach X x y) with hCdef
      have hC : C ∈ edgeComponents X := mem_edgeComponents.mpr ⟨x, hx, rfl⟩
      have hCconn := isConnectedSkew_component hX hC
      have hRskew := isSkew_sdiff_component hX hC
      have hcard : (X \ C).card < n := by
        have h1 := Finset.card_sdiff_add_card_eq_card (component_subset hC)
        have h2 : 0 < C.card := Finset.card_pos.mpr (component_nonempty hC)
        omega
      have hIH := ih _ hcard (X \ C) rfl hRskew
      have hsep : MarkedInner.ContentSep C (X \ C) := fun a ha b hb =>
        MarkedInner.two_le_content_sdiff hX hC ha hb
      have hmod : modComp ω X = modComp ω C * modComp ω (X \ C) := by
        conv_lhs => rw [← union_component_sdiff hC]
        exact modComp_union hsep.disjoint hsep.nonAdjacent
      have hX' : X = C ∪ (X \ C) := (union_component_sdiff hC).symm
      have hcop := MarkedInner.copies_separated hω hsep
      rw [hmod, hIH, modComp_connected_eq_tFun hord hCconn]
      conv_rhs => rw [hX']
      unfold tFun
      rw [MarkedInner.countE_union hsep, MarkedInner.countS_union hsep,
        MarkedInner.countSE_union hsep, MarkedInner.copies_union hord,
        cellSchur_union hcop.disjoint hcop.nonAdjacent]
      ring

end Plan

end GluingCore
