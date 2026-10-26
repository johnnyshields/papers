/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ProfileFiniteEnumeration
import SkewCornerDescent.MarkTranslation
import SkewCornerDescent.OrdinaryGauge

/-!
# Complete finite census of positive ordinary marks and gauge pairs

Supports `shields-2026-skew-corner-descent.tex` (`rem:ordinary-gauge`).
The actual profile census covers every connected skew inner of bounded
area up to literal translation. End-content bounds prune the finite mark
candidates before full I--IV legality is checked. Completeness is proved
for the actual marked inners, not only for their row codes. Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing

/-- Actual lower end-band cells at a prescribed positive width. -/
def censusLowerBand (E : Diagram) (w : ℕ) : Diagram :=
  E.filter fun x => content x < minContent E + (w : ℤ)

/-- Finite actual mark candidates, pruned by the necessary end width,
separation and original displacement content before legality is tested. -/
def positiveMarkCandidates (E : Diagram) (caseTag : AttachCase) : Finset MarkedInner :=
  (Finset.range (span E)).biUnion fun w =>
    if 0 < w ∧ 2*w < span E then
      ((censusLowerBand E w).powerset).biUnion fun W =>
        if W.Nonempty ∧ span W = w then
          (E.filter fun x => content (x-sw E) = (span E : ℤ)-(w : ℤ)).image fun x =>
            { E := E, W := W, v := x-sw E, case := caseTag }
        else ∅
    else ∅

/-- Every positive actual legal marked inner occurs in the finite candidate list. -/
theorem positiveMarkCandidates_complete {ω : MarkedInner} (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω ∈ positiveMarkCandidates ω.E ω.case := by
  have hnon : ω.IsNonemptyMark := by
    rcases h.1.2 with hemp | hnon
    · exact False.elim (hW.ne_empty hemp.1)
    · exact hnon
  have hwidth : 0 < ω.width := Finset.card_pos.mpr (hW.image content)
  have hspan := h.1.span_eq
  have hnarrow := h.2.2.1.2
  have hhalf : 2*ω.width < span ω.E := by omega
  have hlt : ω.width < span ω.E := by omega
  have hband : ω.W ⊆ censusLowerBand ω.E ω.width := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hnon.2.2.1 hx, by
      have hb := (hnon.content_bounds h.1.1).1 x hx
      omega⟩
  have hx : sw ω.E + ω.v ∈ ω.E := by
    apply hnon.2.2.2.1
    apply mem_translate.mpr
    simpa using hnon.2.2.2.2.1
  have hv : (sw ω.E + ω.v)-sw ω.E = ω.v := by abel
  apply Finset.mem_biUnion.mpr
  refine ⟨ω.width, Finset.mem_range.mpr hlt, ?_⟩
  rw [ite_eq_left ⟨hwidth, hhalf⟩]
  apply Finset.mem_biUnion.mpr
  refine ⟨ω.W, Finset.mem_powerset.mpr hband, ?_⟩
  rw [ite_eq_left ⟨hW, rfl⟩]
  apply Finset.mem_image.mpr
  refine ⟨sw ω.E + ω.v, Finset.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩
  · rw [hv]
    change ω.period = (span ω.E : ℤ)-(ω.width : ℤ)
    omega
  · rw [hv]

/-- Necessary local geometry is checked before maximality and condition IV.
The full legality check is retained at the final pair or V-failure stage. -/
def ordinaryGeometricMarks (E : Diagram) (caseTag : AttachCase) : Finset MarkedInner :=
  (positiveMarkCandidates E caseTag).filter fun ω => ω.IsNonemptyMark ∧ IsConnectedSkew ω.middle

/-- The geometric prefilter removes no actual positive legal mark. -/
theorem ordinaryGeometricMarks_complete {ω : MarkedInner} (h : ω.IsLegal)
    (hW : ω.W.Nonempty) : ω ∈ ordinaryGeometricMarks ω.E ω.case := by
  exact Finset.mem_filter.mpr
    ⟨positiveMarkCandidates_complete h hW, h.isNonemptyMark hW, h.middle_connected hW⟩

/-- Southwest-normalized representatives of every actual bounded shape. -/
def profileDiagramCensus (A : ℕ) : List Diagram :=
  (profilesAtMost A).map fun (p : Σ n, Profile n) => SkewGluing.normalize p.2.cells

/-- Every connected actual inner of bounded area has its normalized cell set
in the finite shape census. -/
theorem profileDiagramCensus_complete {E : Diagram} (hE : IsConnectedSkew E)
    (A : ℕ) (harea : E.card ≤ A) : normalize E ∈ profileDiagramCensus A := by
  obtain ⟨p, hp, v, he⟩ := diagram_mem_profile_census hE A harea
  apply List.mem_map.mpr
  refine ⟨p, hp, ?_⟩
  rw [he, normalize_translate p.2.isConnectedSkew_cells.2.1 v]

/-- Fuse shape traversal with union, avoiding comparisons between entire shapes. -/
def diagramCensusUnion {α : Type*} [DecidableEq α] (A : ℕ)
    (f : Diagram → Finset α) : Finset α :=
  (profileDiagramCensus A).foldr (fun E acc => f E ∪ acc) ∅

private theorem mem_list_union {α β : Type*} [DecidableEq α]
    (L : List β) (f : β → Finset α) (x : α) :
    x ∈ L.foldr (fun a acc => f a ∪ acc) ∅ ↔ ∃ a ∈ L, x ∈ f a := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, or_and_right, exists_or]

/-- Membership in the fused census is exactly membership at one listed shape. -/
theorem mem_diagramCensusUnion {α : Type*} [DecidableEq α] (A : ℕ)
    (f : Diagram → Finset α) (x : α) :
    x ∈ diagramCensusUnion A f ↔ ∃ E ∈ profileDiagramCensus A, x ∈ f E :=
  mem_list_union _ _ _

/-- Canonical literal representative of a marked inner's translation class. -/
def normalizeMarkedInner (ω : MarkedInner) : MarkedInner := ω.translateBy (-sw ω.E)

/-- All positive horizontal/vertical readings with the same actual period,
with no assumption of a gauge identity or Hypothesis V failure. -/
def positiveOrdinaryGaugePairs (E : Diagram) : Finset (MarkedInner × MarkedInner) :=
  (((ordinaryGeometricMarks E .a) ×ˢ (ordinaryGeometricMarks E .b)).filter fun p =>
    p.1.period = p.2.period).filter fun p => p.1.IsLegal ∧ p.2.IsLegal

/-- Every positive ordinary gauge candidate through the bounded actual area,
modulo literal translation of the whole marked inner. -/
def ordinaryGaugeCensus (A : ℕ) : Finset (MarkedInner × MarkedInner) :=
  diagramCensusUnion A positiveOrdinaryGaugePairs

/-- The complete finite gauge census contains every actual positive pair
of ordinary readings of the same bounded inner and period. -/
theorem ordinaryGaugeCensus_complete {ωa ωb : MarkedInner}
    (ha : ωa.IsLegal) (hb : ωb.IsLegal) (hWa : ωa.W.Nonempty) (hWb : ωb.W.Nonempty)
    (hca : ωa.case = .a) (hcb : ωb.case = .b) (hE : ωb.E = ωa.E)
    (hperiod : ωa.period = ωb.period) (A : ℕ) (harea : ωa.E.card ≤ A) :
    (normalizeMarkedInner ωa, normalizeMarkedInner ωb) ∈ ordinaryGaugeCensus A := by
  let a := normalizeMarkedInner ωa
  let b := normalizeMarkedInner ωb
  have hla : a.IsLegal := MarkedInner.isLegal_translateBy_nonempty ha hWa (-sw ωa.E)
  have hlb : b.IsLegal := MarkedInner.isLegal_translateBy_nonempty hb hWb (-sw ωb.E)
  have hna : a.W.Nonempty := hWa.image (fun x => x + -(sw ωa.E))
  have hnb : b.W.Nonempty := hWb.image (fun x => x + -(sw ωb.E))
  have hEa : a.E = normalize ωa.E := rfl
  have hEb : b.E = normalize ωa.E := by change normalize ωb.E = normalize ωa.E; rw [hE]
  have hCaseA : a.case = .a := hca
  have hCaseB : b.case = .b := hcb
  have hma := ordinaryGeometricMarks_complete hla hna
  have hmb := ordinaryGeometricMarks_complete hlb hnb
  rw [hEa, hCaseA] at hma
  rw [hEb, hCaseB] at hmb
  apply (mem_diagramCensusUnion A _ _).mpr
  refine ⟨normalize ωa.E, profileDiagramCensus_complete ha.1.1 A harea, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hma, hmb⟩, hperiod⟩, hla, hlb⟩

/-- Cells of one end copy adjacent to the actual middle. -/
def ordinaryAdjacentCells (W O : Diagram) : Diagram :=
  W.filter fun x => ∃ y ∈ O, CellAdj x y

/-- The ordinary Hypothesis V end test: at least one copy has exactly one
cell adjacent to the actual middle. -/
def ordinaryHypothesisV (ω : MarkedInner) : Prop :=
  (ordinaryAdjacentCells ω.W ω.middle).card = 1 ∨
    (ordinaryAdjacentCells ω.upper ω.middle).card = 1

instance (ω : MarkedInner) : Decidable (ordinaryHypothesisV ω) := by
  unfold ordinaryHypothesisV
  infer_instance

/-- Positive ordinary marks failing V, with their actual cell data retained. -/
def ordinaryVFailureCensus (A : ℕ) : Finset MarkedInner :=
  diagramCensusUnion A fun E =>
    (((ordinaryGeometricMarks E .a) ∪ (ordinaryGeometricMarks E .b)).filter fun ω =>
      ¬ ordinaryHypothesisV ω).filter fun ω => ω.IsLegal

/-- The finite end-cardinality test is exactly the stated unique-adjacent-cell
condition, not a geometric proxy. -/
theorem ordinaryAdjacentCells_card_one_iff (W O : Diagram) :
    (ordinaryAdjacentCells W O).card = 1 ↔
      ∃! x, x ∈ W ∧ ∃ y ∈ O, CellAdj x y := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    have hm : a ∈ ordinaryAdjacentCells W O := by rw [ha]; simp
    refine ⟨a, Finset.mem_filter.mp hm, ?_⟩
    intro b hb
    have hbmem : b ∈ ordinaryAdjacentCells W O := Finset.mem_filter.mpr hb
    rwa [ha, Finset.mem_singleton] at hbmem
  · rintro ⟨a, ha, huniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨a, ?_⟩
    ext b
    rw [Finset.mem_singleton]
    constructor
    · intro hb
      exact huniq b (Finset.mem_filter.mp hb)
    · rintro rfl
      exact Finset.mem_filter.mpr ha

/-- The census predicate is precisely ordinary Hypothesis V at either end. -/
theorem ordinaryHypothesisV_iff (ω : MarkedInner) :
    ordinaryHypothesisV ω ↔
      (∃! x, x ∈ ω.W ∧ ∃ y ∈ ω.middle, CellAdj x y) ∨
      (∃! x, x ∈ ω.upper ∧ ∃ y ∈ ω.middle, CellAdj x y) :=
  or_congr (ordinaryAdjacentCells_card_one_iff _ _) (ordinaryAdjacentCells_card_one_iff _ _)

/-- Both the adjacent copy cell and the actual middle neighbor translate. -/
theorem ordinaryAdjacentCells_translate (W O : Diagram) (t : ℤ × ℤ) :
    ordinaryAdjacentCells (translate t W) (translate t O) =
      translate t (ordinaryAdjacentCells W O) := by
  ext x
  simp only [ordinaryAdjacentCells, Finset.mem_filter, mem_translate]
  constructor
  · rintro ⟨hx, y, hy, hadj⟩
    exact ⟨hx, y-t, hy, MarkedInner.cellAdj_sub t hadj⟩
  · rintro ⟨hx, y, hy, hadj⟩
    refine ⟨hx, y+t, by simpa using hy, ?_⟩
    simpa only [sub_neg_eq_add, sub_add_cancel] using MarkedInner.cellAdj_sub (-t) hadj

/-- Ordinary Hypothesis V is invariant under the whole literal mark translation. -/
theorem ordinaryHypothesisV_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    ordinaryHypothesisV (ω.translateBy t) ↔ ordinaryHypothesisV ω := by
  unfold ordinaryHypothesisV
  rw [MarkedInner.middle_translateBy, MarkedInner.upper_translateBy]
  change (ordinaryAdjacentCells (translate t ω.W) (translate t ω.middle)).card = 1 ∨
    (ordinaryAdjacentCells (translate t ω.upper) (translate t ω.middle)).card = 1 ↔ _
  have hc (S : Diagram) : (translate t S).card = S.card :=
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
  rw [ordinaryAdjacentCells_translate, ordinaryAdjacentCells_translate, hc, hc]

/-- Positivity at one of two equal-period readings forces positivity at the other. -/
theorem ordinaryGauge_nonempty_other {ωa ωb : MarkedInner}
    (ha : ωa.IsLegal) (hb : ωb.IsLegal) (hWa : ωa.W.Nonempty)
    (hE : ωb.E = ωa.E) (hperiod : ωa.period = ωb.period) : ωb.W.Nonempty := by
  by_contra hn
  have hempty : ωb.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hwb : ωb.width = 0 := by simp only [MarkedInner.width, hempty, span, contents,
    Finset.image_empty, Finset.card_empty]
  have hwa : 0 < ωa.width := Finset.card_pos.mpr (hWa.image content)
  have hsa := ha.1.span_eq
  have hsb := hb.1.span_eq
  rw [hE, hwb] at hsb
  omega

/-- Every positive actual ordinary V failure is represented in the bounded
failure census after the same complete southwest normalization. -/
theorem ordinaryVFailureCensus_complete {ω : MarkedInner} (h : ω.IsLegal)
    (hW : ω.W.Nonempty) (hcase : ω.case = .a ∨ ω.case = .b)
    (hnot : ¬ ordinaryHypothesisV ω) (A : ℕ) (harea : ω.E.card ≤ A) :
    normalizeMarkedInner ω ∈ ordinaryVFailureCensus A := by
  let a := normalizeMarkedInner ω
  have hla : a.IsLegal := MarkedInner.isLegal_translateBy_nonempty h hW (-sw ω.E)
  have hna : a.W.Nonempty := hW.image (fun x => x + -(sw ω.E))
  have hEa : a.E = normalize ω.E := rfl
  have hca : a.case = ω.case := rfl
  have hm := ordinaryGeometricMarks_complete hla hna
  rw [hEa, hca] at hm
  have hmember : a ∈ ordinaryGeometricMarks (normalize ω.E) .a ∪
      ordinaryGeometricMarks (normalize ω.E) .b := by
    rcases hcase with hc | hc
    · rw [hc] at hm
      exact Finset.mem_union.mpr (Or.inl hm)
    · rw [hc] at hm
      exact Finset.mem_union.mpr (Or.inr hm)
  apply (mem_diagramCensusUnion A _ _).mpr
  refine ⟨normalize ω.E, profileDiagramCensus_complete h.1.1 A harea, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmember,
    fun hv => hnot ((ordinaryHypothesisV_translateBy ω (-sw ω.E)).mp hv)⟩, hla⟩

/-- The complete canonical marked representative is unchanged by translation. -/
theorem normalizeMarkedInner_translateBy (ω : MarkedInner) (hE : ω.E.Nonempty)
    (t : ℤ × ℤ) :
    normalizeMarkedInner (ω.translateBy t) = normalizeMarkedInner ω := by
  change (ω.translateBy t).translateBy (-(sw (translate t ω.E))) =
    ω.translateBy (-sw ω.E)
  rw [sw_translate hE t, MarkedInner.translateBy_add]
  have he : t + -(sw ω.E+t) = -sw ω.E := by abel
  rw [he]

/-- Equality of the canonical marked representatives is exactly literal
translation equivalence, so the census counts translation classes once. -/
theorem normalizeMarkedInner_eq_iff {ωa ωb : MarkedInner} (hE : ωa.E.Nonempty) :
    normalizeMarkedInner ωa = normalizeMarkedInner ωb ↔ ωa.EquivTranslate ωb := by
  constructor
  · intro he
    refine ⟨sw ωb.E-sw ωa.E, ?_⟩
    have ht := congrArg (fun ω => ω.translateBy (sw ωb.E)) he
    unfold normalizeMarkedInner at ht
    rw [MarkedInner.translateBy_add, MarkedInner.translateBy_add, neg_add_cancel,
      MarkedInner.translateBy_zero] at ht
    have hv : -sw ωa.E+sw ωb.E = sw ωb.E-sw ωa.E := by abel
    rw [hv] at ht
    exact ht.symm
  · rintro ⟨t, rfl⟩
    exact (normalizeMarkedInner_translateBy ωa hE t).symm

end SkewCornerDescent
