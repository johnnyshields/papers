/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.FirstVariations
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Finite endpoint counts

The strict finite-set enumeration and endpoint-count argument in
`sec:restoration` of `shields-2026-skew-cofactor-independence.tex`.
-/

namespace SkewCofactorIndependence
namespace BetaEndpointCounts

open scoped BigOperators

/-- The decreasing enumeration of a finite integer set. -/
noncomputable def descending (s : Finset ℤ) {n : ℕ} (h : s.card = n) : Fin n → ℤ :=
  fun i => s.orderEmbOfFin h i.rev

theorem descending_strictAnti (s : Finset ℤ) {n : ℕ} (h : s.card = n) :
    StrictAnti (descending s h) := by
  intro i j hij
  apply (s.orderEmbOfFin h).strictMono
  simpa using Fin.rev_lt_rev.mpr hij

theorem descending_mem (s : Finset ℤ) {n : ℕ} (h : s.card = n) (i : Fin n) :
    descending s h i ∈ s := (s.orderIsoOfFin h i.rev).property

theorem descending_surjective (s : Finset ℤ) {n : ℕ} (h : s.card = n)
    {x : ℤ} (hx : x ∈ s) : ∃ i, descending s h i = x := by
  refine ⟨((s.orderIsoOfFin h).symm ⟨x, hx⟩).rev, ?_⟩
  simp [descending, ← Finset.coe_orderIsoOfFin_apply]

theorem image_descending (s : Finset ℤ) {n : ℕ} (h : s.card = n) :
    Finset.univ.image (descending s h) = s := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ descending_mem s h i, descending_surjective s h⟩

/-- Number of endpoints strictly above an integer cut. -/
noncomputable def above (s : Finset ℤ) (x : ℤ) : ℕ := (s.filter (x < ·)).card

theorem above_image_at {n : ℕ} (f : Fin n → ℤ) (hf : StrictAnti f) (i : Fin n) :
    above (Finset.univ.image f) (f i) = i.val := by
  classical
  have he : (Finset.univ.image f).filter (f i < ·) = (Finset.Iio i).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, (hf.lt_iff_gt).mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hf hj⟩
  rw [above, he, Finset.card_image_of_injective _ hf.injective]
  simp

theorem above_mono {s : Finset ℤ} {x y : ℤ} (hxy : x ≤ y) :
    above s y ≤ above s x := by
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, lt_of_le_of_lt hxy hz.2⟩

theorem above_lt_at {n : ℕ} (f : Fin n → ℤ) (hf : StrictAnti f)
    (i : Fin n) {x : ℤ} (hx : x < f i) :
    i.val < above (Finset.univ.image f) x := by
  classical
  have hs : (Finset.univ.image f).filter (f i < ·) ⊂
      (Finset.univ.image f).filter (x < ·) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hx.trans hz.2⟩
    · intro he
      have hm : f i ∈ (Finset.univ.image f).filter (x < ·) := by simp [hx]
      rw [← he] at hm
      simp at hm
  have hc := Finset.card_lt_card hs
  change above (Finset.univ.image f) (f i) < above (Finset.univ.image f) x at hc
  rw [above_image_at f hf i] at hc
  exact hc

theorem above_le_at {n : ℕ} (f : Fin n → ℤ) (hf : StrictAnti f)
    (i : Fin n) {x : ℤ} (hx : f i ≤ x) :
    above (Finset.univ.image f) x ≤ i.val := by
  simpa only [above_image_at f hf i] using
    (above_mono (s := Finset.univ.image f) hx)

theorem above_le_iff {n : ℕ} (f : Fin n → ℤ) (hf : StrictAnti f)
    (i : Fin n) (x : ℤ) : above (Finset.univ.image f) x ≤ i.val ↔ f i ≤ x := by
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge h) (above_lt_at f hf i (lt_of_not_ge hn))
  · exact above_le_at f hf i

theorem above_union (s z : Finset ℤ) (h : Disjoint s z) (x : ℤ) :
    above (s ∪ z) x = above s x + above z x := by
  classical
  rw [above, Finset.filter_union, Finset.card_union_of_disjoint]
  · rfl
  · exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem above_difference (r c : Finset ℤ) (x : ℤ) :
    (above (r \ c) x : ℤ) - above (c \ r) x = (above r x : ℤ) - above c x := by
  classical
  have hr : Disjoint (r \ c) (r ∩ c) := by
    apply Finset.disjoint_left.mpr
    intro z hz hi
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp hi).2
  have hc : Disjoint (c \ r) (r ∩ c) := by
    apply Finset.disjoint_left.mpr
    intro z hz hi
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp hi).1
  have er : (r \ c) ∪ (r ∩ c) = r := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_sdiff.mp hz).1
      · exact (Finset.mem_inter.mp hz).1
    · intro hz
      by_cases hc : z ∈ c
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, hc⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hc⟩)
  have ec : (c \ r) ∪ (r ∩ c) = c := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_sdiff.mp hz).1
      · exact (Finset.mem_inter.mp hz).2
    · intro hz
      by_cases hr : z ∈ r
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hr, hz⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hr⟩)
  have ar := above_union (r \ c) (r ∩ c) hr x
  have ac := above_union (c \ r) (r ∩ c) hc x
  rw [er] at ar
  rw [ec] at ac
  omega

/-- A finite beta pair whose endpoint difference is positive throughout its span. -/
structure SpanPair (r c : Finset ℤ) where
  /-- The smallest column beta. -/
  bottom : ℤ
  /-- The largest row beta. -/
  top : ℤ
  bottom_mem : bottom ∈ c
  top_mem : top ∈ r
  lower : ∀ x ∈ r ∪ c, bottom ≤ x
  upper : ∀ x ∈ r ∪ c, x ≤ top
  strict_span : bottom < top
  positive : ∀ x : ℤ, bottom ≤ x → x < top → above c x < above r x
  equal_card : r.card = c.card

theorem SpanPair.card_pos {r c : Finset ℤ} (p : SpanPair r c) : 0 < r.card :=
  Finset.card_pos.mpr ⟨p.top, p.top_mem⟩

theorem SpanPair.top_not_col {r c : Finset ℤ} (p : SpanPair r c) : p.top ∉ c := by
  classical
  intro ht
  have ha : above r (p.top - 1) = 1 := by
    unfold above
    have he : r.filter (p.top - 1 < ·) = {p.top} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hlt⟩
        have hu := p.upper z (Finset.mem_union_left _ hz)
        omega
      · rintro rfl
        exact ⟨p.top_mem, by omega⟩
    rw [he, Finset.card_singleton]
  have hb : p.bottom ≤ p.top - 1 := by have := p.strict_span; omega
  have hpos := p.positive (p.top - 1) hb (by omega)
  have hc : 0 < above c (p.top - 1) := by
    exact Finset.card_pos.mpr ⟨p.top, by simp [ht]⟩
  omega

theorem SpanPair.bottom_not_row {r c : Finset ℤ} (p : SpanPair r c) :
    p.bottom ∉ r := by
  classical
  intro hb
  have count (s : Finset ℤ) (hs : p.bottom ∈ s)
      (hl : ∀ z ∈ s, p.bottom ≤ z) : above s p.bottom = s.card - 1 := by
    have he : s.filter (p.bottom < ·) = s.erase p.bottom := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz, hlt⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_erase.mpr ⟨ne_of_gt hlt, hz⟩
      · intro hz
        obtain ⟨hne, hz⟩ := Finset.mem_erase.mp hz
        have hlow : p.bottom ≤ z := hl z hz
        exact Finset.mem_filter.mpr ⟨hz, lt_of_le_of_ne hlow hne.symm⟩
    change (s.filter (p.bottom < ·)).card = s.card - 1
    rw [he, Finset.card_erase_of_mem hs]
  have hr := count r hb (fun z hz => p.lower z (Finset.mem_union_left _ hz))
  have hc := count c p.bottom_mem (fun z hz => p.lower z (Finset.mem_union_right _ hz))
  have hp := p.positive p.bottom le_rfl p.strict_span
  rw [hr, hc, p.equal_card] at hp
  omega

/-- Cancel all common betas while preserving the endpoints and positive span. -/
noncomputable def SpanPair.cancel {r c : Finset ℤ} (p : SpanPair r c) :
    SpanPair (r \ c) (c \ r) where
  bottom := p.bottom
  top := p.top
  bottom_mem := Finset.mem_sdiff.mpr ⟨p.bottom_mem, p.bottom_not_row⟩
  top_mem := Finset.mem_sdiff.mpr ⟨p.top_mem, p.top_not_col⟩
  lower x hx := p.lower x (by
    rcases Finset.mem_union.mp hx with hr | hc
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hr).1
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1)
  upper x hx := p.upper x (by
    rcases Finset.mem_union.mp hx with hr | hc
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hr).1
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1)
  strict_span := p.strict_span
  positive x hlow hhigh := by
    have h := p.positive x hlow hhigh
    have he := above_difference r c x
    omega
  equal_card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm c r, p.equal_card]

/-- Restore a disjoint common beta set strictly between the endpoints. -/
noncomputable def SpanPair.restore {r c : Finset ℤ} (p : SpanPair r c)
    (z : Finset ℤ) (hr : Disjoint r z) (hc : Disjoint c z)
    (hz : ∀ x ∈ z, p.bottom < x ∧ x < p.top) : SpanPair (r ∪ z) (c ∪ z) where
  bottom := p.bottom
  top := p.top
  bottom_mem := Finset.mem_union_left _ p.bottom_mem
  top_mem := Finset.mem_union_left _ p.top_mem
  lower x hx := by
    simp only [Finset.mem_union] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact p.lower x (Finset.mem_union_left _ hx)
    · exact (hz x hx).1.le
    · exact p.lower x (Finset.mem_union_right _ hx)
    · exact (hz x hx).1.le
  upper x hx := by
    simp only [Finset.mem_union] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact p.upper x (Finset.mem_union_left _ hx)
    · exact (hz x hx).2.le
    · exact p.upper x (Finset.mem_union_right _ hx)
    · exact (hz x hx).2.le
  strict_span := p.strict_span
  positive x hlow hhigh := by
    rw [above_union r z hr, above_union c z hc]
    exact Nat.add_lt_add_right (p.positive x hlow hhigh) _
  equal_card := by
    rw [Finset.card_union_of_disjoint hr, Finset.card_union_of_disjoint hc, p.equal_card]

/-- Sorting a positive-span pair produces nonempty rows, rather than assuming them. -/
noncomputable def SpanPair.diagram {r c : Finset ℤ} (p : SpanPair r c)
    {n : ℕ} (hr : r.card = n) : BetaDiagram n where
  row := descending r hr
  col := descending c (p.equal_card.symm.trans hr)
  row_strictAnti := descending_strictAnti r hr
  col_strictAnti := descending_strictAnti c (p.equal_card.symm.trans hr)
  row_nonempty i := by
    let a := descending r hr
    let b := descending c (p.equal_card.symm.trans hr)
    have hm := descending_mem c (p.equal_card.symm.trans hr) i
    have hl := p.lower (b i) (Finset.mem_union_right _ hm)
    have hu : b i < p.top := by
      have hu := p.upper (b i) (Finset.mem_union_right _ hm)
      have hn : b i ≠ p.top := by intro he; exact p.top_not_col (he ▸ hm)
      omega
    have hp := p.positive (b i) hl hu
    have hc : above c (b i) = i.val := by
      rw [← image_descending c (p.equal_card.symm.trans hr)]
      exact above_image_at b (descending_strictAnti c _) i
    by_contra hn
    have hc' : above r (b i) ≤ i.val := by
      rw [← image_descending r hr]
      exact above_le_at a (descending_strictAnti r _) i (le_of_not_gt hn)
    omega

theorem SpanPair.diagram_connected {r c : Finset ℤ} (p : SpanPair r c)
    {n : ℕ} (hr : r.card = n) : (p.diagram hr).Connected := by
  have hn : 0 < n := by have := p.card_pos; omega
  refine ⟨hn, ?_⟩
  intro i hi
  let j : Fin n := ⟨i.val + 1, hi⟩
  let a := descending r hr
  let b := descending c (p.equal_card.symm.trans hr)
  have hm := descending_mem r hr j
  have hl := p.lower (a j) (Finset.mem_union_left _ hm)
  have hu : a j < p.top := by
    let zero : Fin n := ⟨0, hn⟩
    have hj : zero < j := by simp [zero, j]
    have hs := descending_strictAnti r hr hj
    have ht := p.upper (a zero)
      (Finset.mem_union_left _ (descending_mem r hr zero))
    exact lt_of_lt_of_le hs ht
  have hp := p.positive (a j) hl hu
  have hc : above r (a j) = i.val + 1 := by
    rw [← image_descending r hr, above_image_at a (descending_strictAnti r hr) j]
  change b i ≤ a j
  apply (above_le_iff b (descending_strictAnti c _) i (a j)).mp
  rw [image_descending]
  omega

theorem strictAnti_eq_of_image {n : ℕ} (f g : Fin n → ℤ)
    (hf : StrictAnti f) (hg : StrictAnti g)
    (he : Finset.univ.image f = Finset.univ.image g) : f = g := by
  classical
  funext i
  have hm : f i ∈ Finset.univ.image g := by rw [← he]; simp
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
  have hcount := above_image_at f hf i
  rw [he, ← hj, above_image_at g hg j] at hcount
  have hij : i = j := Fin.ext hcount.symm
  simpa [hij] using hj.symm

end BetaEndpointCounts
end SkewCofactorIndependence
