import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.LeftCells
import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.RightCount

/-!
# Counting the diagonals, rows and columns lost by removing a left ribbon

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the exponents of thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), "counting boxes as in the proof of Lemma 5.4.6", for a ribbon
`leftStrip D j₀ m` removable on the left from `D`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {D : Diagram} {j0 : ℤ} {m : ℕ}

theorem rLone_subset_contents_L (hw : LeftWindow D j0 m) :
    rLone D j0 m ⊆ contents D := by
  obtain ⟨hmem, -⟩ := outer_facts hw.conn
  intro j hj
  rw [mem_rLone] at hj
  have h0 := (hmem j0).mp hw.start
  have h1 := (hmem (j0 + (m : ℤ) - 1)).mp hw.stop
  rw [hmem]
  omega

theorem contents_XL_eq (hw : LeftWindow D j0 m) :
    contents (D \ leftStrip D j0 m) = contents D \ rLone D j0 m := by
  ext j
  rw [contents_XL hw, Finset.mem_sdiff, mem_rLone]
  tauto

theorem card_rLone_L (hw : LeftWindow D j0 m) :
    (rLone D j0 m).card = span D - span (D \ leftStrip D j0 m) := by
  have h1 := Finset.card_sdiff_of_subset (rLone_subset_contents_L hw)
  have h2 : span (D \ leftStrip D j0 m) = span D - (rLone D j0 m).card := by
    unfold span
    rw [contents_XL_eq hw, h1]
  have h3 : (rLone D j0 m).card ≤ span D := Finset.card_le_card (rLone_subset_contents_L hw)
  omega

theorem exists_max_col {X : Diagram} {i : ℤ} (h : ∃ c, (i, c) ∈ X) :
    ∃ cm, (i, cm) ∈ X ∧ ∀ c', (i, c') ∈ X → c' ≤ cm := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (X.filter fun x => x.1 = i) Prod.snd
    ⟨(i, c), Finset.mem_filter.mpr ⟨hc, rfl⟩⟩
  obtain ⟨hxX, hx1⟩ := Finset.mem_filter.mp hx
  refine ⟨x.2, ?_, fun c' hc' => hmax (i, c') (Finset.mem_filter.mpr ⟨hc', rfl⟩)⟩
  have : x = (i, x.2) := Prod.ext hx1 rfl
  rw [← this]; exact hxX

theorem exists_max_row {X : Diagram} {c : ℤ} (h : ∃ i, (i, c) ∈ X) :
    ∃ rm, (rm, c) ∈ X ∧ ∀ r', (r', c) ∈ X → r' ≤ rm := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (X.filter fun x => x.2 = c) Prod.fst
    ⟨(i, c), Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  obtain ⟨hxX, hx1⟩ := Finset.mem_filter.mp hx
  refine ⟨x.1, ?_, fun r' hr' => hmax (r', c) (Finset.mem_filter.mpr ⟨hr', rfl⟩)⟩
  have : x = (x.1, c) := Prod.ext rfl hx1
  rw [← this]; exact hxX

theorem lone_cell_mem_leftStrip {j : ℤ} (hj : j ∈ rLone D j0 m) :
    (diagLo D j, diagLo D j + j) ∈ leftStrip D j0 m := by
  rw [mem_rLone] at hj
  rw [mem_leftStrip]
  have e : content (diagLo D j, diagLo D j + j) = j := by simp [content]
  rw [e]
  exact ⟨hj.1.1, hj.1.2, rfl⟩

theorem lone_cell_mem_D_L (hw : LeftWindow D j0 m) {j : ℤ} (hj : j ∈ rLone D j0 m) :
    (diagLo D j, diagLo D j + j) ∈ D :=
  diagLo_mem (rLone_subset_contents_L hw hj)

theorem rows_lost_L (hw : LeftWindow D j0 m) (i : ℤ) :
    i ∈ rowSet D \ rowSet (D \ leftStrip D j0 m) ↔
      ∃ j ∈ lLoneE D j0 m, diagLo D j = i := by
  have hDs := hw.conn.1
  have hdown := (mem_leftRibbons.mp hw.mem).2.2.2
  rw [Finset.mem_sdiff, mem_rowSet_iff, mem_rowSet_iff]
  constructor
  · rintro ⟨⟨c, hc⟩, hnot⟩
    have hnot' : ∀ c', (i, c') ∈ D → (i, c') ∈ leftStrip D j0 m := by
      intro c' hc'
      by_contra hA
      exact hnot ⟨c', Finset.mem_sdiff.mpr ⟨hc', hA⟩⟩
    obtain ⟨cm, hℓ, hmax⟩ := exists_max_col ⟨c, hc⟩
    have hA := hnot' cm hℓ
    rw [mem_leftStrip] at hA
    obtain ⟨hA1, hA2, hA3⟩ := hA
    simp only [content] at hA1 hA2 hA3
    set j := cm - i with hj
    have hcell : (i, cm) = (i, i + j) := Prod.ext rfl (by omega)
    rw [hcell] at hℓ
    have hjC : j ∈ contents D := mem_contents_iff.mpr ⟨i, hℓ⟩
    have hlone : diagLo D j = diagHi D j := by
      by_contra hne
      have hle := diagLo_le_diagHi hjC
      have hb' : (i + 1, i + 1 + j) ∈ D :=
        (mem_skew_iff hDs).mpr ⟨hjC, by omega, by omega⟩
      have := hDs.mem (a := i) (b := i + j) (c := i + 1) (d := i + 1 + j) (i := i)
        (j := i + 1 + j) hℓ hb' (by omega) (by omega) le_rfl (by omega) (by omega) le_rfl
      have := hmax _ this
      omega
    refine ⟨j, ?_, by omega⟩
    rw [mem_lLoneE hDs, mem_rLone]
    refine ⟨⟨⟨by omega, by omega⟩, hlone⟩, ?_⟩
    rintro ⟨h1', h2', h3'⟩
    have hlo : diagLo D j = i := by omega
    have := hmax (i + 1 + j) (by
      have e : (i, i + 1 + j) = (i, i + (j + 1)) := Prod.ext rfl (by ring)
      rw [e]
      exact (mem_skew_iff hDs).mpr ⟨h1', by omega, by omega⟩)
    omega
  · rintro ⟨j, hj, rfl⟩
    have hjL : j ∈ rLone D j0 m := (Finset.mem_filter.mp hj).1
    have hbD := lone_cell_mem_D_L hw hjL
    have hbA := lone_cell_mem_leftStrip hjL
    refine ⟨⟨_, hbD⟩, ?_⟩
    rintro ⟨c, hc⟩
    obtain ⟨hcD, hcA⟩ := Finset.mem_sdiff.mp hc
    have hE := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy c (diagLo D j + j) with hlt | heq | hgt
    · exact hcA (hdown.2 _ hcD _ hbA le_rfl hlt.le)
    · rw [heq] at hcA
      exact hcA hbA
    · apply hE
      have := hDs.mem (a := diagLo D j) (b := diagLo D j + j) (c := diagLo D j) (d := c)
        (i := diagLo D j) (j := diagLo D j + (j + 1)) hbD hcD le_rfl hgt.le le_rfl le_rfl
        (by omega) (by omega)
      exact this

theorem card_lLoneE (hw : LeftWindow D j0 m) :
    (lLoneE D j0 m).card = numRows D - numRows (D \ leftStrip D j0 m) := by
  have hDs := hw.conn.1
  have hsub : rowSet (D \ leftStrip D j0 m) ⊆ rowSet D :=
    Finset.image_subset_image Finset.sdiff_subset
  have himg : rowSet D \ rowSet (D \ leftStrip D j0 m) =
      (lLoneE D j0 m).image (diagLo D) := by
    ext i
    rw [rows_lost_L hw, Finset.mem_image]
  have hinj : Set.InjOn (diagLo D) (lLoneE D j0 m : Set ℤ) := by
    have key : ∀ j ∈ lLoneE D j0 m, ∀ j' ∈ lLoneE D j0 m, j < j' → diagLo D j = diagLo D j' →
        False := by
      intro j hj j' hj' hlt he
      have hjL := (Finset.mem_filter.mp hj).1
      have hjL' := (Finset.mem_filter.mp hj').1
      have hb := lone_cell_mem_D_L hw hjL
      have hb' := lone_cell_mem_D_L hw hjL'
      apply (Finset.mem_filter.mp hj).2
      have := hDs.mem (a := diagLo D j) (b := diagLo D j + j) (c := diagLo D j')
        (d := diagLo D j' + j') (i := diagLo D j) (j := diagLo D j + (j + 1)) hb hb'
        (by omega) (by omega) le_rfl (by omega) (by omega) (by omega)
      exact this
    intro j hj j' hj' he
    rcases lt_trichotomy j j' with h | h | h
    · exact (key j hj j' hj' h he).elim
    · exact h
    · exact (key j' hj' j hj h he.symm).elim
  have hc := Finset.card_sdiff_of_subset hsub
  rw [himg, Finset.card_image_of_injOn hinj] at hc
  unfold numRows
  have hle : (rowSet (D \ leftStrip D j0 m)).card ≤ (rowSet D).card := Finset.card_le_card hsub
  omega

theorem cols_lost_L (hw : LeftWindow D j0 m) (c : ℤ) :
    c ∈ D.image Prod.snd \ (D \ leftStrip D j0 m).image Prod.snd ↔
      ∃ j ∈ lLoneS D j0 m, diagLo D j + j = c := by
  have hDs := hw.conn.1
  have hdown := (mem_leftRibbons.mp hw.mem).2.2.2
  have hmem : ∀ (X : Diagram) (c : ℤ), c ∈ X.image Prod.snd ↔ ∃ r, (r, c) ∈ X := by
    intro X c
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨a, b⟩, hx, rfl⟩
      exact ⟨a, hx⟩
    · rintro ⟨r, hr⟩
      exact ⟨(r, c), hr, rfl⟩
  rw [Finset.mem_sdiff, hmem, hmem]
  constructor
  · rintro ⟨⟨r, hr⟩, hnot⟩
    have hnot' : ∀ r', (r', c) ∈ D → (r', c) ∈ leftStrip D j0 m := by
      intro r' hr'
      by_contra hA
      exact hnot ⟨r', Finset.mem_sdiff.mpr ⟨hr', hA⟩⟩
    obtain ⟨rm, hℓ, hmax⟩ := exists_max_row ⟨r, hr⟩
    have hA := hnot' rm hℓ
    rw [mem_leftStrip] at hA
    obtain ⟨hA1, hA2, hA3⟩ := hA
    simp only [content] at hA1 hA2 hA3
    set j := c - rm with hj
    have hcell : (rm, c) = (rm, rm + j) := Prod.ext rfl (by omega)
    rw [hcell] at hℓ
    have hjC : j ∈ contents D := mem_contents_iff.mpr ⟨rm, hℓ⟩
    have hlone : diagLo D j = diagHi D j := by
      by_contra hne
      have hle := diagLo_le_diagHi hjC
      have hb' : (rm + 1, rm + 1 + j) ∈ D :=
        (mem_skew_iff hDs).mpr ⟨hjC, by omega, by omega⟩
      have := hDs.mem (a := rm) (b := rm + j) (c := rm + 1) (d := rm + 1 + j) (i := rm + 1)
        (j := rm + j) hℓ hb' (by omega) (by omega) (by omega) (by omega) le_rfl (by omega)
      have := hmax _ (by
        have e : (rm + 1, c) = (rm + 1, rm + j) := Prod.ext rfl (by omega)
        rw [e]; exact this)
      omega
    refine ⟨j, ?_, by omega⟩
    rw [mem_lLoneS hDs, mem_rLone]
    refine ⟨⟨⟨by omega, by omega⟩, hlone⟩, ?_⟩
    rintro ⟨h1', h2', h3'⟩
    have hlo : diagLo D j = rm := by omega
    have := hmax (rm + 1) (by
      have e : (rm + 1, c) = (rm + 1, (rm + 1) + (j - 1)) := Prod.ext rfl (by omega)
      rw [e]
      exact (mem_skew_iff hDs).mpr ⟨h1', by omega, by omega⟩)
    omega
  · rintro ⟨j, hj, rfl⟩
    have hjL : j ∈ rLone D j0 m := (Finset.mem_filter.mp hj).1
    have hbD := lone_cell_mem_D_L hw hjL
    have hbA := lone_cell_mem_leftStrip hjL
    refine ⟨⟨_, hbD⟩, ?_⟩
    rintro ⟨r, hr⟩
    obtain ⟨hrD, hrA⟩ := Finset.mem_sdiff.mp hr
    have hS := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy r (diagLo D j) with hlt | heq | hgt
    · exact hrA (hdown.2 _ hrD _ hbA hlt.le le_rfl)
    · rw [heq] at hrA
      exact hrA hbA
    · apply hS
      have := hDs.mem (a := diagLo D j) (b := diagLo D j + j) (c := r) (d := diagLo D j + j)
        (i := diagLo D j + 1) (j := diagLo D j + j) hbD hrD hgt.le le_rfl (by omega) (by omega)
        le_rfl le_rfl
      have e : (diagLo D j + 1) + (j - 1) = diagLo D j + j := by ring
      rw [e]; exact this

theorem card_lLoneS (hw : LeftWindow D j0 m) :
    (lLoneS D j0 m).card = numCols D - numCols (D \ leftStrip D j0 m) := by
  have hDs := hw.conn.1
  have hsub : (D \ leftStrip D j0 m).image Prod.snd ⊆ D.image Prod.snd :=
    Finset.image_subset_image Finset.sdiff_subset
  have himg : D.image Prod.snd \ (D \ leftStrip D j0 m).image Prod.snd =
      (lLoneS D j0 m).image (fun j => diagLo D j + j) := by
    ext c
    rw [cols_lost_L hw, Finset.mem_image]
  have hinj : Set.InjOn (fun j => diagLo D j + j) (lLoneS D j0 m : Set ℤ) := by
    have key : ∀ j ∈ lLoneS D j0 m, ∀ j' ∈ lLoneS D j0 m, j < j' →
        diagLo D j + j = diagLo D j' + j' → False := by
      intro j hj j' hj' hlt he
      have hjL := (Finset.mem_filter.mp hj).1
      have hjL' := (Finset.mem_filter.mp hj').1
      have hb := lone_cell_mem_D_L hw hjL
      have hb' := lone_cell_mem_D_L hw hjL'
      apply (Finset.mem_filter.mp hj').2
      have := hDs.mem (a := diagLo D j') (b := diagLo D j' + j') (c := diagLo D j)
        (d := diagLo D j + j) (i := diagLo D j' + 1) (j := diagLo D j' + j') hb' hb (by omega)
        (by omega) (by omega) (by omega) le_rfl (by omega)
      have e : (diagLo D j' + 1) + (j' - 1) = diagLo D j' + j' := by ring
      rw [e]; exact this
    intro j hj j' hj' he
    rcases lt_trichotomy j j' with h | h | h
    · exact (key j hj j' hj' h he).elim
    · exact h
    · exact (key j' hj' j hj h he.symm).elim
  have hc := Finset.card_sdiff_of_subset hsub
  rw [himg, Finset.card_image_of_injOn hinj] at hc
  rw [numCols_eq_card_image_snd, numCols_eq_card_image_snd]
  have hle := Finset.card_le_card hsub
  omega

end Rem

end Corner

end Plan

end SkewGluing
