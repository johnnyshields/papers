import SkewGluing.OlsonHarris.Plan.EdgeCase.EsDiff.Coords

/-!
# The pieces of one copy of `E`

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): the decomposition behind thesis
Lemma 5.4.3 (`OlsonHarris2024HopfApplications`) of one copy of `E` in the composite of a legal mark
of case (a).

`EdgeLocal ω` collects the cell-level facts about a single copy `E` that the proof of the
removal of a key ribbon uses: `E` is the disjoint union of the key ribbon and the three pieces
`pieceE` (a translate of `W`, shared with the copy to the east), `pieceS` (a translate of
`\overline W`, shared with the copy to the south) and `pieceSE` (a translate of `\overline O`,
shared with the copy to the southeast); the key ribbon meets no copy at a neighbor; the pieces lie
on pairwise separated contents.  They are proved for a nonempty mark in diagonal coordinates and
for the empty mark directly.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewGluing

namespace Plan

namespace EsDiff

open scoped Classical

open SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- The cell-level facts about one copy `E` of a legal mark of case (a). -/
structure EdgeLocal (ω : MarkedInner) : Prop where
  key_sub : ∀ z ∈ keyRibbon ω, z ∈ ω.E
  pieceE_sub : ∀ z ∈ pieceE ω, z ∈ ω.E
  pieceS_sub : ∀ z ∈ pieceS ω, z ∈ ω.E
  pieceSE_sub : ∀ z ∈ pieceSE ω, z ∈ ω.E
  cover : ∀ z ∈ ω.E, z ∈ keyRibbon ω ∨ z ∈ pieceE ω ∨ z ∈ pieceS ω ∨ z ∈ pieceSE ω
  key_disj : ∀ z ∈ keyRibbon ω, z ∉ pieceE ω ∧ z ∉ pieceS ω ∧ z ∉ pieceSE ω
  key_east : ∀ s : ℤ, 0 ≤ s → ∀ z ∈ keyRibbon ω, z - (ω.v + s • eCell) ∉ ω.E
  key_same : ∀ s : ℤ, 1 ≤ s → ∀ z ∈ keyRibbon ω, z - s • eCell ∉ ω.E
  key_south : ∀ s : ℤ, 1 ≤ s → ∀ z ∈ keyRibbon ω, z - (-ω.v + s • eCell) ∉ ω.E
  pieceE_cover : ∀ z ∈ pieceE ω, z - ω.v ∈ ω.E
  pieceS_cover : ∀ z ∈ pieceS ω, z - (-ω.v + eCell) ∈ ω.E
  pieceSE_cover : ∀ z ∈ pieceSE ω, z - eCell ∈ ω.E
  pieceS_content : ∀ z ∈ pieceS ω, content z ≤ minContent ω.E + ω.width - 1
  pieceSE_content : ∀ z ∈ pieceSE ω,
    minContent ω.E + ω.width + 1 ≤ content z ∧ content z ≤ minContent ω.E + ω.period - 2
  pieceE_content : ∀ z ∈ pieceE ω, minContent ω.E + ω.period ≤ content z

theorem cell_sub_smul_eCell (ω : MarkedInner) (a r s : ℤ) :
    ω.cell a r - s • eCell = ω.cell a (r - s) := by
  unfold MarkedInner.cell eCell
  ext
  · simp
  · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]; omega

/-- All facts on the first and last rows of the diagonals that the cell-level proofs use. -/
theorem facts_at (h : ω.IsLegalNonempty) (hc : ω.case = .a) (a : ℤ) :
    (0 ≤ a → a ≤ ω.widthZ - 1 →
      ω.lo a + ω.rowShift - 1 ≤ ω.lo (a + ω.period) ∧
        ω.lo (a + ω.period) ≤ ω.lo a + ω.rowShift ∧
        ω.hi a + ω.rowShift - 1 ≤ ω.hi (a + ω.period) ∧
        ω.hi (a + ω.period) ≤ ω.hi a + ω.rowShift ∧
        ω.lo a + ω.rowShift ≤ ω.hi (a + ω.period)) ∧
    (ω.period ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      ω.lo (a - ω.period) + ω.rowShift - 1 ≤ ω.lo a ∧
        ω.lo a ≤ ω.lo (a - ω.period) + ω.rowShift ∧
        ω.hi (a - ω.period) + ω.rowShift - 1 ≤ ω.hi a ∧
        ω.hi a ≤ ω.hi (a - ω.period) + ω.rowShift) ∧
    (0 ≤ a → a ≤ ω.period + ω.widthZ - 1 → ω.lo a ≤ ω.hi a) ∧
    (a = ω.widthZ → ω.lo a = ω.hi a) ∧ (a = ω.period - 1 → ω.lo a = ω.hi a) := by
  refine ⟨fun h0 h1 => ?_, fun h0 h1 => bounds_up h hc h0 h1, fun h0 h1 => h.lo_le_hi h0 h1,
    fun e => e ▸ h.lo_w_eq_hi_w, fun e => by rw [e]; exact h.lo_pred_period_eq_hi⟩
  have := bounds_a h hc h0 h1
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, lo_le_hi_upper h hc h0 h1⟩

theorem edgeLocal_nonempty (h : ω.IsLegalNonempty) (hc : ω.case = .a) : EdgeLocal ω := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hc0 : ∀ a r : ℤ, content (ω.cell a r) = minContent ω.E + a := fun a r =>
    MarkedInner.content_cell ω a r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (mem_keyRibbon.mp hz).1.1
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_pieceE_cell h hc] at hz
    rw [h.mem_E]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_pieceS_cell h hc] at hz
    rw [h.mem_E]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_pieceSE_cell h] at hz
    rw [h.mem_E]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [h.mem_E] at hz
    rw [mem_keyRibbon_cell h hc, mem_pieceE_cell h hc, mem_pieceS_cell h hc,
      mem_pieceSE_cell h]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_keyRibbon_cell h hc] at hz
    rw [mem_pieceE_cell h hc, mem_pieceS_cell h hc, mem_pieceSE_cell h]
    omega
  · intro s hs z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_keyRibbon_cell h hc] at hz
    rw [sub_add_eq_sub_sub, cell_sub_v', cell_sub_smul_eCell, h.mem_E]
    omega
  · intro s hs z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_keyRibbon_cell h hc] at hz
    rw [cell_sub_smul_eCell, h.mem_E]
    omega
  · intro s hs z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    have := facts_at h hc (a + ω.period)
    rw [mem_keyRibbon_cell h hc] at hz
    rw [sub_add_eq_sub_sub, sub_neg_eq_add,
      show ω.cell a r + ω.v = _ from MarkedInner.cell_add_v ω a r,
      cell_sub_smul_eCell, h.mem_E]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_pieceE_cell h hc] at hz
    rw [cell_sub_v', h.mem_E]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    have := facts_at h hc (a + ω.period)
    rw [mem_pieceS_cell h hc] at hz
    rw [sub_add_eq_sub_sub, sub_neg_eq_add,
      show ω.cell a r + ω.v = _ from MarkedInner.cell_add_v ω a r,
      cell_sub_eCell, h.mem_E]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_pieceSE_cell h] at hz
    rw [cell_sub_eCell, h.mem_E]
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    rw [mem_pieceS_cell h hc] at hz
    rw [hc0]
    have : (ω.width : ℤ) = ω.widthZ := rfl
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    have := facts_at h hc a
    rw [mem_pieceSE_cell h] at hz
    rw [hc0]
    have : (ω.width : ℤ) = ω.widthZ := rfl
    omega
  · intro z hz
    obtain ⟨a, r, rfl⟩ := ω.exists_cell z
    rw [mem_pieceE_cell h hc] at hz
    rw [hc0]
    omega

end EsDiff

end Plan

end SkewGluing
