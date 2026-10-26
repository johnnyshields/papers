import SkewGluing.OlsonHarris.Plan.EdgeCase.EsDiff.Defs

/-!
# Diagonal coordinates of a legal mark of case (a)

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): the cell-level description of `E`, `W₋`,
`W₊`, the middle and the key ribbon used in thesis Lemma 5.4.3 (`OlsonHarris2024HopfApplications`).

A cell is written `ω.cell a r`, with `a` the content relative to the least content of `E` and `r`
the row.  For a legal nonempty mark of case (a), on a marked diagonal `0 ≤ a < w` the first rows
of `E` at `a + q` and at `a` differ by `p` or `p - 1`, and so do the last rows
(`bounds_a`); the key ribbon contains the first cell of every diagonal `a` with `t ≤ a < q + t`,
where `t` is the number of diagonals carrying an upper tail (`mem_keyRibbon_cell`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewGluing

namespace Plan

namespace EsDiff

open scoped Classical

open SkewGluing.MarkedInner

variable {ω : MarkedInner}

theorem cell_sub_eCell (ω : MarkedInner) (a r : ℤ) : ω.cell a r - eCell = ω.cell a (r - 1) := by
  unfold MarkedInner.cell eCell
  ext
  · simp
  · simp only [Prod.snd_sub]; omega

theorem cell_sub_v' (ω : MarkedInner) (a r : ℤ) :
    ω.cell a r - ω.v = ω.cell (a - ω.period) (r - ω.rowShift) := by
  have := MarkedInner.cell_sub_v ω (a - ω.period) r
  rw [sub_add_cancel] at this
  exact this

/-- On a marked diagonal, the rows of `E` at `a + q`, shifted back by `p`, are those of `E` at
`a` extended by at most one cell at the top and shortened by at most one cell at the bottom. -/
theorem bounds_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    ω.lo a + ω.rowShift - 1 ≤ ω.lo (a + ω.period) ∧ ω.lo (a + ω.period) ≤ ω.lo a + ω.rowShift ∧
      ω.hi a + ω.rowShift - 1 ≤ ω.hi (a + ω.period) ∧
      ω.hi (a + ω.period) ≤ ω.hi a + ω.rowShift := by
  have s1 := h.sides_a hc h0 h1
  have s2 := h.thin_upper h0 h1
  have s3 := h.thin_lower a h0 h1
  unfold MarkedInner.dLo MarkedInner.dHi at s1 s2 s3
  omega

theorem mem_E_lower (h : ω.IsLegalNonempty) {a r : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.cell a r ∈ ω.E ↔ ω.lo a ≤ r ∧ r ≤ ω.hi a := by
  have := h.width_lt_period
  rw [h.mem_E]
  omega

theorem mem_E_upper (h : ω.IsLegalNonempty) {a r : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    ω.cell (a + ω.period) r ∈ ω.E ↔ ω.lo (a + ω.period) ≤ r ∧ r ≤ ω.hi (a + ω.period) := by
  have := h.width_lt_period
  rw [h.mem_E]
  omega

theorem mem_W_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a r : ℤ}
    (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    ω.cell a r ∈ ω.W ↔ ω.lo a ≤ r ∧ r ≤ ω.hi (a + ω.period) - ω.rowShift := by
  have b := bounds_a h hc h0 h1
  rw [h.mem_W]
  omega

theorem mem_upper_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a r : ℤ}
    (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    ω.cell (a + ω.period) r ∈ ω.upper ↔
      ω.lo a + ω.rowShift ≤ r ∧ r ≤ ω.hi (a + ω.period) := by
  rw [h.mem_upper, mem_W_a h hc h0 h1]
  omega

/-- A marked diagonal carries a cell of `W₋`. -/
theorem lo_le_hi_upper (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a : ℤ}
    (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) : ω.lo a + ω.rowShift ≤ ω.hi (a + ω.period) := by
  obtain ⟨r, hr⟩ := h.exists_W h0 h1
  rw [mem_W_a h hc h0 h1] at hr
  omega


theorem bounds_up (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a : ℤ} (h0 : ω.period ≤ a)
    (h1 : a ≤ ω.period + ω.widthZ - 1) :
    ω.lo (a - ω.period) + ω.rowShift - 1 ≤ ω.lo a ∧ ω.lo a ≤ ω.lo (a - ω.period) + ω.rowShift ∧
      ω.hi (a - ω.period) + ω.rowShift - 1 ≤ ω.hi a ∧
      ω.hi a ≤ ω.hi (a - ω.period) + ω.rowShift := by
  have := bounds_a h hc (a := a - ω.period) (by omega) (by omega)
  rw [sub_add_cancel] at this
  exact this

theorem t_le_iff (h : ω.IsLegalNonempty) (hc : ω.case = .a) {s t : ℤ} (hp : ω.IsPhases s t)
    {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    t ≤ a ↔ ω.lo (a + ω.period) = ω.lo a + ω.rowShift := by
  obtain ⟨-, -, -, -, -, hT⟩ := hp
  have h2 := hT a h0 h1
  have b := bounds_a h hc h0 h1
  have s1 := h.sides_a hc h0 h1
  have s2 := h.thin_upper h0 h1
  unfold MarkedInner.TailUpper MarkedInner.dLo MarkedInner.dHi at h2 s1 s2
  omega

theorem maxContent_middle (h : ω.IsLegalNonempty) {s t : ℤ} (hp : ω.IsPhases s t) :
    maxContent ω.middle = minContent ω.E + ω.period + t - 1 := by
  have hc := h.contents_middle hp
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := hp
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmem : minContent ω.E + ω.period + t - 1 ∈ contents ω.middle := by
    rw [hc, Finset.mem_Icc]; omega
  refine maxContent_eq_of hmem fun k hk => ?_
  rw [hc, Finset.mem_Icc] at hk
  omega

/-- The key ribbon, cell by cell: the first cell of the diagonal `a`, for `t ≤ a < q + t`.
On the lower marked diagonals the condition `t ≤ a` is `ℓ_{a+q} = ℓ_a + p`, on the upper ones the
condition `a < q + t` is `ℓ_a < ℓ_{a-q} + p`. -/
theorem mem_keyRibbon_cell (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a r : ℤ} :
    ω.cell a r ∈ keyRibbon ω ↔
      0 ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧ r = ω.lo a ∧
        (a ≤ ω.widthZ - 1 → ω.lo (a + ω.period) = ω.lo a + ω.rowShift) ∧
        (ω.period ≤ a → ω.lo a < ω.lo (a - ω.period) + ω.rowShift) := by
  obtain ⟨s, t, hp⟩ := h.exists_phases
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmax := maxContent_middle h hp
  have f1 : 0 ≤ a → a ≤ ω.widthZ - 1 → (t ≤ a ↔ ω.lo (a + ω.period) = ω.lo a + ω.rowShift) :=
    fun h0 h1 => t_le_iff h hc hp h0 h1
  have f2 : ω.period ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      (t ≤ a - ω.period ↔ ω.lo a = ω.lo (a - ω.period) + ω.rowShift) := by
    intro h0 h1
    have := t_le_iff h hc hp (a := a - ω.period) (by omega) (by omega)
    rwa [sub_add_cancel] at this
  have f3 : 0 ≤ a → a ≤ ω.period + ω.widthZ - 1 → ω.lo a ≤ ω.hi a :=
    fun h0 h1 => h.lo_le_hi h0 h1
  have f4 : ω.period ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      ω.lo (a - ω.period) + ω.rowShift - 1 ≤ ω.lo a ∧ ω.lo a ≤ ω.lo (a - ω.period) + ω.rowShift :=
    fun h0 h1 => ⟨(bounds_up h hc h0 h1).1, (bounds_up h hc h0 h1).2.1⟩
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := hp
  rw [mem_keyRibbon, cell_sub_eCell, h.mem_E, h.mem_E, hmax]
  simp only [MarkedInner.content_cell]
  omega

theorem mem_pieceE_cell (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a r : ℤ} :
    ω.cell a r ∈ pieceE ω ↔ ω.period ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧
      ω.lo (a - ω.period) + ω.rowShift ≤ r ∧ r ≤ ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have f4 : ω.period ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      ω.lo (a - ω.period) + ω.rowShift - 1 ≤ ω.lo a ∧ ω.lo a ≤ ω.lo (a - ω.period) + ω.rowShift ∧
      ω.hi (a - ω.period) + ω.rowShift - 1 ≤ ω.hi a ∧ ω.hi a ≤ ω.hi (a - ω.period) + ω.rowShift :=
    fun h0 h1 => bounds_up h hc h0 h1
  rw [mem_pieceE, cell_sub_v', h.mem_W]
  simp only [sub_add_cancel]
  omega

theorem mem_pieceS_cell (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a r : ℤ} :
    ω.cell a r ∈ pieceS ω ↔ 0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧
      ω.lo (a + ω.period) - ω.rowShift + 1 ≤ r ∧ r ≤ ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have f4 : 0 ≤ a → a ≤ ω.widthZ - 1 →
      ω.lo a + ω.rowShift - 1 ≤ ω.lo (a + ω.period) ∧ ω.lo (a + ω.period) ≤ ω.lo a + ω.rowShift ∧
      ω.hi a + ω.rowShift - 1 ≤ ω.hi (a + ω.period) ∧
      ω.hi (a + ω.period) ≤ ω.hi a + ω.rowShift :=
    fun h0 h1 => bounds_a h hc h0 h1
  have f5 : 0 ≤ a → a ≤ ω.widthZ - 1 → ω.lo a + ω.rowShift ≤ ω.hi (a + ω.period) :=
    fun h0 h1 => lo_le_hi_upper h hc h0 h1
  rw [mem_pieceS, Plan.MarkedInner.hatMarkFin_eq_hatMarkWindow h.1.1 h.1.2.2.1,
    Plan.MarkedInner.mem_hatMarkWindow, Plan.MarkedInner.mem_windowCells,
    Plan.MarkedInner.mem_windowCells, cell_sub_eCell, MarkedInner.cell_add_e]
  simp only [MarkedInner.cell_add_v, h.mem_E, h.mem_W, show r - 1 + 1 = r by ring]
  omega

theorem mem_pieceSE_cell (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ pieceSE ω ↔ ω.widthZ ≤ a ∧ a ≤ ω.period - 1 ∧ ω.lo a + 1 ≤ r ∧ r ≤ ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [mem_pieceSE, Plan.MarkedInner.mem_hatMiddleFin, cell_sub_eCell, MarkedInner.cell_add_e,
    show r - 1 + 1 = r by ring]
  by_cases hmid : ω.widthZ ≤ a ∧ a ≤ ω.period - 1
  · rw [h.mem_middle_private hmid.1 (by omega), h.mem_middle_private hmid.1 (by omega)]
    omega
  · have hthin : ω.cell a (r - 1) ∈ ω.middle → ω.cell a r ∈ ω.middle → False := by
      intro hx hy
      have := h.middle_thin hx hy (by simp [MarkedInner.content_cell]) (by
        simp only [MarkedInner.content_cell]; omega)
      simp only [MarkedInner.cell, Prod.mk.injEq] at this
      omega
    constructor
    · rintro ⟨hx, hy⟩
      exact (hthin hx hy).elim
    · intro hh
      omega

end EsDiff

end Plan

end SkewGluing
