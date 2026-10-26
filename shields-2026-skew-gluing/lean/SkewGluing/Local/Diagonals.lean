import SkewGluing.Composition

/-!
# Diagonal data of a legal nonempty mark

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local`).

For a legal marked inner `ω` with a nonempty mark, this file expresses the diagrams `E`, `W₋`,
`W₊` and the middle through the row intervals `[lo a, hi a]` of the diagonals of `E` at the
relative content `a = c - c₀`, where `c₀` is the least content of `E`.  The copy `W₋` is the full
intersection, so on a marked diagonal `a < w` it consists of the rows `r` with `r ∈ E_a` and
`r + p ∈ E_{a+q}`, where `v = (p, p + q)`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

/-- A legal mark with a nonempty copy. -/
def IsLegalNonempty (ω : MarkedInner) : Prop := ω.IsLegal ∧ ω.W.Nonempty

/-- The width as an integer. -/
def widthZ (ω : MarkedInner) : ℤ := (ω.width : ℤ)

/-- The row displacement `p`, so that `v = (p, p + q)`. -/
def rowShift (ω : MarkedInner) : ℤ := ω.v.1

/-- The first row `ℓ_a` of the diagonal of `E` at the relative content `a`. -/
def lo (ω : MarkedInner) (a : ℤ) : ℤ := diagLo ω.E (minContent ω.E + a)

/-- The last row `h_a` of the diagonal of `E` at the relative content `a`. -/
def hi (ω : MarkedInner) (a : ℤ) : ℤ := diagHi ω.E (minContent ω.E + a)

/-- The cell in row `r` on the diagonal of relative content `a`. -/
def cell (ω : MarkedInner) (a r : ℤ) : ℤ × ℤ := (r, r + (minContent ω.E + a))

theorem period_eq (ω : MarkedInner) : ω.period = ω.v.2 - ω.v.1 := rfl

theorem v_eq (ω : MarkedInner) : ω.v = (ω.rowShift, ω.rowShift + ω.period) := by
  ext
  · rfl
  · simp [rowShift, period_eq]

theorem cell_add_v (ω : MarkedInner) (a r : ℤ) :
    ω.cell a r + ω.v = ω.cell (a + ω.period) (r + ω.rowShift) := by
  have := period_eq ω
  unfold cell rowShift
  ext
  · simp
  · simp only [Prod.snd_add]; omega

theorem cell_sub_v (ω : MarkedInner) (a r : ℤ) :
    ω.cell (a + ω.period) r - ω.v = ω.cell a (r - ω.rowShift) := by
  have := period_eq ω
  unfold cell rowShift
  ext
  · simp
  · simp only [Prod.snd_sub]; omega

theorem cell_add_e (ω : MarkedInner) (a r : ℤ) :
    ω.cell a r + eCell = ω.cell a (r + 1) := by
  unfold cell eCell
  ext
  · simp
  · simp only [Prod.snd_add]; omega

theorem cell_inj (ω : MarkedInner) {a r a' r' : ℤ} (h : ω.cell a r = ω.cell a' r') :
    a = a' ∧ r = r' := by
  unfold cell at h
  simp only [Prod.mk.injEq] at h
  omega

theorem content_cell (ω : MarkedInner) (a r : ℤ) : content (ω.cell a r) = minContent ω.E + a := by
  simp [cell, content]

theorem exists_cell (ω : MarkedInner) (x : ℤ × ℤ) :
    ∃ a r, x = ω.cell a r := by
  refine ⟨content x - minContent ω.E, x.1, ?_⟩
  unfold cell content
  ext
  · simp
  · simp

variable {ω : MarkedInner}

theorem IsLegalNonempty.nonemptyMark (h : ω.IsLegalNonempty) : ω.IsNonemptyMark := by
  obtain ⟨⟨⟨_, hm⟩, -⟩, hW⟩ := h
  rcases hm with hm | hm
  · exact absurd hm.1 hW.ne_empty
  · exact hm

theorem IsLegalNonempty.isConnectedSkew_E (h : ω.IsLegalNonempty) : IsConnectedSkew ω.E :=
  h.1.1.1

theorem IsLegalNonempty.shape (h : ω.IsLegalNonempty) : HasDiagonalShape ω.E :=
  isConnectedSkew_iff_diagonal.mp h.isConnectedSkew_E

theorem IsLegalNonempty.span_eq (h : ω.IsLegalNonempty) :
    (span ω.E : ℤ) = ω.period + ω.widthZ := h.1.1.span_eq

theorem IsLegalNonempty.width_pos (h : ω.IsLegalNonempty) : 1 ≤ ω.widthZ := by
  have hn := h.nonemptyMark
  have hne : (contents ω.W).Nonempty := hn.1.image _
  have : 0 < (contents ω.W).card := Finset.card_pos.mpr hne
  have h2 : ω.width = (contents ω.W).card := rfl
  unfold widthZ
  omega

theorem IsLegalNonempty.width_lt_period (h : ω.IsLegalNonempty) : ω.widthZ < ω.period :=
  h.1.2.2.1.2

theorem IsLegalNonempty.contents_E (h : ω.IsLegalNonempty) :
    contents ω.E = Finset.Icc (minContent ω.E) (minContent ω.E + ω.period + ω.widthZ - 1) :=
  h.1.1.contents_eq

theorem IsLegalNonempty.mem_E (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ ω.E ↔
      0 ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a := by
  have hs := h.shape
  have := hs.mem_iff (k := minContent ω.E + a) (i := r)
  rw [cell, show r + (minContent ω.E + a) = r + (minContent ω.E + a) from rfl, this,
    h.contents_E, Finset.mem_Icc]
  unfold lo hi
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4⟩


theorem IsLegalNonempty.bit_lo (h : ω.IsLegalNonempty) {a : ℤ} (h1 : 1 ≤ a)
    (h2 : a ≤ ω.period + ω.widthZ - 1) :
    ω.lo (a - 1) - ω.lo a = 0 ∨ ω.lo (a - 1) - ω.lo a = 1 := by
  have hs := h.shape
  have hc := h.contents_E
  have m1 : minContent ω.E + a ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have m2 : minContent ω.E + a - 1 ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have := (hs.2.2.2.1 _ m1 m2).1
  simp only [bitA, Finset.mem_insert, Finset.mem_singleton] at this
  have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
  simp only [lo, e]
  omega

theorem IsLegalNonempty.bit_hi (h : ω.IsLegalNonempty) {a : ℤ} (h1 : 1 ≤ a)
    (h2 : a ≤ ω.period + ω.widthZ - 1) :
    ω.hi (a - 1) - ω.hi a = 0 ∨ ω.hi (a - 1) - ω.hi a = 1 := by
  have hs := h.shape
  have hc := h.contents_E
  have m1 : minContent ω.E + a ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have m2 : minContent ω.E + a - 1 ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have := (hs.2.2.2.1 _ m1 m2).2
  simp only [bitB, Finset.mem_insert, Finset.mem_singleton] at this
  have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
  simp only [hi, e]
  omega

theorem IsLegalNonempty.lo_le_hi (h : ω.IsLegalNonempty) {a : ℤ} (h1 : 0 ≤ a)
    (h2 : a ≤ ω.period + ω.widthZ - 1) : ω.lo a ≤ ω.hi a := by
  have hc := h.contents_E
  have m1 : minContent ω.E + a ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  exact diagLo_le_diagHi m1

theorem IsLegalNonempty.lo_zero (h : ω.IsLegalNonempty) : ω.lo 0 = ω.hi 0 := by
  have hs := h.shape
  have hc := h.contents_E
  have m1 : minContent ω.E + 0 ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; have := h.width_pos; have := h.width_lt_period; omega
  have := hs.2.2.2.2 _ m1 (Or.inl (by
    rw [hc, Finset.mem_Icc]; omega))
  simpa [lo, hi] using this

theorem IsLegalNonempty.lo_last (h : ω.IsLegalNonempty) :
    ω.lo (ω.period + ω.widthZ - 1) = ω.hi (ω.period + ω.widthZ - 1) := by
  have hs := h.shape
  have hc := h.contents_E
  have m1 : minContent ω.E + (ω.period + ω.widthZ - 1) ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; have := h.width_pos; have := h.width_lt_period; omega
  have := hs.2.2.2.2 _ m1 (Or.inr (by
    rw [hc, Finset.mem_Icc]; omega))
  simpa [lo, hi] using this

/-- The lower copy is the set of cells of `E` whose translate by `v` stays in `E`: on the
relative content `a < w`, the rows `r` of `E_a` with `r + p ∈ E_{a+q}`. -/
theorem IsLegalNonempty.mem_W (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ ω.W ↔ 0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a ∧
      ω.lo (a + ω.period) ≤ r + ω.rowShift ∧ r + ω.rowShift ≤ ω.hi (a + ω.period) := by
  rw [h.1.W_eq_fullIntersection h.2]
  simp only [fullIntersection, Finset.mem_filter]
  rw [cell_add_v, h.mem_E, h.mem_E]
  have := h.width_pos
  have := h.width_lt_period
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩
    exact ⟨h1, by omega, h3, h4, h7, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨h1, by omega, h3, h4⟩, by omega, by omega, h5, h6⟩

theorem IsLegalNonempty.mem_upper (_h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell (a + ω.period) r ∈ ω.upper ↔ ω.cell a (r - ω.rowShift) ∈ ω.W := by
  unfold upper
  rw [mem_translate, cell_sub_v]

theorem IsLegalNonempty.mem_middle (_h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ ω.middle ↔
      ω.cell a r ∈ ω.E ∧ ω.cell a r ∉ ω.W ∧ ω.cell a r ∉ ω.upper := by
  unfold middle
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or]

theorem IsLegalNonempty.minContent_W (h : ω.IsLegalNonempty) :
    minContent ω.W = minContent ω.E := by
  have hn := h.nonemptyMark
  have hb := hn.content_bounds h.isConnectedSkew_E
  have hne := hn.1
  have hsw := hn.2.2.2.2.1
  have hEne : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  apply le_antisymm
  · have : content (sw ω.E) ∈ contents ω.W := content_mem_contents hsw
    rw [content_sw hEne] at this
    exact minContent_le this
  · obtain ⟨i, hi⟩ := mem_contents_iff.mp (minContent_mem hne)
    have := (hb.1 _ hi).1
    simpa [content] using this

theorem IsLegalNonempty.exists_W (h : ω.IsLegalNonempty) {a : ℤ} (h1 : 0 ≤ a)
    (h2 : a ≤ ω.widthZ - 1) : ∃ r, ω.cell a r ∈ ω.W := by
  have hn := h.nonemptyMark
  have hWs := hn.2.1
  have hWd := isConnectedSkew_iff_diagonal.mp hWs
  have hmin := h.minContent_W
  have hspan := span_eq_of_isConnectedSkew hWs
  have hk : minContent ω.E + a ∈ contents ω.W := by
    rw [hWd.mem_contents_iff]
    have : (span ω.W : ℤ) = ω.widthZ := rfl
    constructor <;> omega
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
  exact ⟨i, by simpa [cell] using hi⟩

theorem IsLegalNonempty.sw_cell (h : ω.IsLegalNonempty) : ω.cell 0 (ω.lo 0) ∈ ω.W := by
  have hn := h.nonemptyMark
  have hsw := hn.2.2.2.2.1
  have hEne : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  convert hsw using 1
  unfold cell sw lo
  have : minContent ω.E + 0 = minContent ω.E := by ring
  rw [this]

theorem IsLegalNonempty.maxContent_E (h : ω.IsLegalNonempty) :
    maxContent ω.E = minContent ω.E + ω.period + ω.widthZ - 1 := by
  have := span_eq_of_isConnectedSkew h.isConnectedSkew_E
  have := h.span_eq
  omega

theorem IsLegalNonempty.ne_cell (h : ω.IsLegalNonempty) :
    ω.cell (ω.widthZ - 1 + ω.period) (ω.lo (ω.period + ω.widthZ - 1)) ∈ ω.upper := by
  have hn := h.nonemptyMark
  have hneU := hn.2.2.2.2.2.1
  convert hneU using 1
  unfold cell ne lo
  have := h.maxContent_E
  have e : minContent ω.E + (ω.widthZ - 1 + ω.period) = maxContent ω.E := by omega
  have e2 : minContent ω.E + (ω.period + ω.widthZ - 1) = maxContent ω.E := by omega
  rw [e, e2]

theorem IsLegalNonempty.ne_cell_W (h : ω.IsLegalNonempty) :
    ω.cell (ω.widthZ - 1) (ω.lo (ω.period + ω.widthZ - 1) - ω.rowShift) ∈ ω.W := by
  have := h.mem_upper (a := ω.widthZ - 1) (r := ω.lo (ω.period + ω.widthZ - 1))
  exact this.mp h.ne_cell

theorem IsLegalNonempty.bit_lo' (h : ω.IsLegalNonempty) {a b : ℤ} (hb : b = a + 1) (h1 : 0 ≤ a)
    (h2 : b ≤ ω.period + ω.widthZ - 1) : ω.lo a - ω.lo b = 0 ∨ ω.lo a - ω.lo b = 1 := by
  have := h.bit_lo (a := b) (by omega) h2
  have e : b - 1 = a := by omega
  rwa [e] at this

theorem IsLegalNonempty.bit_hi' (h : ω.IsLegalNonempty) {a b : ℤ} (hb : b = a + 1) (h1 : 0 ≤ a)
    (h2 : b ≤ ω.period + ω.widthZ - 1) : ω.hi a - ω.hi b = 0 ∨ ω.hi a - ω.hi b = 1 := by
  have := h.bit_hi (a := b) (by omega) h2
  have e : b - 1 = a := by omega
  rwa [e] at this

theorem IsLegalNonempty.W_row (h : ω.IsLegalNonempty) {a : ℤ} (h1 : 0 ≤ a)
    (h2 : a ≤ ω.widthZ - 1) : ∃ r, ω.lo a ≤ r ∧ r ≤ ω.hi a ∧ ω.lo (a + ω.period) ≤ r + ω.rowShift ∧
      r + ω.rowShift ≤ ω.hi (a + ω.period) := by
  obtain ⟨r, hr⟩ := h.exists_W h1 h2
  rw [h.mem_W] at hr
  exact ⟨r, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩

/-- Condition IV at the lower copy: a cell `x` of the middle whose diagonal successor `x + e` is
also in the middle is not adjacent to a cell of the hatted mark `Ŵ₋` (both `x ∈ E`, `x + e ∈ W₋`
and `x ∈ W₋`, `x + e ∈ E` are in `Ŵ₋`). -/
theorem IsLegalNonempty.iv_local (h : ω.IsLegalNonempty) {x y : ℤ × ℤ} (hx : x ∈ ω.middle)
    (hx' : x + eCell ∈ ω.middle) (hadj : CellAdj x y)
    (hy : (y ∈ ω.E ∧ y + eCell ∈ ω.W) ∨ (y ∈ ω.W ∧ y + eCell ∈ ω.E)) : False := by
  have hIV := h.1.2.2.2.2
  refine hIV 0 0 x ?_ y ?_ hadj
  · simp only [zero_smul, translate_zero, hatMiddle, Set.mem_ofPred_eq]
    exact ⟨hx, hx'⟩
  · simp only [zero_smul, translate_zero, hatMark, Set.mem_union, Set.mem_ofPred_eq]
    have hE0 : ∀ z, z ∈ ω.E → z ∈ ω.periodicUnion := fun z hz => ⟨0, by simpa using hz⟩
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hE0 _ h1, h2⟩
    · exact Or.inr ⟨h1, hE0 _ h2⟩

theorem IsLegalNonempty.not_upper_of_lt (h : ω.IsLegalNonempty) {a r : ℤ} (ha : a < ω.period) :
    ω.cell a r ∉ ω.upper := by
  intro hu
  have e : a = (a - ω.period) + ω.period := by ring
  rw [e, h.mem_upper, h.mem_W] at hu
  omega

theorem IsLegalNonempty.mem_middle_lt (h : ω.IsLegalNonempty) {a r : ℤ} (ha : a < ω.period) :
    ω.cell a r ∈ ω.middle ↔ ω.cell a r ∈ ω.E ∧ ω.cell a r ∉ ω.W := by
  rw [h.mem_middle]
  simp [h.not_upper_of_lt ha]

theorem IsLegalNonempty.iv_west (h : ω.IsLegalNonempty) {j k r : ℤ} (hjk : k = j + 1)
    (hx : ω.cell k r ∈ ω.middle) (hx' : ω.cell k (r + 1) ∈ ω.middle)
    (hy : (ω.cell j r ∈ ω.E ∧ ω.cell j (r + 1) ∈ ω.W) ∨
      (ω.cell j r ∈ ω.W ∧ ω.cell j (r + 1) ∈ ω.E)) : False := by
  subst hjk
  refine h.iv_local hx (by rwa [cell_add_e]) (y := ω.cell j r) ?_ (by rwa [cell_add_e])
  rw [cellAdj_iff]
  left
  unfold cell
  simp only [true_and]
  omega

theorem IsLegalNonempty.iv_south (h : ω.IsLegalNonempty) {j k r : ℤ} (hjk : k = j + 1)
    (hx : ω.cell k r ∈ ω.middle) (hx' : ω.cell k (r + 1) ∈ ω.middle)
    (hy : (ω.cell j (r + 1) ∈ ω.E ∧ ω.cell j (r + 2) ∈ ω.W) ∨
      (ω.cell j (r + 1) ∈ ω.W ∧ ω.cell j (r + 2) ∈ ω.E)) : False := by
  subst hjk
  refine h.iv_local hx (by rwa [cell_add_e]) (y := ω.cell j (r + 1)) ?_ ?_
  · rw [cellAdj_iff]
    right
    unfold cell
    refine ⟨?_, Or.inr ?_⟩
    · simp only; omega
    · simp only
  · rw [cell_add_e]
    have e : r + 1 + 1 = r + 2 := by ring
    rwa [e]

/-- The middle on a lower diagonal `a < q`, in terms of row bounds. -/
theorem IsLegalNonempty.mem_middle_lower (h : ω.IsLegalNonempty) {a r : ℤ} (ha : a < ω.period) :
    ω.cell a r ∈ ω.middle ↔
      (0 ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a) ∧
      ¬ (0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a ∧
        ω.lo (a + ω.period) ≤ r + ω.rowShift ∧ r + ω.rowShift ≤ ω.hi (a + ω.period)) := by
  rw [h.mem_middle_lt ha, h.mem_E, h.mem_W]

end MarkedInner

end SkewGluing
