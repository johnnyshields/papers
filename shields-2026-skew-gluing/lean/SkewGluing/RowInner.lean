import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SkewGluing.CellSchur
import SkewGluing.Composition
import SkewGluing.RowTransport

/-!
# Row inners on cells

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
`lem:gluing-row-action` and `lem:gluing-row-transport`, on cell diagrams.

* `rowMark s`: the case-(a) mark `ω_{q,w}` on the row `(q + w)`, `s : RowShift`;
  `rowMark_isLegal`: it is legal.
* `cellProfile_rowMark_compose` (`eq:gluing-row-action`): for every connected outer `D`, the
  composite `ω_{q,w}.compose D` is connected and its profile is `𝓛_{q,w}` of the profile of `D`,
  `(r; g) ∘_{ω_{q,w}} E = (q r + w; q g + w)`.
* `MarkedInner.IsLegal.exists_isRowMark`: a legal mark on a row of at least two cells is
  `ω_{q,w}`; `MarkedInner.IsRowMark.cellProfile_compose`, `.hasResidue`, `.outer_unique`,
  `.beta_lists`: the chart of a row inner has this form, every row length and every overlap minus
  one of the composite is `≡ w` modulo `q`, the outer is unique and has the divided beta lists.
* `exists_rowMark_compose_of_hasResidue`: conversely, a connected diagram with at least two rows
  and all row lengths and overlaps minus one `≡ w` modulo `q` is such a composite.
* `liftAny_bijOn_schurClass`, `cellSchur_liftCells_eq`, `exists_translate_of_liftCells`,
  `exists_liftCells_of_cellSchur_eq`, `liftCells_rotate`, `jtNegativePositions_liftCells`:
  `lem:gluing-row-transport` on cells.  The row invariants are supplied by
  `reinerRowInvariants`, so these statements are unconditional.

Sorry-free.
-/

namespace SkewGluing

/-! ### Rows of cells -/

/-- The row of cells `(0, j)`, `s ≤ j < e`. -/
def rowCells (s e : ℤ) : Diagram := (Finset.Ico s e).image fun j => ((0 : ℤ), j)

theorem mem_rowCells {s e a b : ℤ} : (a, b) ∈ rowCells s e ↔ a = 0 ∧ s ≤ b ∧ b < e := by
  simp only [rowCells, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨rfl, hj⟩
  · rintro ⟨rfl, hb⟩; exact ⟨b, hb, rfl, rfl⟩

theorem contents_rowCells (s e : ℤ) : contents (rowCells s e) = Finset.Ico s e := by
  ext k
  rw [mem_contents_iff, Finset.mem_Ico]
  simp only [mem_rowCells]
  constructor
  · rintro ⟨i, rfl, h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨0, rfl, by omega, by omega⟩

theorem span_rowCells (s e : ℤ) : span (rowCells s e) = (e - s).toNat := by
  unfold span
  rw [contents_rowCells, Int.card_Ico]

theorem rowCells_nonempty {s e : ℤ} (h : s < e) : (rowCells s e).Nonempty :=
  ⟨(0, s), mem_rowCells.mpr ⟨rfl, le_refl _, h⟩⟩

theorem minContent_rowCells {s e : ℤ} (h : s < e) : minContent (rowCells s e) = s := by
  apply minContent_eq_of
  · rw [contents_rowCells]; exact Finset.mem_Ico.mpr ⟨le_refl _, h⟩
  · intro k hk
    rw [contents_rowCells, Finset.mem_Ico] at hk
    exact hk.1

theorem maxContent_rowCells {s e : ℤ} (h : s < e) : maxContent (rowCells s e) = e - 1 := by
  apply maxContent_eq_of
  · rw [contents_rowCells]; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk
    rw [contents_rowCells, Finset.mem_Ico] at hk
    omega

theorem diagLo_rowCells {s e k : ℤ} (hk : s ≤ k) (hk' : k < e) : diagLo (rowCells s e) k = 0 := by
  apply diagLo_eq_of (l := 0)
  · rw [zero_add]; exact mem_rowCells.mpr ⟨rfl, hk, hk'⟩
  · intro i hi
    have := (mem_rowCells.mp hi).1
    omega

theorem sw_rowCells {s e : ℤ} (h : s < e) : sw (rowCells s e) = (0, s) := by
  unfold sw
  rw [minContent_rowCells h, diagLo_rowCells (le_refl _) h]
  simp

theorem ne_rowCells {s e : ℤ} (h : s < e) : ne (rowCells s e) = (0, e - 1) := by
  unfold ne
  rw [maxContent_rowCells h, diagLo_rowCells (by omega) (by omega)]
  simp

theorem isConnectedSkew_rowCells {s e : ℤ} (h : s < e) : IsConnectedSkew (rowCells s e) := by
  have hs : IsSkew (rowCells s e) := by
    intro x hx y hy h1 h2 i hi j hj
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    obtain ⟨ha, hb1, hb2⟩ := mem_rowCells.mp hx
    obtain ⟨hc, hd1, hd2⟩ := mem_rowCells.mp hy
    simp only [Finset.mem_Icc] at hi hj
    exact mem_rowCells.mpr ⟨by omega, by omega, by omega⟩
  refine ⟨hs, isEdgeConnected_of_reach (c₀ := (0, s)) (mem_rowCells.mpr ⟨rfl, le_refl _, h⟩) ?_⟩
  intro x hx
  obtain ⟨a, b⟩ := x
  obtain ⟨ha, hb1, hb2⟩ := mem_rowCells.mp hx
  subst ha
  exact hs.reach_row (mem_rowCells.mpr ⟨rfl, le_refl _, h⟩) hx

/-! ### The row mark `ω_{q,w}` -/

/-- The case-(a) mark `ω_{q,w}` on the row `E = (q + w)`: the lower and upper copies are its first
and last `w` cells, on the contents `[0, w - 1]` and `[q, q + w - 1]`; the displacement is
`(0, q)`.  For `w = 0` this is the horizontal empty mark. -/
def rowMark (s : RowShift) : MarkedInner where
  E := rowCells 0 (s.q + s.w)
  W := rowCells 0 s.w
  v := (0, (s.q : ℤ))
  case := .a

namespace RowShift

theorem q_pos (s : RowShift) : (0 : ℤ) < s.q := by have := s.two_le_q; omega

theorem w_lt_q' (s : RowShift) : (s.w : ℤ) < s.q := by have := s.w_lt_q; omega

end RowShift

section RowMarkFacts

variable (s : RowShift)

/-- The upper copy of the row mark is the last `w` cells of the row. -/
theorem rowMark_upper : (rowMark s).upper = rowCells s.q (s.q + s.w) := by
  ext ⟨a, b⟩
  have e : ((a, b) : ℤ × ℤ) - (0, (s.q : ℤ)) = (a - 0, b - s.q) := rfl
  simp only [MarkedInner.upper, rowMark, mem_translate]
  rw [e, mem_rowCells, mem_rowCells]
  omega

/-- The middle of the row mark is the row on the contents `[w, q - 1]`. -/
theorem rowMark_middle : (rowMark s).middle = rowCells s.w s.q := by
  ext ⟨a, b⟩
  rw [MarkedInner.middle, rowMark_upper]
  simp only [rowMark, Finset.mem_sdiff, Finset.mem_union, mem_rowCells]
  have := s.q_pos
  have := s.w_lt_q'
  omega

/-- The lower copy of the row mark has span `w`. -/
theorem rowMark_span_W : span (rowMark s).W = s.w := by
  simp [rowMark, span_rowCells]

theorem rowMark_width : (rowMark s).width = s.w := rowMark_span_W s

theorem rowMark_period : (rowMark s).period = s.q := by
  simp [MarkedInner.period, rowMark, content]

theorem rowMark_isConnectedSkew_E : IsConnectedSkew (rowMark s).E :=
  isConnectedSkew_rowCells (by have := s.q_pos; omega)

theorem rowMark_vH (hw : s.w = 0) : vH (rowMark s).E = (0, (s.q : ℤ)) := by
  have h : (0 : ℤ) < (s.q : ℤ) + s.w := by have := s.q_pos; omega
  simp only [vH, rowMark]
  rw [ne_rowCells h, sw_rowCells h]
  ext <;> simp [hw]

/-- The row mark is a marked inner of the paper (well formed). -/
theorem rowMark_isWellFormed : (rowMark s).IsWellFormed := by
  refine ⟨rowMark_isConnectedSkew_E s, ?_⟩
  by_cases hw : s.w = 0
  · left
    refine ⟨?_, ?_, rfl⟩
    · simp [rowMark, hw, rowCells]
    · rw [rowMark_vH s hw]; rfl
  · right
    have hwpos : 0 < s.w := Nat.pos_of_ne_zero hw
    have hq := s.q_pos
    have hwq := s.w_lt_q'
    have hE : (0 : ℤ) < (s.q : ℤ) + s.w := by omega
    have hsw : sw (rowMark s).E = (0, 0) := by
      simp only [rowMark]; rw [sw_rowCells hE]
    have hne : ne (rowMark s).E = (0, ((s.q : ℤ) + s.w) - 1) := by
      simp only [rowMark]; rw [ne_rowCells hE]
    have hmid := rowMark_middle s
    refine ⟨⟨(0, 0), mem_rowCells.mpr ⟨rfl, le_refl _, by omega⟩⟩,
      isConnectedSkew_rowCells (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, b⟩ := x
      obtain ⟨h1, h2, h3⟩ := mem_rowCells.mp hx
      exact mem_rowCells.mpr ⟨h1, h2, by omega⟩
    · rw [rowMark_upper]
      intro x hx
      obtain ⟨a, b⟩ := x
      obtain ⟨h1, h2, h3⟩ := mem_rowCells.mp hx
      exact mem_rowCells.mpr ⟨h1, by omega, h3⟩
    · rw [hsw]; exact mem_rowCells.mpr ⟨rfl, le_refl _, by omega⟩
    · rw [hne, rowMark_upper]
      exact mem_rowCells.mpr ⟨rfl, by omega, by omega⟩
    · refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd h (by simp [rowMark]),
        fun h => absurd h (by simp [rowMark]), fun h => absurd h (by simp [rowMark])⟩
      · refine ⟨(0, (s.w : ℤ)), ?_, ?_, ?_⟩
        · rw [hmid]; exact mem_rowCells.mpr ⟨rfl, le_refl _, by omega⟩
        · rw [hmid, minContent_rowCells (by omega)]; simp [content]
        · simp only [rowMark]; exact mem_rowCells.mpr ⟨rfl, by omega, by omega⟩
      · refine ⟨(0, (s.q : ℤ) - 1), ?_, ?_, ?_⟩
        · rw [hmid]; exact mem_rowCells.mpr ⟨rfl, by omega, by omega⟩
        · rw [hmid, maxContent_rowCells (by omega)]; simp [content]
        · rw [rowMark_upper]; exact mem_rowCells.mpr ⟨rfl, by omega, by omega⟩

/-- Condition I for the row mark: a row has one cell on each content. -/
theorem rowMark_isMaximal : (rowMark s).IsMaximal := by
  intro W' hW' hlt _ hc x hx
  exfalso
  have hsub : W' ⊆ rowCells 0 (s.q + s.w) := Finset.mem_powerset.mp hW'
  have hW : W' ⊆ (rowMark s).W := by
    intro y hy
    obtain ⟨a, b⟩ := y
    obtain ⟨h1, -, -⟩ := mem_rowCells.mp (hsub hy)
    have : content (a, b) ∈ contents W' := content_mem_contents hy
    rw [hc] at this
    simp only [rowMark, contents_rowCells, Finset.mem_Ico, content] at this
    subst h1
    exact mem_rowCells.mpr ⟨rfl, by omega, by omega⟩
  exact absurd hW (not_subset_of_ssubset hlt)

/-- Condition II for the row mark: `0 ≤ w < q`. -/
theorem rowMark_isNarrow : (rowMark s).IsNarrow := by
  rw [MarkedInner.IsNarrow, rowMark_width, rowMark_period]
  exact ⟨by positivity, s.w_lt_q'⟩

/-- Condition III for the row mark: removing either copy leaves a row. -/
theorem rowMark_removalsConnected : (rowMark s).RemovalsConnected := by
  have hq := s.q_pos
  have hwq := s.w_lt_q'
  constructor
  · have : (rowMark s).E \ (rowMark s).W = rowCells s.w (s.q + s.w) := by
      ext ⟨a, b⟩
      simp only [rowMark, Finset.mem_sdiff, mem_rowCells]
      omega
    rw [this]
    exact isConnectedSkew_rowCells (by omega)
  · have : (rowMark s).E \ (rowMark s).upper = rowCells 0 s.q := by
      ext ⟨a, b⟩
      rw [rowMark_upper]
      simp only [rowMark, Finset.mem_sdiff, mem_rowCells]
      omega
    rw [this]
    exact isConnectedSkew_rowCells (by omega)

/-- Condition IV for the row mark: the middle row has empty hat. -/
theorem rowMark_noHatAdjacency : (rowMark s).NoHatAdjacency := by
  intro k m x hx
  exfalso
  obtain ⟨hx1, hx2⟩ := hx
  have hmid := rowMark_middle s
  have row0 : ∀ y ∈ translate (k • (rowMark s).v) (rowMark s).middle, y.1 = 0 := by
    intro y hy
    obtain ⟨a, b⟩ := y
    have := mem_translate.mp hy
    rw [hmid] at this
    have h2 := (mem_rowCells.mp (by simpa [rowMark] using this)).1
    simpa [rowMark] using h2
  have h1 := row0 x hx1
  have h2 := row0 (x + eCell) hx2
  simp [eCell] at h2
  omega

/-- **The row mark is legal** (`lem:gluing-row-action`). -/
theorem rowMark_isLegal : (rowMark s).IsLegal :=
  ⟨rowMark_isWellFormed s, rowMark_isMaximal s, rowMark_isNarrow s, rowMark_removalsConnected s,
    rowMark_noHatAdjacency s⟩

end RowMarkFacts

/-! ### Composition with a row mark -/

section RowCompose

variable (s : RowShift)

/-- In case (a) the copy of the inner at the cell `(i, i + j)` of the outer starts at `(i, q j +
i)`. -/
theorem rowMark_origin (D : Diagram) (d : ℤ × ℤ) :
    (rowMark s).origin D d = (d.1, (d.2 - d.1) * s.q + d.1) := by
  simp only [MarkedInner.origin, rowMark, content, eCell]
  ext <;> simp

theorem rowMark_sameRibbon (D : Diagram) (d : ℤ × ℤ) : ¬ (rowMark s).SameRibbon D d := by
  simp [MarkedInner.SameRibbon, rowMark]

/-- A cell of the composite with the row mark lies in a copy of the row on its row. -/
theorem mem_rowMark_compose {D : Diagram} (hD : D.Nonempty) {a b : ℤ} :
    (a, b) ∈ (rowMark s).compose D ↔ ∃ c, (a, c) ∈ D ∧
      0 ≤ b - ((c - a) * s.q + a) ∧ b - ((c - a) * s.q + a) < s.q + s.w := by
  rw [MarkedInner.mem_compose hD]
  simp only [rowMark_sameRibbon, false_and, and_false, exists_false, or_false]
  constructor
  · rintro ⟨d, hd, hx⟩
    obtain ⟨d1, d2⟩ := d
    rw [mem_translate, rowMark_origin] at hx
    have e : ((a, b) : ℤ × ℤ) - (d1, (d2 - d1) * s.q + d1) =
        (a - d1, b - ((d2 - d1) * s.q + d1)) := rfl
    rw [e] at hx
    simp only [rowMark, mem_rowCells] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    have : d1 = a := by omega
    subst this
    exact ⟨d2, hd, h2, by omega⟩
  · rintro ⟨c, hc, h1, h2⟩
    refine ⟨(a, c), hc, ?_⟩
    rw [mem_translate, rowMark_origin]
    have e : ((a, b) : ℤ × ℤ) - (a, (c - a) * s.q + a) =
        (a - a, b - ((c - a) * s.q + a)) := rfl
    rw [e]
    simp only [rowMark, mem_rowCells]
    exact ⟨by omega, h1, by omega⟩

end RowCompose

section RowComposeCells

variable (s : RowShift) {n : ℕ}

/-- **Composition with a row mark, on cells.**  Composing the cell diagram of a profile `P`
(placed with top row `t` and column offset `c₀`) with the row mark `ω_{q,w}` gives the cell
diagram of `𝓛_{q,w} P`, up to translation. -/
theorem rowMark_compose_translate_cells (P : Profile n) (t c₀ : ℤ) :
    (rowMark s).compose (translate (t, c₀) P.cells) =
      translate (t, (s.q : ℤ) * (c₀ - t) + t) (P.lift s).cells := by
  have hq := s.q_pos
  have hD : (translate (t, c₀) P.cells).Nonempty := P.cells_nonempty.image _
  ext ⟨a, b⟩
  rw [mem_rowMark_compose s hD]
  have e : ((a, b) : ℤ × ℤ) - (t, (s.q : ℤ) * (c₀ - t) + t) =
      (a - t, b - ((s.q : ℤ) * (c₀ - t) + t)) := rfl
  rw [mem_translate, e, Profile.mem_cells]
  have eD : ∀ c : ℤ, (a, c) ∈ translate (t, c₀) P.cells ↔ (a - t, c - c₀) ∈ P.cells := by
    intro c
    rw [mem_translate]; rfl
  simp only [eD, Profile.mem_cells, Profile.zeta_lift, Profile.xi_lift]
  constructor
  · rintro ⟨c, ⟨i, hi, h1, h2⟩, h3, h4⟩
    refine ⟨i, hi, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right (show c₀ - t + P.zeta i ≤ c - a by omega) hq.le
      nlinarith
    · have := mul_le_mul_of_nonneg_right (show c - a ≤ c₀ - t + P.xi i - 1 by omega) hq.le
      nlinarith
  · rintro ⟨i, hi, h1, h2⟩
    set u : ℤ := b - a with hu
    have hM0 : (s.q : ℤ) * (P.zeta i + c₀ - t) ≤ u := by nlinarith
    have hM1 : u < (s.q : ℤ) * (P.xi i - 1 + c₀ - t + 1) + s.w := by nlinarith
    have hlt : P.zeta i < P.xi i := by
      have := P.xi_sub_zeta i; have := P.r_pos i; omega
    have hdiv1 : u / s.q * s.q ≤ u := Int.ediv_mul_le u hq.ne'
    have hdiv2 : u < (u / s.q + 1) * s.q := Int.lt_ediv_add_one_mul_self u hq
    have hdiv3 : P.zeta i + c₀ - t ≤ u / s.q := by
      apply Int.le_ediv_of_mul_le hq
      linarith
    set m : ℤ := min (P.xi i - 1 + c₀ - t) (u / s.q) with hm
    have hm1 : P.zeta i + c₀ - t ≤ m := le_min (by omega) hdiv3
    have hm2 : m ≤ P.xi i - 1 + c₀ - t := min_le_left _ _
    have hm3 : m * s.q ≤ u := by
      rcases min_cases (P.xi i - 1 + c₀ - t) (u / s.q) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [hm, h]
        have := mul_le_mul_of_nonneg_right (show P.xi i - 1 + c₀ - t ≤ u / s.q by
          have := min_le_right (P.xi i - 1 + c₀ - t) (u / s.q); omega) hq.le
        linarith
      · rw [hm, h]; exact hdiv1
    have hm4 : u < m * s.q + s.q + s.w := by
      rcases min_cases (P.xi i - 1 + c₀ - t) (u / s.q) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [hm, h]; nlinarith
      · rw [hm, h]; nlinarith
    have hca : a + m - a = m := by ring
    refine ⟨a + m, ⟨i, hi, ?_, ?_⟩, ?_, ?_⟩
    · omega
    · omega
    · rw [hca]; omega
    · rw [hca]; omega

/-- **`lem:gluing-row-action`, first assertion (profile form, `eq:gluing-row-action`).**  For
every connected outer, the composite with the row mark `ω_{q,w}` is a connected diagram whose
profile is `𝓛_{q,w}` of the profile of the outer: `(r; g) ∘_{ω_{q,w}} E = (q r + w; q g + w)`. -/
theorem cellProfile_rowMark_compose {D : Diagram} (hD : IsConnectedSkew D) :
    cellProfile ((rowMark s).compose D) = ⟨(cellProfile D).1, (cellProfile D).2.lift s⟩ := by
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have := rowMark_compose_translate_cells s (cellProfile D).2 v.1 v.2
  rw [Prod.mk.eta, ← hv] at this
  exact cellProfile_of_eq_translate this

/-- The composite of a connected outer with the row mark is connected skew. -/
theorem isConnectedSkew_rowMark_compose {D : Diagram} (hD : IsConnectedSkew D) :
    IsConnectedSkew ((rowMark s).compose D) := by
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have := rowMark_compose_translate_cells s (cellProfile D).2 v.1 v.2
  rw [Prod.mk.eta, ← hv] at this
  rw [this]
  exact isConnectedSkew_translate _ (Profile.isConnectedSkew_cells _)

end RowComposeCells

/-! ### The converse: a row inner has the form `ω_{q,w}` -/

section RowConverse

/-- Translating the inner diagram and its marked copy translates the composite. -/
theorem compose_translate_inner {ω ω₀ : MarkedInner} (u : ℤ × ℤ) (hE : ω.E = translate u ω₀.E)
    (hW : ω.W = translate u ω₀.W) (hv : ω.v = ω₀.v) (hc : ω.case = ω₀.case) {D : Diagram}
    (hD : D.Nonempty) : ω.compose D = translate u (ω₀.compose D) := by
  have horigin : ∀ d, ω.origin D d = ω₀.origin D d := by
    intro d; simp only [MarkedInner.origin, hv, hc]
  have hup : ω.upper = translate u ω₀.upper := by
    simp only [MarkedInner.upper, hW, hv, translate_translate, add_comm]
  have hshift : ω.supplementalShift = ω₀.supplementalShift := by
    simp only [MarkedInner.supplementalShift, hc]
  have hrib : ∀ d, ω.SameRibbon D d ↔ ω₀.SameRibbon D d := by
    intro d; simp only [MarkedInner.SameRibbon, hc]
  ext x
  have key : ∀ (o : ℤ × ℤ) (A : Diagram),
      x ∈ translate o (translate u A) ↔ x - u ∈ translate o A := by
    intro o A
    simp only [mem_translate]
    rw [sub_right_comm]
  rw [MarkedInner.mem_compose hD, mem_translate, MarkedInner.mem_compose hD]
  simp only [horigin, hshift, hrib, hE, hup, key]

/-- A nonempty skew diagram contained in one row is a translate of a row of cells. -/
theorem exists_eq_translate_rowCells {W : Diagram} (hs : IsSkew W) (hne : W.Nonempty) {a : ℤ}
    (hrow : ∀ x ∈ W, x.1 = a) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ rowLo W a = lo ∧ rowHi W a = hi ∧
      W = translate (a, lo) (rowCells 0 (hi - lo + 1)) := by
  obtain ⟨x, hx⟩ := hne
  have hxa := hrow x hx
  have hnon : (rowCols W a).Nonempty := ⟨x.2, mem_rowCols.mpr (by rw [← hxa]; exact hx)⟩
  have hle : rowLo W a ≤ rowHi W a := by
    have h1 := mem_rowCols.mp hnon.choose_spec
    exact (rowLo_le h1).trans (le_rowHi h1)
  refine ⟨rowLo W a, rowHi W a, hle, rfl, rfl, ?_⟩
  ext ⟨b1, b2⟩
  rw [mem_translate]
  have e : ((b1, b2) : ℤ × ℤ) - (a, rowLo W a) = (b1 - a, b2 - rowLo W a) := rfl
  rw [e, mem_rowCells]
  constructor
  · intro h
    have h1 := hrow _ h
    simp only at h1
    have := (hs.mem_iff_row hnon).mp (by rw [← h1]; exact h)
    omega
  · rintro ⟨h1, h2, h3⟩
    have : b1 = a := by omega
    subst this
    exact (hs.mem_iff_row hnon).mpr ⟨by omega, by omega⟩

theorem mem_row_of_mem {u : ℤ × ℤ} {m : ℕ} {x : ℤ × ℤ} (hx : x ∈ translate u (rowCells 0 m)) :
    x.1 = u.1 ∧ u.2 ≤ x.2 ∧ x.2 < u.2 + m := by
  obtain ⟨a, b⟩ := x
  have e : ((a, b) : ℤ × ℤ) - u = (a - u.1, b - u.2) := rfl
  rw [mem_translate, e, mem_rowCells] at hx
  simp only
  omega

/-- **A legal mark on a row is a row mark** (`lem:gluing-row-action`, converse).  A legal marked
inner whose diagram is a row of at least two cells is the row mark `ω_{q,w}` with `q ≥ 2`,
`0 ≤ w < q`, placed where its row sits. -/
theorem exists_rowMark_of_isLegal {ω : MarkedInner} (hω : ω.IsLegal) {u : ℤ × ℤ} {m : ℕ}
    (hE : ω.E = translate u (rowCells 0 m)) (hm : 2 ≤ m) :
    ∃ s : RowShift, ω.E = translate u (rowMark s).E ∧ ω.W = translate u (rowMark s).W ∧
      ω.v = (rowMark s).v ∧ ω.case = (rowMark s).case := by
  obtain ⟨⟨hEcs, hmark⟩, -, hII, -, -⟩ := hω
  have hmpos : (0 : ℤ) < m := by omega
  have hcell : ∀ x ∈ ω.E, x.1 = u.1 ∧ u.2 ≤ x.2 ∧ x.2 < u.2 + m := fun x hx =>
    mem_row_of_mem (by rw [← hE]; exact hx)
  have hswE : sw ω.E = u := by
    rw [hE, sw_translate (rowCells_nonempty hmpos), sw_rowCells hmpos]
    ext <;> simp
  have hneE : ne ω.E = (u.1, u.2 + m - 1) := by
    rw [hE, ne_translate (rowCells_nonempty hmpos), ne_rowCells hmpos]
    ext <;> simp; ring
  rcases hmark with ⟨hW, hv, hc⟩ | ⟨hWne, hWcs, hWE, hUE, hsw, hneU, hatt⟩
  · -- the empty mark
    have hvv : ω.v = (0, (m : ℤ)) := by
      rw [hv, vH, hswE, hneE]
      ext <;> simp; omega
    refine ⟨⟨m, 0, hm, by omega⟩, ?_, ?_, ?_, hc⟩
    · rw [hE]; simp [rowMark]
    · rw [hW]; simp [rowMark, rowCells, translate]
    · rw [hvv]; simp [rowMark]
  · -- a nonempty mark
    have hWrow : ∀ x ∈ ω.W, x.1 = u.1 := fun x hx => (hcell x (hWE hx)).1
    obtain ⟨lo, hi, hlohi, hlo, hhi, hWeq⟩ :=
      exists_eq_translate_rowCells hWcs.1 hWne hWrow
    obtain ⟨x0, hx0⟩ := hWne
    have hv1 : ω.v.1 = 0 := by
      have h1 := hUE (show x0 + ω.v ∈ ω.upper from mem_translate.mpr (by simpa using hx0))
      have h2 := (hcell _ h1).1
      have h3 := hWrow x0 hx0
      simp only [Prod.fst_add] at h2
      omega
    set q' := ω.v.2 with hq'
    have hvq : ω.v = (0, q') := Prod.ext hv1 rfl
    -- the lower copy starts at the southwest cell of `E`
    have hlo2 : lo = u.2 := by
      have h1 := rowLo_le (show (u.1, u.2) ∈ ω.W by rw [← hswE]; exact hsw)
      have h2 := (hcell _ (hWE (rowLo_mem (D := ω.W) (a := u.1)
        ⟨x0.2, mem_rowCols.mpr (by rw [← hWrow x0 hx0]; exact hx0)⟩))).2.1
      rw [hlo] at h1 h2
      have : lo ≤ u.2 := by simpa using h1
      simp only at h2
      omega
    subst hlo2
    -- the upper copy ends at the northeast cell of `E`
    have hhi2 : hi + q' = u.2 + m - 1 := by
      have hmemhi : (u.1, hi) ∈ ω.W := by
        have := rowHi_mem (D := ω.W) (a := u.1)
          ⟨x0.2, mem_rowCols.mpr (by rw [← hWrow x0 hx0]; exact hx0)⟩
        rwa [hhi] at this
      have h1 := hUE (show (u.1, hi) + ω.v ∈ ω.upper from mem_translate.mpr (by simpa using hmemhi))
      have h2 := (hcell _ h1).2.2
      simp only [Prod.snd_add] at h2
      have h3 : (u.1, u.2 + m - 1) ∈ ω.upper := by rw [← hneE]; exact hneU
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp h3
      have hy2 := le_rowHi (D := ω.W) hy
      rw [hWrow y hy, hhi] at hy2
      have := congrArg Prod.snd hyv
      simp only [Prod.snd_add] at this
      omega
    have hw : (ω.width : ℤ) = hi - u.2 + 1 := by
      rw [MarkedInner.width, hWeq, span_translate, span_rowCells]
      omega
    have hnarrow := hII
    rw [MarkedInner.IsNarrow] at hnarrow
    have hper : ω.period = q' := by simp [MarkedInner.period, content, hv1, hq']
    rw [hw, hper] at hnarrow
    have hq2 : 2 ≤ q' := by omega
    refine ⟨⟨q'.toNat, (hi - u.2 + 1).toNat, by omega, by omega⟩, ?_, ?_, ?_, ?_⟩
    · rw [hE]
      simp only [rowMark]
      congr 2
      omega
    · rw [hWeq]
      simp only [rowMark]
      congr 2
      omega
    · rw [hvq]
      simp only [rowMark]
      ext <;> simp; omega
    · obtain ⟨-, hb, hcc, hd⟩ := hatt
      simp only [rowMark]
      cases hcase : ω.case
      · rfl
      · exfalso
        obtain ⟨⟨x, hxm, -, hx⟩, -⟩ := hb hcase
        have h1 := (hcell x (by
          have : x ∈ ω.middle := hxm
          exact (Finset.mem_sdiff.mp this).1)).1
        have h2 := hWrow _ hx
        simp only at h2
        omega
      · exfalso
        obtain ⟨-, ⟨x, hxm, -, hx⟩⟩ := hcc hcase
        have h1 := (hcell x (by
          have : x ∈ ω.middle := hxm
          exact (Finset.mem_sdiff.mp this).1)).1
        have h2 := (hcell _ (hUE hx)).1
        simp only at h2
        omega
      · exfalso
        obtain ⟨⟨x, hxm, -, hx⟩, -⟩ := hd hcase
        have h1 := (hcell x (by
          have : x ∈ ω.middle := hxm
          exact (Finset.mem_sdiff.mp this).1)).1
        have h2 := hWrow _ hx
        simp only at h2
        omega

end RowConverse

/-- `𝓛_{q,w}` is injective on profiles with any number of rows. -/
theorem eq_of_lift_sigma_eq (s : RowShift) (G G' : AnyProfile)
    (h : (⟨G.1, G.2.lift s⟩ : AnyProfile) = ⟨G'.1, G'.2.lift s⟩) : G = G' := by
  obtain ⟨n, P⟩ := G
  obtain ⟨n', P'⟩ := G'
  obtain ⟨hn, hP⟩ := Sigma.mk.inj_iff.mp h
  simp only at hn
  subst hn
  simp only [heq_eq_eq] at hP
  rw [Profile.lift_injective s hP]

/-- The marked inner `ω` is the row mark `ω_{q,w}` placed with its row translated by `u`. -/
def MarkedInner.IsRowMark (ω : MarkedInner) (s : RowShift) (u : ℤ × ℤ) : Prop :=
  ω.E = translate u (rowMark s).E ∧ ω.W = translate u (rowMark s).W ∧ ω.v = (rowMark s).v ∧
    ω.case = (rowMark s).case

section RowChart

variable {ω : MarkedInner} {s : RowShift} {u : ℤ × ℤ}

/-- The period of a row mark is `q`. -/
theorem MarkedInner.IsRowMark.period (h : ω.IsRowMark s u) : ω.period = s.q := by
  rw [MarkedInner.period, h.2.2.1]
  simp [rowMark, content]

/-- The width of a row mark is `w`. -/
theorem MarkedInner.IsRowMark.width (h : ω.IsRowMark s u) : ω.width = s.w := by
  rw [MarkedInner.width, h.2.1, span_translate, rowMark_span_W]

/-- Composition with a placed row mark is a translate of composition with `ω_{q,w}`. -/
theorem MarkedInner.IsRowMark.compose (h : ω.IsRowMark s u) {D : Diagram} (hD : D.Nonempty) :
    ω.compose D = translate u ((rowMark s).compose D) :=
  compose_translate_inner u h.1 h.2.1 h.2.2.1 h.2.2.2 hD

/-- **`lem:gluing-row-action`, converse.**  If a legal marked inner on a row of at least two cells
composes with a connected outer `D`, then the chart has the form `ω_{q,w}`: its period and width
are `q` and `w`, and the composite has profile `𝓛_{q,w}` of the profile of `D`. -/
theorem MarkedInner.IsRowMark.cellProfile_compose (h : ω.IsRowMark s u) {D : Diagram}
    (hD : IsConnectedSkew D) :
    IsConnectedSkew (ω.compose D) ∧
      cellProfile (ω.compose D) = ⟨(cellProfile D).1, (cellProfile D).2.lift s⟩ := by
  rw [h.compose hD.2.1]
  refine ⟨(isConnectedSkew_translate_iff u).mpr (isConnectedSkew_rowMark_compose s hD), ?_⟩
  rw [cellProfile_translate (isConnectedSkew_rowMark_compose s hD),
    cellProfile_rowMark_compose s hD]

/-- **Every row length and every overlap minus one of the composite is congruent to `w`
modulo `q`.** -/
theorem MarkedInner.IsRowMark.hasResidue (h : ω.IsRowMark s u) {D : Diagram}
    (hD : IsConnectedSkew D) : (cellProfile (ω.compose D)).2.HasResidue s := by
  rw [(h.cellProfile_compose hD).2]
  exact Profile.hasResidue_lift s _

/-- **The outer of the chart is unique**: two connected outers with the same composite profile
are translates of each other. -/
theorem MarkedInner.IsRowMark.outer_unique (h : ω.IsRowMark s u) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hF : cellProfile (ω.compose D') = cellProfile (ω.compose D)) :
    ∃ v, D' = translate v D := by
  rw [(h.cellProfile_compose hD').2, (h.cellProfile_compose hD).2] at hF
  have : cellProfile D' = cellProfile D := eq_of_lift_sigma_eq s _ _ hF
  exact exists_translate_of_cellProfile_eq hD hD' this.symm

/-- **The beta lists of the outer** are `(ξ_i - w) / q` and `ζ_i / q`, where `ξ`, `ζ` are the beta
lists of the composite. -/
theorem MarkedInner.IsRowMark.beta_lists (h : ω.IsRowMark s u) {D : Diagram}
    (hD : IsConnectedSkew D) :
    ∃ P : Profile (cellProfile D).1, cellProfile (ω.compose D) = ⟨(cellProfile D).1, P⟩ ∧
      ∀ i, (cellProfile D).2.xi i = (P.xi i - s.w) / s.q ∧
        (cellProfile D).2.zeta i = P.zeta i / s.q :=
  ⟨(cellProfile D).2.lift s, (h.cellProfile_compose hD).2,
    fun i => Profile.xi_zeta_of_lift_eq s rfl i⟩

/-- **A legal mark on a row of at least two cells is a row mark** (`lem:gluing-row-action`). -/
theorem MarkedInner.IsLegal.exists_isRowMark (hω : ω.IsLegal) {m : ℕ}
    (hE : ω.E = translate u (rowCells 0 m)) (hm : 2 ≤ m) : ∃ s : RowShift, ω.IsRowMark s u :=
  exists_rowMark_of_isLegal hω hE hm

end RowChart

section RowDivide

variable (s : RowShift)

/-- **Quotient of a profile with the residue** (`lem:gluing-row-action`): a connected diagram with
at least two rows whose row lengths and overlaps minus one are all congruent to `w` modulo `q` is
the composition of a connected outer with the row mark `ω_{q,w}`, up to translation. -/
theorem exists_rowMark_compose_of_hasResidue {F : Diagram} (hF : IsConnectedSkew F)
    (hn : 0 < (cellProfile F).1) (hres : (cellProfile F).2.HasResidue s) :
    ∃ D : Diagram, IsConnectedSkew D ∧ ∃ v : ℤ × ℤ, F = translate v ((rowMark s).compose D) := by
  obtain ⟨v, hv⟩ := hF.exists_translate_cells
  set P := (cellProfile F).2 with hP
  have hlen := Profile.le_r_of_hasResidue hres hn
  set P' := P.divide s hres hlen with hP'
  have hcomp := rowMark_compose_translate_cells s P' 0 0
  rw [Profile.lift_divide] at hcomp
  refine ⟨P'.cells, P'.isConnectedSkew_cells, v, ?_⟩
  have e : ((0 : ℤ), (0 : ℤ)) = 0 := rfl
  rw [e, translate_zero] at hcomp
  rw [hcomp]
  simp only [mul_zero, sub_zero, add_zero]
  rw [show ((0 : ℤ), (0 : ℤ)) = 0 from rfl, translate_zero]
  exact hv

end RowDivide

/-! ### The worked example `(2, 1) ↦ (5, 3; 1)` -/

section Examples

/-- Composing the hook `(2, 1)` with the row mark `ω_{2,1}` gives the profile `(5, 3; 1)`. -/
example : cellProfile ((rowMark rowShiftTwoOne).compose (skewOf [2, 1] [])) =
    ⟨1, hookProfile.lift rowShiftTwoOne⟩ := by
  have h := cellProfile_rowMark_compose rowShiftTwoOne (D := skewOf [2, 1] []) (by decide)
  rw [h, cellProfile_hook]

example : ((rowMark rowShiftTwoOne).compose (skewOf [2, 1] [])).card = 8 := by decide +kernel

example : (rowMark rowShiftTwoOne).compose (skewOf [2, 1] []) =
    ((Finset.Ico (0 : ℤ) 5).image fun j => ((0 : ℤ), j)) ∪
    ((Finset.Ico (-1 : ℤ) 2).image fun j => ((1 : ℤ), j)) := by decide +kernel

end Examples

/-! ### `lem:gluing-row-transport` on cells -/

section RowTransportCells

variable (s : RowShift)

/-- The cell diagram `𝓛_{q,w} D` of a connected diagram `D`: the cell diagram of
`(q r + w; q g + w)`, in the position of its profile.  It is defined up to translation. -/
noncomputable def liftCells (D : Diagram) : Diagram := ((cellProfile D).2.lift s).cells

/-- `𝓛_{q,w} D` is connected skew. -/
theorem isConnectedSkew_liftCells (D : Diagram) : IsConnectedSkew (liftCells s D) :=
  Profile.isConnectedSkew_cells _

/-- The profile of `𝓛_{q,w} D` is `𝓛_{q,w}` of the profile of `D`. -/
theorem cellProfile_liftCells (D : Diagram) :
    cellProfile (liftCells s D) = ⟨(cellProfile D).1, (cellProfile D).2.lift s⟩ :=
  cellProfile_cells _

/-- Composition with the row mark `ω_{q,w}` is `𝓛_{q,w}` on cells, up to translation. -/
theorem rowMark_compose_eq_liftCells {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ v, (rowMark s).compose D = translate v (liftCells s D) := by
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have := rowMark_compose_translate_cells s (cellProfile D).2 v.1 v.2
  rw [Prod.mk.eta, ← hv] at this
  exact ⟨_, this⟩

/-- The function of `𝓛_{q,w} D` is the Jacobi--Trudi function of the lifted profile. -/
theorem cellSchur_liftCells (D : Diagram) :
    cellSchur (liftCells s D) = ((cellProfile D).2.lift s).schur := cellSchur_cells _

/-- Connected diagrams with the same function have profiles with the same number of rows, so
the profile map `𝓛` applies to both (`reinerRowInvariants`). -/
theorem cellProfile_fst_eq_of_cellSchur_eq {C C' : Diagram} (hC : IsConnectedSkew C)
    (hC' : IsConnectedSkew C') (h : cellSchur C = cellSchur C') :
    (cellProfile C).1 = (cellProfile C').1 := by
  rw [cellSchur_of_isConnectedSkew hC, cellSchur_of_isConnectedSkew hC'] at h
  exact (reinerRowInvariants _ _ _ _ h).1

/-- **`𝓛_{q,w}` preserves Schur-equality.**  If connected diagrams `E`, `D` have the same
function, so do `𝓛_{q,w} E` and `𝓛_{q,w} D`. -/
theorem cellSchur_liftCells_eq {E D : Diagram} (hE : IsConnectedSkew E) (hD : IsConnectedSkew D)
    (h : cellSchur E = cellSchur D) : cellSchur (liftCells s E) = cellSchur (liftCells s D) := by
  have hn := cellProfile_fst_eq_of_cellSchur_eq hE hD h
  rw [cellSchur_liftCells, cellSchur_liftCells]
  rw [cellSchur_of_isConnectedSkew hE, cellSchur_of_isConnectedSkew hD] at h
  revert h
  generalize cellProfile E = G at hn ⊢
  generalize cellProfile D = G' at hn ⊢
  obtain ⟨n, P⟩ := G
  obtain ⟨n', P'⟩ := G'
  simp only at hn
  subst hn
  intro h
  exact (Profile.schur_lift_eq_iff s P P').mpr h

/-- **`𝓛_{q,w}` is injective on diagrams up to translation.** -/
theorem exists_translate_of_liftCells {E E' : Diagram} (hE : IsConnectedSkew E)
    (hE' : IsConnectedSkew E') (v : ℤ × ℤ) (h : liftCells s E' = translate v (liftCells s E)) :
    ∃ w, E' = translate w E := by
  have h1 := cellProfile_liftCells s E'
  have h2 := cellProfile_liftCells s E
  rw [h, cellProfile_translate (isConnectedSkew_liftCells s E), h2] at h1
  exact exists_translate_of_cellProfile_eq hE hE' (eq_of_lift_sigma_eq s _ _ h1)

/-- **Surjectivity of `𝓛_{q,w}` on Schur classes.**  Every connected diagram whose function is
that of `𝓛_{q,w} D` is a translate of `𝓛_{q,w} E` for a connected `E` with the function of `D`.
The row invariants are supplied by `reinerRowInvariants`. -/
theorem exists_liftCells_of_cellSchur_eq {D H : Diagram} (hD : IsConnectedSkew D)
    (hH : IsConnectedSkew H) (h : cellSchur H = cellSchur (liftCells s D)) :
    ∃ E : Diagram, IsConnectedSkew E ∧ cellSchur E = cellSchur D ∧
      ∃ v, H = translate v (liftCells s E) := by
  rw [cellSchur_of_isConnectedSkew hH, cellSchur_liftCells] at h
  have hn : (cellProfile H).1 = (cellProfile D).1 :=
    (reinerRowInvariants _ _ _ _ h).1
  obtain ⟨w, hw⟩ := hH.exists_translate_cells
  revert h hn hw
  generalize cellProfile H = G
  obtain ⟨m, Q⟩ := G
  intro h hn hw
  simp only at hn h hw
  subst hn
  have hbij := Profile.lift_bijOn_schurClass reinerRowInvariants s (cellProfile D).2
  obtain ⟨Q', hQ', hQQ⟩ := hbij.surjOn
    (show Q ∈ Profile.schurFiber ((cellProfile D).2.lift s) from h)
  refine ⟨Q'.cells, Q'.isConnectedSkew_cells, ?_, w, ?_⟩
  · rw [cellSchur_cells, cellSchur_of_isConnectedSkew hD]
    exact hQ'
  · rw [hw, ← hQQ]
    unfold liftCells
    rw [cellProfile_cells]

/-- **`𝓛_{q,w}` commutes with rotation**, on cells and up to translation. -/
theorem liftCells_rotate {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ v, liftCells s (rotate D) = translate v (rotate (liftCells s D)) := by
  refine ⟨((cellProfile D).1, ((cellProfile D).2.lift s).xi 0 + (cellProfile D).1 - 1), ?_⟩
  unfold liftCells
  rw [cellProfile_rotate hD]
  exact ((cellProfile D).2.lift s).cells_rotate

/-- The positions `(i, j)` at which the Jacobi--Trudi index `ξ_i - ζ_j` of the profile of `D` is
negative. -/
def jtNegativePositions (D : Diagram) : Set (ℕ × ℕ) :=
  {p | ∃ (h1 : p.1 < (cellProfile D).1 + 1) (h2 : p.2 < (cellProfile D).1 + 1),
    (cellProfile D).2.xi ⟨p.1, h1⟩ - (cellProfile D).2.zeta ⟨p.2, h2⟩ < 0}

/-- **`𝓛_{q,w}` preserves the set of positions with negative Jacobi--Trudi index**, including the
positions where `ξ_i = ζ_j`. -/
theorem jtNegativePositions_liftCells (D : Diagram) :
    jtNegativePositions (liftCells s D) = jtNegativePositions D := by
  have key := Set.ext_iff.mp (Profile.negativePositions_lift s (cellProfile D).2)
  unfold jtNegativePositions
  rw [cellProfile_liftCells]
  ext ⟨i, j⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h⟩
    refine ⟨h1, h2, ?_⟩
    have := (key (⟨i, h1⟩, ⟨j, h2⟩)).mp (by simpa [Profile.negativePositions] using h)
    simpa [Profile.negativePositions] using this
  · rintro ⟨h1, h2, h⟩
    refine ⟨h1, h2, ?_⟩
    have := (key (⟨i, h1⟩, ⟨j, h2⟩)).mpr (by simpa [Profile.negativePositions] using h)
    simpa [Profile.negativePositions] using this

/-- The map `𝓛_{q,w}` on connected diagrams with any number of rows, up to translation (that is,
on `AnyProfile`, which `cellProfile` identifies with the translation classes of connected skew
diagrams). -/
def liftAny (G : AnyProfile) : AnyProfile := ⟨G.1, G.2.lift s⟩

/-- **`lem:gluing-row-transport`.**  For every connected `D`, the map `𝓛_{q,w}` is a bijection
from the translation classes of connected diagrams with the function of `D` onto those with the
function of `𝓛_{q,w} D`.  The row invariants are supplied by `reinerRowInvariants`, so the
statement is unconditional, and no assumption is made on the number of rows. -/
theorem liftAny_bijOn_schurClass {n : ℕ} (P : Profile n) :
    Set.BijOn (liftAny s) (schurClass P) (schurClass (P.lift s)) := by
  refine ⟨fun G hG => ?_, fun G _ G' _ h => eq_of_lift_sigma_eq s G G' h, fun H hH => ?_⟩
  · obtain ⟨m, Q⟩ := G
    have hQ : Q.schur = P.schur := hG
    have hm : m = n := by
      have := reinerRowInvariants m n Q P hQ
      exact this.1
    subst hm
    exact (Profile.schur_lift_eq_iff s Q P).mpr hQ
  · obtain ⟨m, Q⟩ := H
    have hQ : Q.schur = (P.lift s).schur := hH
    have hm : m = n := (reinerRowInvariants m n Q (P.lift s) hQ).1
    subst hm
    obtain ⟨Q', hQ', hQQ⟩ := (Profile.lift_bijOn_schurClass reinerRowInvariants s P).surjOn
      (show Q ∈ Profile.schurFiber (P.lift s) from hQ)
    exact ⟨⟨_, Q'⟩, hQ', by simp only [liftAny, hQQ]⟩

end RowTransportCells

end SkewGluing
