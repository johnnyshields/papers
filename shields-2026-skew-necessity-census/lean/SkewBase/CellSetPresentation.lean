import SkewBase.CellSetConnected

/-!
# Every skew cell set is presented by beta lists

Formalizes `shields-2026-skew-base-computational.tex`, `lem:invariants`: the skew Schur function
`s_H` of a skew diagram `H` given as a cell set.

A skew cell set whose rows start at row `0` is the set of cells of a diagram given by beta lists
(`BetaRows.cells`): row `i` of the diagram is the column interval `[μ_i, λ_i)`, where `μ_i` is the
least column of a cell in a row `≤ i` and `λ_i` is the end of row `i` when row `i` is nonempty and
`μ_i` otherwise, so that an empty row sits where the neighboring rows put it.  Skewness makes `μ`
and `λ` weakly decrease; the beta lists are `λ_i - i` and `μ_i - i`.  A translate of a skew cell
set is such a cell set, so every skew cell set has a presentation (`exists_hasSchur_of_isSkew`),
and `HasSchur` is satisfiable for every skew diagram.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-- The columns of the cells in the rows up to `i`. -/
def columnsUpTo (D : Diagram) (i : ℤ) : Finset ℤ := (D.filter fun x => x.1 ≤ i).image Prod.snd

/-- The start `μ_i` of row `i`: the least column of a cell in a row `≤ i`. -/
def leftEdge (D : Diagram) (i : ℤ) : ℤ :=
  if h : (columnsUpTo D i).Nonempty then (columnsUpTo D i).min' h else 0

/-- The end `λ_i` of row `i`: one past its last column if it is nonempty, and `μ_i` if it is
empty. -/
def rightEdge (D : Diagram) (i : ℤ) : ℤ :=
  if h : (columnsOfRow D i).Nonempty then (columnsOfRow D i).max' h + 1 else leftEdge D i

theorem mem_columnsUpTo {D : Diagram} {i c : ℤ} :
    c ∈ columnsUpTo D i ↔ ∃ j, j ≤ i ∧ (j, c) ∈ D := by
  unfold columnsUpTo
  simp only [Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨h1, h2⟩, rfl⟩
    exact ⟨a, h2, h1⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, c, ⟨h, hj⟩, rfl⟩

section

variable {D : Diagram}

theorem leftEdge_le {i j c : ℤ} (hj : j ≤ i) (h : (j, c) ∈ D) : leftEdge D i ≤ c := by
  have hne : (columnsUpTo D i).Nonempty := ⟨c, mem_columnsUpTo.mpr ⟨j, hj, h⟩⟩
  simp only [leftEdge, hne, ↓reduceDIte]
  exact Finset.min'_le _ _ (mem_columnsUpTo.mpr ⟨j, hj, h⟩)

theorem exists_leftEdge {i : ℤ} (hne : (columnsUpTo D i).Nonempty) :
    ∃ j, j ≤ i ∧ (j, leftEdge D i) ∈ D := by
  simp only [leftEdge, hne, ↓reduceDIte]
  exact mem_columnsUpTo.mp (Finset.min'_mem _ hne)

theorem leftEdge_anti {i i' : ℤ} (hne : (columnsUpTo D i).Nonempty) (h : i ≤ i') :
    leftEdge D i' ≤ leftEdge D i := by
  obtain ⟨j, hj, hjD⟩ := exists_leftEdge hne
  exact leftEdge_le (hj.trans h) hjD

/-- In a skew set, a cell in a row above a nonempty row `i` lies at or right of the start of
row `i`. -/
theorem le_of_mem_above (hs : IsSkew D) {i j c : ℤ} (hrow : (columnsOfRow D i).Nonempty)
    (hj : j ≤ i) (h : (j, c) ∈ D) : (columnsOfRow D i).min' hrow ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  have hmem : (i, (columnsOfRow D i).min' hrow) ∈ D := mem_columnsOfRow.mp (Finset.min'_mem _ hrow)
  have := hs.mem h hmem hj hlt.le hj le_rfl le_rfl hlt.le
  exact absurd (Finset.min'_le _ _ (mem_columnsOfRow.mpr this)) (not_le.mpr hlt)

/-- In a skew set, a cell in a row below a nonempty row `i` lies left of the end of row `i`. -/
theorem lt_end_of_mem_below (hs : IsSkew D) {i j c : ℤ} (hrow : (columnsOfRow D i).Nonempty)
    (hj : i ≤ j) (h : (j, c) ∈ D) : c < (columnsOfRow D i).max' hrow + 1 := by
  by_contra hlt
  rw [not_lt] at hlt
  have hmem : (i, (columnsOfRow D i).max' hrow) ∈ D := mem_columnsOfRow.mp (Finset.max'_mem _ hrow)
  have := hs.mem hmem h hj (by omega) le_rfl hj (by omega) le_rfl
  have h2 := Finset.le_max' _ _ (mem_columnsOfRow.mpr this)
  omega

/-- In a skew set, a cell in a row above an empty row `i` lies right of the end of any nonempty
row below `i`. -/
theorem end_le_of_empty_between (hs : IsSkew D) {i i' j c : ℤ}
    (hempty : ¬ (columnsOfRow D i).Nonempty) (hi : i < i') (hrow : (columnsOfRow D i').Nonempty)
    (hj : j ≤ i) (h : (j, c) ∈ D) : (columnsOfRow D i').max' hrow + 1 ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  have hmem : (i', (columnsOfRow D i').max' hrow) ∈ D :=
    mem_columnsOfRow.mp (Finset.max'_mem _ hrow)
  have := hs.mem h hmem (by omega) (by omega) hj hi.le le_rfl (by omega)
  exact hempty ⟨c, mem_columnsOfRow.mpr this⟩

theorem leftEdge_eq_of_nonempty (hs : IsSkew D) {i : ℤ} (hrow : (columnsOfRow D i).Nonempty)
    (hup : (columnsUpTo D i).Nonempty) : leftEdge D i = (columnsOfRow D i).min' hrow := by
  refine le_antisymm ?_ ?_
  · exact leftEdge_le le_rfl (mem_columnsOfRow.mp (Finset.min'_mem _ hrow))
  · obtain ⟨j, hj, hjD⟩ := exists_leftEdge hup
    exact le_of_mem_above hs hrow hj hjD

end

section

variable {D : Diagram}

theorem columnsUpTo_nonempty (h0 : ∃ c, ((0 : ℤ), c) ∈ D) {i : ℤ} (hi : 0 ≤ i) :
    (columnsUpTo D i).Nonempty := by
  obtain ⟨c, hc⟩ := h0
  exact ⟨c, mem_columnsUpTo.mpr ⟨0, hi, hc⟩⟩

theorem leftEdge_le_rightEdge (hs : IsSkew D) (h0 : ∃ c, ((0 : ℤ), c) ∈ D) {i : ℤ} (hi : 0 ≤ i) :
    leftEdge D i ≤ rightEdge D i := by
  by_cases hr : (columnsOfRow D i).Nonempty
  · have hl := leftEdge_eq_of_nonempty hs hr (columnsUpTo_nonempty h0 hi)
    have := Finset.min'_le_max' (columnsOfRow D i) hr
    simp only [rightEdge, hr, ↓reduceDIte]
    omega
  · simp [rightEdge, hr]

theorem rightEdge_anti (hs : IsSkew D) (h0 : ∃ c, ((0 : ℤ), c) ∈ D) {i i' : ℤ} (hi : 0 ≤ i)
    (h : i ≤ i') : rightEdge D i' ≤ rightEdge D i := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  by_cases hr : (columnsOfRow D i).Nonempty <;> by_cases hr' : (columnsOfRow D i').Nonempty
  · have hm : (i', (columnsOfRow D i').max' hr') ∈ D :=
      mem_columnsOfRow.mp (Finset.max'_mem _ hr')
    have := lt_end_of_mem_below hs hr h hm
    simp only [rightEdge, hr, hr', ↓reduceDIte]
    omega
  · have ha : (i, (columnsOfRow D i).min' hr) ∈ D := mem_columnsOfRow.mp (Finset.min'_mem _ hr)
    have h1 := leftEdge_le h ha
    have h2 := Finset.min'_le_max' (columnsOfRow D i) hr
    simp only [rightEdge, hr, hr', ↓reduceDIte]
    omega
  · obtain ⟨j, hj, hjD⟩ := exists_leftEdge (columnsUpTo_nonempty h0 hi)
    have := end_le_of_empty_between hs hr hlt hr' hj hjD
    simp only [rightEdge, hr, hr', ↓reduceDIte]
    omega
  · have := leftEdge_anti (columnsUpTo_nonempty h0 hi) h
    simp only [rightEdge, hr, hr', ↓reduceDIte]
    exact this

end

/-- The diagram given by beta lists with `ℓ` rows that presents a skew cell set whose rows start
at row `0`: row `i` is `[μ_i, λ_i)`, and `ξ_i = λ_i - i`, `ζ_i = μ_i - i`. -/
def presentation {D : Diagram} (hs : IsSkew D) (h0 : ∃ c, ((0 : ℤ), c) ∈ D) (ℓ : ℕ) :
    BetaRows ℓ where
  xi i := rightEdge D i - i
  zeta i := leftEdge D i - i
  xi_lt i j hij _ := by
    have := rightEdge_anti hs h0 (i := (i : ℤ)) (i' := (j : ℤ)) (by positivity)
      (by exact_mod_cast hij.le)
    have hij' : (i : ℤ) < j := by exact_mod_cast hij
    omega
  zeta_lt i j hij _ := by
    have := leftEdge_anti (columnsUpTo_nonempty h0 (i := (i : ℤ)) (by positivity))
      (show (i : ℤ) ≤ j by exact_mod_cast hij.le)
    have hij' : (i : ℤ) < j := by exact_mod_cast hij
    omega
  zeta_le i _ := by
    have := leftEdge_le_rightEdge hs h0 (i := (i : ℤ)) (by positivity)
    omega

theorem cells_presentation {D : Diagram} (hs : IsSkew D) (h0 : ∃ c, ((0 : ℤ), c) ∈ D) {ℓ : ℕ}
    (hnn : ∀ x ∈ D, 0 ≤ x.1) (hℓ : ∀ x ∈ D, x.1 < ℓ) : (presentation hs h0 ℓ).cells = D := by
  ext ⟨x1, x2⟩
  constructor
  · intro hx
    obtain ⟨i, hi1, hiℓ, h1, h2⟩ := BetaRows.exists_mem_cells hx
    simp only at hi1
    subst hi1
    simp only [presentation] at h1 h2
    by_cases hr : (columnsOfRow D i).Nonempty
    · have hl := leftEdge_eq_of_nonempty hs hr
        (columnsUpTo_nonempty h0 (i := (i : ℤ)) (by positivity))
      simp only [rightEdge, hr, ↓reduceDIte] at h2
      have ha : ((i : ℤ), (columnsOfRow D i).min' hr) ∈ D :=
        mem_columnsOfRow.mp (Finset.min'_mem _ hr)
      have hm : ((i : ℤ), (columnsOfRow D i).max' hr) ∈ D :=
        mem_columnsOfRow.mp (Finset.max'_mem _ hr)
      exact hs.mem ha hm le_rfl (Finset.min'_le_max' _ hr) le_rfl le_rfl (by omega) (by omega)
    · simp only [rightEdge, hr, ↓reduceDIte] at h2
      omega
  · intro hx
    have h0x := hnn _ hx
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, x1 = i := ⟨x1.toNat, by omega⟩
    have hr : (columnsOfRow D i).Nonempty := ⟨x2, mem_columnsOfRow.mpr hx⟩
    have hiℓ := hℓ _ hx
    simp only at hiℓ
    refine BetaRows.mem_cells.mpr ⟨by exact_mod_cast hiℓ, ?_, ?_⟩
    · simp only [presentation]
      have := leftEdge_le (i := (i : ℤ)) le_rfl hx
      omega
    · simp only [presentation, rightEdge, hr, ↓reduceDIte]
      have := Finset.le_max' _ _ (mem_columnsOfRow.mpr hx)
      omega

/-- Every skew cell set has a presentation by beta lists, so `HasSchur` is satisfiable for every
skew diagram. -/
theorem exists_hasSchur_of_isSkew {D : Diagram} (hs : IsSkew D) : ∃ f, HasSchur D f := by
  by_cases hD : D = ∅
  · subst hD
    let B : BetaRows 0 :=
      { xi := fun _ => 0, zeta := fun _ => 0, xi_lt := fun _ _ _ h => absurd h (by omega),
        zeta_lt := fun _ _ _ h => absurd h (by omega), zeta_le := fun _ h => absurd h (by omega) }
    refine ⟨B.schur, 0, B, 0, ?_, rfl⟩
    rw [translate_zero]
    simp [BetaRows.cells]
  · have hne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD
    have hrows : (D.image Prod.fst).Nonempty := hne.image _
    set r0 := (D.image Prod.fst).min' hrows with hr0
    set N := (D.image Prod.fst).max' hrows with hN
    set w : ℤ × ℤ := (r0, 0) with hw
    have hmem : ∀ x : ℤ × ℤ, x ∈ translate (-w) D ↔ (x.1 + r0, x.2) ∈ D := by
      intro x
      rw [mem_translate]
      have : x - -w = (x.1 + r0, x.2) := by ext <;> simp [hw]
      rw [this]
    have hs0 : IsSkew (translate (-w) D) := isSkew_translate _ hs
    have hnn : ∀ x ∈ translate (-w) D, 0 ≤ x.1 := by
      intro x hx
      have := Finset.min'_le (D.image Prod.fst) _
        (Finset.mem_image_of_mem Prod.fst ((hmem x).mp hx))
      simp only at this
      omega
    have hℓ : ∀ x ∈ translate (-w) D, x.1 < (((N - r0).toNat + 1 : ℕ) : ℤ) := by
      intro x hx
      have := Finset.le_max' (D.image Prod.fst) _
        (Finset.mem_image_of_mem Prod.fst ((hmem x).mp hx))
      simp only at this
      push_cast
      omega
    have h0 : ∃ c, ((0 : ℤ), c) ∈ translate (-w) D := by
      obtain ⟨y, hy, hy1⟩ := Finset.mem_image.mp (Finset.min'_mem (D.image Prod.fst) hrows)
      refine ⟨y.2, (hmem (0, y.2)).mpr ?_⟩
      change (0 + r0, y.2) ∈ D
      rw [zero_add]
      have : y = (r0, y.2) := Prod.ext hy1 rfl
      rwa [← this]
    refine ⟨(presentation hs0 h0 ((N - r0).toNat + 1)).schur, (N - r0).toNat + 1,
      presentation hs0 h0 _, w, ?_, rfl⟩
    rw [cells_presentation hs0 h0 hnn hℓ, SkewGluing.translate_translate]
    simp [translate_zero]

end SkewBase
