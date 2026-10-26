import SkewGluing.Local.Caps
import SkewGluing.Local.Assemble

/-!
# The rows of a composite diagram

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3),
via `eq:gluing-offsets`).

For a connected outer `D` with contents `[m, M]` and diagonal rows `[dl j, dh j]`, the copy of `E`
placed at the cell `d = (i, i + j)` has origin row `originRow ω D j i`.  Over the cells of the
diagonal `j` of `D` these rows form the interval `[oRowLo j, oRowHi j]`, so the cells of the
composite on the diagonal of relative content `J q + a` are described by two or three row
intervals (the copy `J`, the copy `J - 1`, and in the mixed cases the supplemental copy).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner}

/-- The row of the origin `L_ω(d)` for the cell `d = (i, i + j)` of `D`, by `eq:gluing-offsets`. -/
def originRow (ω : MarkedInner) (D : Diagram) (j i : ℤ) : ℤ :=
  match ω.case with
  | .a => j * ω.rowShift + i
  | .b => j * ω.rowShift - i
  | .c => j * ω.rowShift + (i - diagLo D j)
  | .d => j * ω.rowShift - (diagHi D j - i)

/-- The least origin row over the diagonal `j` of `D`. -/
def oRowLo (ω : MarkedInner) (D : Diagram) (j : ℤ) : ℤ :=
  match ω.case with
  | .a => j * ω.rowShift + diagLo D j
  | .b => j * ω.rowShift - diagHi D j
  | .c => j * ω.rowShift
  | .d => j * ω.rowShift - (diagHi D j - diagLo D j)

/-- The greatest origin row over the diagonal `j` of `D`. -/
def oRowHi (ω : MarkedInner) (D : Diagram) (j : ℤ) : ℤ :=
  match ω.case with
  | .a => j * ω.rowShift + diagHi D j
  | .b => j * ω.rowShift - diagLo D j
  | .c => j * ω.rowShift + (diagHi D j - diagLo D j)
  | .d => j * ω.rowShift

theorem origin_fst (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) :
    (ω.origin D d).1 = ω.originRow D (content d) d.1 := by
  unfold origin originRow
  cases ω.case <;> simp [rowShift, eCell, content]

theorem cell_sub_origin (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) (k r : ℤ) :
    ω.cell k r - ω.origin D d =
      ω.cell (k - content d * ω.period) (r - (ω.origin D d).1) := by
  have hc := content_origin ω D d
  unfold content at hc
  unfold cell
  ext
  · simp
  · simp only [Prod.snd_sub, content]; omega

variable {D : Diagram}

theorem mem_D (hD : IsConnectedSkew D) {i j : ℤ} :
    (i, i + j) ∈ D ↔ minContent D ≤ j ∧ j ≤ maxContent D ∧ diagLo D j ≤ i ∧ i ≤ diagHi D j := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  rw [hs.mem_iff, hs.mem_contents_iff]
  tauto

theorem IsLegalNonempty.mem_main (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) {k r : ℤ} :
    (∃ d ∈ D, ω.cell k r ∈ translate (ω.origin D d) ω.E) ↔
      ∃ j i, minContent D ≤ j ∧ j ≤ maxContent D ∧ diagLo D j ≤ i ∧ i ≤ diagHi D j ∧
        0 ≤ k - j * ω.period ∧ k - j * ω.period ≤ ω.period + ω.widthZ - 1 ∧
        ω.lo (k - j * ω.period) ≤ r - ω.originRow D j i ∧
        r - ω.originRow D j i ≤ ω.hi (k - j * ω.period) := by
  constructor
  · rintro ⟨d, hd, hx⟩
    obtain ⟨d1, d2⟩ := d
    have hdc : content (d1, d2) = d2 - d1 := rfl
    have hd' : (d1, d1 + (d2 - d1)) ∈ D := by simpa using hd
    rw [mem_D hD] at hd'
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst] at hx
    simp only [hdc] at hx
    exact ⟨d2 - d1, d1, hd'.1, hd'.2.1, hd'.2.2.1, hd'.2.2.2, by omega,
      by omega, by omega, by omega⟩
  · rintro ⟨j, i, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨(i, i + j), (mem_D hD).mpr ⟨h1, h2, h3, h4⟩, ?_⟩
    have hdc : content (i, i + j) = j := by simp [content]
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst, hdc]
    exact ⟨h5, h6, h7, h8⟩

theorem range_j {q w J j a : ℤ} (hq : 0 < q) (hwq : w < q) (h0 : 0 ≤ a) (h1 : a < q)
    (_hw : 0 ≤ w) (h2 : 0 ≤ J * q + a - j * q) (h3 : J * q + a - j * q ≤ q + w - 1) :
    j = J ∨ (j = J - 1 ∧ a < w) := by
  by_cases hj : j ≤ J - 2
  · have := mul_le_mul_of_nonneg_right hj hq.le
    nlinarith
  · by_cases hj1 : J + 1 ≤ j
    · have := mul_le_mul_of_nonneg_right hj1 hq.le
      nlinarith
    · by_cases hj2 : j = J
      · exact Or.inl hj2
      · have : j = J - 1 := by omega
        subst this
        right
        refine ⟨rfl, ?_⟩
        have : (J - 1) * q = J * q - q := by ring
        omega

/-- The rows of the copies of `E` at the diagonal `j` of `D`, on the diagonal of `E` of relative
content `b`, when `lo b ≤ hi b`, form the interval `[oRowLo j + ℓ_b, oRowHi j + h_b]`. -/
theorem piece_iff (hD : IsConnectedSkew D) {j A B r : ℤ} (hA : A ≤ B)
    (hj : minContent D ≤ j ∧ j ≤ maxContent D) :
    (∃ i, diagLo D j ≤ i ∧ i ≤ diagHi D j ∧ A ≤ r - ω.originRow D j i ∧
      r - ω.originRow D j i ≤ B) ↔ ω.oRowLo D j + A ≤ r ∧ r ≤ ω.oRowHi D j + B := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hne : diagLo D j ≤ diagHi D j := diagLo_le_diagHi (hs.mem_contents_iff.mpr hj)
  unfold originRow oRowLo oRowHi
  cases ω.case
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (r - j * ω.rowShift - B), by omega, by omega, by omega, by omega⟩
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (A + j * ω.rowShift - r), by omega, by omega, by omega, by omega⟩
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (r - j * ω.rowShift + diagLo D j - B), by omega, by omega, by omega,
        by omega⟩
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (r - j * ω.rowShift + diagHi D j - B), by omega, by omega, by omega,
        by omega⟩


/-- The composite of an ordinary mark: on the diagonal of relative content `J q + a`
(`0 ≤ a < q`), the rows of the copy `J` (the interval `P₁`) together with those of the copy
`J - 1` on the diagonal `a + q` of `E` (the interval `P₂`, present only for `a < w`). -/
theorem IsLegalNonempty.cell_mem_compose_ord (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hmix : ¬ ω.case.IsMixed) {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ ω.compose D ↔
      (minContent D ≤ J ∧ J ≤ maxContent D ∧ ω.oRowLo D J + ω.lo a ≤ r ∧
        r ≤ ω.oRowHi D J + ω.hi a) ∨
      (a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D ∧
        ω.oRowLo D (J - 1) + ω.lo (a + ω.period) ≤ r ∧
        r ≤ ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [cell, compose_of_ordinary hD.2.1 hmix]
  have key := h.mem_main hD (k := J * ω.period + a) (r := r)
  unfold cell at key
  rw [key]
  have hlh : ∀ b, 0 ≤ b → b ≤ ω.period + ω.widthZ - 1 → ω.lo b ≤ ω.hi b :=
    fun b h1 h2 => h.lo_le_hi h1 h2
  constructor
  · rintro ⟨j, i, h1, h2, h3, h4, h5, h6, h7, h8⟩
    rcases range_j (by omega) hq ha0 haq (by omega) h5 h6 with rfl | ⟨rfl, hl⟩
    · left
      have e : j * ω.period + a - j * ω.period = a := by ring
      rw [e] at h7 h8
      have := (piece_iff (ω := ω) hD (r := r) (A := ω.lo a) (B := ω.hi a)
        (hlh a ha0 (by omega)) ⟨h1, h2⟩).mp ⟨i, h3, h4, h7, h8⟩
      exact ⟨h1, h2, this.1, this.2⟩
    · right
      have e : J * ω.period + a - (J - 1) * ω.period = a + ω.period := by ring
      rw [e] at h7 h8
      have := (piece_iff (ω := ω) hD (r := r) (A := ω.lo (a + ω.period))
        (B := ω.hi (a + ω.period)) (hlh _ (by omega) (by omega)) ⟨h1, h2⟩).mp
        ⟨i, h3, h4, h7, h8⟩
      exact ⟨hl, h1, h2, this.1, this.2⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨hl, h1, h2, h3, h4⟩)
    · obtain ⟨i, hi⟩ := (piece_iff (ω := ω) hD (r := r) (A := ω.lo a) (B := ω.hi a)
        (hlh a ha0 (by omega)) ⟨h1, h2⟩).mpr ⟨h3, h4⟩
      have e : J * ω.period + a - J * ω.period = a := by ring
      refine ⟨J, i, h1, h2, hi.1, hi.2.1, by omega, by omega, ?_, ?_⟩
      · rw [e]; exact hi.2.2.1
      · rw [e]; exact hi.2.2.2
    · obtain ⟨i, hi⟩ := (piece_iff (ω := ω) hD (r := r) (A := ω.lo (a + ω.period))
        (B := ω.hi (a + ω.period)) (hlh _ (by omega) (by omega)) ⟨h1, h2⟩).mpr ⟨h3, h4⟩
      have e : J * ω.period + a - (J - 1) * ω.period = a + ω.period := by ring
      refine ⟨J - 1, i, h1, h2, hi.1, hi.2.1, by rw [e]; omega, by rw [e]; omega, ?_, ?_⟩
      · rw [e]; exact hi.2.2.1
      · rw [e]; exact hi.2.2.2
end MarkedInner

end SkewGluing
