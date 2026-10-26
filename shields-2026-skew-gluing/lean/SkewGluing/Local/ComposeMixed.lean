import SkewGluing.Local.ComposeOrd

/-!
# The supplemental copies of a case-(d) composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3),
`eq:gluing-offsets` and `eq:gluing-mixed-profile`).

In case (d) a vertical pair of cells of `D` on the same southeast boundary ribbon contributes the
supplemental copy `W₊ + L_ω(d) - e`, where `d` is the lower cell of the pair.  This file computes
the rows that these copies contribute on each diagonal class, and the rows of the whole composite.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem supplementalShift_d (hc : ω.case = .d) : ω.supplementalShift = -eCell := by
  simp [supplementalShift, hc]

theorem IsLegalNonempty.mem_suppCell (h : ω.IsLegalNonempty) (hc : ω.case = .d) (d : ℤ × ℤ)
    (k r : ℤ) :
    ω.cell k r ∈ translate (ω.origin D d + ω.supplementalShift) ω.upper ↔
      ω.cell (k - content d * ω.period - ω.period) (r - (ω.origin D d).1 + 1 - ω.rowShift) ∈
        ω.W := by
  rw [mem_translate]
  have hco := content_origin ω D d
  unfold content at hco
  have e : ω.cell k r - (ω.origin D d + ω.supplementalShift) =
      ω.cell (k - content d * ω.period - ω.period + ω.period) (r - (ω.origin D d).1 + 1) := by
    rw [supplementalShift_d hc]
    unfold cell eCell
    ext
    · simp only [Prod.fst_sub, Prod.fst_add, Prod.fst_neg]; ring
    · simp only [Prod.snd_sub, Prod.snd_add, Prod.snd_neg, content] at hco ⊢; omega
  rw [e, h.mem_upper]


theorem range_j' {q w J j a : ℤ} (hq : 0 < q) (hwq : w < q) (h0 : 0 ≤ a) (h1 : a < q)
    (h2 : 0 ≤ J * q + a - j * q - q) (h3 : J * q + a - j * q - q ≤ w - 1) : j = J - 1 := by
  by_cases hj : j ≤ J - 2
  · have := mul_le_mul_of_nonneg_right hj hq.le
    nlinarith
  · by_cases hj1 : J ≤ j
    · have := mul_le_mul_of_nonneg_right hj1 hq.le
      nlinarith
    · omega

/-- The supplemental copies of case (d) on the class `(J, a)`: the vertical pairs `(d, d')` of `D`
on the diagonals `J - 1`, `J` that lie on one southeast ribbon (`h_J = h_{J-1} - 1`) contribute
the rows `[J p - h_{J-1} + ℓ_J + ŵ_a, J p + w̌_a - 1]`, where `[ŵ_a, w̌_a]` are the rows of `W₋`
on the diagonal `a`. -/
theorem IsLegalNonempty.mem_supp_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hc : ω.case = .d) {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    (∃ d ∈ D, ω.SameRibbon D d ∧
      ω.cell (J * ω.period + a) r ∈ translate (ω.origin D d + ω.supplementalShift) ω.upper) ↔
    (a < ω.widthZ ∧ minContent D + 1 ≤ J ∧ J ≤ maxContent D ∧
      diagHi D (J - 1) - diagHi D J = 1 ∧
      J * ω.rowShift - diagHi D (J - 1) + diagLo D J +
        max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift) ≤ r ∧
      r ≤ J * ω.rowShift + min (ω.hi a) (ω.hi (a + ω.period) - ω.rowShift) - 1) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  constructor
  · rintro ⟨⟨d1, d2⟩, hd, hsr, hx⟩
    obtain ⟨j, rfl⟩ : ∃ j, d2 = d1 + j := ⟨d2 - d1, by ring⟩
    have hdc : content (d1, d1 + j) = j := by simp [content]
    simp only [SameRibbon, hc, hdc] at hsr
    rw [h.mem_suppCell hc, origin_fst, hdc, h.mem_W] at hx
    have hd' := (mem_D hD).mp (show (d1, d1 + j) ∈ D from hd)
    have hn : (d1 - 1, d1 + j) = (d1 - 1, d1 - 1 + (j + 1)) :=
      Prod.ext rfl (by ring)
    have hn' := (mem_D hD).mp (show (d1 - 1, d1 - 1 + (j + 1)) ∈ D by rw [← hn]; exact hsr.1)
    have hJ := range_j' (J := J) (j := j) (q := ω.period) (w := ω.widthZ) (by omega) hq ha0 haq
      (by simp only [originRow] at hx; omega) (by simp only [originRow] at hx; omega)
    obtain rfl : J = j + 1 := by omega
    have e1 : (j + 1) * ω.period + a - j * ω.period - ω.period = a := by ring
    have e2 : (j + 1) * ω.rowShift = j * ω.rowShift + ω.rowShift := by ring
    simp only [originRow, hc, e1] at hx
    simp only [add_sub_cancel_right]
    have hs := hsr.2
    have hs' : diagHi D j - d1 = diagHi D (j + 1) - (d1 - 1) := hs
    obtain ⟨x0, x1, x2, x3, x4, x5⟩ := hx
    refine ⟨by omega, by omega, hn'.2.1, by omega, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨hl, hJ1, hJ2, hB, hr1, hr2⟩
    obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row ha0 (by omega : a ≤ ω.widthZ - 1)
    have hlo : minContent D ≤ J - 1 := by omega
    have hsD := isConnectedSkew_iff_diagonal.mp hD
    have hb := D_bits hD hJ1 hJ2
    have hdlh := diagLo_le_diagHi (hsD.mem_contents_iff.mpr ⟨by omega, hJ2⟩ : J ∈ contents D)
    obtain ⟨i, hi⟩ : ∃ i, i = max (diagLo D J + 1) (r - J * ω.rowShift + diagHi D (J - 1) + 1 -
        min (ω.hi a) (ω.hi (a + ω.period) - ω.rowShift)) := ⟨_, rfl⟩
    have hi1 : diagLo D J + 1 ≤ i := by omega
    have hi2 : i ≤ diagHi D (J - 1) := by omega
    have hi3 : r - J * ω.rowShift + diagHi D (J - 1) + 1 - min (ω.hi a)
        (ω.hi (a + ω.period) - ω.rowShift) ≤ i := by omega
    have hi4 : i ≤ r - J * ω.rowShift + diagHi D (J - 1) + 1 - max (ω.lo a)
        (ω.lo (a + ω.period) - ω.rowShift) := by omega
    have hdc : content (i, i + (J - 1)) = J - 1 := by simp [content]
    have e1 : J * ω.period + a - (J - 1) * ω.period - ω.period = a := by ring
    have e2 : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
    refine ⟨(i, i + (J - 1)), (mem_D hD).mpr ⟨hlo, by omega, by omega, hi2⟩, ?_, ?_⟩
    · simp only [SameRibbon, hc, hdc, sub_add_cancel]
      refine ⟨?_, by omega⟩
      have hn : (i - 1, i + (J - 1)) = (i - 1, i - 1 + J) :=
        Prod.ext rfl (by ring)
      rw [hn]
      exact (mem_D hD).mpr ⟨by omega, hJ2, by omega, by omega⟩
    · rw [h.mem_suppCell hc, origin_fst, hdc, h.mem_W]
      simp only [originRow, hc, e1]
      refine ⟨ha0, by omega, by omega, by omega, by omega, by omega⟩


theorem IsLegalNonempty.mem_main_class (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) {J a r : ℤ}
    (ha0 : 0 ≤ a) (haq : a < ω.period) :
    (∃ d ∈ D, ω.cell (J * ω.period + a) r ∈ translate (ω.origin D d) ω.E) ↔
      (minContent D ≤ J ∧ J ≤ maxContent D ∧ ω.oRowLo D J + ω.lo a ≤ r ∧
        r ≤ ω.oRowHi D J + ω.hi a) ∨
      (a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D ∧
        ω.oRowLo D (J - 1) + ω.lo (a + ω.period) ≤ r ∧
        r ≤ ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.mem_main hD]
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

/-- The rows of the case-(d) composite on the class `(J, a)`: the copy `J`, the copy `J - 1`
(for `a < w`) and the supplemental copy. -/
theorem IsLegalNonempty.cell_mem_compose_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hc : ω.case = .d) {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ ω.compose D ↔
      (minContent D ≤ J ∧ J ≤ maxContent D ∧ ω.oRowLo D J + ω.lo a ≤ r ∧
        r ≤ ω.oRowHi D J + ω.hi a) ∨
      (a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D ∧
        ω.oRowLo D (J - 1) + ω.lo (a + ω.period) ≤ r ∧
        r ≤ ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) ∨
      (a < ω.widthZ ∧ minContent D + 1 ≤ J ∧ J ≤ maxContent D ∧
        diagHi D (J - 1) - diagHi D J = 1 ∧
        J * ω.rowShift - diagHi D (J - 1) + diagLo D J +
          max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift) ≤ r ∧
        r ≤ J * ω.rowShift + min (ω.hi a) (ω.hi (a + ω.period) - ω.rowShift) - 1) := by
  rw [cell, mem_compose hD.2.1]
  have e1 := h.mem_main_class hD (J := J) (r := r) ha0 haq
  have e2 := h.mem_supp_d hD hc (J := J) (r := r) ha0 haq
  unfold cell at e1 e2
  rw [e1, e2, or_assoc]

end MarkedInner

end SkewGluing
