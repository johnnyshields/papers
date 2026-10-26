/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Local.ComposeCoordinates

/-!
# Empty mark composition

TODO-COPIED: skew-factor-gluing/lean/SkewGluing/Local/EmptyMark.lean.
Proves connected skewness of actual empty-mark compositions for
`lem:row-amalgamation` in `shields-2026-skew-corner-descent.tex`,
«Marked inners and finite end caps».
Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- A legal empty mark. -/
def IsLegalEmpty (ω : MarkedInner) : Prop := ω.IsLegal ∧ ω.W = ∅

theorem IsLegalEmpty.width_zero (h : ω.IsLegalEmpty) : ω.widthZ = 0 := by
  have : ω.width = 0 := by simp [width, span, contents, h.2]
  simp [widthZ, this]

theorem IsLegalEmpty.isEmptyMark (h : ω.IsLegalEmpty) : ω.IsEmptyMark := by
  rcases h.1.1.2 with hm | hm
  · exact hm
  · exact absurd h.2 hm.1.ne_empty

theorem IsLegalEmpty.case_a (h : ω.IsLegalEmpty) : ω.case = .a := h.isEmptyMark.2.2

theorem IsLegalEmpty.shape (h : ω.IsLegalEmpty) : HasDiagonalShape ω.E :=
  isConnectedSkew_iff_diagonal.mp h.1.1.1

theorem IsLegalEmpty.span_eq (h : ω.IsLegalEmpty) : (span ω.E : ℤ) = ω.period := by
  have := h.1.1.span_eq
  have := h.width_zero
  unfold widthZ at this
  omega

theorem IsLegalEmpty.period_pos (h : ω.IsLegalEmpty) : 0 < ω.period := by
  have hp := h.1.2.2.1.2
  have hw := h.width_zero
  change (ω.width : ℤ) = 0 at hw
  omega

theorem IsLegalEmpty.mem_E (h : ω.IsLegalEmpty) {a r : ℤ} :
    ω.cell a r ∈ ω.E ↔
      0 ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a := by
  have hs := h.shape
  have := hs.mem_iff (k := minContent ω.E + a) (i := r)
  have hc := h.1.1.contents_eq
  have hw := h.width_zero
  rw [cell, this, hc, Finset.mem_Icc]
  unfold lo hi
  have hw2 : (ω.width : ℤ) = 0 := hw
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4⟩

theorem IsLegalEmpty.lo_le_hi (h : ω.IsLegalEmpty) {a : ℤ} (h1 : 0 ≤ a)
    (h2 : a ≤ ω.period - 1) : ω.lo a ≤ ω.hi a := by
  have hc := h.1.1.contents_eq
  have hw := h.width_zero
  have hw2 : (ω.width : ℤ) = 0 := hw
  have m1 : minContent ω.E + a ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  exact diagLo_le_diagHi m1

theorem IsLegalEmpty.bit_lo' (h : ω.IsLegalEmpty) {a b : ℤ} (hb : b = a + 1) (h1 : 0 ≤ a)
    (h2 : b ≤ ω.period - 1) : ω.lo a - ω.lo b = 0 ∨ ω.lo a - ω.lo b = 1 := by
  have hs := h.shape
  have hc := h.1.1.contents_eq
  have hw := h.width_zero
  have hw2 : (ω.width : ℤ) = 0 := hw
  have m1 : minContent ω.E + b ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have m2 : minContent ω.E + b - 1 ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have := (hs.2.2.2.1 _ m1 m2).1
  simp only [bitA, Finset.mem_insert, Finset.mem_singleton] at this
  have e : minContent ω.E + a = minContent ω.E + b - 1 := by omega
  simp only [lo, e]
  omega

theorem IsLegalEmpty.bit_hi' (h : ω.IsLegalEmpty) {a b : ℤ} (hb : b = a + 1) (h1 : 0 ≤ a)
    (h2 : b ≤ ω.period - 1) : ω.hi a - ω.hi b = 0 ∨ ω.hi a - ω.hi b = 1 := by
  have hs := h.shape
  have hc := h.1.1.contents_eq
  have hw := h.width_zero
  have hw2 : (ω.width : ℤ) = 0 := hw
  have m1 : minContent ω.E + b ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have m2 : minContent ω.E + b - 1 ∈ contents ω.E := by
    rw [hc, Finset.mem_Icc]; omega
  have := (hs.2.2.2.1 _ m1 m2).2
  simp only [bitB, Finset.mem_insert, Finset.mem_singleton] at this
  have e : minContent ω.E + a = minContent ω.E + b - 1 := by omega
  simp only [hi, e]
  omega

theorem IsLegalEmpty.ends (h : ω.IsLegalEmpty) :
    ω.lo 0 = ω.hi 0 ∧ ω.lo (ω.period - 1) = ω.hi (ω.period - 1) := by
  have hs := h.shape
  have hc := h.1.1.contents_eq
  have hw := h.width_zero
  have hq := h.period_pos
  have hw2 : (ω.width : ℤ) = 0 := hw
  constructor
  · have m1 : minContent ω.E + 0 ∈ contents ω.E := by
      rw [hc, Finset.mem_Icc]; omega
    have := hs.2.2.2.2 _ m1 (Or.inl (by rw [hc, Finset.mem_Icc]; omega))
    simpa [lo, hi] using this
  · have m1 : minContent ω.E + (ω.period - 1) ∈ contents ω.E := by
      rw [hc, Finset.mem_Icc]; omega
    have := hs.2.2.2.2 _ m1 (Or.inr (by rw [hc, Finset.mem_Icc]; omega))
    simpa [lo, hi] using this

theorem IsLegalEmpty.rowShift_eq (h : ω.IsLegalEmpty) :
    ω.rowShift = ω.lo (ω.period - 1) - ω.lo 0 := by
  have hv := h.isEmptyMark.2.1
  have hEne : ω.E.Nonempty := h.1.1.1.2.1
  have hsp := span_eq_of_isConnectedSkew h.1.1.1
  have h2 := h.span_eq
  have e : maxContent ω.E = minContent ω.E + (ω.period - 1) := by omega
  unfold rowShift lo
  rw [hv, vH]
  simp only [Prod.fst_add, Prod.fst_sub, ne, sw, e, add_zero]

theorem IsLegalEmpty.cell_mem_compose (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) {J a r : ℤ}
    (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ ω.compose D ↔
      minContent D ≤ J ∧ J ≤ maxContent D ∧ ω.oRowLo D J + ω.lo a ≤ r ∧
        r ≤ ω.oRowHi D J + ω.hi a := by
  have hq := h.period_pos
  have hw := h.width_zero
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, h.case_a]
  have hlh : ω.lo a ≤ ω.hi a := h.lo_le_hi ha0 (by omega)
  rw [compose_of_ordinary hD.2.1 hmix]
  constructor
  · rintro ⟨⟨d1, d2⟩, hd, hx⟩
    obtain ⟨j, rfl⟩ : ∃ j, d2 = d1 + j := ⟨d2 - d1, by ring⟩
    have hdc : content (d1, d1 + j) = j := by simp [content]
    have hd' := (mem_D hD).mp (show (d1, d1 + j) ∈ D from hd)
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst, hdc] at hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only at x3 x4
    rcases range_j (by omega) (by omega) ha0 haq (by omega) (J := J) (j := j)
      (by omega) (by omega) with hj | ⟨-, hj⟩
    · subst hj
      have e : j * ω.period + a - j * ω.period = a := by ring
      rw [e] at x3 x4
      have := (piece_iff (ω := ω) hD (r := r) (A := ω.lo a) (B := ω.hi a) hlh
        ⟨hd'.1, hd'.2.1⟩).mp ⟨d1, hd'.2.2.1, hd'.2.2.2, x3, x4⟩
      exact ⟨hd'.1, hd'.2.1, this.1, this.2⟩
    · omega
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨i, hi⟩ := (piece_iff (ω := ω) hD (r := r) (A := ω.lo a) (B := ω.hi a) hlh
      ⟨h1, h2⟩).mpr ⟨h3, h4⟩
    refine ⟨(i, i + J), (mem_D hD).mpr ⟨h1, h2, hi.1, hi.2.1⟩, ?_⟩
    have hdc : content (i, i + J) = J := by simp [content]
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst, hdc]
    have e : J * ω.period + a - J * ω.period = a := by ring
    rw [e]
    exact ⟨ha0, by omega, hi.2.2.1, hi.2.2.2⟩

/-- The diagonal classes of the composite of the empty mark. -/
theorem IsLegalEmpty.classRows (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) :
    ClassRows (ω.compose D) (minContent ω.E) ω.period ω.widthZ (minContent D) (maxContent D)
      (fun J a => ω.oRowLo D J + ω.lo a) (fun J a => ω.oRowHi D J + ω.hi a) := by
  have hq := h.period_pos
  have hw := h.width_zero
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hp := h.rowShift_eq
  have hends := h.ends
  have hcase : ω.case = .a := h.case_a
  have hR : ∀ J, ω.oRowLo D J = J * ω.rowShift + diagLo D J ∧
      ω.oRowHi D J = J * ω.rowShift + diagHi D J := by
    intro J; simp [oRowLo, oRowHi, hcase]
  have hc : ClassRows (ω.compose D) (minContent ω.E) ω.period ω.widthZ (minContent D)
      (maxContent D) (fun J a => ω.oRowLo D J + ω.lo a) (fun J a => ω.oRowHi D J + ω.hi a) := by
    refine ⟨hq, by omega, by omega, hmM, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro J a r h0 h1
      change ω.cell (J * ω.period + a) r ∈ ω.compose D ↔ _
      rw [h.cell_mem_compose hD h0 h1]
      unfold ValidClass
      constructor
      · rintro ⟨x1, x2, x3, x4⟩; exact ⟨Or.inl ⟨x1, x2⟩, x3, x4⟩
      · rintro ⟨x1 | x1, x3, x4⟩
        · exact ⟨x1.1, x1.2, x3, x4⟩
        · omega
    · intro J a h0 h1 hv
      have hJ : minContent D ≤ J ∧ J ≤ maxContent D := by unfold ValidClass at hv; omega
      have := oRow_le (ω := ω) hD hJ
      have := h.lo_le_hi h0 (by omega : a ≤ ω.period - 1)
      omega
    · intro J a h1 h2 hv
      have b1 := h.bit_lo' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
      have b2 := h.bit_hi' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
      omega
    · intro J hv1 hv2
      have hJ : minContent D ≤ J ∧ J ≤ maxContent D := by unfold ValidClass at hv1; omega
      have hJ1 : minContent D ≤ J + 1 ∧ J + 1 ≤ maxContent D := by unfold ValidClass at hv2; omega
      have hb := D_bits hD (J := J + 1) (by omega) hJ1.2
      simp only [add_sub_cancel_right] at hb
      have hp2 : (J + 1) * ω.rowShift = J * ω.rowShift + ω.rowShift := by ring
      have r1 := hR J
      have r2 := hR (J + 1)
      constructor <;> omega
    · have := (hR (minContent D))
      have := D_ends hD
      omega
    · intro h0; omega
    · intro _
      have := hR (maxContent D)
      have := D_ends hD
      omega
  exact hc


/-- Actual composition with every connected outer is connected skew. -/
theorem IsLegalEmpty.isConnectedSkew_compose (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) :
    IsConnectedSkew (ω.compose D) :=
  (h.classRows hD).isConnectedSkew

end MarkedInner
end SkewGluing
