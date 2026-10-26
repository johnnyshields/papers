/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.CaseDNorthwest
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MarkFacts.HatMark
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Pieces

/-!
# The strip remainder of a case-(d) row power

The identification (3.7) of `shields-2026-skew-marked-factor.tex`, in the proof of «Mixed weighted
covariance» (`rt:mixed-covariance`): deleting the northwest border segment of `k p` cells that
starts at content `(m - k) p + s` from `F_m = Row_m ∘_η E` leaves the disjoint union of
`F_{m-k}`, the translates `Ô + j v + e` for `m - k ≤ j < m` and the translates
`Ŵ + j v + e` for `m - k < j ≤ m`.  The pieces are separated by at least two contents, so the
Schur function of the remainder is `s_{F_{m-k}} (s_Ô s_Ŵ)^k`.
-/

namespace SkewMarkedFactor
open Gluing Gluing.MarkedInner Gluing.Plan

section Hats

variable {η : MarkedInner}

/-- The hatted middle in cell coordinates: it lives on the diagonals `w + 1, …, p - 2`, on the
rows of `E` that have a successor on the same diagonal. -/
theorem mem_hatMiddleFin_cell (h : η.IsLegalNonempty) {a r : ℤ} :
    η.cell a r ∈ hatMiddleFin η ↔
      η.widthZ + 1 ≤ a ∧ a ≤ η.period - 2 ∧ η.lo a ≤ r ∧ r ≤ η.hi a - 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold hatMiddleFin
  rw [Finset.mem_filter, cell_add_e]
  constructor
  · rintro ⟨hx, hx'⟩
    have hne : η.cell a r ≠ η.cell a (r + 1) := by
      intro he
      have := (η.cell_inj he).2
      omega
    have hrange : η.widthZ ≤ a ∧ a < η.period := by
      by_contra hcon
      apply hne
      refine h.middle_thin hx hx' (by rw [content_cell, content_cell]) ?_
      rw [content_cell]
      omega
    have e1 := (h.mem_middle_private hrange.1 hrange.2).mp hx
    have e2 := (h.mem_middle_private hrange.1 hrange.2).mp hx'
    have s1 := h.lo_w_eq_hi_w
    have s2 := h.lo_pred_period_eq_hi
    have : a ≠ η.widthZ := by
      rintro rfl; omega
    have : a ≠ η.period - 1 := by
      rintro rfl; omega
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(h.mem_middle_private (by omega) (by omega)).mpr ⟨h3, by omega⟩,
      (h.mem_middle_private (by omega) (by omega)).mpr ⟨by omega, by omega⟩⟩

/-- The hatted mark in cell coordinates, case (d): on each marked diagonal `a`, the rows
`[ℓ_a - [a < t], h_a - 1]`. -/
theorem mem_hatMarkFin_cell (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) {a r : ℤ} :
    η.cell a r ∈ hatMarkFin η ↔
      0 ≤ a ∧ a ≤ η.widthZ - 1 ∧ η.lo a - (if a < t then 1 else 0) ≤ r ∧
        r ≤ η.hi a - 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.hatMarkFin_eq, hatBand, Finset.mem_filter, Finset.mem_filter, cell_add_e,
    content_cell]
  constructor
  · rintro ⟨⟨hx, hx'⟩, hb1, hb2⟩
    have ha0 : 0 ≤ a := by omega
    have ha1 : a ≤ η.widthZ - 1 := by omega
    have fa := d_E_facts h hd hph ha0 ha1
    rw [h.mem_amalgam_cell] at hx hx'
    simp only [dLo, dHi] at fa
    refine ⟨ha0, ha1, ?_, ?_⟩
    · split_ifs with hat
      · omega
      · omega
    · omega
  · rintro ⟨ha0, ha1, h3, h4⟩
    have fa := d_E_facts h hd hph ha0 ha1
    simp only [dLo, dHi] at fa
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩ <;> rw [h.mem_amalgam_cell]
    · split_ifs at h3 with hat <;> omega
    · split_ifs at h3 with hat <;> omega

end Hats

section RowPowerCells

variable {η : MarkedInner} {m : ℕ}

/-- The cells of the case-(d) row power in the coordinates `(J p + a, r)` of the least content:
on a class `(J, a)` the rows run from the first row of `diagLo_rowPower` to `J v₁ + h_a`. -/
theorem mem_rowPower_cell (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {J a r : ℤ} (ha0 : 0 ≤ a)
    (haq : a < η.period) :
    η.cell (J * η.period + a) r ∈ η.compose (rowCells 0 m) ↔
      ((0 ≤ J ∧ J ≤ (m : ℤ) - 1) ∨ (J = m ∧ a < η.widthZ)) ∧
        J * η.rowShift + η.lo a - (if 1 ≤ J ∧ a < t then 1 else 0) +
          (if J = m ∧ s ≤ a then 1 else 0) ≤ r ∧ r ≤ J * η.rowShift + η.hi a := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hmin := minContent_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hmax := maxContent_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hcr := mix_classRows h hD hd hph hlt
  rw [hmin, hmax] at hcr
  have hrows := hcr.rows J a r ha0 haq
  have hcell : η.cell (J * η.period + a) r = (r, r + (minContent η.E + (J * η.period + a))) := rfl
  rw [hcell, hrows]
  unfold ValidClass
  constructor
  · rintro ⟨hv, h1, h2⟩
    have hv' : (0 ≤ J ∧ J ≤ (m : ℤ) - 1) ∨ (J = m ∧ a < η.widthZ) := by
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr ⟨by omega, hv.2⟩
    have hl := diagLo_rowPower h hd hph hlt hm ha0 haq hv'
    have hv2 : ValidClass 0 ((m : ℤ) - 1) η.widthZ J a := hv
    rw [hcr.diagLo_eq ha0 haq hv2] at hl
    exact ⟨hv', by rw [← hl]; exact h1, h2⟩
  · rintro ⟨hv', h1, h2⟩
    have hv : ValidClass 0 ((m : ℤ) - 1) η.widthZ J a := by
      unfold ValidClass
      rcases hv' with hv | hv
      · exact Or.inl hv
      · exact Or.inr ⟨by omega, hv.2⟩
    have hl := diagLo_rowPower h hd hph hlt hm ha0 haq hv'
    rw [hcr.diagLo_eq ha0 haq hv] at hl
    exact ⟨hv, by rw [hl]; exact h1, h2⟩

theorem compose_rowCells_zero (η : MarkedInner) : η.compose (rowCells 0 0) = η.W := by
  have : rowCells 0 (0 : ℤ) = ∅ := by
    ext x; simp [rowCells]
  simp [this, MarkedInner.compose]

/-- If `J p + a` lies in `[0, p)` with `0 ≤ a < p`, then `J = 0`. -/
theorem class_zero {p J a : ℤ} (hp : 0 < p) (ha0 : 0 ≤ a) (hap : a < p)
    (h0 : 0 ≤ J * p + a) (h1 : J * p + a < p) : J = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · nlinarith
  · nlinarith

/-- The lower copy `W` is the zeroth row power: it has the same cell description. -/
theorem mem_W_cell (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < η.period) :
    η.cell (J * η.period + a) r ∈ η.W ↔
      J = 0 ∧ a < η.widthZ ∧ η.lo a + (if s ≤ a then 1 else 0) ≤ r ∧ r ≤ η.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.mem_W]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    have hJ : J = 0 := class_zero (by omega) ha0 haq h0 (by omega)
    subst hJ
    have fa := d_E_facts h hd hph (a := a) (by omega) (by omega)
    simp only [dLo, dHi] at fa
    simp only [zero_mul, zero_add] at h2 h3 h4 h5
    refine ⟨rfl, by omega, ?_, by omega⟩
    split_ifs with hs <;> omega
  · rintro ⟨rfl, h1, h2, h3⟩
    have fa := d_E_facts h hd hph (a := a) ha0 (by omega)
    simp only [dLo, dHi] at fa
    simp only [zero_mul, zero_add]
    refine ⟨ha0, by omega, ?_, h3, ?_, ?_⟩
    · split_ifs at h2 <;> omega
    · split_ifs at h2 with hs <;> omega
    · omega

/-- `mem_rowPower_cell`, including the zeroth power `W`. -/
theorem mem_rowPower_cell' (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (m : ℕ) {J a r : ℤ} (ha0 : 0 ≤ a)
    (haq : a < η.period) :
    η.cell (J * η.period + a) r ∈ η.compose (rowCells 0 m) ↔
      ((0 ≤ J ∧ J ≤ (m : ℤ) - 1) ∨ (J = m ∧ a < η.widthZ)) ∧
        J * η.rowShift + η.lo a - (if 1 ≤ J ∧ a < t then 1 else 0) +
          (if J = m ∧ s ≤ a then 1 else 0) ≤ r ∧ r ≤ J * η.rowShift + η.hi a := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : ((0 : ℕ) : ℤ) = 0 := rfl
    rw [e, compose_rowCells_zero, mem_W_cell h hd hph ha0 haq]
    constructor
    · rintro ⟨rfl, h1, h2, h3⟩
      refine ⟨Or.inr ⟨rfl, h1⟩, ?_, ?_⟩
      · simpa using h2
      · simpa using h3
    · rintro ⟨hv, h2, h3⟩
      have hJ : J = 0 := by
        rcases hv with hv | hv
        · omega
        · exact hv.1
      subst hJ
      refine ⟨rfl, ?_, ?_, ?_⟩
      · rcases hv with hv | hv <;> omega
      · simpa using h2
      · simpa using h3
  · exact mem_rowPower_cell h hd hph hlt hm ha0 haq

end RowPowerCells



section Translates

variable {η : MarkedInner}

theorem cell_sub_vE (η : MarkedInner) (j A r : ℤ) :
    η.cell A r - (j • η.v + eCell) = η.cell (A - j * η.period) (r - j * η.rowShift - 1) := by
  have hv := η.v_eq
  unfold cell
  ext
  · rw [hv]; simp [eCell]; ring
  · rw [hv]; simp [eCell]; ring

/-- The translate of the hatted middle by `j v + e`, in cell coordinates. -/
theorem mem_translate_hatMiddle_cell (h : η.IsLegalNonempty) {J a r j : ℤ} (ha0 : 0 ≤ a)
    (haq : a < η.period) :
    η.cell (J * η.period + a) r ∈ translate (j • η.v + eCell) (hatMiddleFin η) ↔
      J = j ∧ η.widthZ + 1 ≤ a ∧ a ≤ η.period - 2 ∧ η.lo a ≤ r - j * η.rowShift - 1 ∧
        r - j * η.rowShift - 1 ≤ η.hi a - 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [mem_translate, cell_sub_vE, mem_hatMiddleFin_cell h]
  have e : J * η.period + a - j * η.period = (J - j) * η.period + a := by ring
  rw [e]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hJ : J - j = 0 := class_zero (by omega) ha0 haq (by omega) (by omega)
    have hJ' : J = j := by omega
    subst hJ'
    simp only [sub_self, zero_mul, zero_add] at h3 h4
    exact ⟨rfl, by omega, by omega, h3, h4⟩
  · rintro ⟨rfl, h1, h2, h3, h4⟩
    simp only [sub_self, zero_mul, zero_add]
    exact ⟨h1, h2, h3, h4⟩

/-- The translate of the hatted mark by `j v + e`, in cell coordinates. -/
theorem mem_translate_hatMark_cell (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) {J a r j : ℤ} (ha0 : 0 ≤ a) (haq : a < η.period) :
    η.cell (J * η.period + a) r ∈ translate (j • η.v + eCell) (hatMarkFin η) ↔
      J = j ∧ a ≤ η.widthZ - 1 ∧ η.lo a - (if a < t then 1 else 0) ≤ r - j * η.rowShift - 1 ∧
        r - j * η.rowShift - 1 ≤ η.hi a - 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [mem_translate, cell_sub_vE, mem_hatMarkFin_cell h hd hph]
  have e : J * η.period + a - j * η.period = (J - j) * η.period + a := by ring
  rw [e]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hJ : J - j = 0 := class_zero (by omega) ha0 haq (by omega) (by omega)
    have hJ' : J = j := by omega
    subst hJ'
    simp only [sub_self, zero_mul, zero_add] at h3 h4
    exact ⟨rfl, by omega, h3, h4⟩
  · rintro ⟨rfl, h1, h2, h3⟩
    simp only [sub_self, zero_mul, zero_add]
    exact ⟨by omega, h1, h2, h3⟩

end Translates

section Segment

theorem mem_segment_iff' {X : Diagram} {c0 : ℤ} {n : ℕ} {x : ℤ × ℤ} :
    x ∈ Plan.segment X c0 n ↔
      c0 ≤ content x ∧ content x < c0 + n ∧ x.1 = diagLo X (content x) := by
  rw [Plan.mem_segment]
  constructor
  · rintro ⟨c, h1, h2, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp only [content] <;> first | omega | (congr 1; ring)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨content x, h1, h2, ?_⟩
    obtain ⟨u, v⟩ := x
    simp only [content] at h1 h2 h3 ⊢
    refine Prod.ext h3 ?_
    simp only
    rw [← h3]
    omega

end Segment

section Strip

/-- The cell-by-cell form of the strip remainder: on the class `(J, a)` of the least content, the
rows of the row power `F_m` outside the border segment are those of `F_{m-k}`, of the translates
of `Ô` and of the translates of `Ŵ`. -/
theorem strip_pointwise {m k p w s t ρ J a r L H : ℤ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hp : 0 < p)
    (hw : 1 ≤ w) (hwp : w < p) (hsw : s ≤ w) (ht0 : 0 ≤ t) (hts : t < s)
    (ha0 : 0 ≤ a) (hap : a < p) (hL : (a = w ∨ a = p - 1) → L = H) :
    ((((0 ≤ J ∧ J ≤ m - 1) ∨ (J = m ∧ a < w)) ∧
        J * ρ + L - (if 1 ≤ J ∧ a < t then 1 else 0) + (if J = m ∧ s ≤ a then 1 else 0) ≤ r ∧
        r ≤ J * ρ + H) ∧
      ¬ ((m - k) * p + s ≤ J * p + a ∧ J * p + a < (m - k) * p + s + k * p ∧
        r = J * ρ + L - (if 1 ≤ J ∧ a < t then 1 else 0) + (if J = m ∧ s ≤ a then 1 else 0))) ↔
    ((((0 ≤ J ∧ J ≤ (m - k) - 1) ∨ (J = m - k ∧ a < w)) ∧
        J * ρ + L - (if 1 ≤ J ∧ a < t then 1 else 0) + (if J = m - k ∧ s ≤ a then 1 else 0) ≤ r ∧
        r ≤ J * ρ + H) ∨
      ((m - k ≤ J ∧ J ≤ m - 1) ∧ w + 1 ≤ a ∧ a ≤ p - 2 ∧ L ≤ r - J * ρ - 1 ∧
        r - J * ρ - 1 ≤ H - 1) ∨
      ((m - k + 1 ≤ J ∧ J ≤ m) ∧ a ≤ w - 1 ∧ L - (if a < t then 1 else 0) ≤ r - J * ρ - 1 ∧
        r - J * ρ - 1 ≤ H - 1)) := by
  have e1 : m * p = (m - k) * p + k * p := by ring
  have e2 : p ≤ k * p := by nlinarith
  rcases lt_trichotomy J (m - k) with hJ | hJ | hJ
  · have h1 : J * p + p ≤ (m - k) * p := by nlinarith
    split_ifs <;> omega
  · subst hJ
    have h1 : (m - k) * p ≤ m * p := by nlinarith
    split_ifs <;> omega
  · rcases lt_trichotomy J m with hJm | hJm | hJm
    · have h1 : (m - k) * p + p ≤ J * p := by nlinarith
      have h2 : J * p + p ≤ m * p := by nlinarith
      split_ifs <;> omega
    · subst hJm
      split_ifs <;> omega
    · have h1 : m * p + p ≤ J * p := by nlinarith
      split_ifs <;> omega

end Strip


section StripSet

variable {η : MarkedInner} {m k : ℕ}

/-- **The strip remainder (3.7).**  Deleting the border segment of `k p` cells that starts at
content `(m - k) p + s` from the case-(d) row power `F_m` leaves `F_{m-k}`, the `k` translates
`Ô + j v + e` for `m - k ≤ j < m` and the `k` translates `Ŵ + j v + e` for `m - k < j ≤ m`.
For `m = k` the first term is `W`. -/
theorem rowPower_strip_eq (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    η.compose (rowCells 0 m) \
        Plan.segment (η.compose (rowCells 0 m))
          (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat) =
      η.compose (rowCells 0 ((m - k : ℕ) : ℤ)) ∪
        ((Finset.range k).biUnion fun i =>
          translate ((((m : ℤ) - k + i) : ℤ) • η.v + eCell) (hatMiddleFin η)) ∪
        ((Finset.range k).biUnion fun i =>
          translate ((((m : ℤ) - k + 1 + i) : ℤ) • η.v + eCell) (hatMarkFin η)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hkmz : (k : ℤ) ≤ m := by exact_mod_cast hkm
  have hpp : 0 < η.period := by omega
  have hcast : ((k * η.period.toNat : ℕ) : ℤ) = (k : ℤ) * η.period := by
    push_cast; rw [Int.toNat_of_nonneg hpp.le]
  have hsub : (((m - k : ℕ) : ℤ)) = (m : ℤ) - k := by push_cast [Nat.cast_sub hkm]; ring
  ext x
  obtain ⟨A, r, rfl⟩ := η.exists_cell x
  obtain ⟨J, a, ha0, haq, hA⟩ : ∃ J a : ℤ, 0 ≤ a ∧ a < η.period ∧ A = J * η.period + a :=
    ⟨A / η.period, A % η.period, Int.emod_nonneg _ hpp.ne', Int.emod_lt_of_pos _ hpp, by
      have := Int.mul_ediv_add_emod A η.period
      have e : A / η.period * η.period = η.period * (A / η.period) := by ring
      omega⟩
  subst hA
  have hLw : (a = η.widthZ ∨ a = η.period - 1) → η.lo a = η.hi a := by
    rintro (rfl | rfl)
    · exact h.lo_w_eq_hi_w
    · exact h.lo_pred_period_eq_hi
  have hF := mem_rowPower_cell' h hd hph hlt m (J := J) (r := r) ha0 haq
  have hF' := mem_rowPower_cell' h hd hph hlt (m - k) (J := J) (r := r) ha0 haq
  rw [hsub] at hF'
  have hO : (∃ i ∈ Finset.range k, η.cell (J * η.period + a) r ∈
      translate ((((m : ℤ) - k + i) : ℤ) • η.v + eCell) (hatMiddleFin η)) ↔
      (((m : ℤ) - k ≤ J ∧ J ≤ m - 1) ∧ η.widthZ + 1 ≤ a ∧ a ≤ η.period - 2 ∧
        η.lo a ≤ r - J * η.rowShift - 1 ∧ r - J * η.rowShift - 1 ≤ η.hi a - 1) := by
    constructor
    · rintro ⟨i, hi, hmem⟩
      rw [Finset.mem_range] at hi
      rw [mem_translate_hatMiddle_cell h ha0 haq] at hmem
      obtain ⟨hJ, h1, h2, h3, h4⟩ := hmem
      subst hJ
      refine ⟨⟨by omega, by omega⟩, h1, h2, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩
      refine ⟨(J - ((m : ℤ) - k)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      rw [mem_translate_hatMiddle_cell h ha0 haq]
      have e : ((m : ℤ) - k + ((J - ((m : ℤ) - k)).toNat : ℕ)) = J := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      rw [e]
      exact ⟨rfl, h3, h4, h5, h6⟩
  have hW : (∃ i ∈ Finset.range k, η.cell (J * η.period + a) r ∈
      translate ((((m : ℤ) - k + 1 + i) : ℤ) • η.v + eCell) (hatMarkFin η)) ↔
      (((m : ℤ) - k + 1 ≤ J ∧ J ≤ m) ∧ a ≤ η.widthZ - 1 ∧
        η.lo a - (if a < t then 1 else 0) ≤ r - J * η.rowShift - 1 ∧
        r - J * η.rowShift - 1 ≤ η.hi a - 1) := by
    constructor
    · rintro ⟨i, hi, hmem⟩
      rw [Finset.mem_range] at hi
      rw [mem_translate_hatMark_cell h hd hph ha0 haq] at hmem
      obtain ⟨hJ, h1, h2, h3⟩ := hmem
      subst hJ
      refine ⟨⟨by omega, by omega⟩, h1, h2, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      refine ⟨(J - ((m : ℤ) - k + 1)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      rw [mem_translate_hatMark_cell h hd hph ha0 haq]
      have e : ((m : ℤ) - k + 1 + ((J - ((m : ℤ) - k + 1)).toNat : ℕ)) = J := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      rw [e]
      exact ⟨rfl, h3, h4, h5⟩
  have hY : η.cell (J * η.period + a) r ∈ Plan.segment (η.compose (rowCells 0 m))
      (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat) ↔
      (((m : ℤ) - k) * η.period + s ≤ J * η.period + a ∧
        J * η.period + a < ((m : ℤ) - k) * η.period + s + k * η.period) ∧
      r = diagLo (η.compose (rowCells 0 m)) (minContent η.E + (J * η.period + a)) := by
    rw [mem_segment_iff', hcast]
    have hc : content (η.cell (J * η.period + a) r) = minContent η.E + (J * η.period + a) :=
      content_cell _ _ _
    rw [hc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, by omega, h3⟩
  rw [hsub, Finset.mem_sdiff, Finset.mem_union, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_biUnion, hF, hF', hY, hO, hW, or_assoc]
  have key := strip_pointwise (m := (m : ℤ)) (k := (k : ℤ)) (p := η.period)
    (w := η.widthZ) (s := s) (t := t) (ρ := η.rowShift) (J := J) (a := a) (r := r)
    (L := η.lo a) (H := η.hi a) hkz hkmz hpp hw hq hs2 ht1 hlt ha0 haq hLw
  by_cases hv : (0 ≤ J ∧ J ≤ (m : ℤ) - 1) ∨ (J = m ∧ a < η.widthZ)
  · have hl := diagLo_rowPower h hd hph hlt hm ha0 haq hv
    rw [hl]
    rw [← key]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h3 => h2 ⟨⟨h3.1, h3.2.1⟩, h3.2.2⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h3 => h2 ⟨h3.1.1, h3.1.2, h3.2⟩⟩
  · constructor
    · rintro ⟨h1, -⟩; exact absurd h1.1 hv
    · intro h1
      exact absurd (key.mpr h1).1.1 hv

end StripSet

section Separation

variable {η : MarkedInner}

/-- Cells of contents differing by at least two are neither equal nor adjacent. -/
theorem disjoint_nonAdjacent_of_gap {A B : Diagram}
    (h : ∀ x ∈ A, ∀ y ∈ B, content x + 2 ≤ content y ∨ content y + 2 ≤ content x) :
    Disjoint A B ∧ NonAdjacent A B := by
  refine ⟨Finset.disjoint_left.mpr fun z hA hB => ?_, fun x hx y hy hadj => ?_⟩
  · have := h z hA z hB
    omega
  · have := h x hx y hy
    unfold CellAdj at hadj
    simp only [content] at this
    rcases abs_cases (x.1 - y.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (x.2 - y.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem exists_class (η : MarkedInner) (hpp : 0 < η.period) (x : ℤ × ℤ) :
    ∃ J a r : ℤ, 0 ≤ a ∧ a < η.period ∧ x = η.cell (J * η.period + a) r := by
  obtain ⟨A, r, rfl⟩ := η.exists_cell x
  refine ⟨A / η.period, A % η.period, r, Int.emod_nonneg _ hpp.ne', Int.emod_lt_of_pos _ hpp, ?_⟩
  have := Int.mul_ediv_add_emod A η.period
  have e : A / η.period * η.period + A % η.period = A := by
    have e2 : A / η.period * η.period = η.period * (A / η.period) := by ring
    omega
  rw [e]

/-- Contents of the row power `F_{m'}`. -/
theorem content_range_rowPower (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (m' : ℕ) {x : ℤ × ℤ}
    (hx : x ∈ η.compose (rowCells 0 m')) :
    minContent η.E ≤ content x ∧
      content x ≤ minContent η.E + ((m' : ℤ) * η.period + η.widthZ - 1) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpp : 0 < η.period := by omega
  obtain ⟨J, a, r, ha0, haq, rfl⟩ := exists_class η hpp x
  rw [mem_rowPower_cell' h hd hph hlt m' ha0 haq] at hx
  rw [content_cell]
  obtain ⟨hv, -⟩ := hx
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : J * η.period ≤ ((m' : ℤ) - 1) * η.period := by nlinarith
    constructor
    · nlinarith
    · nlinarith
  · subst h1
    constructor <;> nlinarith

theorem content_range_hatMiddle (h : η.IsLegalNonempty) (j : ℤ) {x : ℤ × ℤ}
    (hx : x ∈ translate (j • η.v + eCell) (hatMiddleFin η)) :
    minContent η.E + (j * η.period + η.widthZ + 1) ≤ content x ∧
      content x ≤ minContent η.E + (j * η.period + η.period - 2) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpp : 0 < η.period := by omega
  obtain ⟨J, a, r, ha0, haq, rfl⟩ := exists_class η hpp x
  rw [mem_translate_hatMiddle_cell h ha0 haq] at hx
  obtain ⟨rfl, h1, h2, -⟩ := hx
  rw [content_cell]
  constructor <;> omega

theorem content_range_hatMark (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (j : ℤ) {x : ℤ × ℤ}
    (hx : x ∈ translate (j • η.v + eCell) (hatMarkFin η)) :
    minContent η.E + (j * η.period) ≤ content x ∧
      content x ≤ minContent η.E + (j * η.period + η.widthZ - 1) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpp : 0 < η.period := by omega
  obtain ⟨J, a, r, ha0, haq, rfl⟩ := exists_class η hpp x
  rw [mem_translate_hatMark_cell h hd hph ha0 haq] at hx
  obtain ⟨rfl, h1, -⟩ := hx
  rw [content_cell]
  constructor <;> omega

end Separation

section Product

variable {η : MarkedInner}

private theorem gap_OO (h : η.IsLegalNonempty) {u u' : ℤ} (hu : u < u') :
    ∀ x ∈ translate (u • η.v + eCell) (hatMiddleFin η),
      ∀ y ∈ translate (u' • η.v + eCell) (hatMiddleFin η),
        content x + 2 ≤ content y ∨ content y + 2 ≤ content x := by
  intro x hx y hy
  have hq := h.width_lt_period
  have hw := h.width_pos
  have h1 := content_range_hatMiddle h u hx
  have h2 := content_range_hatMiddle h u' hy
  have : u * η.period + η.period ≤ u' * η.period := by nlinarith
  left; omega

private theorem gap_WW (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) {u u' : ℤ} (hu : u < u') :
    ∀ x ∈ translate (u • η.v + eCell) (hatMarkFin η),
      ∀ y ∈ translate (u' • η.v + eCell) (hatMarkFin η),
        content x + 2 ≤ content y ∨ content y + 2 ≤ content x := by
  intro x hx y hy
  have hq := h.width_lt_period
  have hw := h.width_pos
  have h1 := content_range_hatMark h hd hph u hx
  have h2 := content_range_hatMark h hd hph u' hy
  have : u * η.period + η.period ≤ u' * η.period := by nlinarith
  left; omega

private theorem gap_OW (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) {u u' : ℤ} (hu : u + 1 ≤ u' ∨ u' ≤ u) :
    ∀ x ∈ translate (u • η.v + eCell) (hatMiddleFin η),
      ∀ y ∈ translate (u' • η.v + eCell) (hatMarkFin η),
        content x + 2 ≤ content y ∨ content y + 2 ≤ content x := by
  intro x hx y hy
  have hq := h.width_lt_period
  have hw := h.width_pos
  have h1 := content_range_hatMiddle h u hx
  have h2 := content_range_hatMark h hd hph u' hy
  rcases hu with hu | hu
  · have : u * η.period + η.period ≤ u' * η.period := by nlinarith
    left; omega
  · have : u' * η.period ≤ u * η.period := by nlinarith
    right; omega

private theorem gap_FO (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (m' : ℕ) {u : ℤ} (hu : (m' : ℤ) ≤ u) :
    ∀ x ∈ η.compose (rowCells 0 m'),
      ∀ y ∈ translate (u • η.v + eCell) (hatMiddleFin η),
        content x + 2 ≤ content y ∨ content y + 2 ≤ content x := by
  intro x hx y hy
  have hq := h.width_lt_period
  have hw := h.width_pos
  have h1 := content_range_rowPower h hd hph hlt m' hx
  have h2 := content_range_hatMiddle h u hy
  have : (m' : ℤ) * η.period ≤ u * η.period := by nlinarith
  left; omega

private theorem gap_FW (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (m' : ℕ) {u : ℤ} (hu : (m' : ℤ) + 1 ≤ u) :
    ∀ x ∈ η.compose (rowCells 0 m'),
      ∀ y ∈ translate (u • η.v + eCell) (hatMarkFin η),
        content x + 2 ≤ content y ∨ content y + 2 ≤ content x := by
  intro x hx y hy
  have hq := h.width_lt_period
  have hw := h.width_pos
  have h1 := content_range_rowPower h hd hph hlt m' hx
  have h2 := content_range_hatMark h hd hph u hy
  have : ((m' : ℤ) + 1) * η.period ≤ u * η.period := by nlinarith
  have e : ((m' : ℤ) + 1) * η.period = (m' : ℤ) * η.period + η.period := by ring
  left; omega

end Product

section StripProduct

variable {η : MarkedInner} {m k : ℕ}

/-- **The strip remainder as a product.**  The cell set of `F_m` minus the border segment of
`k p` cells at content `(m - k) p + s` has Schur function `s_{F_{m-k}} (s_Ô s_Ŵ)^k`, where
`F_0 = W`.  Here `s_Ô = cellSchur (hatMiddleFin η)` and `s_Ŵ = cellSchur (hatMarkFin η)`. -/
theorem rowPower_strip_cellSchur (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    cellSchur (η.compose (rowCells 0 m) \
        Plan.segment (η.compose (rowCells 0 m))
          (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) =
      cellSchur (hatMarkFin η) ^ k * cellSchur (hatMiddleFin η) ^ k *
        cellSchur (η.compose (rowCells 0 ((m - k : ℕ) : ℤ))) := by
  classical
  have hsub : (((m - k : ℕ) : ℤ)) = (m : ℤ) - k := by push_cast [Nat.cast_sub hkm]; ring
  rw [rowPower_strip_eq h hd hph hlt hm hk hkm]
  set Fp := η.compose (rowCells 0 ((m - k : ℕ) : ℤ)) with hFp
  set fO : ℕ → Diagram := fun i =>
    translate ((((m : ℤ) - k + i) : ℤ) • η.v + eCell) (hatMiddleFin η) with hfO
  set fW : ℕ → Diagram := fun i =>
    translate ((((m : ℤ) - k + 1 + i) : ℤ) • η.v + eCell) (hatMarkFin η) with hfW
  have hOO : ∀ i ∈ Finset.range k, ∀ i' ∈ Finset.range k, i ≠ i' →
      Disjoint (fO i) (fO i') ∧ NonAdjacent (fO i) (fO i') := by
    intro i _ i' _ hne
    apply disjoint_nonAdjacent_of_gap
    intro x hx y hy
    rcases lt_or_gt_of_ne hne with hlt' | hlt'
    · exact gap_OO h (u := (m : ℤ) - k + i) (u' := (m : ℤ) - k + i') (by omega) x hx y hy
    · exact (gap_OO h (u := (m : ℤ) - k + i') (u' := (m : ℤ) - k + i) (by omega) y hy x hx).symm
  have hWW : ∀ i ∈ Finset.range k, ∀ i' ∈ Finset.range k, i ≠ i' →
      Disjoint (fW i) (fW i') ∧ NonAdjacent (fW i) (fW i') := by
    intro i _ i' _ hne
    apply disjoint_nonAdjacent_of_gap
    intro x hx y hy
    rcases lt_or_gt_of_ne hne with hlt' | hlt'
    · exact gap_WW h hd hph (u := (m : ℤ) - k + 1 + i) (u' := (m : ℤ) - k + 1 + i') (by omega)
        x hx y hy
    · exact (gap_WW h hd hph (u := (m : ℤ) - k + 1 + i') (u' := (m : ℤ) - k + 1 + i)
        (by omega) y hy x hx).symm
  have hFO : Disjoint Fp ((Finset.range k).biUnion fO) ∧
      NonAdjacent Fp ((Finset.range k).biUnion fO) := by
    apply disjoint_nonAdjacent_of_gap
    intro x hx y hy
    obtain ⟨i, _, hy'⟩ := Finset.mem_biUnion.mp hy
    exact gap_FO h hd hph hlt (m - k) (u := (m : ℤ) - k + i) (by rw [hsub]; omega) x hx y hy'
  have hOW : Disjoint ((Finset.range k).biUnion fO) ((Finset.range k).biUnion fW) ∧
      NonAdjacent ((Finset.range k).biUnion fO) ((Finset.range k).biUnion fW) := by
    apply disjoint_nonAdjacent_of_gap
    intro x hx y hy
    obtain ⟨i, _, hx'⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i', _, hy'⟩ := Finset.mem_biUnion.mp hy
    exact gap_OW h hd hph (u := (m : ℤ) - k + i) (u' := (m : ℤ) - k + 1 + i')
      (by omega) x hx' y hy'
  have hFW : Disjoint Fp ((Finset.range k).biUnion fW) ∧
      NonAdjacent Fp ((Finset.range k).biUnion fW) := by
    apply disjoint_nonAdjacent_of_gap
    intro x hx y hy
    obtain ⟨i, _, hy'⟩ := Finset.mem_biUnion.mp hy
    exact gap_FW h hd hph hlt (m - k) (u := (m : ℤ) - k + 1 + i) (by rw [hsub]; omega) x hx y hy'
  have hUW : Disjoint (Fp ∪ (Finset.range k).biUnion fO) ((Finset.range k).biUnion fW) ∧
      NonAdjacent (Fp ∪ (Finset.range k).biUnion fO) ((Finset.range k).biUnion fW) := by
    refine ⟨Finset.disjoint_union_left.mpr ⟨hFW.1, hOW.1⟩, ?_⟩
    exact nonAdjacent_union_left hFW.2 hOW.2
  rw [Plan.cellSchur_union hUW.1 hUW.2, Plan.cellSchur_union hFO.1 hFO.2,
    Plan.cellSchur_biUnion _ _ (fun i hi j hj hij => (hOO i hi j hj hij).1)
      (fun i hi j hj hij => (hOO i hi j hj hij).2),
    Plan.cellSchur_biUnion _ _ (fun i hi j hj hij => (hWW i hi j hj hij).1)
      (fun i hi j hj hij => (hWW i hi j hj hij).2)]
  simp only [hfO, hfW, cellSchur_translate, Finset.prod_const, Finset.card_range]
  ring

end StripProduct

section StripHeight

variable {η : MarkedInner} {m k : ℕ}

/-- The northwest border at the start of the surviving segment drops by one: `ℓ_{s-1} - ℓ_s = 1`. -/
theorem lo_pred_phase_sub (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) : η.lo (s - 1) - η.lo s = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have b1 := h.bit_lo' (a := s - 1) (b := s) (by ring) (by omega) (by omega)
  have f1 := d_E_facts h hd hph (a := s - 1) (by omega) (by omega)
  simp only [dLo, dHi] at f1
  by_cases hsw : s = η.widthZ
  · have hc := (d_caps h hd).1
    simp only [dLo, dHi] at hc
    have e : η.widthZ - 1 = s - 1 := by omega
    rw [e] at hc
    have e2 : η.widthZ = s := hsw.symm
    rw [e2] at hc
    omega
  · have f2 := d_E_facts h hd hph (a := s) (by omega) (by omega)
    simp only [dLo, dHi] at f2
    have b2 := h.bit_lo' (a := s - 1 + η.period) (b := s + η.period) (by ring) (by omega)
      (by omega)
    have e : s - 1 + η.period = s - 1 + η.period := rfl
    omega

/-- **The height of the surviving segment.**  The border segment of `k p` cells at content
`(m - k) p + s` has `-k v₁` rows, so its height plus one is `-k v₁`. -/
theorem rowPower_strip_height (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    (ribbonHeight (Plan.segment (η.compose (rowCells 0 m))
        (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) : ℤ) + 1 =
      -(k : ℤ) * η.v.1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hkmz : (k : ℤ) ≤ m := by exact_mod_cast hkm
  have hpp : 0 < η.period := by omega
  have hcast : ((k * η.period.toNat : ℕ) : ℤ) = (k : ℤ) * η.period := by
    push_cast; rw [Int.toNat_of_nonneg hpp.le]
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hF := h.1.isConnectedSkew_compose hD
  obtain ⟨hmn, hmx⟩ := rowPower_content_range h hm
  have hkn : 0 < k * η.period.toNat := Nat.mul_pos hk (by omega)
  have hmk : 0 ≤ ((m : ℤ) - k) * η.period := mul_nonneg (by omega) hpp.le
  have hc1 : minContent (η.compose (rowCells 0 m)) ≤
      minContent η.E + (((m : ℤ) - k) * η.period + s) := by omega
  have e1 : minContent η.E + (((m : ℤ) - k) * η.period + s) + ((k * η.period.toNat : ℕ) : ℤ) - 1 =
      minContent η.E + ((m : ℤ) * η.period + (s - 1)) := by
    rw [hcast]; ring
  have hc2 : minContent η.E + (((m : ℤ) - k) * η.period + s) + ((k * η.period.toNat : ℕ) : ℤ) - 1 ≤
      maxContent (η.compose (rowCells 0 m)) := by
    rw [e1, hmx]; omega
  have hrh := ribbonHeight_segment (isConnectedSkew_iff_diagonal.mp hF) hkn hc1 hc2
  rw [e1] at hrh
  have d1 := diagLo_rowPower h hd hph hlt hm (J := (m : ℤ) - k) (a := s) (by omega) (by omega)
    (Or.inl ⟨by omega, by omega⟩)
  have d2 := diagLo_rowPower h hd hph hlt hm (J := (m : ℤ)) (a := s - 1) (by omega) (by omega)
    (Or.inr ⟨rfl, by omega⟩)
  rw [hrh, d1, d2]
  have hb := lo_pred_phase_sub h hd hph
  have hv : η.rowShift = η.v.1 := rfl
  have e3 : ((m : ℤ) - k) * η.rowShift = (m : ℤ) * η.rowShift - k * η.rowShift := by ring
  have e4 : -(k : ℤ) * η.v.1 = -((k : ℤ) * η.rowShift) := by rw [hv]; ring
  rw [e4]
  rw [e3] at *
  split_ifs <;> omega

end StripHeight

section StripSigned

variable {η : MarkedInner} {m k : ℕ}

/-- The sign of the surviving segment: its height is `k (-v₁) - 1`. -/
theorem rowPower_strip_sign (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    ribbonSign (Plan.segment (η.compose (rowCells 0 m))
        (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) =
      -((-1 : ℤ) ^ (k * (-η.v.1).toNat)) := by
  have hh := rowPower_strip_height h hd hph hlt hm hk hkm
  set ht := ribbonHeight (Plan.segment (η.compose (rowCells 0 m))
        (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) with hht
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have e0 : -(k : ℤ) * η.v.1 = -((k : ℤ) * η.v.1) := by ring
  rw [e0] at hh
  have hneg : η.v.1 < 0 := by
    by_contra hcon
    have : (0 : ℤ) ≤ η.v.1 := by omega
    have := mul_nonneg (by omega : (0 : ℤ) ≤ k) this
    omega
  have hn : k * (-η.v.1).toNat = ht + 1 := by
    have e : (((-η.v.1).toNat : ℕ) : ℤ) = -η.v.1 := Int.toNat_of_nonneg (by omega)
    have : ((k * (-η.v.1).toNat : ℕ) : ℤ) = ((ht + 1 : ℕ) : ℤ) := by
      push_cast; rw [e]; linarith
    exact_mod_cast this
  unfold ribbonSign
  rw [← hht, hn, pow_succ]
  ring

/-- **The signed strip remainder.**  With the northwest border segment `Y` of `k p` cells at
content `(m - k) p + s`, the signed cofactor of the case-(d) row power is
`-(-1)^{-k v₁} (s_Ŵ s_Ô)^k s_{F_{m-k}}`, where `F_0 = W`. -/
theorem rowPower_strip_signed (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    (ribbonSign (Plan.segment (η.compose (rowCells 0 m))
        (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) : Lambda) *
      cellSchur (η.compose (rowCells 0 m) \
        Plan.segment (η.compose (rowCells 0 m))
          (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) =
      -((-1 : Lambda) ^ (k * (-η.v.1).toNat)) *
        (cellSchur (hatMarkFin η) ^ k * cellSchur (hatMiddleFin η) ^ k *
          cellSchur (η.compose (rowCells 0 ((m - k : ℕ) : ℤ)))) := by
  rw [rowPower_strip_sign h hd hph hlt hm hk hkm, rowPower_strip_cellSchur h hd hph hlt hm hk hkm]
  push_cast
  ring

end StripSigned

end SkewMarkedFactor
