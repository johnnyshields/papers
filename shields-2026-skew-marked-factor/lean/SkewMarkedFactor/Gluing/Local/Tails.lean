/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Local/Tails.lean
import Mathlib.Data.Int.LeastGreatest
import SkewMarkedFactor.Gluing.Local.RotateData

/-!
# Middle tails of a legal mark

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local`).

On a marked diagonal `a < w` compare the diagonal of `E` at `a` with the diagonal at `a + q`
translated back by `-v`: `dLo a = ℓ_{a+q} - p - ℓ_a` and `dHi a = h_{a+q} - p - h_a`.  The lower
middle tail has `max (dLo a) 0` cells northwest and `max (-dHi a) 0` cells southeast of `W₋`;
the upper middle tail has `max (-dLo a) 0` northwest and `max (dHi a) 0` southeast cells.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

variable {ω : MarkedInner}

/-- `dLo a = ℓ_{a+q} - p - ℓ_a`: the northwest offset of `E_{a+q} - v` against `E_a`. -/
def dLo (ω : MarkedInner) (a : ℤ) : ℤ := ω.lo (a + ω.period) - ω.rowShift - ω.lo a

/-- `dHi a = h_{a+q} - p - h_a`: the southeast offset of `E_{a+q} - v` against `E_a`. -/
def dHi (ω : MarkedInner) (a : ℤ) : ℤ := ω.hi (a + ω.period) - ω.rowShift - ω.hi a

/-- Lower-end condition: the southwest cell of `E` lies in `W₋`. -/
theorem IsLegalNonempty.dLo_zero_le (h : ω.IsLegalNonempty) : ω.dLo 0 ≤ 0 ∧ 0 ≤ ω.dHi 0 := by
  have h1 := h.mem_W.mp h.sw_cell
  have h2 := h.lo_zero
  unfold dLo dHi
  omega

/-- Upper-end condition: the northeast cell of `E` lies in `W₊`. -/
theorem IsLegalNonempty.last_dLo (h : ω.IsLegalNonempty) :
    0 ≤ ω.dLo (ω.widthZ - 1) ∧ ω.dHi (ω.widthZ - 1) ≤ 0 := by
  have h1 := h.mem_W.mp h.ne_cell_W
  have h2 := h.lo_last
  have e : ω.widthZ - 1 + ω.period = ω.period + ω.widthZ - 1 := by ring
  unfold dLo dHi
  rw [e]
  omega

/-- The northwest tail of `E_a` beside `W₋` and the southeast tail are not both present
(`III`: the diagonals of `E \ W₋` are row intervals), and the lower tail has at most one cell
(`IV`); the tails are thin on the lower marked diagonals.
**Differs from the paper's route.**  The paper argues with the first diagonal carrying two
middle cells; here the same adjacency contradiction of IV is run by induction on the offsets
`dLo`, `dHi`. -/
theorem IsLegalNonempty.thin_lower (h : ω.IsLegalNonempty) :
    ∀ a : ℤ, 0 ≤ a → a ≤ ω.widthZ - 1 → ω.dLo a ≤ 1 ∧ -1 ≤ ω.dHi a := by
  intro a h0
  induction a, h0 using Int.leInduction with
  | base =>
    intro _
    have := h.dLo_zero_le
    omega
  | succ k hk ih =>
    intro hkw
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hw := h.width_pos
    have hwq := h.width_lt_period
    have bA := h.bit_lo' (a := k) (b := k + 1) rfl hk (by omega)
    have bA' := h.bit_lo' (a := k + ω.period) (b := k + 1 + ω.period) (by ring) (by omega)
      (by omega)
    have bB := h.bit_hi' (a := k) (b := k + 1) rfl hk (by omega)
    have bB' := h.bit_hi' (a := k + ω.period) (b := k + 1 + ω.period) (by ring) (by omega)
      (by omega)
    obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row (a := k) hk (by omega)
    obtain ⟨r1, c0, c1, c2, c3⟩ := h.W_row (a := k + 1) (by omega) hkw
    unfold dLo dHi at *
    constructor
    · by_contra hc
      refine h.iv_south (j := k) (k := k + 1) (r := ω.lo (k + 1)) rfl ?_ ?_ (Or.inl ⟨?_, ?_⟩)
      · rw [h.mem_middle_lower (by omega)]; omega
      · rw [h.mem_middle_lower (by omega)]; omega
      · exact h.mem_E.mpr ⟨by omega, by omega, by omega, by omega⟩
      · exact h.mem_W.mpr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · by_contra hc
      refine h.iv_west (j := k) (k := k + 1) (r := ω.hi (k + 1) - 1) rfl ?_ ?_ (Or.inr ⟨?_, ?_⟩)
      · rw [h.mem_middle_lower (by omega)]; omega
      · rw [h.mem_middle_lower (by omega)]; omega
      · exact h.mem_W.mpr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact h.mem_E.mpr ⟨by omega, by omega, by omega, by omega⟩


theorem IsLegalNonempty.dLo_rotate (h : ω.IsLegalNonempty) (a : ℤ) :
    ω.rotate.dLo (ω.widthZ - 1 - a) = ω.dHi a := by
  simp only [dLo, dHi, h.lo_rotate, period_rotate, rowShift_rotate]
  have e1 : ω.period + ω.widthZ - 1 - (ω.widthZ - 1 - a + ω.period) = a := by ring
  have e2 : ω.period + ω.widthZ - 1 - (ω.widthZ - 1 - a) = a + ω.period := by ring
  rw [e1, e2]
  ring

theorem IsLegalNonempty.dHi_rotate (h : ω.IsLegalNonempty) (a : ℤ) :
    ω.rotate.dHi (ω.widthZ - 1 - a) = ω.dLo a := by
  simp only [dLo, dHi, h.hi_rotate, period_rotate, rowShift_rotate]
  have e1 : ω.period + ω.widthZ - 1 - (ω.widthZ - 1 - a + ω.period) = a := by ring
  have e2 : ω.period + ω.widthZ - 1 - (ω.widthZ - 1 - a) = a + ω.period := by ring
  rw [e1, e2]
  ring

/-- The upper middle tail is thin as well: it has at most one cell on each marked diagonal. -/
theorem IsLegalNonempty.thin_upper (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : -1 ≤ ω.dLo a ∧ ω.dHi a ≤ 1 := by
  have := h.rotate.thin_lower (ω.widthZ - 1 - a) (by omega)
    (by rw [widthZ_rotate]; omega)
  rw [h.dLo_rotate, h.dHi_rotate] at this
  omega

/-! ### Consequences of III for the lower copy -/

/-- A lower marked diagonal carries a middle tail (a cell of `E \ W₋`). -/
def TailLower (ω : MarkedInner) (a : ℤ) : Prop := 0 < ω.dLo a ∨ ω.dHi a < 0

theorem IsLegalNonempty.shape_sdiff (h : ω.IsLegalNonempty) : HasDiagonalShape (ω.E \ ω.W) :=
  isConnectedSkew_iff_diagonal.mp h.1.2.2.2.1.1

theorem IsLegalNonempty.mem_sdiff_cell (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ ω.E \ ω.W ↔
      (0 ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a) ∧
      ¬ (0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a ∧
        ω.lo (a + ω.period) ≤ r + ω.rowShift ∧ r + ω.rowShift ≤ ω.hi (a + ω.period)) := by
  rw [Finset.mem_sdiff, h.mem_E, h.mem_W]

theorem IsLegalNonempty.interval_lower (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ¬ (0 < ω.dLo a ∧ ω.dHi a < 0) := by
  rintro ⟨hp, hn⟩
  have hd := h.shape_sdiff
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row h0 h1
  unfold dLo at hp
  unfold dHi at hn
  have hx : ω.cell a (ω.lo a) ∈ ω.E \ ω.W := by
    rw [h.mem_sdiff_cell]; omega
  have hy : ω.cell a (ω.hi a) ∈ ω.E \ ω.W := by
    rw [h.mem_sdiff_cell]; omega
  have := hd.2.2.1 _ hx _ hy (by simp [cell, content]) r0
    (Finset.mem_Icc.mpr ⟨by simp only [cell]; omega, by simp only [cell]; omega⟩)
  have e : (r0, r0 + content (ω.cell a (ω.lo a))) = ω.cell a r0 := by simp [cell, content]
  rw [e, h.mem_sdiff_cell] at this
  omega

theorem IsLegalNonempty.exists_tail_cell (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) (ht : ω.TailLower a) : ∃ r, ω.cell a r ∈ ω.E \ ω.W := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row h0 h1
  unfold TailLower dLo dHi at ht
  rcases ht with ht | ht
  · exact ⟨ω.lo a, by rw [h.mem_sdiff_cell]; omega⟩
  · exact ⟨ω.hi a, by rw [h.mem_sdiff_cell]; omega⟩

theorem IsLegalNonempty.tail_of_cell (h : ω.IsLegalNonempty) {a r : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) (hc : ω.cell a r ∈ ω.E \ ω.W) : ω.TailLower a := by
  rw [h.mem_sdiff_cell] at hc
  unfold TailLower dLo dHi
  omega

theorem IsLegalNonempty.cell_w_mem (h : ω.IsLegalNonempty) {r : ℤ} (h1 : ω.lo ω.widthZ ≤ r)
    (h2 : r ≤ ω.hi ω.widthZ) : ω.cell ω.widthZ r ∈ ω.E \ ω.W := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.mem_sdiff_cell]
  omega

/-- The lower tails form a final segment of the lower marked diagonals (`III`: the contents of
`E \ W₋` form an interval). -/
theorem IsLegalNonempty.tail_mono (h : ω.IsLegalNonempty) {a b : ℤ} (h0 : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ ω.widthZ - 1) (ht : ω.TailLower a) : ω.TailLower b := by
  have hd := h.shape_sdiff
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨r, hr⟩ := h.exists_tail_cell h0 (by omega) ht
  have hl := h.lo_le_hi (a := ω.widthZ) (by omega) (by omega)
  have hy := h.cell_w_mem (le_refl _) hl
  have hk := hd.2.1 _ hr _ hy (minContent ω.E + b) (by
    rw [Finset.mem_Icc]
    simp only [content_cell]
    omega)
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
  exact h.tail_of_cell (r := i) (by omega) hb (by simpa [cell] using hi)

/-- If the last lower marked diagonal has no tail, then diagonal `w` is a singleton (the least
diagonal of `E \ W₋` is a singleton). -/
theorem IsLegalNonempty.diag_w_of_no_tail (h : ω.IsLegalNonempty)
    (ht : ¬ ω.TailLower (ω.widthZ - 1)) :
    ω.lo ω.widthZ = ω.hi ω.widthZ := by
  by_contra hne
  have hd := h.shape_sdiff
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hl := h.lo_le_hi (a := ω.widthZ) (by omega) (by omega)
  have hx := h.cell_w_mem (le_refl (ω.lo ω.widthZ)) hl
  have hy := h.cell_w_mem hl (le_refl (ω.hi ω.widthZ))
  have hk : minContent ω.E + ω.widthZ ∈ contents (ω.E \ ω.W) := by
    have := content_mem_contents hx
    simpa [content_cell] using this
  have hnot : minContent ω.E + ω.widthZ - 1 ∉ contents (ω.E \ ω.W) := by
    intro hc
    obtain ⟨i, hi⟩ := mem_contents_iff.mp hc
    refine ht (h.tail_of_cell (r := i) (by omega) (le_refl _) ?_)
    have e : (i, i + (minContent ω.E + ω.widthZ - 1)) = ω.cell (ω.widthZ - 1) i := by
      simp only [cell]; ext
      · rfl
      · simp only; ring
    rwa [← e]
  have heq := hd.2.2.2.2 _ hk (Or.inl hnot)
  have h1 : diagLo (ω.E \ ω.W) (minContent ω.E + ω.widthZ) ≤ ω.lo ω.widthZ :=
    diagLo_le (D := ω.E \ ω.W) (k := minContent ω.E + ω.widthZ) hx (by simp)
  have h2 : ω.hi ω.widthZ ≤ diagHi (ω.E \ ω.W) (minContent ω.E + ω.widthZ) :=
    le_diagHi (D := ω.E \ ω.W) (k := minContent ω.E + ω.widthZ) hy (by simp)
  omega

/-- **Private diagonal `w` is a singleton** (`lem:gluing-local` (1)). -/
theorem IsLegalNonempty.lo_w_eq_hi_w (h : ω.IsLegalNonempty) :
    ω.lo ω.widthZ = ω.hi ω.widthZ := by
  by_cases ht : ω.TailLower (ω.widthZ - 1)
  swap
  · exact h.diag_w_of_no_tail ht
  by_contra hne
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hl := h.lo_le_hi (a := ω.widthZ) (by omega) (by omega)
  obtain ⟨l1, l2⟩ := h.last_dLo
  obtain ⟨t1, t2⟩ := h.thin_lower (ω.widthZ - 1) (by omega) (le_refl _)
  have hint := h.interval_lower (a := ω.widthZ - 1) (by omega) (le_refl _)
  have hjk : ω.widthZ = ω.widthZ - 1 + 1 := by ring
  have bA := h.bit_lo' (a := ω.widthZ - 1) (b := ω.widthZ) (by ring) (by omega) (by omega)
  have bB := h.bit_hi' (a := ω.widthZ - 1) (b := ω.widthZ) (by ring) (by omega) (by omega)
  obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row (a := ω.widthZ - 1) (by omega) (le_refl _)
  unfold TailLower at ht
  unfold dLo dHi at *
  have hcase : (0 < ω.lo (ω.widthZ - 1 + ω.period) - ω.rowShift - ω.lo (ω.widthZ - 1)) ∨
      (ω.hi (ω.widthZ - 1 + ω.period) - ω.rowShift - ω.hi (ω.widthZ - 1) < 0) := ht
  by_cases hs : ω.hi (ω.widthZ - 1 + ω.period) - ω.rowShift - ω.hi (ω.widthZ - 1) < 0
  · rcases bB with b0 | b1
    · refine h.iv_west (j := ω.widthZ - 1) (k := ω.widthZ) (r := ω.hi ω.widthZ - 1) hjk ?_ ?_
        (Or.inr ⟨?_, ?_⟩)
      · rw [h.mem_middle_lower hq]; omega
      · rw [h.mem_middle_lower hq]; omega
      · exact h.mem_W.mpr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact h.mem_E.mpr ⟨by omega, by omega, by omega, by omega⟩
    · refine h.iv_south (j := ω.widthZ - 1) (k := ω.widthZ) (r := ω.hi ω.widthZ - 1) hjk ?_ ?_
        (Or.inr ⟨?_, ?_⟩)
      · rw [h.mem_middle_lower hq]; omega
      · rw [h.mem_middle_lower hq]; omega
      · exact h.mem_W.mpr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact h.mem_E.mpr ⟨by omega, by omega, by omega, by omega⟩
  · rcases bA with b0 | b1
    · refine h.iv_west (j := ω.widthZ - 1) (k := ω.widthZ) (r := ω.lo ω.widthZ) hjk ?_ ?_
        (Or.inl ⟨?_, ?_⟩)
      · rw [h.mem_middle_lower hq]; omega
      · rw [h.mem_middle_lower hq]; omega
      · exact h.mem_E.mpr ⟨by omega, by omega, by omega, by omega⟩
      · exact h.mem_W.mpr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · refine h.iv_south (j := ω.widthZ - 1) (k := ω.widthZ) (r := ω.lo ω.widthZ) hjk ?_ ?_
        (Or.inl ⟨?_, ?_⟩)
      · rw [h.mem_middle_lower hq]; omega
      · rw [h.mem_middle_lower hq]; omega
      · exact h.mem_E.mpr ⟨by omega, by omega, by omega, by omega⟩
      · exact h.mem_W.mpr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **Private diagonal `q - 1` is a singleton** (`lem:gluing-local` (1)), by rotation. -/
theorem IsLegalNonempty.lo_pred_period_eq_hi (h : ω.IsLegalNonempty) :
    ω.lo (ω.period - 1) = ω.hi (ω.period - 1) := by
  have := h.rotate.lo_w_eq_hi_w
  rw [h.lo_rotate, h.hi_rotate, widthZ_rotate] at this
  have e : ω.period + ω.widthZ - 1 - ω.widthZ = ω.period - 1 := by ring
  rw [e] at this
  omega

/-! ### The upper tails, by rotation -/

/-- An upper marked diagonal carries a middle tail (a cell of `E \ W₊`). -/
def TailUpper (ω : MarkedInner) (a : ℤ) : Prop := ω.dLo a < 0 ∨ 0 < ω.dHi a

theorem IsLegalNonempty.tailUpper_iff (h : ω.IsLegalNonempty) (a : ℤ) :
    ω.TailUpper a ↔ ω.rotate.TailLower (ω.widthZ - 1 - a) := by
  unfold TailUpper TailLower
  rw [h.dLo_rotate, h.dHi_rotate]
  omega

theorem IsLegalNonempty.tail_mono_upper (h : ω.IsLegalNonempty) {a b : ℤ} (h0 : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ ω.widthZ - 1) (ht : ω.TailUpper b) : ω.TailUpper a := by
  rw [h.tailUpper_iff] at ht ⊢
  exact h.rotate.tail_mono (by omega) (by omega) (by rw [widthZ_rotate]; omega) ht

theorem IsLegalNonempty.interval_upper (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ¬ (ω.dLo a < 0 ∧ 0 < ω.dHi a) := by
  have := h.rotate.interval_lower (a := ω.widthZ - 1 - a) (by omega)
    (by rw [widthZ_rotate]; omega)
  rw [h.dLo_rotate, h.dHi_rotate] at this
  omega

/-! ### The side of the lower tail -/

/-- Noncrossing: a southeast tail on `a` forces no northwest tail on `a + 1` (`E \ W₋` is skew). -/
theorem IsLegalNonempty.noncross_se_nw (h : ω.IsLegalNonempty) {b : ℤ} (h0 : 0 ≤ b)
    (h1 : b + 1 ≤ ω.widthZ - 1) (hs : ω.dHi b < 0) : ω.dLo (b + 1) ≤ 0 := by
  by_contra hn
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hsk := h.1.2.2.2.1.1.1
  obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row (a := b) h0 (by omega)
  have bA := h.bit_lo' (a := b) (b := b + 1) rfl h0 (by omega)
  have bA' := h.bit_lo' (a := b + ω.period) (b := b + 1 + ω.period) (by ring) (by omega)
    (by omega)
  have l1 := h.lo_le_hi (a := b + 1) (by omega) (by omega)
  unfold dLo at hn
  unfold dHi at hs
  have hx : ω.cell b (ω.hi b) ∈ ω.E \ ω.W := by
    rw [h.mem_sdiff_cell]; omega
  have hy : ω.cell (b + 1) (ω.lo (b + 1)) ∈ ω.E \ ω.W := by
    rw [h.mem_sdiff_cell]; omega
  have := hsk _ hy _ hx (by simp only [cell]; omega) (by simp only [cell]; omega) r0
    (Finset.mem_Icc.mpr ⟨by simp only [cell]; omega, by simp only [cell]; omega⟩)
    (r0 + (minContent ω.E + b))
    (Finset.mem_Icc.mpr ⟨by simp only [cell]; omega, by simp only [cell]; omega⟩)
  have e : (r0, r0 + (minContent ω.E + b)) = ω.cell b r0 := rfl
  rw [e, h.mem_sdiff_cell] at this
  omega

/-- Noncrossing: a northwest tail on `a` forces no southeast tail on `a + 1`. -/
theorem IsLegalNonempty.noncross_nw_se (h : ω.IsLegalNonempty) {b : ℤ} (h0 : 0 ≤ b)
    (h1 : b + 1 ≤ ω.widthZ - 1) (hs : 0 < ω.dLo b) : 0 ≤ ω.dHi (b + 1) := by
  by_contra hn
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hsk := h.1.2.2.2.1.1.1
  obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row (a := b) h0 (by omega)
  have bB := h.bit_hi' (a := b) (b := b + 1) rfl h0 (by omega)
  have bB' := h.bit_hi' (a := b + ω.period) (b := b + 1 + ω.period) (by ring) (by omega)
    (by omega)
  have l1 := h.lo_le_hi (a := b + 1) (by omega) (by omega)
  unfold dHi at hn
  unfold dLo at hs
  have hx : ω.cell b (ω.lo b) ∈ ω.E \ ω.W := by
    rw [h.mem_sdiff_cell]; omega
  have hy : ω.cell (b + 1) (ω.hi (b + 1)) ∈ ω.E \ ω.W := by
    rw [h.mem_sdiff_cell]; omega
  have := hsk _ hx _ hy (by simp only [cell]; omega) (by simp only [cell]; omega) r0
    (Finset.mem_Icc.mpr ⟨by simp only [cell]; omega, by simp only [cell]; omega⟩)
    (r0 + (minContent ω.E + b))
    (Finset.mem_Icc.mpr ⟨by simp only [cell]; omega, by simp only [cell]; omega⟩)
  have e : (r0, r0 + (minContent ω.E + b)) = ω.cell b r0 := rfl
  rw [e, h.mem_sdiff_cell] at this
  omega

theorem IsLegalNonempty.first_tail (h : ω.IsLegalNonempty)
    (hex : ∃ a, 0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.TailLower a) :
    ∃ s, 1 ≤ s ∧ s ≤ ω.widthZ - 1 ∧ ω.TailLower s ∧ ∀ b, 0 ≤ b → b < s → ¬ ω.TailLower b := by
  obtain ⟨s, ⟨hs0, hs1, hs2⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => 0 ≤ z ∧ z ≤ ω.widthZ - 1 ∧ ω.TailLower z) ⟨0, fun z hz => hz.1⟩ hex
  refine ⟨s, ?_, hs1, hs2, fun b hb hbs ht => ?_⟩
  · by_contra hs
    have : s = 0 := by omega
    subst this
    have h1 := h.dLo_zero_le
    unfold TailLower at hs2
    omega
  · have := hmin b ⟨hb, by omega, ht⟩
    omega

/-- At the first lower tail `s`, the southwest cell of the middle has its lower attachment
neighbor in `W₋`. -/
theorem IsLegalNonempty.first_tail_cell (h : ω.IsLegalNonempty) {s : ℤ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ ω.widthZ - 1) (hst : ω.TailLower s)
    (hmin : ∀ b, 0 ≤ b → b < s → ¬ ω.TailLower b) :
    (ω.LowerH → ∃ r, ω.cell s r ∈ ω.middle ∧ ω.cell (s - 1) r ∈ ω.W) ∧
    (ω.LowerV → ∃ r, ω.cell s r ∈ ω.middle ∧ ω.cell (s - 1) (r + 1) ∈ ω.W) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨r1, hr1⟩ := h.exists_tail_cell hs0 hs1 hst
  have hr1m : ω.cell s r1 ∈ ω.middle := (h.mem_middle_lt (by omega)).mpr
    (Finset.mem_sdiff.mp hr1)
  have hle : minContent ω.middle ≤ minContent ω.E + s := by
    have := minContent_le (content_mem_contents hr1m)
    rwa [content_cell] at this
  have key : ∀ x ∈ ω.middle, content x = minContent ω.middle → ∃ r, x = ω.cell s r := by
    intro x hx hxc
    obtain ⟨a', r, rfl⟩ := ω.exists_cell x
    rw [content_cell] at hxc
    have hE := (h.mem_E).mp (Finset.mem_sdiff.mp hx).1
    have hxs : a' ≤ s := by omega
    have hxe : ω.cell a' r ∈ ω.E \ ω.W := by
      refine Finset.mem_sdiff.mpr ⟨(h.mem_middle.mp hx).1, (h.mem_middle.mp hx).2.1⟩
    by_cases hlt : a' < s
    · exact absurd (h.tail_of_cell (by omega) (by omega) hxe) (hmin _ (by omega) hlt)
    · have : a' = s := by omega
      subst this
      exact ⟨r, rfl⟩
  constructor
  · rintro ⟨x, hx, hxc, hxW⟩
    obtain ⟨r, rfl⟩ := key x hx hxc
    refine ⟨r, hx, ?_⟩
    have e : ((ω.cell s r).1, (ω.cell s r).2 - 1) = ω.cell (s - 1) r := by
      simp only [cell]; ext
      · rfl
      · simp only; ring
    rwa [e] at hxW
  · rintro ⟨x, hx, hxc, hxW⟩
    obtain ⟨r, rfl⟩ := key x hx hxc
    refine ⟨r, hx, ?_⟩
    have e : ((ω.cell s r).1 + 1, (ω.cell s r).2) = ω.cell (s - 1) (r + 1) := by
      simp only [cell]; ext
      · rfl
      · simp only; ring
    rwa [e] at hxW

/-- With a horizontal lower attachment (cases (a), (c)), the lower middle tail lies southeast
of `W₋`. -/
theorem IsLegalNonempty.lowerH_dLo (h : ω.IsLegalNonempty) (hH : ω.LowerH) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.dLo a ≤ 0 := by
  by_contra hpos
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨s, hs1, hs2, hst, hmin⟩ := h.first_tail ⟨a, h0, h1, Or.inl (by omega)⟩
  obtain ⟨r, hrm, hrW⟩ := (h.first_tail_cell (by omega) hs2 hst hmin).1 hH
  have bA' := h.bit_lo' (a := s - 1 + ω.period) (b := s + ω.period) (by ring) (by omega)
    (by omega)
  have hrW' := h.mem_W.mp hrW
  rw [h.mem_middle_lower (by omega : s < ω.period)] at hrm
  have hint := h.interval_lower (a := s) (by omega) hs2
  have hdLo : ω.dLo s ≤ 0 := by
    unfold dLo dHi at *
    omega
  have prop : ∀ b, s ≤ b → b ≤ ω.widthZ - 1 → ω.dLo b ≤ 0 := by
    intro b hb
    induction b, hb using Int.leInduction with
    | base => intro _; exact hdLo
    | succ b hb ih =>
      intro hb1
      have ih' := ih (by omega)
      have ht := h.tail_mono (by omega) hb (by omega) hst
      have hdHi : ω.dHi b < 0 := by
        unfold TailLower at ht; omega
      exact h.noncross_se_nw (by omega) hb1 hdHi
  have has : s ≤ a := by
    by_contra hlt
    exact hmin a h0 (by omega) (Or.inl (by omega))
  have := prop a has h1
  omega

/-- With a vertical lower attachment (cases (b), (d)), the lower middle tail lies northwest
of `W₋`. -/
theorem IsLegalNonempty.lowerV_dHi (h : ω.IsLegalNonempty) (hV : ω.LowerV) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : 0 ≤ ω.dHi a := by
  by_contra hneg
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨s, hs1, hs2, hst, hmin⟩ := h.first_tail ⟨a, h0, h1, Or.inr (by omega)⟩
  obtain ⟨r, hrm, hrW⟩ := (h.first_tail_cell (by omega) hs2 hst hmin).2 hV
  have bB' := h.bit_hi' (a := s - 1 + ω.period) (b := s + ω.period) (by ring) (by omega)
    (by omega)
  have hrW' := h.mem_W.mp hrW
  rw [h.mem_middle_lower (by omega : s < ω.period)] at hrm
  have hint := h.interval_lower (a := s) (by omega) hs2
  have hdHi : 0 ≤ ω.dHi s := by
    unfold dLo dHi at *
    omega
  have prop : ∀ b, s ≤ b → b ≤ ω.widthZ - 1 → 0 ≤ ω.dHi b := by
    intro b hb
    induction b, hb using Int.leInduction with
    | base => intro _; exact hdHi
    | succ b hb ih =>
      intro hb1
      have ih' := ih (by omega)
      have ht := h.tail_mono (by omega) hb (by omega) hst
      have hdLo : 0 < ω.dLo b := by
        unfold TailLower at ht; omega
      exact h.noncross_nw_se (by omega) hb1 hdLo
  have has : s ≤ a := by
    by_contra hlt
    exact hmin a h0 (by omega) (Or.inr (by omega))
  have := prop a has h1
  omega
end MarkedInner

end SkewMarkedFactor.Gluing
