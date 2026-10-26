/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.OrdinaryFold.Mark


/-!
# Slot data of a legal case-(a) mark

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`.  A legal case-(a) mark
with a nonempty copy, translated to the least content `0`, is the mark `SlotGeom.mark` of its own
diagonal data: the data `SlotGeom` hold with the middle phases `(τ, σ) = (t, s)`, and the end
diagonals of the lower copy satisfy `ℓ_{w-1} = ℓ_w` and `h_{q-1} = h_q`.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

theorem minContent_of_contents_Icc {D : Diagram} {a b : ℤ} (h : contents D = Finset.Icc a b)
    (hab : a ≤ b) : minContent D = a ∧ maxContent D = b := by
  have hne : D.Nonempty := by
    have : a ∈ contents D := by rw [h]; exact Finset.mem_Icc.mpr ⟨le_rfl, hab⟩
    obtain ⟨i, hi⟩ := mem_contents_iff.mp this
    exact ⟨_, hi⟩
  have h1 := minContent_mem hne
  have h2 := maxContent_mem hne
  rw [h, Finset.mem_Icc] at h1 h2
  have h3 : a ∈ contents D := by rw [h]; exact Finset.mem_Icc.mpr ⟨le_rfl, hab⟩
  have h4 : b ∈ contents D := by rw [h]; exact Finset.mem_Icc.mpr ⟨hab, le_rfl⟩
  have := minContent_le h3
  have := le_maxContent h4
  omega

/-- The diagonal shape of a legal mark's inner, in the function form. -/
theorem diagShape_of_legal (h : ω.IsLegalNonempty) :
    DiagShape 0 (ω.period + ω.widthZ - 1) ω.lo ω.hi := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  refine ⟨by omega, fun k h0 h1 => h.lo_le_hi h0 h1, fun k h0 h1 => ?_, fun k h0 h1 => ?_,
    h.lo_zero, h.lo_last⟩
  · exact h.bit_lo (by omega) h1
  · exact h.bit_hi (by omega) h1

/-- The inner translated to the least content `0`. -/
theorem diagSet_E_of_legal (h : ω.IsLegalNonempty) :
    DiagSet (translate (0, -minContent ω.E) ω.E) 0 (ω.period + ω.widthZ - 1) ω.lo ω.hi := by
  intro i k
  rw [mem_translate]
  have e : (i, i + k) - (0, -minContent ω.E) = ω.cell k i := by
    ext <;> simp [cell]
    ring
  rw [e, h.mem_E]

/-- The slot data of a legal case-(a) mark. -/
theorem slotGeom_a_of_legal (h : ω.IsLegalNonempty) (hc : ω.case = .a) {s t : ℤ}
    (hp : ω.IsPhases s t) :
    SlotGeom ω.period ω.widthZ t s ω.rowShift ω.lo ω.hi := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hp
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpa := h.attach.1 hc
  have hsh := diagShape_of_legal h
  have hcm := h.contents_middle ⟨hs1, hs2, ht1, ht2, hS, hT⟩
  have hmm := minContent_of_contents_Icc hcm (by omega)
  have hn := h.nonemptyMark
  have hWd := isConnectedSkew_iff_diagonal.mp hn.2.1
  have hmin := h.minContent_W
  have hspan := span_eq_of_isConnectedSkew hn.2.1
  have hcapB : ω.hi (s - 1) = ω.hi s ∨ ¬ s < ω.widthZ := by
    by_cases hsw : s < ω.widthZ
    · left
      have m1 : minContent ω.E + s ∈ contents ω.W := by
        rw [hWd.mem_contents_iff]; have : (span ω.W : ℤ) = ω.widthZ := rfl
        constructor <;> omega
      have m2 : minContent ω.E + s - 1 ∈ contents ω.W := by
        rw [hWd.mem_contents_iff]; have : (span ω.W : ℤ) = ω.widthZ := rfl
        constructor <;> omega
      have hb := (hWd.2.2.2.1 _ m1 m2).2
      simp only [bitB, Finset.mem_insert, Finset.mem_singleton] at hb
      have e : minContent ω.E + s - 1 = minContent ω.E + (s - 1) := by ring
      rw [e, h.diagHi_W (by omega) (by omega), h.diagHi_W (by omega) (by omega)] at hb
      have d0 := h.sides_a hc (a := s - 1) (by omega) (by omega)
      have d1 := h.sides_a hc (a := s) (by omega) (by omega)
      have d2 : ¬ ω.TailLower (s - 1) := fun hh => by
        have := (hS (s - 1) (by omega) (by omega)).mp hh; omega
      have d3 : ω.TailLower s := (hS s (by omega) (by omega)).mpr le_rfl
      have t1 := h.thin_lower s (by omega) (by omega)
      unfold TailLower at d2 d3
      unfold dLo dHi at d0 d1 d2 d3 t1
      have b1 := h.bit_hi (a := s) (by omega) (by omega)
      omega
    · right; exact hsw
  have hcell : ∀ (a r : ℤ), (r, r + (minContent ω.E + a)) = ω.cell a r := fun a r => rfl
  refine ⟨hw, hq, hs1, hs2, ht1, ht2, hsh, ?_, ?_, ?_, ?_, h.lo_w_eq_hi_w,
    h.lo_pred_period_eq_hi, ?_, ?_, ?_, ?_⟩
  · intro r h0 h1
    have d := h.sides_a hc (a := r) h0 (by omega)
    have d2 := h.thin_upper (a := r) h0 (by omega)
    have d3 : ω.TailUpper r := (hT r h0 (by omega)).mpr h1
    unfold TailUpper at d3
    unfold dLo dHi at d d2 d3
    rw [add_comm ω.period r]
    omega
  · intro r h0 h1
    have d := h.sides_a hc (a := r) (by omega) (by omega)
    have d3 : ¬ ω.TailUpper r := fun hh => by
      have := (hT r (by omega) (by omega)).mp hh; omega
    unfold TailUpper at d3
    unfold dLo dHi at d d3
    rw [add_comm ω.period r]
    omega
  · intro r h0 h1
    have d := h.sides_a hc (a := r) h0 (by omega)
    have d3 : ¬ ω.TailLower r := fun hh => by
      have := (hS r h0 (by omega)).mp hh; omega
    unfold TailLower at d3
    unfold dLo dHi at d d3
    rw [add_comm ω.period r]
    omega
  · intro r h0 h1
    have d := h.sides_a hc (a := r) (by omega) (by omega)
    have d2 := h.thin_lower r (by omega) (by omega)
    have d3 : ω.TailLower r := (hS r (by omega) (by omega)).mpr h0
    unfold TailLower at d3
    unfold dLo dHi at d d2 d3
    rw [add_comm ω.period r]
    omega
  · intro r h0 h1
    by_cases hr : s ≤ r
    · obtain ⟨ρ, a1, a2, a3, a4⟩ := h.W_row (a := r) h0 (by omega)
      have d := h.sides_a hc (a := r) h0 (by omega)
      have d2 := h.thin_lower r h0 (by omega)
      have d3 : ω.TailLower r := (hS r h0 (by omega)).mpr hr
      unfold TailLower at d3
      unfold dLo dHi at d d2 d3
      simp only [hr, ite_true]
      omega
    · have := h.lo_le_hi (a := r) h0 (by omega)
      simp only [hr, ite_false]
      omega
  · intro hsw
    rcases hcapB with hb | hb
    · exact hb
    · exact absurd hsw hb
  · obtain ⟨x, hx, hxc, hxW⟩ := hpa.1
    obtain ⟨a, r, rfl⟩ := ω.exists_cell x
    rw [content_cell, hmm.1] at hxc
    have ha : a = s := by omega
    subst ha
    have e : ((ω.cell a r).1, (ω.cell a r).2 - 1) = ω.cell (a - 1) r := by
      simp only [cell]; ext
      · rfl
      · simp only; ring
    rw [e] at hxW
    have h1 := (h.mem_W.mp hxW)
    have h2 := (h.mem_E.mp (h.mem_middle.mp hx).1)
    omega
  · obtain ⟨x, hx, hxc, hxU⟩ := hpa.2
    obtain ⟨a, r, rfl⟩ := ω.exists_cell x
    rw [content_cell, hmm.2] at hxc
    have ha : a = ω.period + t - 1 := by omega
    subst ha
    have e : ((ω.cell (ω.period + t - 1) r).1, (ω.cell (ω.period + t - 1) r).2 + 1) =
        ω.cell (ω.period + t) r := by
      simp only [cell]; ext
      · rfl
      · simp only; ring
    rw [e] at hxU
    have h1 := h.mem_E.mp (hn.2.2.2.1 hxU)
    have h2 := (h.mem_E.mp (h.mem_middle.mp hx).1)
    omega

end SkewClassInflation
