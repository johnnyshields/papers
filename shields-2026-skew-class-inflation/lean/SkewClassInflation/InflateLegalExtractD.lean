/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalMixed
import SkewClassInflation.InflateLegalExtractA
import SkewClassInflation.InflateLegalTranslate

/-!
# Diagonal data of a legal case-(d) mark

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`.  A legal case-(d) mark
with a nonempty copy, translated to the least content `0`, satisfies the diagonal data
`MixFoldDiag`, and its full intersection is `mixFoldMark`.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

theorem period_toNat (h : ω.IsLegalNonempty) : ((ω.period.toNat : ℕ) : ℤ) = ω.period := by
  have := h.width_lt_period
  have := h.width_pos
  exact Int.toNat_of_nonneg (by omega)

theorem mixFoldDiag_of_legal (h : ω.IsLegalNonempty) (hc : ω.case = .d) {s t : ℤ}
    (hp : ω.IsPhases s t) :
    MixFoldDiag (translate (0, -minContent ω.E) ω.E) ω.period.toNat ω.width ω.rowShift s t := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpt := period_toNat h
  have hG := diagSet_E_of_legal h
  have hsh := diagShape_of_legal h
  have hwz : (ω.width : ℤ) = ω.widthZ := rfl
  have hLo : ∀ a, 0 ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      diagLo (translate (0, -minContent ω.E) ω.E) a = ω.lo a := fun a h0 h1 =>
    hG.diagLo_eq hsh h0 h1
  have hHi : ∀ a, 0 ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      diagHi (translate (0, -minContent ω.E) ω.E) a = ω.hi a := fun a h0 h1 =>
    hG.diagHi_eq hsh h0 h1
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hp
  have hlt := (h.phases_lt (by rw [hc]; right; rfl) ⟨hs1, hs2, ht1, ht2, hS, hT⟩)
  have hpa := h.attach.2.2.2 hc
  have hcapV := h.lower_caps_V hpa.1
  have hcapH := h.upper_caps_H hpa.2
  have hdt : ∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 →
      ω.hi (a + ω.period) = ω.hi a + ω.rowShift ∧
      ω.lo (a + ω.period) = ω.lo a + ω.rowShift +
        (if a < t then -1 else if a < s then 0 else 1) := by
    intro a h0 h1
    have d := h.sides_d hc h0 h1
    have d1 := h.thin_lower a h0 h1
    have d2 := h.thin_upper h0 h1
    have u1 := (hS a h0 h1)
    have u2 := (hT a h0 h1)
    unfold TailLower at u1
    unfold TailUpper at u2
    unfold dLo dHi at d d1 d2 u1 u2
    refine ⟨by omega, ?_⟩
    split_ifs with h3 h4
    · have := u2.mpr h3; omega
    · have := mt u1.mp (show ¬ s ≤ a by omega); omega
    · have := u1.mpr (by omega); omega
  have wz : ∀ a : ℤ, a < (ω.width : ℤ) ↔ a < ω.widthZ := fun a => Iff.rfl
  refine ⟨hG.isConnectedSkew hsh, hG.minContent_eq hsh, ?_, ?_, ?_, ht1, hlt, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [span_translate]
    have := h.span_eq
    omega
  · have := hw; unfold MarkedInner.widthZ at this; omega
  · have := hwz; omega
  · omega
  · intro a h0 h1
    simp only [hpt]
    have := (hdt a h0 (by omega)).1
    rw [hHi (a + ω.period) (by omega) (by omega), hHi a (by omega) (by omega)]
    exact this
  · intro a h0 h1
    simp only [hpt]
    have := (hdt a h0 (by omega)).2
    rw [hLo (a + ω.period) (by omega) (by omega), hLo a (by omega) (by omega)]
    exact this
  · simp only [hwz]
    rw [hLo _ (by omega) (by omega), hHi _ (by omega) (by omega)]
    exact h.lo_w_eq_hi_w
  · simp only [hpt]
    rw [hLo _ (by omega) (by omega), hHi _ (by omega) (by omega)]
    exact h.lo_pred_period_eq_hi
  · have d1 := (hdt (s - 1) (by omega) (by omega)).2
    simp only [show ¬ (s - 1 < t) by omega, show s - 1 < s by omega, ite_true,
      ite_false] at d1
    rw [hLo _ (by omega) (by omega), hLo _ (by omega) (by omega)]
    by_cases hsw : s < ω.widthZ
    · have d2 := (hdt s (by omega) (by omega)).2
      have b1 := h.bit_lo' (a := s - 1) (b := s) (by ring) (by omega) (by omega)
      have b2 := h.bit_lo' (a := s - 1 + ω.period) (b := s + ω.period) (by ring) (by omega)
        (by omega)
      simp only [show ¬ (s < s) by omega, show ¬ (s < t) by omega, ite_false] at d2
      omega
    · have hsw' : s = ω.widthZ := by omega
      have cv := hcapV.2.2
      unfold dLo at cv
      subst hsw'
      omega
  · intro ht0
    simp only [hpt]
    rw [hHi _ (by omega) (by omega), hHi _ (by omega) (by omega)]
    have := hcapH.2.1
    omega
  · intro ht0
    simp only [hpt]
    have d1 := (hdt (t - 1) (by omega) (by omega)).2
    have d2 := (hdt t (by omega) (by omega)).2
    have b1 := h.bit_lo' (a := t - 1) (b := t) (by ring) (by omega) (by omega)
    have b2 := h.bit_lo' (a := t - 1 + ω.period) (b := t + ω.period) (by ring) (by omega)
      (by omega)
    rw [hLo _ (by omega) (by omega), hLo _ (by omega) (by omega)]
    simp only [show t - 1 < t by omega, show ¬ (t < t) by omega, show t < s by omega, ite_true,
      ite_false] at d1 d2
    have e1 : ω.period + t - 1 = t - 1 + ω.period := by ring
    have e2 : ω.period + t = t + ω.period := by ring
    rw [e1, e2]
    omega

end SkewClassInflation
