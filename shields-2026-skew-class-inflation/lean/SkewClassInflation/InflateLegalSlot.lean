/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalDiag
import SkewGluing.OrdinaryFold.Mark

/-!
# Inflated slot data

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, case (a), \(0<w<q-1\).
The diagonal data `SlotGeom` of a case-(a) mark of period \(q\), width \(w\) and phases
\((\tau,\sigma)\) give, after inflation, diagonal data of period \(q\), width \(w+1\) and phases
\((\tau,\sigma+1)\), provided the two private pinches hold.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing (Diagram DiagSet DiagShape SlotGeom)

theorem slotGeom_inflate {q w τ σ p : ℤ} {lo hi : ℤ → ℤ} (hs : SlotGeom q w τ σ p lo hi)
    (hw1 : w + 1 < q) (c1 : lo (w - 1) = lo w) (c2 : hi (q - 1) = hi q)
    (h1 : lo (w + 1) = lo w) (h2 : hi (q - 2) = hi (q - 1)) :
    SlotGeom q (w + 1) τ (σ + 1) p (loI (q + w - 1) lo) (hiI hi) := by
  have hw := hs.w_pos
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  have sh := hs.shape
  refine ⟨by omega, hw1, by omega, by omega, hτ0, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have := diagShape_inflate sh
    rwa [show q + w - 1 + 1 = q + (w + 1) - 1 by ring] at this
  · intro r h0 h1'
    rw [loI_of_le (by omega), loI_of_le (by omega)]
    exact hs.elo_lt r h0 h1'
  · intro r h0 h1'
    by_cases hr : r < w
    · rw [loI_of_le (by omega), loI_of_le (by omega)]
      exact hs.elo_ge r h0 hr
    · have hrw : r = w := by omega
      have e := hs.elo_ge (w - 1) (by omega) (by omega)
      have e2 : q + (w - 1) = q + w - 1 := by ring
      rw [e2] at e
      rw [hrw]
      unfold loI
      rw [min_eq_right (by omega), min_eq_left (by omega)]
      omega
  · intro r h0 h1'
    by_cases hr : r = 0
    · subst hr
      rw [hiI_of_pos (by omega), hiI_zero]
      have := hs.ehi_lt 0 le_rfl (by omega)
      simp only [add_zero] at this ⊢
      omega
    · rw [hiI_of_pos (by omega), hiI_of_pos (by omega)]
      have := hs.ehi_lt (r - 1) (by omega) (by omega)
      have e2 : q + (r - 1) = q + r - 1 := by ring
      rw [e2] at this
      exact this
  · intro r h0 h1'
    rw [hiI_of_pos (by omega), hiI_of_pos (by omega)]
    have := hs.ehi_ge (r - 1) (by omega) (by omega)
    have e2 : q + (r - 1) = q + r - 1 := by ring
    rw [e2] at this
    exact this
  · rw [loI_of_le (by omega), hiI_of_pos (by omega)]
    simp only [add_sub_cancel_right]
    have := hs.sing_w
    omega
  · rw [loI_of_le (by omega), hiI_of_pos (by omega), show q - 1 - 1 = q - 2 by ring]
    have := hs.sing_q
    omega
  · intro r h0 h1'
    have hp := hs.pos
    by_cases hr : r < w
    · rw [loI_of_le (by omega)]
      by_cases hr0 : r = 0
      · subst hr0
        rw [hiI_zero]
        have := hp 0 le_rfl (by omega)
        simp only [show ¬ (σ ≤ 0) by omega, ite_false] at this
        simp only [show ¬ (σ + 1 ≤ 0) by omega, ite_false]
        omega
      · rw [hiI_of_pos (by omega)]
        have := hp r h0 hr
        have b := sh.stepHi r (by omega) (by omega)
        split_ifs at this ⊢ <;> omega
    · have : r = w := by omega
      subst this
      rw [loI_of_le (by omega), hiI_of_pos (by omega)]
      have := hp (r - 1) (by omega) (by omega)
      have b := sh.stepLo r (by omega) (by omega)
      have s1 := hs.sing_w
      split_ifs at this ⊢ <;> omega
  · intro hlt
    have := hs.capB (by omega)
    rw [show σ + 1 - 1 = σ by ring, hiI_of_pos (by omega), hiI_of_pos (by omega)]
    simpa using this
  · rw [show σ + 1 - 1 = σ by ring, loI_of_le (by omega), hiI_of_pos (by omega)]
    simp only [add_sub_cancel_right]
    exact sh.ne σ (by omega) (by omega)
  · rw [show q + τ - 1 = q + τ - 1 by ring, loI_of_le (by omega), hiI_of_pos (by omega)]
    exact sh.ne (q + τ - 1) (by omega) (by omega)

end SkewClassInflation
