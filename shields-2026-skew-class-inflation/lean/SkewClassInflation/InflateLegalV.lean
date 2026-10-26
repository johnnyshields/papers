/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalSlot
import SkewGluing.OrdinaryFold.Mark
import SkewClassInflation.InflateConnected

/-!
# Vertical inflation in diagonal-function form

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, case (b).  Antitransposition
turns the east inflation of a case-(b) mark into the vertical inflation \(D\mapsto D\cup(D-(1,0))\)
of a case-(a) mark.  A diagram with the rows \([\mathrm{lo}\,k,\mathrm{hi}\,k]\) on the contents
\(0\le k\le M\) inflates vertically to the diagram with the rows
\([\mathrm{lo}(k-1)-1,\mathrm{hi}\,k]\), and the slot data of a case-(a) mark of width \(w\) and
phases \((\tau,\sigma)\) become slot data of width \(w+1\) and phases \((\tau+1,\sigma)\) under the
two private pinches.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing (Diagram DiagSet DiagShape SlotGeom)

/-- Vertical inflation: every column gains one cell to the north. -/
def vInflateCells (D : Diagram) : Diagram := D ∪ SkewGluing.translate (-1, 0) D

theorem mem_vInflateCells {D : Diagram} {a b : ℤ} :
    (a, b) ∈ vInflateCells D ↔ (a, b) ∈ D ∨ (a + 1, b) ∈ D := by
  unfold vInflateCells
  rw [Finset.mem_union, SkewGluing.mem_translate]
  simp only [Prod.mk_sub_mk, sub_neg_eq_add, sub_zero]

/-- First rows of the vertically inflated diagram. -/
def loV (lo : ℤ → ℤ) (k : ℤ) : ℤ := if k = 0 then lo 0 else lo (k - 1) - 1

/-- Last rows of the vertically inflated diagram. -/
def hiV (M : ℤ) (hi : ℤ → ℤ) (k : ℤ) : ℤ := if k ≤ M then hi k else hi M - 1

theorem loV_zero {lo : ℤ → ℤ} : loV lo 0 = lo 0 := by simp [loV]

theorem loV_of_pos {lo : ℤ → ℤ} {k : ℤ} (h : 1 ≤ k) : loV lo k = lo (k - 1) - 1 := by
  unfold loV; rw [if_neg (by omega)]

theorem hiV_of_le {M : ℤ} {hi : ℤ → ℤ} {k : ℤ} (h : k ≤ M) : hiV M hi k = hi k := by
  unfold hiV; rw [if_pos h]

theorem hiV_succ {M : ℤ} {hi : ℤ → ℤ} : hiV M hi (M + 1) = hi M - 1 := by
  unfold hiV; rw [if_neg (by omega)]

theorem diagShape_vinflate {M : ℤ} {lo hi : ℤ → ℤ} (hs : DiagShape 0 M lo hi) :
    DiagShape 0 (M + 1) (loV lo) (hiV M hi) := by
  have hM := hs.le
  refine ⟨by omega, fun k h0 h1 => ?_, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, ?_⟩
  · by_cases hk0 : k = 0
    · subst hk0
      rw [loV_zero, hiV_of_le hM]
      exact hs.ne 0 le_rfl hM
    by_cases hk1 : k = M + 1
    · subst hk1
      rw [loV_of_pos (by omega), hiV_succ]
      have := hs.ne M hM le_rfl
      simp only [add_sub_cancel_right]
      omega
    · have := hs.ne k (by omega) (by omega)
      have h2 := hs.stepLo k (by omega) (by omega)
      rw [loV_of_pos (by omega), hiV_of_le (by omega)]
      omega
  · by_cases hk1 : k = 1
    · subst hk1
      unfold loV
      simp
    · have := hs.stepLo (k - 1) (by omega) (by omega)
      rw [loV_of_pos (by omega), loV_of_pos (by omega)]
      omega
  · by_cases hk1 : k = M + 1
    · subst hk1
      rw [hiV_succ, hiV_of_le (by omega)]
      simp
    · have := hs.stepHi k h0 (by omega)
      rw [hiV_of_le (by omega), hiV_of_le (by omega)]
      exact this
  · rw [loV_zero, hiV_of_le hM]
    exact hs.endLo
  · rw [loV_of_pos (by omega), hiV_succ]
    simp only [add_sub_cancel_right]
    have := hs.endHi
    omega

theorem diagSet_vinflate {M : ℤ} {lo hi : ℤ → ℤ} {G : Diagram} (hG : DiagSet G 0 M lo hi)
    (hs : DiagShape 0 M lo hi) :
    DiagSet (vInflateCells G) 0 (M + 1) (loV lo) (hiV M hi) := by
  have hM := hs.le
  intro i k
  rw [mem_vInflateCells]
  have e : i + 1 + (k - 1) = i + k := by ring
  have e2 : (i + 1, i + k) = (i + 1, i + 1 + (k - 1)) := by rw [e]
  rw [e2, hG, hG]
  by_cases hk0 : k < 0
  · constructor
    · rintro (h | h) <;> omega
    · intro h; omega
  by_cases hk2 : M + 1 < k
  · constructor
    · rintro (h | h) <;> omega
    · intro h; omega
  by_cases hk : k = 0
  · subst hk
    rw [loV_zero, hiV_of_le hM]
    constructor
    · rintro (h | h)
      · exact ⟨le_rfl, by omega, h.2.2.1, h.2.2.2⟩
      · omega
    · intro h
      left
      exact ⟨le_rfl, hM, h.2.2.1, h.2.2.2⟩
  by_cases hkM : k = M + 1
  · subst hkM
    rw [loV_of_pos (by omega), hiV_succ]
    simp only [add_sub_cancel_right]
    constructor
    · rintro (h | h)
      · omega
      · exact ⟨by omega, by omega, by omega, by omega⟩
    · intro h
      right
      exact ⟨by omega, by omega, by omega, by omega⟩
  · have h1 := hs.stepLo k (by omega) (by omega)
    have h2 := hs.stepHi k (by omega) (by omega)
    have h3 := hs.ne k (by omega) (by omega)
    have h4 := hs.ne (k - 1) (by omega) (by omega)
    rw [loV_of_pos (by omega), hiV_of_le (by omega)]
    constructor
    · rintro (h | h)
      · exact ⟨by omega, by omega, by omega, by omega⟩
      · exact ⟨by omega, by omega, by omega, by omega⟩
    · intro h
      by_cases hi' : lo k ≤ i
      · left; exact ⟨by omega, by omega, hi', by omega⟩
      · right; exact ⟨by omega, by omega, by omega, by omega⟩

theorem slotGeom_vinflate {q w τ σ p : ℤ} {lo hi : ℤ → ℤ} (hs : SlotGeom q w τ σ p lo hi)
    (hw1 : w + 1 < q) (Y1 : lo (q - 1) = lo 0 + p) (Y2 : hi (q + w - 1) = hi w + p)
    (c1 : lo (w - 1) = lo w) (P1 : hi (w + 1) = hi w - 1) (P2 : lo (q - 2) = lo (q - 1) + 1) :
    SlotGeom q (w + 1) (τ + 1) σ p (loV lo) (hiV (q + w - 1) hi) := by
  have hw := hs.w_pos
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  have sh := hs.shape
  refine ⟨by omega, hw1, hσ, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have := diagShape_vinflate sh
    rwa [show q + w - 1 + 1 = q + (w + 1) - 1 by ring] at this
  · intro r h0 h1
    rw [loV_of_pos (by omega)]
    by_cases hr : r = 0
    · subst hr
      rw [loV_zero]
      simp only [add_zero] at *
      omega
    · rw [loV_of_pos (by omega)]
      have := hs.elo_lt (r - 1) (by omega) (by omega)
      rw [show q + (r - 1) = q + r - 1 by ring] at this
      omega
  · intro r h0 h1
    rw [loV_of_pos (by omega), loV_of_pos (by omega)]
    have := hs.elo_ge (r - 1) (by omega) (by omega)
    rw [show q + (r - 1) = q + r - 1 by ring] at this
    omega
  · intro r h0 h1
    rw [hiV_of_le (by omega), hiV_of_le (by omega)]
    exact hs.ehi_lt r h0 h1
  · intro r h0 h1
    by_cases hr : r < w
    · rw [hiV_of_le (by omega), hiV_of_le (by omega)]
      exact hs.ehi_ge r h0 hr
    · have hrw : r = w := by omega
      subst hrw
      have h3 : hiV (q + r - 1) hi (q + r) = hi (q + r - 1) - 1 := by
        have := @hiV_succ (q + r - 1) hi
        rwa [sub_add_cancel] at this
      rw [h3, hiV_of_le (by omega)]
      omega
  · rw [loV_of_pos (by omega), hiV_of_le (by omega)]
    simp only [add_sub_cancel_right]
    have := hs.sing_w
    omega
  · rw [loV_of_pos (by omega), hiV_of_le (by omega), show q - 1 - 1 = q - 2 by ring]
    have := hs.sing_q
    omega
  · intro r h0 h1
    have hp := hs.pos
    by_cases hr0 : r = 0
    · subst hr0
      rw [loV_zero, hiV_of_le (by omega)]
      have := hp 0 le_rfl (by omega)
      simp only [show ¬ (σ ≤ 0) by omega, ite_false] at this ⊢
      omega
    · rw [loV_of_pos (by omega), hiV_of_le (by omega)]
      by_cases hr : r < w
      · have := hp r h0 hr
        have b := sh.stepLo r (by omega) (by omega)
        split_ifs at this ⊢ <;> omega
      · have hrw : r = w := by omega
        subst hrw
        have := hs.sing_w
        simp only [show σ ≤ r by omega, ite_true]
        omega
  · intro hlt
    rw [hiV_of_le (by omega), hiV_of_le (by omega)]
    by_cases hσ' : σ < w
    · exact hs.capB hσ'
    · have hσw' : σ = w := by omega
      subst hσw'
      have := hs.ehi_lt (σ - 1) (by omega) (by omega)
      rw [show q + (σ - 1) = q + σ - 1 by ring] at this
      omega
  · rw [hiV_of_le (by omega)]
    by_cases hs1 : σ = 1
    · subst hs1
      simp only [sub_self]
      rw [loV_zero]
      exact hs.lowerH
    · rw [loV_of_pos (by omega)]
      have b := sh.stepLo (σ - 1) (by omega) (by omega)
      have := hs.lowerH
      omega
  · have e1 : q + (τ + 1) - 1 - 1 = q + τ - 1 := by ring
    rw [loV_of_pos (by omega), e1]
    have := hs.upperH
    by_cases hτ : τ + 1 < w
    · have e2 : q + (τ + 1) = q + τ + 1 := by ring
      rw [e2, hiV_of_le (by omega)]
      have b := sh.stepHi (q + τ + 1) (by omega) (by omega)
      rw [show q + τ + 1 - 1 = q + τ by ring] at b
      omega
    · have hτ' : τ + 1 = w := by omega
      have h3 : hiV (q + w - 1) hi (q + (τ + 1)) = hi (q + w - 1) - 1 := by
        have := @hiV_succ (q + w - 1) hi
        rw [sub_add_cancel] at this
        rw [← this]
        congr 1
        omega
      rw [h3]
      have this' : lo (q + τ - 1) ≤ hi (q + w - 1) := by
        have hq : q + τ = q + w - 1 := by omega
        rw [← hq]; exact this
      omega

end SkewClassInflation
