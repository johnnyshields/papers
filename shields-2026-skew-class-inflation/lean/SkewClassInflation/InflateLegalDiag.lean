/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateConnected
import SkewGluing.OrdinaryFold.Interval

/-!
# Inflation in diagonal-function form

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`.  A diagram with the
rows \([\mathrm{lo}\,k,\mathrm{hi}\,k]\) on the contents \(0\le k\le M\) inflates to the diagram with the rows
\([\mathrm{lo}(\min(k,M)),\mathrm{hi}(\max(k-1,0))]\) on the contents \(0\le k\le M+1\).
Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing (Diagram DiagSet DiagShape)

/-- First rows of the inflated diagram. -/
def loI (M : ℤ) (lo : ℤ → ℤ) (k : ℤ) : ℤ := lo (min k M)

/-- Last rows of the inflated diagram. -/
def hiI (hi : ℤ → ℤ) (k : ℤ) : ℤ := hi (max (k - 1) 0)

theorem loI_of_le {M : ℤ} {lo : ℤ → ℤ} {k : ℤ} (h : k ≤ M) : loI M lo k = lo k := by
  unfold loI; rw [min_eq_left h]

theorem loI_succ {M : ℤ} {lo : ℤ → ℤ} : loI M lo (M + 1) = lo M := by
  unfold loI; rw [min_eq_right (by omega)]

theorem hiI_of_pos {hi : ℤ → ℤ} {k : ℤ} (h : 1 ≤ k) : hiI hi k = hi (k - 1) := by
  unfold hiI; rw [max_eq_left (by omega)]

theorem hiI_zero {hi : ℤ → ℤ} : hiI hi 0 = hi 0 := by
  unfold hiI; rw [max_eq_right (by omega)]

theorem diagShape_inflate {M : ℤ} {lo hi : ℤ → ℤ} (hs : DiagShape 0 M lo hi) :
    DiagShape 0 (M + 1) (loI M lo) (hiI hi) := by
  have hM := hs.le
  refine ⟨by omega, fun k h0 h1 => ?_, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, ?_⟩
  · by_cases hk0 : k = 0
    · subst hk0
      rw [loI_of_le hM, hiI_zero]
      exact hs.ne 0 le_rfl hM
    by_cases hk1 : k = M + 1
    · subst hk1
      rw [loI_succ, hiI_of_pos (by omega)]
      simpa using hs.ne M hM le_rfl
    · have := hs.ne k (by omega) (by omega)
      have h2 := hs.stepHi k (by omega) (by omega)
      rw [loI_of_le (by omega), hiI_of_pos (by omega)]
      omega
  · by_cases hk1 : k = M + 1
    · subst hk1
      rw [loI_succ, loI_of_le (by omega)]
      simp
    · have := hs.stepLo k h0 (by omega)
      rw [loI_of_le (by omega), loI_of_le (by omega)]
      exact this
  · by_cases hk1 : k = 1
    · subst hk1
      rw [hiI_of_pos le_rfl, show (1 : ℤ) - 1 = 0 by norm_num, hiI_zero]
      simp
    · have := hs.stepHi (k - 1) (by omega) (by omega)
      rw [hiI_of_pos (by omega), hiI_of_pos (by omega)]
      exact this
  · rw [loI_of_le hM, hiI_zero]
    exact hs.endLo
  · rw [loI_succ, hiI_of_pos (by omega)]
    simpa using hs.endHi

theorem diagSet_inflate {M : ℤ} {lo hi : ℤ → ℤ} {G : Diagram} (hG : DiagSet G 0 M lo hi)
    (hs : DiagShape 0 M lo hi) : DiagSet (inflateCells G) 0 (M + 1) (loI M lo) (hiI hi) := by
  have hM := hs.le
  intro i k
  rw [mem_inflateCells]
  have e : i + k - 1 = i + (k - 1) := by ring
  rw [e, hG, hG]
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
    rw [loI_of_le hM, hiI_zero]
    constructor
    · rintro (h | h)
      · exact ⟨by omega, by omega, h.2.2.1, h.2.2.2⟩
      · omega
    · intro h
      left
      exact ⟨le_rfl, hM, h.2.2.1, h.2.2.2⟩
  by_cases hkM : k = M + 1
  · subst hkM
    rw [loI_succ, hiI_of_pos (by omega)]
    constructor
    · rintro (h | h)
      · omega
      · exact ⟨by omega, by omega, by simpa using h.2.2.1, h.2.2.2⟩
    · intro h
      right
      exact ⟨by omega, by omega, by simpa using h.2.2.1, h.2.2.2⟩
  · have h1 := hs.stepLo k (by omega) (by omega)
    have h2 := hs.stepHi k (by omega) (by omega)
    have h3 := hs.ne k (by omega) (by omega)
    have h4 := hs.ne (k - 1) (by omega) (by omega)
    rw [loI_of_le (by omega), hiI_of_pos (by omega)]
    constructor
    · rintro (h | h) <;> refine ⟨by omega, by omega, by omega, by omega⟩
    · intro h
      by_cases hi' : i ≤ hi k
      · left; exact ⟨by omega, by omega, by omega, hi'⟩
      · right; exact ⟨by omega, by omega, by omega, by omega⟩

end SkewClassInflation
