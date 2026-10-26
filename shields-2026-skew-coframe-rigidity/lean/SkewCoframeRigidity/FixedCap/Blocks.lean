/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.BlockId

/-!
# The next strict block

For a connected normalized diagram with a cut at `q`, the next cut `r` bounds the next strict block
of the proper matrix.  The block is either the true unit, or a connected normalized diagram `E`
obtained by translating the rows and columns `q, …, r - 1` down by its last column
(`blockOf`).  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The block of the proper indices `q, …, q + m0` of `D`, translated by its last column. -/
def blockOf (D : BetaDiagram (n + 1)) (q m0 : ℕ) (hr : q + m0 + 1 ≤ n)
    (hpos : ∀ i : Fin (m0 + 1), D.col ⟨q + i.val, by omega⟩ < D.row ⟨q + 1 + i.val, by omega⟩) :
    BetaDiagram (m0 + 1) where
  row i := D.row ⟨q + 1 + i.val, by omega⟩ - D.col ⟨q + m0, by omega⟩
  col i := D.col ⟨q + i.val, by omega⟩ - D.col ⟨q + m0, by omega⟩
  row_strictAnti := fun i j hij => by
    beta_reduce
    have := D.row_strictAnti (show (⟨q + 1 + i.val, by omega⟩ : Fin (n + 1)) <
      ⟨q + 1 + j.val, by omega⟩ from by rw [Fin.lt_def]; simp; exact hij)
    omega
  col_strictAnti := fun i j hij => by
    beta_reduce
    have := D.col_strictAnti (show (⟨q + i.val, by omega⟩ : Fin (n + 1)) <
      ⟨q + j.val, by omega⟩ from by rw [Fin.lt_def]; simp; exact hij)
    omega
  row_nonempty := fun i => by
    have := hpos i
    omega

theorem blockOf_blockRel (D : BetaDiagram (n + 1)) (q m0 : ℕ) (hr : q + m0 + 1 ≤ n) (hpos) :
    BlockRel D q m0 (blockOf D q m0 hr hpos) (D.col ⟨q + m0, by omega⟩) where
  hr := hr
  row := fun i => by simp [blockOf]
  col := fun i => by simp [blockOf]

theorem blockOf_isNorm (D : BetaDiagram (n + 1)) (q m0 : ℕ) (hr : q + m0 + 1 ≤ n) (hpos) :
    IsNorm (blockOf D q m0 hr hpos) := by
  change D.col ⟨q + (Fin.last m0).val, _⟩ - D.col ⟨q + m0, _⟩ = 0
  simp

theorem blockOf_connected {D : BetaDiagram (n + 1)} (q m0 : ℕ) (hr : q + m0 + 1 ≤ n) (hpos)
    (hnc : ∀ i : ℕ, ∀ hi : i < m0, D.col ⟨q + i, by omega⟩ ≤ D.row ⟨q + i + 2, by omega⟩) :
    (blockOf D q m0 hr hpos).Connected := by
  refine ⟨Nat.succ_pos _, fun i hi => ?_⟩
  have := hnc i.val (by omega)
  change D.col ⟨q + i.val, _⟩ - _ ≤ D.row ⟨q + 1 + (i.val + 1), _⟩ - _
  have e : (⟨q + 1 + (i.val + 1), by omega⟩ : Fin (n + 1)) = ⟨q + i.val + 2, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [e]
  omega

/-- A cut at `j` is the single condition on the last prefix column and the next row. -/
theorem cutAt_iff {D : BetaDiagram (n + 1)} {j : ℕ} (hj0 : 0 < j) (hjn : j < n) :
    CutAt D j ↔ D.row ⟨j + 1, by omega⟩ < D.col ⟨j - 1, by omega⟩ := by
  constructor
  · intro h
    have := h ⟨j, hjn⟩ ⟨j - 1, by omega⟩ le_rfl (by simp; omega)
    exact this
  · intro h i i' hi hi'
    have h1 : D.row i.succ ≤ D.row ⟨j + 1, by omega⟩ :=
      D.row_strictAnti.antitone (by rw [Fin.le_def]; simp; omega)
    have h2 : D.col ⟨j - 1, by omega⟩ ≤ D.col i'.castSucc :=
      D.col_strictAnti.antitone (by rw [Fin.le_def]; simp; omega)
    omega

theorem cutAt_n (D : BetaDiagram (n + 1)) : CutAt D n := fun i _ hi _ => by
  have := i.2; omega

theorem cutAt_zero (D : BetaDiagram (n + 1)) : CutAt D 0 := fun _ j _ hj => by omega

/-- **The next strict block.**  The first cut `r` after `q` bounds a block that is either the true
unit (`r = q + 1` with a zero diagonal entry) or a connected normalized diagram. -/
theorem exists_block {D : BetaDiagram (n + 1)} (hDc : D.Connected) {q : ℕ} (hqn : q < n) :
    ∃ r, q < r ∧ r ≤ n ∧ CutAt D r ∧ (∀ j, q < j → j < r → ¬ CutAt D j) ∧
      ((r = q + 1 ∧ D.col ⟨q, by omega⟩ = D.row ⟨q + 1, by omega⟩) ∨
        ∃ (m0 : ℕ) (E : BetaDiagram (m0 + 1)) (b0 : ℤ), r = q + m0 + 1 ∧ IsNorm E ∧
          E.Connected ∧ BlockRel D q m0 E b0 ∧ ∀ i : Fin (m0 + 1), 0 < E.row i - E.col i) := by
  classical
  have hex : ∃ r, q < r ∧ r ≤ n ∧ CutAt D r := ⟨n, hqn, le_rfl, cutAt_n D⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ {j : ℕ}, j < Nat.find hex → ¬ (q < j ∧ j ≤ n ∧ CutAt D j) :=
    fun {j} hj => Nat.find_min hex hj
  set r := Nat.find hex with hr
  obtain ⟨hqr, hrn, hcr⟩ := hspec
  have hmin' : ∀ j, q < j → j < r → ¬ CutAt D j := fun j h1 h2 hc =>
    hmin h2 ⟨h1, by omega, hc⟩
  refine ⟨r, hqr, hrn, hcr, hmin', ?_⟩
  by_cases hall : ∀ i : ℕ, ∀ hi : q ≤ i ∧ i < r, D.col ⟨i, by omega⟩ < D.row ⟨i + 1, by omega⟩
  · right
    obtain ⟨m0, hm0⟩ : ∃ m0, r = q + m0 + 1 := ⟨r - q - 1, by omega⟩
    have hr' : q + m0 + 1 ≤ n := by omega
    have hpos : ∀ i : Fin (m0 + 1), D.col ⟨q + i.val, by omega⟩ <
        D.row ⟨q + 1 + i.val, by omega⟩ := fun i => by
      have := hall (q + i.val) ⟨by omega, by omega⟩
      have e : (⟨q + 1 + i.val, by omega⟩ : Fin (n + 1)) = ⟨q + i.val + 1, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e]; exact this
    refine ⟨m0, blockOf D q m0 hr' hpos, _, hm0, blockOf_isNorm D q m0 hr' hpos,
      blockOf_connected q m0 hr' hpos (fun i hi => ?_), blockOf_blockRel D q m0 hr' hpos,
      fun i => ?_⟩
    · have hj := hmin' (q + i + 1) (by omega) (by omega)
      rw [cutAt_iff (by omega) (by omega), not_lt] at hj
      exact hj
    · have := hpos i
      change 0 < D.row _ - D.col _ - (D.col _ - D.col _)
      omega
  · left
    push Not at hall
    obtain ⟨i, hi, hile⟩ := hall
    have hdiag := hDc.2 ⟨i, by omega⟩ (by simp; omega)
    have hui : D.col ⟨i, by omega⟩ = D.row ⟨i + 1, by omega⟩ := le_antisymm hdiag (by
      simpa using hile)
    have hcut1 : CutAt D (i + 1) := by
      by_cases h : i + 1 = n
      · rw [h]; exact cutAt_n D
      · rw [cutAt_iff (by omega) (by omega)]
        have := D.row_strictAnti (show (⟨i + 1, by omega⟩ : Fin (n + 1)) <
          ⟨i + 1 + 1, by omega⟩ from by rw [Fin.lt_def]; simp)
        simp only [Nat.add_sub_cancel]
        omega
    have hri : r ≤ i + 1 := by
      by_contra hlt
      exact hmin' (i + 1) (by omega) (by omega) hcut1
    have hiq : i = q := by
      by_contra hne
      have hcut2 : CutAt D i := by
        rw [cutAt_iff (by omega) (by omega)]
        have := D.col_strictAnti (show (⟨i - 1, by omega⟩ : Fin (n + 1)) <
          ⟨i, by omega⟩ from by rw [Fin.lt_def]; simp; omega)
        omega
      exact hmin' i (by omega) (by omega) hcut2
    subst hiq
    exact ⟨by omega, hui⟩

end SkewCoframeRigidity.FixedCap
