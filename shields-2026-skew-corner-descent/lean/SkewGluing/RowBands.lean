/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowPieceFamily

/-!
# Content bands of finite row factors

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:row-cofactor`).  Marked and middle bands are separated
by the missing private singleton diagonals.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

/-- The period block occupied by a row factor. -/
def rowPieceBlock (m : ℕ) : RowPieceIndex m → ℕ
  | .inl false => 0
  | .inl true => m
  | .inr (.inl j) => j.val
  | .inr (.inr j) => j.val + 1

/-- Middle factors use the open private band; every other factor uses a marked band. -/
def rowPieceIsMiddle (m : ℕ) : RowPieceIndex m → Bool
  | .inr (.inl _) => true
  | _ => false

variable {ω : MarkedInner}

/-- The exact marked or middle content interval containing each actual factor. -/
theorem IsLegal.rowPiece_content_bounds (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) (i : RowPieceIndex m) {x : ℤ × ℤ} (hx : x ∈ ω.rowPiece m i) :
    if rowPieceIsMiddle m i then
      minContent ω.E + (rowPieceBlock m i : ℤ) * ω.period + ω.width + 1 ≤ content x ∧
        content x ≤ minContent ω.E + ((rowPieceBlock m i : ℤ) + 1) * ω.period - 2
    else
      minContent ω.E + (rowPieceBlock m i : ℤ) * ω.period ≤ content x ∧
        content x ≤ minContent ω.E + (rowPieceBlock m i : ℤ) * ω.period + ω.width - 1 := by
  have hn := h.isNonemptyMark hW
  have hmax := hn.maxContent_E h.1.1
  rcases i with b | j | j
  · cases b
    · change minContent ω.E + 0 * ω.period ≤ content x ∧
        content x ≤ minContent ω.E + 0 * ω.period + ω.width - 1
      obtain ⟨hxI, hxc⟩ := Finset.mem_filter.mp hx
      have hlo := (interior_content_strict h.1.1 hxI).1
      constructor <;> omega
    · change minContent ω.E + (m : ℤ) * ω.period ≤ content x ∧
        content x ≤ minContent ω.E + (m : ℤ) * ω.period + ω.width - 1
      have hy := mem_translate.mp hx
      obtain ⟨hyI, hyc⟩ := Finset.mem_filter.mp hy
      have hhi := (interior_content_strict h.1.1 hyI).2
      rw [content_sub, content_smul] at hyc hhi
      have hc : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
      change minContent ω.E + ω.period - 1 < content x - ((m - 1 : ℕ) : ℤ) * ω.period at hyc
      change content x - ((m - 1 : ℕ) : ℤ) * ω.period < maxContent ω.E at hhi
      rw [hc] at hyc hhi
      constructor <;> nlinarith
  · change minContent ω.E + (j.val : ℤ) * ω.period + ω.width + 1 ≤ content x ∧
      content x ≤ minContent ω.E + ((j.val : ℤ) + 1) * ω.period - 2
    have hy := h.middleInterior_content hW (mem_translate.mp hx)
    rw [content_sub, content_smul] at hy
    change minContent ω.E + ω.width < content x - (j.val : ℤ) * ω.period ∧
      content x - (j.val : ℤ) * ω.period < minContent ω.E + ω.period - 1 at hy
    constructor <;> nlinarith
  · change minContent ω.E + ((j.val + 1 : ℕ) : ℤ) * ω.period ≤ content x ∧
      content x ≤ minContent ω.E + ((j.val + 1 : ℕ) : ℤ) * ω.period + ω.width - 1
    have hy := mem_translate.mp hx
    rw [h.hatMarkWindow_eq_band hW, Finset.mem_filter] at hy
    have hyc := hy.2
    rw [content_sub, content_smul] at hyc
    change minContent ω.E ≤ content x - ((j.val + 1 : ℕ) : ℤ) * ω.period ∧
      content x - ((j.val + 1 : ℕ) : ℤ) * ω.period ≤ minContent ω.E + ω.width - 1 at hyc
    constructor <;> omega

/-- The block and band kind uniquely identify an actual row factor. -/
theorem rowPiece_location_injective {m : ℕ} (hm : 1 ≤ m) {i j : RowPieceIndex m}
    (hb : rowPieceBlock m i = rowPieceBlock m j)
    (hk : rowPieceIsMiddle m i = rowPieceIsMiddle m j) : i = j := by
  rcases i with b | i | i <;> rcases j with c | j | j
  · cases b <;> cases c <;> simp_all [rowPieceBlock, rowPieceIsMiddle]
    all_goals omega
  · cases b <;> simp [rowPieceIsMiddle] at hk
  · have hj := j.isLt
    cases b <;> simp only [rowPieceBlock] at hb <;> omega
  · cases c <;> simp [rowPieceIsMiddle] at hk
  · change i.val = j.val at hb
    exact congrArg (fun z => Sum.inr (Sum.inl z)) (Fin.ext hb)
  · simp [rowPieceIsMiddle] at hk
  · have hi := i.isLt
    cases c <;> simp only [rowPieceBlock] at hb <;> omega
  · simp [rowPieceIsMiddle] at hk
  · change i.val + 1 = j.val + 1 at hb
    exact congrArg (fun z => Sum.inr (Sum.inr z)) (Fin.ext (by omega))

/-- Distinct marked or private-middle bands have an empty diagonal between them. -/
theorem separated_content_bands (p w c a b u v : ℤ) (ma mb : Bool)
    (hw : 0 ≤ w) (hp : w < p) (hne : a ≠ b ∨ ma ≠ mb)
    (hu : if ma = true then c + a * p + w + 1 ≤ u ∧ u ≤ c + (a + 1) * p - 2
      else c + a * p ≤ u ∧ u ≤ c + a * p + w - 1)
    (hv : if mb = true then c + b * p + w + 1 ≤ v ∧ v ≤ c + (b + 1) * p - 2
      else c + b * p ≤ v ∧ v ≤ c + b * p + w - 1) :
    u + 1 < v ∨ v + 1 < u := by
  have hpp : 0 < p := by omega
  cases ma <;> cases mb <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hu hv hne
  · have hab : a ≠ b := by tauto
    rcases lt_or_gt_of_ne hab with hab | hab
    · have hmul := mul_le_mul_of_nonneg_right (show a + 1 ≤ b by omega) (le_of_lt hpp)
      left
      nlinarith
    · have hmul := mul_le_mul_of_nonneg_right (show b + 1 ≤ a by omega) (le_of_lt hpp)
      right
      nlinarith
  · by_cases hab : a ≤ b
    · have hmul := mul_le_mul_of_nonneg_right hab (le_of_lt hpp)
      left
      nlinarith
    · have hmul := mul_le_mul_of_nonneg_right (show b + 1 ≤ a by omega) (le_of_lt hpp)
      right
      nlinarith
  · by_cases hab : b ≤ a
    · have hmul := mul_le_mul_of_nonneg_right hab (le_of_lt hpp)
      right
      nlinarith
    · have hmul := mul_le_mul_of_nonneg_right (show a + 1 ≤ b by omega) (le_of_lt hpp)
      left
      nlinarith
  · have hab : a ≠ b := by tauto
    rcases lt_or_gt_of_ne hab with hab | hab
    · have hmul := mul_le_mul_of_nonneg_right (show a + 1 ≤ b by omega) (le_of_lt hpp)
      left
      nlinarith
    · have hmul := mul_le_mul_of_nonneg_right (show b + 1 ≤ a by omega) (le_of_lt hpp)
      right
      nlinarith

/-- Cells in distinct actual row factors have content separation strictly exceeding one. -/
theorem IsLegal.rowPiece_content_separated (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) {i j : RowPieceIndex m} (hij : i ≠ j)
    {x y : ℤ × ℤ} (hx : x ∈ ω.rowPiece m i) (hy : y ∈ ω.rowPiece m j) :
    content x + 1 < content y ∨ content y + 1 < content x := by
  have hne : (rowPieceBlock m i : ℤ) ≠ rowPieceBlock m j ∨
      rowPieceIsMiddle m i ≠ rowPieceIsMiddle m j := by
    by_contra hh
    push Not at hh
    exact hij (rowPiece_location_injective hm (by exact_mod_cast hh.1) hh.2)
  exact separated_content_bands ω.period ω.width (minContent ω.E)
    (rowPieceBlock m i) (rowPieceBlock m j) (content x) (content y)
    (rowPieceIsMiddle m i) (rowPieceIsMiddle m j) (by omega) h.2.2.1.2 hne
    (h.rowPiece_content_bounds hW hm i hx) (h.rowPiece_content_bounds hW hm j hy)

/-- Distinct actual row factors are cell-disjoint. -/
theorem IsLegal.rowPiece_disjoint (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) {i j : RowPieceIndex m} (hij : i ≠ j) :
    Disjoint (ω.rowPiece m i) (ω.rowPiece m j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have hs := h.rowPiece_content_separated hW hm hij hx hy
  omega

/-- Distinct actual row factors have no edge adjacency. -/
theorem IsLegal.rowPiece_noAdj (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) {i j : RowPieceIndex m} (hij : i ≠ j)
    {x y : ℤ × ℤ} (hx : x ∈ ω.rowPiece m i) (hy : y ∈ ω.rowPiece m j) :
    ¬ CellAdj x y := by
  intro ha
  have hs := h.rowPiece_content_separated hW hm hij hx hy
  rw [cellAdj_iff] at ha
  simp only [content] at hs
  omega

end SkewGluing.MarkedInner
