/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowPieces

/-!
# Connectedness of finite row windows

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`).  Longer rows are glued to the final two-copy window across
an inhabited private singleton diagonal.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- Content bounds for one actual translated row copy. -/
theorem IsLegal.rowCopy_bounds (h : ω.IsLegal) {j : ℕ} {x : ℤ × ℤ}
    (hx : x ∈ translate ((j : ℤ) • ω.v) ω.E) :
    minContent ω.E + (j : ℤ) * ω.period ≤ content x ∧
      content x ≤ minContent ω.E + (j : ℤ) * ω.period + ω.period + ω.width - 1 := by
  have hc := content_mem_contents (mem_translate.mp hx)
  have hl := minContent_le hc
  have hu := le_maxContent hc
  have hs := h.1.span_eq
  have hsp := span_eq_of_isConnectedSkew h.1.1
  rw [content_sub, content_smul] at hl hu
  change minContent ω.E ≤ content x - (j : ℤ) * ω.period at hl
  change content x - (j : ℤ) * ω.period ≤ maxContent ω.E at hu
  constructor <;> omega

/-- At and above the last private diagonal, only the final copy contributes. -/
theorem IsLegal.mem_rowCopies_above_cut (h : ω.IsLegal) {m : ℕ} (hm : 1 ≤ m)
    {x : ℤ × ℤ} (hc : minContent ω.E + (m : ℤ) * ω.period - 1 ≤ content x) :
    x ∈ ω.rowCopies m ↔ x ∈ translate (((m - 1 : ℕ) : ℤ) • ω.v) ω.E := by
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hw := h.2.2.1.2
  simp only [rowCopies, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hx⟩
    have hb := h.rowCopy_bounds hx
    have hjlast : j = m - 1 := by
      by_contra hh
      have hji : (j : ℤ) ≤ (m : ℤ) - 2 := by omega
      have hmul := mul_le_mul_of_nonneg_right hji (le_of_lt hp)
      nlinarith
    simpa only [hjlast] using hx
  · intro hx
    exact ⟨m - 1, by omega, hx⟩

/-- Adding one copy is exactly the union of the old row and the new final copy. -/
theorem rowCopies_succ (m : ℕ) :
    ω.rowCopies (m + 1) = ω.rowCopies m ∪ translate ((m : ℤ) • ω.v) ω.E := by
  simp only [rowCopies, Finset.range_add_one, Finset.biUnion_insert]
  rw [Finset.union_comm]

/-- The translated final two-copy window is the final old copy together with the new copy. -/
theorem translated_window {m : ℕ} (hm : 1 ≤ m) :
    translate ((m : ℤ) • ω.v) ω.windowCells =
      translate (((m - 1 : ℕ) : ℤ) • ω.v) ω.E ∪ translate ((m : ℤ) • ω.v) ω.E := by
  rw [windowCells, translate_union, translate_translate, Finset.union_comm]
  congr 2
  have hc : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hc]
  module

/-- The finite row is obtained by the diagonal gluing construction at its last private cut. -/
theorem IsLegal.rowCopies_succ_eq_glue (h : ω.IsLegal) {m : ℕ} (hm : 1 ≤ m) :
    ω.rowCopies (m + 1) = glueAt (ω.rowCopies m)
      (translate ((m : ℤ) • ω.v) ω.windowCells)
      (minContent ω.E + (m : ℤ) * ω.period - 1) := by
  rw [rowCopies_succ, translated_window hm]
  ext x
  rw [mem_glueAt]
  simp only [Finset.mem_union]
  have hnew : x ∈ translate ((m : ℤ) • ω.v) ω.E →
      minContent ω.E + (m : ℤ) * ω.period - 1 < content x := by
    intro hx
    have hb := h.rowCopy_bounds hx
    omega
  have hprev : x ∈ translate (((m - 1 : ℕ) : ℤ) • ω.v) ω.E → x ∈ ω.rowCopies m := by
    intro hx
    exact Finset.mem_biUnion.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), hx⟩
  constructor
  · rintro (hx | hx)
    · by_cases hc : content x ≤ minContent ω.E + (m : ℤ) * ω.period - 1
      · exact Or.inl ⟨hc, hx⟩
      · exact Or.inr ⟨by omega, Or.inl ((h.mem_rowCopies_above_cut hm (by omega)).mp hx)⟩
    · exact Or.inr ⟨le_of_lt (hnew hx), Or.inr hx⟩
  · rintro (⟨_, hx⟩ | ⟨_, hx | hx⟩)
    · exact Or.inl hx
    · exact Or.inl (hprev hx)
    · exact Or.inr hx

/-- The private gluing cut is occupied in the final old copy. -/
theorem IsLegal.row_private_cut_nonempty (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ x ∈ translate (((m - 1 : ℕ) : ℤ) • ω.v) ω.E,
      content x = minContent ω.E + (m : ℤ) * ω.period - 1 := by
  obtain ⟨z, hz⟩ := h.private_upper_eq_singleton hW
  have hzmem : z ∈ ω.E.filter (fun x => content x = minContent ω.E + ω.period - 1) := by
    rw [hz]
    exact Finset.mem_singleton_self z
  obtain ⟨hzE, hcz⟩ := Finset.mem_filter.mp hzmem
  refine ⟨z + ((m - 1 : ℕ) : ℤ) • ω.v, ?_, ?_⟩
  · rw [mem_translate]
    simpa only [add_sub_cancel_right] using hzE
  · rw [content_add, content_smul, hcz]
    change minContent ω.E + ω.period - 1 + ((m - 1 : ℕ) : ℤ) * ω.period = _
    have hc : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    rw [hc]
    ring

/-- Every nonempty finite row of a nonempty legal marked inner is connected skew. -/
theorem IsLegal.isConnectedSkew_rowCopies (h : ω.IsLegal) (hW : ω.W.Nonempty)
    (m : ℕ) (hm : 1 ≤ m) : IsConnectedSkew (ω.rowCopies m) := by
  induction m with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simpa [rowCopies, translate_zero] using h.1.1
    | succ k =>
      have hn : 1 ≤ k + 1 := by omega
      have hA := ih hn
      have hB : IsConnectedSkew (translate (((k + 1 : ℕ) : ℤ) • ω.v) ω.windowCells) :=
        isConnectedSkew_translate _ (isConnectedSkew_iff_diagonal.mpr
          (IsLegalNonempty.amalgam_hasDiagonalShape ⟨h, hW⟩))
      obtain ⟨z, hz, hcz⟩ := h.row_private_cut_nonempty hW hn
      have hzA : z ∈ ω.rowCopies (k + 1) :=
        Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), by simpa using hz⟩
      have hzB : z ∈ translate (((k + 1 : ℕ) : ℤ) • ω.v) ω.windowCells := by
        rw [translated_window hn]
        exact Finset.mem_union_left _ hz
      rw [h.rowCopies_succ_eq_glue hn]
      refine isConnectedSkew_glueAt hA hB
        (by rw [← hcz]; exact content_mem_contents hzA)
        (by rw [← hcz]; exact content_mem_contents hzB) ?_
      intro x hc
      rw [h.mem_rowCopies_above_cut hn (by omega), translated_window hn, Finset.mem_union]
      constructor
      · exact Or.inl
      · rintro (hx | hx)
        · exact hx
        · have hb := h.rowCopy_bounds hx
          omega

/-- The actual horizontal-row composite is connected skew
under the same nonempty-mark assumptions. -/
theorem IsLegal.isConnectedSkew_compose_horizontalRow (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) : IsConnectedSkew (ω.compose (horizontalRow m)) := by
  rw [ω.compose_horizontalRow hm]
  exact h.isConnectedSkew_rowCopies hW m hm

end SkewGluing.MarkedInner
