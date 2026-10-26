/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationMarkBasics
import SkewClassInflation.SaturationMarkRemovals
import SkewClassInflation.SaturationMarkHats

/-!
# Full legality and unique attachments of the general end-row chart

Hypotheses I--V of `prop:saturation-chart` in
`shields-2026-skew-class-inflation.tex`.  The two actual attachment
sets are computed as literal singleton cell sets.  All standing
geometric conditions are supplied by the original inner parameters.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewGluing

variable (A : SaturationInner)

/-- Exactly the final lower marked cell shares an edge with the actual middle. -/
theorem lower_attachmentCells :
    attachmentCells A.markedInner.W A.markedInner.middle = {((A.k : ℤ), (A.d : ℤ) - 1)} := by
  ext ⟨a, b⟩
  rw [attachmentCells, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  change ((a, b) ∈ A.lowerMark ∧ ∃ y ∈ A.markedInner.middle, CellAdj (a, b) y) ↔ _
  constructor
  · rintro ⟨hW, ⟨⟨r, s⟩, hM, hadj⟩⟩
    have hw := (A.mem_lowerMark a b).mp hW
    have hbounds := A.marked_middle_content_bounds (r, s) hM
    have hE := (Finset.mem_sdiff.mp hM).1
    obtain ⟨i, hi, hlo, _⟩ := (A.mem_innerCells r s).mp hE
    rw [cellAdj_iff] at hadj
    change (a = r ∧ (b = s + 1 ∨ s = b + 1)) ∨
      (b = s ∧ (a = r + 1 ∨ r = a + 1)) at hadj
    simp only [content] at hbounds
    by_cases hil : i.val = A.k
    · exact ⟨hw.1, by omega⟩
    · have hiLt : i.val < A.k := by have := i.isLt; omega
      have hmargin := A.lower_content_margin i hiLt
      omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨(A.mem_lowerMark _ _).mpr ⟨rfl, ?_, by omega⟩,
      (A.k, A.d), A.lower_middle_mem, ?_⟩
    · have hd := A.c_lt_d
      omega
    · rw [cellAdj_iff]
      left
      exact ⟨rfl, Or.inr (by omega)⟩

/-- Exactly the initial upper marked cell shares an edge with the actual middle. -/
theorem upper_attachmentCells :
    attachmentCells A.markedInner.upper A.markedInner.middle =
      {(0, A.profile.xi 0 - A.k - A.d)} := by
  ext ⟨a, b⟩
  rw [attachmentCells, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hW, ⟨⟨r, s⟩, hM, hadj⟩⟩
    have hw := (A.mem_upperMark a b).mp hW
    have hbounds := A.marked_middle_content_bounds (r, s) hM
    have hE := (Finset.mem_sdiff.mp hM).1
    obtain ⟨i, hi, _, hhi⟩ := (A.mem_innerCells r s).mp hE
    rw [cellAdj_iff] at hadj
    change (a = r ∧ (b = s + 1 ∨ s = b + 1)) ∨
      (b = s ∧ (a = r + 1 ∨ r = a + 1)) at hadj
    simp only [content] at hbounds
    by_cases hi0 : i.val = 0
    · exact ⟨hw.1, by omega⟩
    · have hip : 0 < i.val := Nat.pos_of_ne_zero hi0
      have hmargin := A.upper_content_margin i hip
      omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨(A.mem_upperMark _ _).mpr ⟨rfl, le_rfl, ?_⟩,
      (0, A.profile.xi 0 - A.k - A.d - 1), A.upper_middle_mem, ?_⟩
    · have hd := A.c_lt_d
      omega
    · rw [cellAdj_iff]
      left
      exact ⟨rfl, Or.inl (by omega)⟩

/-- Hypothesis V holds for the two actual finite attachment sets. -/
theorem markedInner_hypothesisV :
    (attachmentCells A.markedInner.W A.markedInner.middle).card = 1 ∧
      (attachmentCells A.markedInner.upper A.markedInner.middle).card = 1 := by
  rw [A.lower_attachmentCells, A.upper_attachmentCells, Finset.card_singleton]
  exact ⟨rfl, rfl⟩

/-- The literal general-inner chart is well formed and satisfies all four legality conditions. -/
theorem markedInner_legal : A.markedInner.IsLegal :=
  ⟨A.markedInner_wellFormed, A.markedInner_maximal, A.markedInner_narrow,
    A.markedInner_removalsConnected, A.markedInner_noHatAdjacency⟩

end SkewClassInflation.SaturationInner
