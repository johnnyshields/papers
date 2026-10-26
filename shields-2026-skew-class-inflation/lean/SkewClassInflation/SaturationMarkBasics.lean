/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationMarkedCells

/-!
# Actual general-inner attachment and maximality data

The well-formedness and Hypothesis I inputs of `prop:saturation-chart`
in `shields-2026-skew-class-inflation.tex`.  Both attachment witnesses
are actual cells, and maximality follows from uniqueness of the original
cells on every marked content diagonal.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewGluing

variable (A : SaturationInner)

/-- The southwest-normalized inner starts on the actual bottom-row content diagonal. -/
theorem innerCells_minContent : minContent A.innerCells = -(A.k : ℤ) := by
  have hx : ((A.k : ℤ), 0) ∈ A.innerCells := (A.mem_inner_bottom 0).mpr
    ⟨le_rfl, by have := A.last_bound; omega⟩
  apply minContent_eq_of
  · exact mem_contents_iff.mpr ⟨A.k, by simpa only [add_neg_cancel] using hx⟩
  · intro j hj
    obtain ⟨a, ha⟩ := mem_contents_iff.mp hj
    have hh := A.inner_content_bounds (a, a + j) ha
    simpa only [content, add_sub_cancel_left] using hh.1

/-- The northeast content endpoint is the actual rightmost top-row cell. -/
theorem innerCells_maxContent : maxContent A.innerCells = A.profile.xi 0 - A.k - 1 := by
  have hx : (0, A.profile.xi 0 - A.k - 1) ∈ A.innerCells := by
    apply (A.mem_inner_top _).mpr
    have hrow := A.profile.xi_sub_zeta 0
    change A.profile.xi 0 - A.profile.zeta 0 = (A.r 0 : ℤ) at hrow
    have hr := A.first_bound
    constructor <;> omega
  apply maxContent_eq_of
  · exact mem_contents_iff.mpr ⟨0, by simpa only [zero_add] using hx⟩
  · intro j hj
    obtain ⟨a, ha⟩ := mem_contents_iff.mp hj
    have hh := A.inner_content_bounds (a, a + j) ha
    simp only [content, add_sub_cancel_left] at hh
    omega

/-- Removing both marks leaves only the genuine middle content interval. -/
theorem marked_middle_content_bounds (x : ℤ × ℤ) (hx : x ∈ A.markedInner.middle) :
    (A.d : ℤ) - A.k ≤ content x ∧ content x < A.profile.xi 0 - A.k - A.d := by
  obtain ⟨hE, hnot⟩ := Finset.mem_sdiff.mp hx
  constructor
  · by_contra he
    have hw := A.lower_mark_of_content x hE (by omega)
    exact hnot (Finset.mem_union_left _ hw)
  · by_contra he
    have hw := A.upper_mark_of_content x hE (by omega)
    exact hnot (Finset.mem_union_right _ hw)

/-- The lower middle endpoint is the first bottom-row cell after the actual lower mark. -/
theorem lower_middle_mem : ((A.k : ℤ), (A.d : ℤ)) ∈ A.markedInner.middle := by
  apply Finset.mem_sdiff.mpr
  refine ⟨(A.mem_inner_bottom _).mpr ⟨by positivity, by have := A.last_bound; omega⟩, ?_⟩
  intro h
  rcases Finset.mem_union.mp h with h | h
  · have hh := (A.mem_lowerMark A.k A.d).mp h
    omega
  · have hh := (A.mem_upperMark A.k A.d).mp h
    have hk := A.k_pos
    omega

/-- The upper middle endpoint is the last top-row cell before the actual upper mark. -/
theorem upper_middle_mem :
    (0, A.profile.xi 0 - A.k - A.d - 1) ∈ A.markedInner.middle := by
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · apply (A.mem_inner_top _).mpr
    have hrow := A.profile.xi_sub_zeta 0
    change A.profile.xi 0 - A.profile.zeta 0 = (A.r 0 : ℤ) at hrow
    have hr := A.first_bound
    constructor <;> omega
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · have hh := (A.mem_lowerMark 0 _).mp h
      have hk := A.k_pos
      omega
    · have hh := (A.mem_upperMark 0 _).mp h
      omega

/-- The lower placement attaches horizontally to the actual southwest middle cell. -/
theorem markedInner_lowerH : A.markedInner.LowerH := by
  have hx := A.lower_middle_mem
  have hm : minContent A.markedInner.middle = (A.d : ℤ) - A.k := by
    apply minContent_eq_of
    · exact mem_contents_iff.mpr ⟨A.k, by
        have he : (A.k : ℤ) + (A.d - A.k) = A.d := by ring
        rw [he]
        exact hx⟩
    · intro j hj
      obtain ⟨a, ha⟩ := mem_contents_iff.mp hj
      have hh := A.marked_middle_content_bounds (a, a + j) ha
      simpa only [content, add_sub_cancel_left] using hh.1
  refine ⟨(A.k, A.d), hx, ?_, ?_⟩
  · rw [hm]
    rfl
  · change ((A.k : ℤ), (A.d : ℤ) - 1) ∈ A.lowerMark
    rw [A.mem_lowerMark]
    have hd := A.c_lt_d
    exact ⟨rfl, by omega, by omega⟩

/-- The upper placement attaches horizontally to the actual northeast middle cell. -/
theorem markedInner_upperH : A.markedInner.UpperH := by
  have hx := A.upper_middle_mem
  have hm : maxContent A.markedInner.middle = A.profile.xi 0 - A.k - A.d - 1 := by
    apply maxContent_eq_of
    · exact mem_contents_iff.mpr ⟨0, by simpa only [zero_add] using hx⟩
    · intro j hj
      obtain ⟨a, ha⟩ := mem_contents_iff.mp hj
      have hh := A.marked_middle_content_bounds (a, a + j) ha
      simp only [content, add_sub_cancel_left] at hh
      omega
  refine ⟨(0, A.profile.xi 0 - A.k - A.d - 1), hx, ?_, ?_⟩
  · rw [hm]
    simp only [content, sub_zero]
  · rw [A.mem_upperMark]
    have hd := A.c_lt_d
    exact ⟨rfl, by omega, by omega⟩

/-- The stated ordinary case agrees with the two produced horizontal attachments. -/
theorem markedInner_attachmentMatches : A.markedInner.AttachmentMatches := by
  refine ⟨fun _ => ⟨A.markedInner_lowerH, A.markedInner_upperH⟩, ?_, ?_, ?_⟩ <;>
    intro h <;> cases h

/-- The actual marked inner is well formed and includes both designated extremal cells. -/
theorem markedInner_wellFormed : A.markedInner.IsWellFormed := by
  have hE := A.innerCells_connected
  have hW := A.lowerMark_connected
  have hsub := A.markedInner_subsets
  refine ⟨hE, Or.inr ⟨hW.2.1, hW, hsub.1, hsub.2, ?_, ?_, A.markedInner_attachmentMatches⟩⟩
  · apply A.lower_mark_of_content _ (sw_mem hE.2.1)
    rw [content_sw hE.2.1, A.innerCells_minContent]
    have hd := A.c_lt_d
    omega
  · apply A.upper_mark_of_content _ (ne_mem hE.2.1)
    rw [content_ne hE.2.1, A.innerCells_maxContent]
    have hd := A.c_lt_d
    omega

/-- Hypothesis I holds: no cell can enlarge the mark on those same original content diagonals. -/
theorem markedInner_maximal : A.markedInner.IsMaximal := by
  intro W' hW' hstrict _ hcontents
  have hsub : W' ⊆ A.markedInner.W := by
    intro x hx
    have hE := (Finset.mem_powerset.mp hW') hx
    have hc : content x ∈ contents A.markedInner.W := by
      rw [← hcontents]
      exact content_mem_contents hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hc
    have hb := A.lowerMark_content_bounds y hy
    apply A.lower_mark_of_content x hE
    rw [← he]
    exact hb.2
  have hfalse := (not_lt_of_ge hsub) hstrict
  exact hfalse.elim

end SkewClassInflation.SaturationInner
