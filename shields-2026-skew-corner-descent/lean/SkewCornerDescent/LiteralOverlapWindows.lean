/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LiteralOverlapInventory

/-!
# Complete actual end windows of the literal amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete
matching source windows make the two-copy union contain two intact source profiles in
its end bands. No partial window or Schur-function equality replaces literal cells.
Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- The literal two-copy overlap has the complete source and translated source as its two
end windows. The overlap identity supplies every cell from the other copy in either band. -/
theorem literalOverlap_complete_end_windows (D : Diagram) (L q : ℤ) (v : ℤ × ℤ)
    (hv : content v = q)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < L)
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q)) :
    (D ∪ translate v D).filter (fun x => 0 ≤ content x ∧ content x < L) = D ∧
      (D ∪ translate v D).filter (fun x => q ≤ content x ∧ content x < L + q) =
        translate v D := by
  have hc (x : ℤ × ℤ) : content (x - v) = content x - q := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
    omega
  constructor
  · apply Finset.ext
    intro x
    rw [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hb⟩
      · exact hx
      · have hs := mem_translate.mp hx
        have hsband := hbound (x - v) hs
        rw [hc] at hsband
        have hm : x ∈ translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q) := by
          apply mem_translate.mpr
          exact Finset.mem_filter.mpr ⟨hs, by rw [hc]; omega⟩
        rw [← hwindow] at hm
        exact (Finset.mem_filter.mp hm).1
    · intro hx
      exact ⟨Or.inl hx, hbound x hx⟩
  · apply Finset.ext
    intro x
    rw [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hb⟩
      · have hm : x ∈ D.filter (fun x => q ≤ content x ∧ content x < L) :=
          Finset.mem_filter.mpr ⟨hx, ⟨hb.1, (hbound x hx).2⟩⟩
        rw [hwindow, mem_translate, Finset.mem_filter] at hm
        exact mem_translate.mpr hm.1
      · exact hx
    · intro hx
      have hs := hbound (x - v) (mem_translate.mp hx)
      rw [hc] at hs
      exact ⟨Or.inr hx, by omega⟩

/-- Literal union extrema come from actual source endpoint cells, not a span assumption. -/
theorem literalOverlap_content_extrema (D : Diagram) (hD : D.Nonempty)
    (L q : ℤ) (v : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hmin : minContent D = 0) (hmax : maxContent D = L - 1) :
    minContent (D ∪ translate v D) = 0 ∧
      maxContent (D ∪ translate v D) = L + q - 1 := by
  have hbounds (x : ℤ × ℤ) (hx : x ∈ D) : 0 ≤ content x ∧ content x ≤ L - 1 := by
    have hlo := minContent_le (content_mem_contents hx)
    have hhi := le_maxContent (content_mem_contents hx)
    rw [hmin] at hlo
    rw [hmax] at hhi
    exact ⟨hlo, hhi⟩
  have htranslate (x : ℤ × ℤ) : content (x - v) = content x - q := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
    omega
  constructor
  · apply minContent_eq_of
    · have hx := content_mem_contents
        (Finset.mem_union_left (translate v D) (sw_mem hD))
      rwa [content_sw hD, hmin] at hx
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      rcases Finset.mem_union.mp hi with hi | hi
      · have hb := (hbounds _ hi).1
        simpa only [content, add_sub_cancel_left] using hb
      · have hb := (hbounds _ (mem_translate.mp hi)).1
        rw [htranslate] at hb
        simp only [content, add_sub_cancel_left] at hb
        omega
  · apply maxContent_eq_of
    · have hx := content_mem_contents
        (Finset.mem_union_right D (mem_translate.mpr
          (by simpa only [add_sub_cancel_right] using ne_mem hD :
            ne D + v - v ∈ D)))
      rw [content_add, content_ne hD, hmax, hv] at hx
      convert hx using 1; ring
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      rcases Finset.mem_union.mp hi with hi | hi
      · have hb := (hbounds _ hi).2
        simp only [content, add_sub_cancel_left] at hb
        omega
      · have hb := (hbounds _ (mem_translate.mp hi)).2
        rw [htranslate] at hb
        simp only [content, add_sub_cancel_left] at hb
        omega

end SkewCornerDescent
