/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LiteralWindowPeriod

/-!
# Complete periods and the final literal prefix

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`).

An equality of complete cell windows reconstructs each full period band and the last
partial band with one common displacement. The identities are of actual diagrams.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- An actual content prefix, without any assertion that its cut is an ordinary attachment. -/
def literalPrefix (D : Diagram) (m : ℤ) : Diagram :=
  D.filter fun x => 0 ≤ content x ∧ content x < m

/-- A supported band is exactly a translate of the corresponding first-band prefix. -/
theorem literalWindow_band_eq {D : Diagram} {L q : ℤ} {v : ℤ × ℤ}
    (hq : 0 < q) (hv : content v = q)
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q))
    (j : ℕ) (m : ℤ)
    (hfinal : (j : ℤ) * q + m ≤ L) :
    D.filter (fun x => (j : ℤ) * q ≤ content x ∧
      content x < (j : ℤ) * q + m) =
      translate ((j : ℤ) • v) (literalPrefix D m) := by
  ext x
  have hc : content (x - (j : ℤ) • v) = content x - (j : ℤ) * q := by
    have he := content_add_zsmul (x - (j : ℤ) • v) v j
    rw [sub_add_cancel, hv] at he
    omega
  simp only [Finset.mem_filter, mem_translate, literalPrefix, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hx0, hxm⟩
    have hy0 : 0 ≤ content (x - (j : ℤ) • v) := by omega
    have hyL : content (x - (j : ℤ) • v) + (j : ℤ) * q < L := by omega
    have hy := (literalWindow_iterate hq hv hwindow
      (x - (j : ℤ) • v) hy0 j hyL).mp (by simpa only [sub_add_cancel] using hx)
    exact ⟨hy, hy0, by omega⟩
  · rintro ⟨hy, hy0, hym⟩
    have hyL : content (x - (j : ℤ) • v) + (j : ℤ) * q < L := by omega
    have hx := (literalWindow_iterate hq hv hwindow
      (x - (j : ℤ) • v) hy0 j hyL).mpr hy
    exact ⟨by simpa only [sub_add_cancel] using hx, by omega, by omega⟩

/-- Complete windows yield all full copies and one terminal prefix at actual-cell precision. -/
theorem literalWindow_cells_eq_prefix_copies {D : Diagram} {L q m : ℤ}
    {v : ℤ × ℤ} {k : ℕ} (hq : 0 < q) (hv : content v = q)
    (hm : 0 < m) (hmq : m ≤ q) (hL : L = (k : ℤ) * q + m)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < L)
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q)) :
    D = (Finset.range k).biUnion (fun j =>
      translate ((j : ℤ) • v) (literalPrefix D q)) ∪
      translate ((k : ℤ) • v) (literalPrefix D m) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, y, hy, hy0, hyq, he⟩ :=
      literalWindow_cell_reconstruction hq hv hbound hwindow x hx
    have hc := congrArg content he
    rw [content_add_zsmul, hv] at hc
    have hjk : j ≤ k := by
      have hxL := (hbound x hx).2
      have : (j : ℤ) ≤ (k : ℤ) := by
        by_contra h
        have : (k : ℤ) + 1 ≤ (j : ℤ) := by omega
        nlinarith
      exact_mod_cast this
    by_cases hj : j < k
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
        mem_translate.mpr (by simpa only [he, add_sub_cancel_right, literalPrefix,
          Finset.mem_filter] using And.intro hy (And.intro hy0 hyq))⟩
    · have hj : j = k := by omega
      subst j
      have hym : content y < m := by have hxL := (hbound x hx).2; omega
      exact Finset.mem_union_right _ (mem_translate.mpr
        (by simpa only [he, add_sub_cancel_right, literalPrefix, Finset.mem_filter]
          using And.intro hy (And.intro hy0 hym)))
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hy, hy0, hyq⟩ := Finset.mem_filter.mp (mem_translate.mp hx)
      have hjcast : (j : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast Finset.mem_range.mp hj
      have hyL : content (x - (j : ℤ) • v) + (j : ℤ) * q < L := by nlinarith
      simpa only [sub_add_cancel] using
        (literalWindow_iterate hq hv hwindow _ hy0 j hyL).mpr hy
    · obtain ⟨hy, hy0, hym⟩ := Finset.mem_filter.mp (mem_translate.mp hx)
      have hyL : content (x - (k : ℤ) • v) + (k : ℤ) * q < L := by omega
      simpa only [sub_add_cancel] using
        (literalWindow_iterate hq hv hwindow _ hy0 k hyL).mpr hy

end SkewCornerDescent
