/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LiteralOverlapWindows
import SkewGluing.ProfileStatistics

/-!
# Actual normalized end windows of the amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Literal parent
cells determine the normalization displacement, the complete union width, and both
intact end profiles. No rank, count, or response correspondence is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A normalized profile for the literal overlap union has the actual union extrema. -/
theorem originalAmalgamation_profile_extrema {n m : ℕ} (P : Profile n) (A : Profile m)
    (q : ℤ) (v u : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    content u = 0 ∧ A.xi 0 = P.xi 0 + q := by
  obtain ⟨hmin, hmax⟩ := literalOverlap_content_extrema P.cells
    P.isConnectedSkew_cells.2.1 (P.xi 0) q v hq hv P.minContent_cells P.maxContent_cells
  rw [hA, minContent_translate A.isConnectedSkew_cells.2.1,
    A.minContent_cells, zero_add] at hmin
  rw [hA, maxContent_translate A.isConnectedSkew_cells.2.1,
    A.maxContent_cells, hmin] at hmax
  exact ⟨hmin, by omega⟩

/-- Content-zero normalization commutes with a complete content-band filter. -/
theorem contentZero_translate_filter (D : Diagram) (u : ℤ × ℤ)
    (hu : content u = 0) (lo hi : ℤ) :
    (translate u D).filter (fun x => lo ≤ content x ∧ content x < hi) =
      translate u (D.filter fun x => lo ≤ content x ∧ content x < hi) := by
  have hc (x : ℤ × ℤ) : content (x - u) = content x := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at hu ⊢
    omega
  ext x
  simp only [Finset.mem_filter, mem_translate, hc]

/-- Both source copies are complete end windows of the actual normalized amalgamation. -/
theorem originalAmalgamation_complete_end_windows {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    translate u (A.cells.filter fun x => 0 ≤ content x ∧ content x < A.xi 0 - q) =
        P.cells ∧
      translate u (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) =
        translate v P.cells := by
  have hbound : ∀ x ∈ P.cells, 0 ≤ content x ∧ content x < P.xi 0 := by
    intro x hx
    have hlo := minContent_le (content_mem_contents hx)
    have hhi := le_maxContent (content_mem_contents hx)
    rw [P.minContent_cells] at hlo
    rw [P.maxContent_cells] at hhi
    exact ⟨hlo, by omega⟩
  obtain ⟨hu, hwidth⟩ := originalAmalgamation_profile_extrema P A q v u hq hv hA
  obtain ⟨hleft, hright⟩ := literalOverlap_complete_end_windows P.cells (P.xi 0)
    q v hv hbound hwindow
  rw [hA, contentZero_translate_filter A.cells u hu] at hleft hright
  constructor
  · simpa only [hwidth, add_sub_cancel_right] using hleft
  · simpa only [hwidth] using hright

/-- The two private source cuts produce all four actual amalgamation end-window cuts. -/
theorem originalAmalgamation_private_end_cuts {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∀ x ∈ diagramInterior A.cells, content x ≠ 0 ∧ content x ≠ q ∧
      content x ≠ A.xi 0 - q ∧ content x ≠ A.xi 0 := by
  have hbound : ∀ x ∈ P.cells, 0 ≤ content x ∧ content x < P.xi 0 := by
    intro x hx
    have hlo := minContent_le (content_mem_contents hx)
    have hhi := le_maxContent (content_mem_contents hx)
    rw [P.minContent_cells] at hlo
    rw [P.maxContent_cells] at hhi
    exact ⟨hlo, by omega⟩
  have hiBound (x : ℤ × ℤ) (hx : x ∈ diagramInterior P.cells) :
      0 < content x ∧ content x < P.xi 0 := by
    have hh := interior_content_strict P.isConnectedSkew_cells hx
    rw [P.minContent_cells, P.maxContent_cells] at hh
    omega
  have he := literalOverlap_interior P.cells (P.xi 0) (P.xi 0 - q) v
    (by omega) hbound (by simpa only [sub_sub_cancel] using hwindow)
  obtain ⟨hu, hwidth⟩ := originalAmalgamation_profile_extrema P A q v u hq hv hA
  rw [hA, interior_translate] at he
  intro x hx
  have hx' : x + u ∈ translate u (diagramInterior A.cells) := by
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right] using hx
  rw [he, Finset.mem_union] at hx'
  have hxu : content (x + u) = content x := by rw [content_add, hu, add_zero]
  have hxv : content (x + u - v) = content x - q := by
    simp only [content, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hu hv ⊢
    omega
  rw [hwidth]
  rcases hx' with hx' | hx'
  · have hb := hiBound _ hx'
    have h1 := hcutq _ hx'
    rw [hxu] at hb h1
    omega
  · have hy := mem_translate.mp hx'
    have hb := hiBound _ hy
    have h1 := hcutLq _ hy
    rw [hxv] at hb h1
    omega

end SkewCornerDescent.Matrix
