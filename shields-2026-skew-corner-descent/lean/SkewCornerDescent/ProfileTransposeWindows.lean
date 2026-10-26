/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TransposeResidueMatch

/-!
# Complete literal windows after whole-profile transposition

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Actual transposed profile presentations supply their content normalization.
The complete first and last content windows exchange, retaining all cells and
reversing the literal displacement. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Transposition reverses the extreme contents of a nonempty actual diagram. -/
theorem minContent_transpose (D : Diagram) (hD : D.Nonempty) :
    minContent (transpose D) = -maxContent D := by
  calc
    minContent (transpose D) = minContent (rotate D) := by
      unfold minContent
      rw [contents_transpose, ← contents_rotate]
    _ = -maxContent D := minContent_rotate hD

/-- Any actual transposed profile presentation has the same span and its
normalizing translation has the produced opposite extreme content. -/
theorem transpose_profile_endpoints {n m : ℕ} (P : Profile n) (T : Profile m)
    (v : ℤ × ℤ) (hv : transpose P.cells = translate v T.cells) :
    T.xi 0 = P.xi 0 ∧ content v = 1 - P.xi 0 := by
  have hs := congrArg span hv
  rw [span_transpose, span_translate, P.span_cells_eq_topVar, T.span_cells_eq_topVar] at hs
  have hxi : T.xi 0 = P.xi 0 := by
    have hp := P.topVar_coe
    have ht := T.topVar_coe
    have hcast : (P.topVar : ℤ) = T.topVar := by exact_mod_cast hs
    omega
  have hc := congrArg minContent hv
  rw [minContent_transpose P.cells P.isConnectedSkew_cells.2.1,
    minContent_translate T.isConnectedSkew_cells.2.1, P.maxContent_cells,
    T.minContent_cells, zero_add] at hc
  exact ⟨hxi, by omega⟩

/-- A complete content interval is reflected without losing either endpoint's cells. -/
theorem translated_transpose_content_window (D : Diagram) (a : ℤ × ℤ) (lo hi : ℤ) :
    translate a (transpose (D.filter fun x => lo ≤ content x ∧ content x < hi)) =
      (translate a (transpose D)).filter
        (fun x => content a - hi < content x ∧ content x ≤ content a - lo) := by
  ext x
  simp only [mem_translate, mem_transpose, Finset.mem_filter]
  have hc : content ((x - a).swap) = content a - content x := by
    simp only [content, Prod.fst_swap, Prod.snd_swap, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hc]
  constructor
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, by omega, by omega⟩
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, by omega, by omega⟩

/-- A complete equal-window relation remains a complete equal-window relation
on the actual transposed profile, with the first and last windows interchanged. -/
theorem complete_profile_window_transpose {n m : ℕ} (P : Profile n) (T : Profile m)
    (v a : ℤ × ℤ) (q : ℤ) (ha : transpose P.cells = translate a T.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) :
    T.cells.filter (fun x => q ≤ content x ∧ content x < T.xi 0) =
      translate (-v.swap)
        (T.cells.filter fun x => 0 ≤ content x ∧ content x < T.xi 0 - q) := by
  obtain ⟨hxi, hca⟩ := transpose_profile_endpoints P T a ha
  have hT : translate (-a) (transpose P.cells) = T.cells := by
    rw [ha, translate_translate, neg_add_cancel, translate_zero]
  have hcneg : content (-a) = P.xi 0 - 1 := by
    simp only [content, Prod.fst_neg, Prod.snd_neg] at hca ⊢
    omega
  have hlast : T.cells.filter (fun x => q ≤ content x ∧ content x < T.xi 0) =
      translate (-a) (transpose (P.cells.filter
        fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) := by
    rw [translated_transpose_content_window, hT]
    ext x
    simp only [Finset.mem_filter]
    simp only [hcneg, hxi]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      exact ⟨hx, by omega, by omega⟩
    · rintro ⟨hx, hlo, hhi⟩
      exact ⟨hx, by omega, by omega⟩
  have hfirst : T.cells.filter (fun x => 0 ≤ content x ∧ content x < T.xi 0 - q) =
      translate (-a) (transpose (P.cells.filter
        fun x => q ≤ content x ∧ content x < P.xi 0)) := by
    rw [translated_transpose_content_window, hT]
    ext x
    simp only [Finset.mem_filter]
    simp only [hcneg, hxi]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      exact ⟨hx, by omega, by omega⟩
    · rintro ⟨hx, hlo, hhi⟩
      exact ⟨hx, by omega, by omega⟩
  rw [hlast, hfirst, hwindow, transpose_translate]
  simp only [SkewGluing.translate_translate]
  have he : -v.swap + (-a + v.swap) = -a := by abel
  simp only [he]

/-- The complete first transposed window is precisely the whole transpose
of the original last window, with its produced normalization. -/
theorem transposed_profile_first_window {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (q : ℤ) (ha : transpose P.cells = translate a T.cells) :
    T.cells.filter (fun x => 0 ≤ content x ∧ content x < T.xi 0 - q) =
      translate (-a) (transpose (P.cells.filter
        fun x => q ≤ content x ∧ content x < P.xi 0)) := by
  obtain ⟨hxi, hca⟩ := transpose_profile_endpoints P T a ha
  have hT : translate (-a) (transpose P.cells) = T.cells := by
    rw [ha, SkewGluing.translate_translate, neg_add_cancel, translate_zero]
  have hc : content (-a) = P.xi 0 - 1 := by
    simp only [content, Prod.fst_neg, Prod.snd_neg] at hca ⊢
    omega
  rw [translated_transpose_content_window, hT]
  ext x
  simp only [Finset.mem_filter, hc, hxi]
  constructor
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, by omega, by omega⟩
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, by omega, by omega⟩

/-- Equal complete source windows produce the complete shared window
presentation required by the normalized transposed source chart. -/
theorem complete_transposed_shared_window {n m k s : ℕ}
    (P : Profile n) (T : Profile m) (W : Profile k) (S : Profile s)
    (a v z b : ℤ × ℤ) (q : ℤ)
    (ha : transpose P.cells = translate a T.cells)
    (hb : transpose W.cells = translate b S.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) :
    translate (-a + v.swap + z.swap + b) S.cells =
      T.cells.filter (fun x => 0 ≤ content x ∧ content x < T.xi 0 - q) := by
  rw [transposed_profile_first_window P T a q ha, hwindow, ← hW,
    transpose_translate, transpose_translate, hb]
  simp only [SkewGluing.translate_translate]
  congr 1
  abel

end SkewCornerDescent
