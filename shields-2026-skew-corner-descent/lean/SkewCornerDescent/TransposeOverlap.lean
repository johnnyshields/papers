/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PrivateDiagonalTranspose
import SkewCornerDescent.Matrix.SelectedCoordinate

/-!
# Literal overlap unions under whole-profile transposition

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The complete two-copy overlap union transports to the actual transposed source,
with the exchanged displacement and produced selected-prime span. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Transpose retains both complete sets in an overlap union. -/
theorem transpose_diagram_union (D E : Diagram) :
    transpose (D ∪ E) = transpose D ∪ transpose E := by
  simp only [transpose, Finset.image_union]

/-- Translating a union retains every cell in both complete sets. -/
theorem translate_diagram_union (a : ℤ × ℤ) (D E : Diagram) :
    translate a (D ∪ E) = translate a D ∪ translate a E := by
  simp only [SkewGluing.translate, Finset.image_union]

/-- The reflected complete-window displacement has the original content. -/
theorem content_neg_swap (v : ℤ × ℤ) : content (-v.swap) = content v := by
  simp only [content, Prod.fst_neg, Prod.snd_neg, Prod.fst_swap, Prod.snd_swap]
  ring

/-- The actual complete two-copy union transports to the transposed source.
Its shifted union is the complete transposed amalgamation, not only an interval minor. -/
theorem complete_overlap_union_transpose {n m s : ℕ}
    (P : Profile n) (T : Profile m) (A : Profile s)
    (v a u : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells)
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    T.cells ∪ translate (-v.swap) T.cells =
      translate (-a - v.swap + u.swap) (transpose A.cells) := by
  have hT : translate (-a) (transpose P.cells) = T.cells := by
    rw [ha, SkewGluing.translate_translate, neg_add_cancel, translate_zero]
  have h := congrArg (fun D : Diagram => translate (-a - v.swap) (transpose D)) hA
  simp only [transpose_diagram_union, transpose_translate, translate_diagram_union,
    SkewGluing.translate_translate] at h
  have he : (-a - v.swap) + v.swap = -a := by abel
  have he' : -a - v.swap = -v.swap + -a := by abel
  rw [he, hT, he', ← SkewGluing.translate_translate, hT] at h
  have he'' : -v.swap + -a + u.swap = -a - v.swap + u.swap := by abel
  rw [he''] at h
  exact (Finset.union_comm _ _).trans h

/-- The whole transposed selected diagram produces an actual coordinate with
the same selected index; no span compatibility is left as a binder. -/
theorem exists_transposed_selectedCoordinate {D : Diagram} {hD : IsConnectedSkew D}
    (c : Matrix.SelectedCoordinate D hD) :
    ∃ d : Matrix.SelectedCoordinate (transpose D) (isConnectedSkew_transpose hD), d.top = c.top := by
  obtain ⟨d⟩ := Matrix.exists_selectedCoordinate (isConnectedSkew_transpose hD)
  refine ⟨d, ?_⟩
  have ht := d.span_eq
  rw [span_transpose, ← c.span_eq] at ht
  exact PNat.eq ht

end SkewCornerDescent
