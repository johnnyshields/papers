/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TransposeOverlap
import SkewCornerDescent.Matrix.OriginalHorizontalSplice
import SkewGluing.Local.EmptyMark

/-!
# Actual vertical empty closure and its whole transpose

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The vertical closure is the actual empty-mark composition with a two-cell
column outer. Its complete literal union transposes to the complete horizontal
closure, up to the produced normalization and copy displacement. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Transposition exchanges both content extrema of a nonempty actual diagram. -/
theorem maxContent_transpose (D : Diagram) (hD : D.Nonempty) :
    maxContent (transpose D) = -minContent D := by
  calc
    maxContent (transpose D) = maxContent (rotate D) := by
      unfold maxContent
      rw [contents_transpose, ← contents_rotate]
    _ = -minContent D := maxContent_rotate hD

/-- The southwest cell of the whole transposed connected diagram is the
transposed northeast cell of the complete original diagram. -/
theorem sw_transpose_connected {D : Diagram} (hD : IsConnectedSkew D) :
    sw (transpose D) = (ne D).swap := by
  have ht := isConnectedSkew_transpose hD
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hp : diagLo D (maxContent D) = diagHi D (maxContent D) :=
    hs.2.2.2.2 _ (maxContent_mem hs.1)
      (Or.inr (fun h => by have := le_maxContent h; omega))
  have hm := mem_transpose.mp (sw_mem ht.2.1)
  have hc : content (sw (transpose D)).swap = maxContent D := by
    have h := content_sw ht.2.1
    rw [minContent_transpose D hD.2.1] at h
    simp only [content, Prod.fst_swap, Prod.snd_swap] at h ⊢
    omega
  have he := (private_diagonal_iff_unique D (maxContent D)).mp hp
    _ hm _ (ne_mem hD.2.1) hc (content_ne hD.2.1)
  have h := congrArg Prod.swap he
  simpa only [Prod.swap_swap] using h

/-- The northeast cell transforms with the other complete original endpoint. -/
theorem ne_transpose_connected {D : Diagram} (hD : IsConnectedSkew D) :
    ne (transpose D) = (sw D).swap := by
  have h := sw_transpose_connected (isConnectedSkew_transpose hD)
  rw [transpose_transpose] at h
  have he := congrArg Prod.swap h
  simpa only [Prod.swap_swap] using he.symm

/-- Horizontal empty displacement is invariant under normalization by translation. -/
theorem vH_translate_connected {D : Diagram} (hD : IsConnectedSkew D) (a : ℤ × ℤ) :
    vH (translate a D) = vH D := by
  unfold vH
  rw [ne_translate hD.2.1, sw_translate hD.2.1]
  abel

/-- Transposition exchanges the actual vertical empty displacement with the
oppositely directed horizontal one. -/
theorem vH_transpose_connected {D : Diagram} (hD : IsConnectedSkew D) :
    vH (transpose D) = -(vH D - eCell).swap := by
  rw [vH, sw_transpose_connected hD, ne_transpose_connected hD]
  unfold vH eCell
  apply Prod.ext
  · simp
  · simp
    ring

/-- The actual vertical closure uses the canonical empty mark and a literal
column outer, represented by the antitranspose of the positive two-cell row. -/
def originalVerticalClosure {n : ℕ} (P : Profile n) : Diagram :=
  (emptyMarkH P.cells).compose (antitranspose (horizontalRow 2))

/-- The literal vertical closure is an actual connected skew diagram. -/
theorem originalVerticalClosure_connected {n : ℕ} (P : Profile n) :
    IsConnectedSkew (originalVerticalClosure P) := by
  apply MarkedInner.IsLegalEmpty.isConnectedSkew_compose
    (ω := emptyMarkH P.cells) ⟨emptyMarkH_isLegal P.isConnectedSkew_cells, rfl⟩
  exact isConnectedSkew_antitranspose (isConnectedSkew_horizontalRow (by decide))

/-- Both complete source copies occur in the actual vertical empty closure. -/
theorem originalVerticalClosure_union {n : ℕ} (P : Profile n) :
    originalVerticalClosure P = P.cells ∪ translate (vH P.cells - eCell) P.cells := by
  let ω : MarkedInner := ⟨P.cells, ∅, vH P.cells - eCell, .b⟩
  have h := MarkedInner.compose_antitranspose_gauge
    (D := antitranspose (horizontalRow 2))
    ((horizontalRow_nonempty (by decide : 1 ≤ 2)).image _)
    (ωa := emptyMarkH P.cells) (ωb := ω) rfl rfl rfl (by
      change vH P.cells = vH P.cells - eCell + eCell
      abel)
  rw [antitranspose_antitranspose] at h
  change originalVerticalClosure P = ω.compose (horizontalRow 2) at h
  rw [h, ω.compose_horizontalRow (by decide), MarkedInner.rowCopies]
  simp only [show (2 : ℕ) = (0 + 1) + 1 from rfl, Finset.range_add_one,
    Finset.range_zero, Finset.biUnion_insert, Finset.biUnion_empty, Nat.cast_zero,
    Nat.cast_one, zero_smul, one_smul, ω, SkewGluing.translate_zero,
    Finset.empty_union, Finset.union_comm]

/-- The whole actual vertical closure transposes to the horizontal closure
of any normalized transposed source profile, with the complete union retained. -/
theorem vertical_closure_transpose_profile {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) :
    Matrix.originalHorizontalClosure T =
      translate (-a - (vH P.cells - eCell).swap) (transpose (originalVerticalClosure P)) := by
  have hT : translate (-a) (transpose P.cells) = T.cells := by
    rw [ha, SkewGluing.translate_translate, neg_add_cancel, translate_zero]
  have hv : vH T.cells = -(vH P.cells - eCell).swap := by
    have h := vH_transpose_connected P.isConnectedSkew_cells
    rw [ha, vH_translate_connected T.isConnectedSkew_cells] at h
    exact h
  have hH : Matrix.originalHorizontalClosure T =
      T.cells ∪ translate (vH T.cells) T.cells := by
    unfold Matrix.originalHorizontalClosure
    rw [(emptyMarkH T.cells).compose_horizontalRow (by decide), MarkedInner.rowCopies]
    simp only [show (2 : ℕ) = (0 + 1) + 1 from rfl, Finset.range_add_one,
      Finset.range_zero, Finset.biUnion_insert, Finset.biUnion_empty, Nat.cast_zero,
      Nat.cast_one, zero_smul, one_smul, emptyMarkH, SkewGluing.translate_zero,
      Finset.empty_union, Finset.union_comm]
  rw [hH, hv, originalVerticalClosure_union, transpose_diagram_union,
    transpose_translate, translate_diagram_union]
  have hshift : translate (-a - (vH P.cells - eCell).swap) (transpose P.cells) =
      translate (-(vH P.cells - eCell).swap) T.cells := by
    rw [← hT, SkewGluing.translate_translate]
    congr 1
    abel
  rw [hshift, SkewGluing.translate_translate]
  have he : (-a - (vH P.cells - eCell).swap) + (vH P.cells - eCell).swap = -a := by abel
  rw [he, hT, Finset.union_comm]

end SkewCornerDescent
