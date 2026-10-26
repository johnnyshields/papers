/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalCapVectors
import SkewCornerDescent.Matrix.OriginalHorizontalCapVectors

/-!
# Complete matching of literal horizontal and vertical cap lists

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Both actual closure halves have the same complete source cap lists. Composing
the two produced source equivalences identifies every retained row and column,
not merely their diagonal inverse contractions. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The corresponding complete clipped caps of the two literal closures have
identical beta lists, with neither a matrix nor an inverse match assumed. -/
theorem originalClosures_half_cap_vectors {n m s : ℕ}
    (P : Profile n) (V : Profile m) (H : Profile s) (v w : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hH : originalHorizontalClosure P = translate w H.cells) (copy upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let shift : ℤ := if copy then P.xi 0 else 0
    let dV := originalVerticalClosureSelectedCopy P V v hV copy b
    let dH := originalHorizontalClosureSelectedCopy P H w hH copy b
    ∃ e : {i : OriginalWholeWindowRemaining (hD := hD) V shift (P.xi 0 + shift) //
        originalCapBlockSide upper dV i.1.val} ≃
      {i : OriginalWholeWindowRemaining (hD := hD) H shift (P.xi 0 + shift) //
        originalCapBlockSide upper dH i.1.val},
      ∀ i, originalResponseRows H ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows V ⟨i.val.1.val, i.val.2⟩ ∧
        originalResponseCols H ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols V ⟨i.val.1.val, i.val.2⟩ := by
  intro shift dV dH
  obtain ⟨eV, heV⟩ := originalVerticalClosure_half_cap_vectors P V v hV copy upper b
  obtain ⟨eH, heH⟩ := originalHorizontalClosure_half_cap_vectors P H w hH copy upper b
  dsimp only at eV heV eH heH
  refine ⟨eV.symm.trans eH, ?_⟩
  intro i
  have hv := heV (eV.symm i)
  have hh := heH (eV.symm i)
  rw [eV.apply_symm_apply] at hv
  exact ⟨hh.1.trans hv.1.symm, hh.2.trans hv.2.symm⟩

/-- The same complete comparison in the canonical private-cap bounds of
each actual profile. Arithmetic-equal bounds are transported with proved
preservation of the original beta indices. -/
theorem originalClosures_private_cap_vectors {n m s : ℕ}
    (P : Profile n) (V : Profile m) (H : Profile s) (v w : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hH : originalHorizontalClosure P = translate w H.cells) (copy upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let lo : ℤ := if copy then P.xi 0 else 0
    let hiV : ℤ := if copy then V.xi 0 else P.xi 0
    let hiH : ℤ := if copy then H.xi 0 else P.xi 0
    let dV := originalVerticalClosureSelectedCopy P V v hV copy b
    let dH := originalHorizontalClosureSelectedCopy P H w hH copy b
    ∃ e : {i : OriginalWholeWindowRemaining (hD := hD) V lo hiV //
        originalCapBlockSide upper dV i.1.val} ≃
      {i : OriginalWholeWindowRemaining (hD := hD) H lo hiH //
        originalCapBlockSide upper dH i.1.val},
      ∀ i, originalResponseRows H ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows V ⟨i.val.1.val, i.val.2⟩ ∧
        originalResponseCols H ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols V ⟨i.val.1.val, i.val.2⟩ := by
  intro lo hiV hiH dV dH
  let shift : ℤ := if copy then P.xi 0 else 0
  have htopV := originalVerticalClosure_profile_top P V v hV
  have htopH : H.xi 0 = 2 * P.xi 0 := by
    have h := originalHorizontalClosure_xi_upper P H w hH 0
    change H.xi 0 = P.xi 0 + P.xi 0 at h
    omega
  have hvhi : hiV = P.xi 0 + shift := by
    cases copy <;> simp only [hiV, shift, Bool.false_eq_true, ↓reduceIte, add_zero,
      htopV, two_mul]
  have hhhi : hiH = P.xi 0 + shift := by
    cases copy <;> simp only [hiH, shift, Bool.false_eq_true, ↓reduceIte, add_zero,
      htopH, two_mul]
  obtain ⟨eV, heV⟩ := originalWindow_cap_bound_vectors V lo hiV shift (P.xi 0 + shift)
    rfl hvhi upper dV
  obtain ⟨eH, heH⟩ := originalWindow_cap_bound_vectors H lo hiH shift (P.xi 0 + shift)
    rfl hhhi upper dH
  obtain ⟨e0, he0⟩ := originalClosures_half_cap_vectors P V H v w hV hH copy upper b
  refine ⟨(eV.trans e0).trans eH.symm, ?_⟩
  intro i
  have hv := heV i
  have h0 := he0 (eV i)
  have hh := heH (eH.symm (e0 (eV i)))
  rw [eH.apply_symm_apply] at hh
  exact ⟨hh.1.symm.trans (h0.1.trans hv.1), hh.2.symm.trans (h0.2.trans hv.2)⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
