/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalClosureParentStripPeriod
import SkewCornerDescent.Matrix.OriginalSelectedCells

/-!
# A fixed physical cell translation from genuine literal interval periods

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete original interval copies preserve actual physical row gaps and
beta gaps. Finite telescoping gives one common physical displacement
for every genuine period step, with positive row and negative content
components. No pointwise shift is supplied as a hypothesis. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Genuine literal interval periods produce one fixed nonzero physical cell translation. -/
theorem originalLiteralPeriod_fixed_cell_shift {n : ℕ} (P : Profile n) (r : ℕ) [NeZero r]
    (hr : r < originalSelectedCount (hD := hD) P)
    (hperiod : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1), j.val = i.val+r →
      (originalHessenbergDistance (hD := hD) P
          (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
        originalHessenbergDistance (hD := hD) P
          (originalInternalStateIndex P j) (originalInternalStateIndex P j)) ∧
      originalInternalLiteralCopy P i j) :
    ∃ v : ℤ × ℤ, 0 < v.1 ∧ content v < 0 ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) P - 1), j.val = i.val+r →
        originalInternalCellShift P i j = v) ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val+r →
        (originalSelectedSourceRow P j - originalSelectedSourceRow P i = v.1) ∧
          (originalSelectedSourceBeta P j - originalSelectedSourceBeta P i = content v)) := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  let B := originalSelectedCount (hD := hD) P - 1
  have hcount : 0 < originalSelectedCount (hD := hD) P := by omega
  have hB : B < originalSelectedCount (hD := hD) P := by dsimp only [B]; omega
  have hrB : r ≤ B := by dsimp only [B]; omega
  have hrows : ∀ i : Fin (originalSelectedCount (hD := hD) P - 1), (hi : i.val+r < B) →
      originalInternalSourceRowGap P ⟨i.val+r, hi⟩ = originalInternalSourceRowGap P i := by
    intro i hi
    let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨i.val+r, hi⟩
    have h := hperiod i j rfl
    exact (originalInternal_literal_source_row_gap P i j h.1 h.2).symm
  have hbetas : ∀ i : Fin (originalSelectedCount (hD := hD) P - 1), (hi : i.val+r < B) →
      originalInternalSourceBetaGap P ⟨i.val+r, hi⟩ = originalInternalSourceBetaGap P i := by
    intro i hi
    let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨i.val+r, hi⟩
    have h := hperiod i j rfl
    rw [coord.originalInternal_source_beta_gap_height P j,
      coord.originalInternal_source_beta_gap_height P i, h.1]
  let R := originalSelectedSourceRow P ⟨r, hr⟩ - originalSelectedSourceRow P ⟨0, hcount⟩
  let H := originalSelectedSourceBeta P ⟨r, hr⟩ - originalSelectedSourceBeta P ⟨0, hcount⟩
  have hR := originalSelected_source_row_displacement P r B hB hrB hrows
  have hH := originalSelected_source_beta_displacement P r B hB hrB hbetas
  have hRpos : 0 < R := by
    apply sub_pos.mpr
    apply originalSelectedSourceRow_strictMono P
    change (0 : ℕ) < r
    exact NeZero.pos r
  have hHneg : H < 0 := by
    apply sub_neg.mpr
    apply originalSelectedSourceBeta_strictAnti P
    change (0 : ℕ) < r
    exact NeZero.pos r
  refine ⟨(R,H+R), hRpos, ?_, ?_, ?_⟩
  · change H+R-R < 0
    omega
  · intro i j hij
    have hbound : i.val+r ≤ B := by have := j.isLt; dsimp only [B]; omega
    have hrank := hR i.val hbound
    have hbeta := hH i.val hbound
    have hrank' : (originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ) = R := by
      simpa only [← hij, originalSelectedSourceRow, originalInternalRowStart, R] using hrank
    have hbeta' : originalInternalIntervalShift P i j = H := by
      rw [originalInternalIntervalShift_eq_beta]
      simpa only [← hij] using hbeta
    apply Prod.ext
    · exact hrank'
    · change originalInternalIntervalShift P i j + (originalInternalRowStart P j : ℤ) -
        (originalInternalRowStart P i : ℤ) = H+R
      rw [hbeta']
      calc
        _ = H + ((originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ)) := by ring
        _ = H+R := by rw [hrank']
  · intro i j hij
    have hbound : i.val+r ≤ B := by have := j.isLt; dsimp only [B]; omega
    have hrank := hR i.val hbound
    have hbeta := hH i.val hbound
    change (originalSelectedSourceRow P j - originalSelectedSourceRow P i = R) ∧
      (originalSelectedSourceBeta P j - originalSelectedSourceBeta P i = H+R-R)
    constructor
    · simpa only [← hij] using hrank
    · have hh : originalSelectedSourceBeta P j - originalSelectedSourceBeta P i = H := by
        simpa only [← hij] using hbeta
      omega

end SkewCornerDescent.Matrix.SelectedCoordinate
