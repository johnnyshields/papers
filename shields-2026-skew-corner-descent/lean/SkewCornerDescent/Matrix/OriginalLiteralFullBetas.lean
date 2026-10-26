/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralFullFrameGeometry
import SkewCornerDescent.Matrix.OriginalLiteralPivotBetas
import SkewCornerDescent.Matrix.OriginalIntervalColumnCoverage

/-!
# Complete original beta vectors after restoring all four pivots

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Full physical row and column recovery transports every removed coordinate.
The actual selected endpoint span supplies both omitted row and both omitted
column beta coordinates at the same shift. Complete original source
coverage therefore transports the entire beta frame, not just its
eliminated submatrix or its scalar response. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A genuine literal interval copy transports every original beta coordinate in its full frame. -/
theorem originalInternal_literal_full_betas {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    let hL := (originalInternal_literal_row_frame P i j hheight hcopy).1
    ∀ k : OriginalInternalFullIndex P i,
      (P.xi (originalInternalFullSourceIndex P j (Fin.cast hL k)).succ =
        P.xi (originalInternalFullSourceIndex P i k).succ + originalInternalIntervalShift P i j) ∧
      (P.zeta (originalInternalFullSourceIndex P j (Fin.cast hL k)).castSucc =
        P.zeta (originalInternalFullSourceIndex P i k).castSucc +
          originalInternalIntervalShift P i j) := by
  have hf := originalInternal_literal_row_frame P i j hheight hcopy
  obtain ⟨e, he, hphysical⟩ := originalInternal_literal_physical_both_maps P i j hheight hcopy
  have hbeta := originalInternal_equal_height_pivot_betas P i j hheight
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  dsimp only
  intro k
  let source := originalInternalFullSourceIndex P i k
  let target := originalInternalFullSourceIndex P j (Fin.cast hf.1 k)
  have hs := originalInternalFullSourceIndex_bounds P i k
  have ht := originalInternalFullSourceIndex_bounds P j (Fin.cast hf.1 k)
  have hrelative := originalInternalFullSourceIndex_relative P i j hf.1 k
  have hp := originalInternal_literal_full_pivot_ranks P i j hheight hcopy k
  change originalInternalRowStart P i ≤ source.val ∧ source.val ≤ originalInternalRowLast P i at hs
  change originalInternalRowStart P j ≤ target.val ∧ target.val ≤ originalInternalRowLast P j at ht
  change target.val - originalInternalRowStart P j =
    source.val - originalInternalRowStart P i at hrelative
  have hrank : (target.val : ℤ) = (source.val : ℤ) +
      (originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ) := by omega
  change (P.xi target.succ = P.xi source.succ + originalInternalIntervalShift P i j) ∧
    (P.zeta target.castSucc = P.zeta source.castSucc + originalInternalIntervalShift P i j)
  constructor
  · have hcover := (original_consecutive_row_coverage P ai bi rfl source).mp hs
    rcases hcover with hA | hB | ⟨r, hr⟩
    · have htarget : target = (E aj).val.val := Fin.ext (hp.1 (congrArg Fin.val hA))
      simpa only [htarget, hA] using hbeta.1
    · have htarget : target = (E bj).val.val := Fin.ext (hp.2.1 (congrArg Fin.val hB))
      simpa only [htarget, hB] using hbeta.2.1
    · have hm := (hphysical r).1
      have hrv := congrArg Fin.val hr
      have htarget : originalRemovedRow P (e r).val.val.1 (e r).val.val.2 = target :=
        Fin.ext (by omega)
      have hb := (he r).1
      change P.xi (originalRemovedRow P (e r).val.val.1 (e r).val.val.2).succ =
        P.xi (originalRemovedRow P r.val.val.1 r.val.val.2).succ +
          originalInternalIntervalShift P i j at hb
      simpa only [htarget, hr] using hb
  · have hcover := (original_consecutive_col_coverage P ai bi rfl source).mp hs
    rcases hcover with hA | hB | ⟨r, hr⟩
    · have htarget : target = interiorBlockLast P (E aj).val.val :=
        Fin.ext (hp.2.2.1 (congrArg Fin.val hA))
      simpa only [htarget, hA] using hbeta.2.2.1
    · have htarget : target = interiorBlockLast P (E bj).val.val :=
        Fin.ext (hp.2.2.2 (congrArg Fin.val hB))
      simpa only [htarget, hB] using hbeta.2.2.2
    · have hm := (hphysical r).2
      have hrv := congrArg Fin.val hr
      have htarget : originalRemovedCol P (e r).val.val.1 (e r).val.val.2 = target :=
        Fin.ext (by omega)
      have hb := (he r).2
      change P.zeta (originalRemovedCol P (e r).val.val.1 (e r).val.val.2).castSucc =
        P.zeta (originalRemovedCol P r.val.val.1 r.val.val.2).castSucc +
          originalInternalIntervalShift P i j at hb
      simpa only [htarget, hr] using hb

end SkewCornerDescent.Matrix.SelectedCoordinate
