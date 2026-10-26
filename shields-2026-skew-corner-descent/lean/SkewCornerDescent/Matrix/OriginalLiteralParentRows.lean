/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralFullBetas

/-!
# Complete original parent rows from literal endpoint intervals

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Restored full beta frames identify both left and right parent-row bounds
at one physical row translation. Consecutive complementary positions
are aligned before applying the original parent convention, so no
interior-row shift is mistaken for a parent row. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Literal complete interval frames transport both bounds of every genuine parent row. -/
theorem originalInternal_literal_parent_rows {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j)
    (r : Fin n) (hr : originalInternalRowStart P i + 1 ≤ r.val ∧
      r.val ≤ originalInternalRowLast P i) :
    ∃ s : Fin n, (originalInternalRowStart P j + 1 ≤ s.val ∧
        s.val ≤ originalInternalRowLast P j) ∧
      ((s.val : ℤ) = (r.val : ℤ) + (originalInternalRowStart P j : ℤ) -
        (originalInternalRowStart P i : ℤ)) ∧
      (P.xi s.castSucc = P.xi r.castSucc + originalInternalIntervalShift P i j) ∧
      (P.zeta s.castSucc = P.zeta r.castSucc + originalInternalIntervalShift P i j) := by
  have hf := originalInternal_literal_row_frame P i j hheight hcopy
  let k := (originalInternalFullSourceEquiv P i).symm ⟨r, by omega⟩
  have hsource : originalInternalFullSourceIndex P i k = r :=
    congrArg Subtype.val ((originalInternalFullSourceEquiv P i).apply_symm_apply ⟨r, by omega⟩)
  have hkv := congrArg Fin.val hsource
  change originalInternalRowStart P i + k.val = r.val at hkv
  have hkpos : 0 < k.val := by omega
  let s := originalInternalFullSourceIndex P j (Fin.cast hf.1 k)
  have hs := originalInternalFullSourceIndex_bounds P j (Fin.cast hf.1 k)
  have hrelative := originalInternalFullSourceIndex_relative P i j hf.1 k
  rw [hsource] at hrelative
  change s.val - originalInternalRowStart P j = r.val - originalInternalRowStart P i at hrelative
  have hstep : (s.val : ℤ) = (r.val : ℤ) + (originalInternalRowStart P j : ℤ) -
      (originalInternalRowStart P i : ℤ) := by omega
  let prev : OriginalInternalFullIndex P i := ⟨k.val-1, by have := k.isLt; omega⟩
  have hprevSource : (originalInternalFullSourceIndex P i prev).succ = r.castSucc := by
    apply Fin.ext
    change originalInternalRowStart P i + (k.val-1) + 1 = r.val
    omega
  have hprevTarget : (originalInternalFullSourceIndex P j (Fin.cast hf.1 prev)).succ =
      s.castSucc := by
    apply Fin.ext
    change originalInternalRowStart P j + (k.val-1) + 1 = originalInternalRowStart P j + k.val
    omega
  have hbetas := originalInternal_literal_full_betas P i j hheight hcopy
  have hxi := (hbetas prev).1
  have hzeta := (hbetas k).2
  rw [hprevSource, hprevTarget] at hxi
  rw [hsource] at hzeta
  refine ⟨s, ?_, hstep, hxi, hzeta⟩
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
