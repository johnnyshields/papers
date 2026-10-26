/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralParentRows

/-!
# Complete literal parent-row strips from original interval recovery

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both full parent-row bounds transport after all original pivots are restored.
The resulting one physical translation therefore identifies every cell of
the complete parent-row strip between the selected endpoint cores. This
is an actual parent-cell equality, not an interior or response surrogate.
It does not yet assert transport of the whole parent’s private cuts. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Reversing the actual endpoint comparison negates its beta shift. -/
theorem originalInternalIntervalShift_symm {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalInternalIntervalShift P j i = -originalInternalIntervalShift P i j := by
  unfold originalInternalIntervalShift
  ring

/-- The inverse of a complete paired original interval copy is again a literal copy. -/
theorem originalInternalLiteralCopy_symm {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hcopy : originalInternalLiteralCopy P i j) : originalInternalLiteralCopy P j i := by
  obtain ⟨e, he⟩ := hcopy
  refine ⟨e.symm, ?_⟩
  intro r
  have hh := he (e.symm r)
  simp only [Equiv.apply_symm_apply] at hh
  constructor <;> rw [originalInternalIntervalShift_symm P i j] <;> omega

/-- The actual cell translation determined by physical row and beta displacements. -/
noncomputable def originalInternalCellShift {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) : ℤ × ℤ :=
  ((originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ),
    originalInternalIntervalShift P i j + (originalInternalRowStart P j : ℤ) -
      (originalInternalRowStart P i : ℤ))

/-- Reversing the original interval comparison negates its physical cell translation. -/
theorem originalInternalCellShift_symm {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalInternalCellShift P j i = -originalInternalCellShift P i j := by
  unfold originalInternalCellShift
  rw [originalInternalIntervalShift_symm]
  apply Prod.ext <;> dsimp only [Prod.fst_neg, Prod.snd_neg, Prod.fst, Prod.snd] <;> ring

/-- Every parent cell on the common full row range of the restored original beta frame. -/
noncomputable def originalInternalParentStrip {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : Diagram :=
  P.cells.filter fun x => (originalInternalRowStart P i : ℤ) + 1 ≤ x.1 ∧
    x.1 ≤ (originalInternalRowLast P i : ℤ)

/-- The original complete row map translates every cell of the actual parent strip. -/
theorem originalInternal_parent_strip_point {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j)
    (x : ℤ × ℤ) (hx : x ∈ originalInternalParentStrip P i) :
    x + originalInternalCellShift P i j ∈ originalInternalParentStrip P j := by
  rcases x with ⟨a,b⟩
  obtain ⟨hcell, hbound⟩ := Finset.mem_filter.mp hx
  obtain ⟨r, hra, hcols⟩ := P.mem_cells.mp hcell
  have hf := originalInternal_row_frame_bounds P i
  let r0 : Fin n := ⟨r.val, by omega⟩
  have hra0 : (r0.val : ℤ) = a := hra
  have hcast : r0.castSucc = r := Fin.ext rfl
  have hr0 : originalInternalRowStart P i + 1 ≤ r0.val ∧
      r0.val ≤ originalInternalRowLast P i := by
    change originalInternalRowStart P i + 1 ≤ r.val ∧ r.val ≤ originalInternalRowLast P i
    omega
  obtain ⟨s, hs, hrow, hxi, hzeta⟩ :=
    originalInternal_literal_parent_rows P i j hheight hcopy r0 hr0
  have hc : P.zeta r0.castSucc + (r0.val : ℤ) ≤ b ∧ b < P.xi r0.castSucc + (r0.val : ℤ) := by
    simpa only [hcast] using hcols
  apply Finset.mem_filter.mpr
  constructor
  · apply P.mem_cells.mpr
    refine ⟨s.castSucc, ?_, ?_, ?_⟩
    · change (s.val : ℤ) =
        a + ((originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ))
      omega
    · change P.zeta s.castSucc + (s.val : ℤ) ≤ b +
        (originalInternalIntervalShift P i j + (originalInternalRowStart P j : ℤ) -
          (originalInternalRowStart P i : ℤ))
      rw [hzeta]
      omega
    · change b + (originalInternalIntervalShift P i j + (originalInternalRowStart P j : ℤ) -
        (originalInternalRowStart P i : ℤ)) < P.xi s.castSucc + (s.val : ℤ)
      rw [hxi]
      omega
  · change (originalInternalRowStart P j : ℤ) + 1 ≤
        a + ((originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ)) ∧
      a + ((originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ)) ≤
        (originalInternalRowLast P j : ℤ)
    omega

/-- Whole original interval recovery identifies the complete actual parent-cell strips. -/
theorem originalInternal_literal_parent_strips {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    translate (originalInternalCellShift P i j) (originalInternalParentStrip P i) =
      originalInternalParentStrip P j := by
  apply Finset.ext
  intro x
  rw [mem_translate]
  constructor
  · intro hx
    have hh := originalInternal_parent_strip_point P i j hheight hcopy
      (x - originalInternalCellShift P i j) hx
    simpa only [sub_add_cancel] using hh
  · intro hx
    have hh := originalInternal_parent_strip_point P j i hheight.symm
      (originalInternalLiteralCopy_symm P i j hcopy) x hx
    simpa only [originalInternalCellShift_symm P i j, sub_eq_add_neg] using hh

end SkewCornerDescent.Matrix.SelectedCoordinate
