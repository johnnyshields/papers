/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalClosureBetaDisplacement

/-!
# Actual selected source cells and their common translations

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Each selected starting row supplies a genuine rightmost parent cell. Its
physical row rank increases strictly while its beta coordinate decreases.
Together the recovered physical and beta increments identify the full
cell displacement, not just a content difference. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The genuine rightmost parent cell on a selected starting row. -/
noncomputable def originalSelectedRowRightCell {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) : ℤ × ℤ :=
  (originalSelectedSourceRow P i + 1,
    originalSelectedSourceBeta P i + originalSelectedSourceRow P i)

/-- Every selected starting-row endpoint is an actual parent cell. -/
theorem originalSelectedRowRightCell_mem {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    originalSelectedRowRightCell P i ∈ P.cells := by
  let k := (originalSelectedEnumeration (hD := hD) P i).val.val.succ
  have he : originalSelectedRowRightCell P i = ((k : ℤ), P.xi k + k - 1) := by
    apply Prod.ext
    · simp [originalSelectedRowRightCell, originalSelectedSourceRow, k]
    · dsimp only [originalSelectedRowRightCell, originalSelectedSourceRow,
        originalSelectedSourceBeta, k, Prod.snd]
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
  rw [he]
  exact P.row_right_mem_cells k

/-- Physical selected source-row ranks are strictly increasing. -/
theorem originalSelectedSourceRow_strictMono {n : ℕ} (P : Profile n) :
    StrictMono (originalSelectedSourceRow (hD := hD) P) := by
  intro i j hij
  have h := (originalSelectedEnumeration (hD := hD) P).strictMono hij
  change (originalSelectedEnumeration (hD := hD) P i).val.val.val <
    (originalSelectedEnumeration (hD := hD) P j).val.val.val at h
  dsimp only [originalSelectedSourceRow]
  exact_mod_cast h

/-- The retained selected-row beta coordinates are strictly decreasing. -/
theorem originalSelectedSourceBeta_strictAnti {n : ℕ} (P : Profile n) :
    StrictAnti (originalSelectedSourceBeta (hD := hD) P) := by
  intro i j hij
  apply P.xi_strictAnti
  change (originalSelectedEnumeration (hD := hD) P i).val.val.val + 1 <
    (originalSelectedEnumeration (hD := hD) P j).val.val.val + 1
  have h : (originalSelectedEnumeration (hD := hD) P i).val.val.val <
      (originalSelectedEnumeration (hD := hD) P j).val.val.val :=
    (originalSelectedEnumeration (hD := hD) P).strictMono hij
  omega

/-- Physical and beta displacements together determine the actual cell translation. -/
theorem originalSelectedRowRightCell_translate {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (R H : ℤ)
    (hrow : originalSelectedSourceRow P j - originalSelectedSourceRow P i = R)
    (hbeta : originalSelectedSourceBeta P j - originalSelectedSourceBeta P i = H) :
    originalSelectedRowRightCell P j = originalSelectedRowRightCell P i + (R,H+R) := by
  apply Prod.ext <;>
    dsimp only [originalSelectedRowRightCell, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
  · omega
  · omega

end SkewCornerDescent.Matrix.SelectedCoordinate
