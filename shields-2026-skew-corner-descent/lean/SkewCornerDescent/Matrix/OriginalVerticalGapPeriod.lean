/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalCompletedGaps
import SkewCornerDescent.Matrix.OriginalClosureGapPeriod

/-!
# Exact gap periods in the actual vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The literal completed vertical gap word pulls back the source cycle. Its
period and complete period sum are produced, not assumed at the closure.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The literal vertical gap cycle is the source cycle pulled back along the cyclic projection. -/
theorem originalVerticalClosure_completed_gap_projection {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) Q)]
    (z : ZMod (originalSelectedCount (hD := hD) Q)) :
    c.originalCompletedGap Q ((ZMod.finEquiv _).symm z) =
      c.originalCompletedGap P ((ZMod.finEquiv _).symm
        (ZMod.castHom (show originalSelectedCount (hD := hD) P ∣
          originalSelectedCount (hD := hD) Q by
            rw [originalVerticalClosure_profile_selected_count P Q v hQ]
            exact dvd_mul_left _ _) (ZMod (originalSelectedCount (hD := hD) P)) z)) := by
  have hB : 0 < originalSelectedCount (hD := hD) P := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [c.originalVerticalClosure_completed_gap_mod P Q v hQ hB]
  congr 1
  apply Fin.ext
  simp only [CyclicWindows.finEquiv_symm_val, ZMod.castHom_apply,
    ZMod.cast_eq_val, ZMod.val_natCast]

/-- An actual source gap period produces the same period of the literal closure cycle. -/
theorem originalVerticalClosure_completed_gap_period {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) Q)]
    (r : ℕ)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    Function.Periodic
      (fun z => c.originalCompletedGap Q ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) Q)) := by
  intro z
  dsimp only
  rw [c.originalVerticalClosure_completed_gap_projection P Q v hQ,
    c.originalVerticalClosure_completed_gap_projection P Q v hQ]
  rw [map_add, map_natCast]
  exact hp _

/-- A period-length sum of actual closure gaps equals the same source sum, with all wraps kept. -/
theorem originalVerticalClosure_completed_gap_window {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) Q)] (r : ℕ) :
    CyclicWindows.windowSum
      (fun z => c.originalCompletedGap Q ((ZMod.finEquiv _).symm z)) 1 r 0 =
    CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0 := by
  unfold CyclicWindows.windowSum
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [c.originalVerticalClosure_completed_gap_projection P Q v hQ]
  simp only [map_add, map_zero, map_nsmul, map_one]

end SkewCornerDescent.Matrix.SelectedCoordinate
