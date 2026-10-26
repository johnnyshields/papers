/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalCyclicChargeDerivative
import SkewCornerDescent.Matrix.OriginalInternalInverseJets

/-!
# High-generator exclusion from the actual first cyclic charge

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual short-period geometry fixes the complete first-normal cyclic charge
when the period length is at least three. The two-state boundary is separate
and is not covered by this short-entry argument. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At period length at least three every actual adjacent entry is short.
Consequently the complete first-normal cyclic charge omits the high generator;
all onsite inverse jets remain the original ones. -/
theorem originalInternal_first_cyclic_high_zero {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 3 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (T : ℕ) [NeZero T] (hT : T ≤ originalSelectedCount (hD := hD) P - 1 - 1) :
    let M := (c.originalInternalResponseMatrix P).map c.normalSeries
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (normalCyclicFirstCharge
        (normalDiagonalCycle M (show T ≤ originalSelectedCount (hD := hD) P - 1 by omega))
        (normalAdjacentCycle M hT) c.normalCoefficient⁻¹) = 0 := by
  intro M
  let δ := residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
  have hd (i : Fin (originalSelectedCount (hD := hD) P - 1)) (k : ℕ) :
      δ (PowerSeries.coeff k (c.normalSeries (c.originalInternalResponseMatrix P i i))) = 0 := by
    have he := c.originalInternal_normal_diagonal_high_zero P hmax r d (by omega)
      hp H hH hheight i
    have hh := congrArg (PowerSeries.coeff k) he
    simpa only [residueSeriesGeneratorDeriv_coeff, map_zero] using hh
  have hq (s : ZMod T) :
      δ (PowerSeries.constantCoeff (normalAdjacentCycle M hT s)) = 0 := by
    let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨s.val, by
      have := ZMod.val_lt s
      omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨s.val + 1, by
      have := ZMod.val_lt s
      omega⟩
    have he := c.originalInternal_normal_entry_short P hmax r d hp H hH hheight i j
      (by change s.val ≤ s.val + 1; omega) (by dsimp only [i, j]; omega)
    have hh := congrArg (PowerSeries.coeff 0) he
    rw [residueSeriesGeneratorDeriv_coeff, map_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at hh
    exact hh
  apply normalCyclicFirstCharge_deriv_zero (T := T) (F := OtherField c.top) δ
    (normalDiagonalCycle M (show T ≤ originalSelectedCount (hD := hD) P - 1 by omega))
    (normalAdjacentCycle M hT) c.normalCoefficient⁻¹
  · apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono hH.le c.normalCoordinate_mem_lower.1)
  · intro s
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hd ⟨s.val, (ZMod.val_lt s).trans_le (by omega)⟩ 0
  · intro s
    exact hd ⟨s.val, (ZMod.val_lt s).trans_le (by omega)⟩ 1
  · exact hq

end SkewCornerDescent.Matrix.SelectedCoordinate
