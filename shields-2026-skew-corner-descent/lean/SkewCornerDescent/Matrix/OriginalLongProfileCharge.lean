/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCrossPrefixCharge
import SkewCornerDescent.Matrix.NormalLongPrefixWeights

/-!
# Actual normal long charges as full directed profile prefixes

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual completed-gap geometry produces the full cross-profile gradients,
and the finite actual residue phase produces every inverse window product.
Their composition keeps the extra first-state inverse and all Laurent
resolving offsets. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual period geometry supplies every cross-profile gradient, and the
actual residue phase supplies the entire extra-state inverse product. -/
theorem originalInternal_long_charge_profiles {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (T : ℕ) [NeZero T]
    (hT : T ≤ originalSelectedCount (hD := hD) P - 1 - d * r)
    (hres : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      j.val = i.val + r → c.originalInternalResidue P i = c.originalInternalResidue P j)
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let hrN : r ≤ originalSelectedCount (hD := hD) P - 1 := by
      have ht := NeZero.pos T
      have hd : 0 < d := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp [hz] at hn
      have hnN : d * r ≤ originalSelectedCount (hD := hD) P - 1 := by omega
      nlinarith
    normalLongPrefixCharge ((c.originalInternalResponseMatrix P).map c.normalSeries)
      δ (d * r - 1) T (by omega) =
      (∏ i : Fin r, (c.originalInternalResidue P ⟨i.val, i.isLt.trans_le hrN⟩)⁻¹)^d *
        c.originalCrossPrefixCharge P (d * r) J T hT := by
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp [hz] at hn
  have hr : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp [hz] at hn
  let : NeZero r := ⟨ne_of_gt hr⟩
  have ht := NeZero.pos T
  have hrN : r ≤ originalSelectedCount (hD := hD) P - 1 := by
    have hnN : d * r ≤ originalSelectedCount (hD := hD) P - 1 := by omega
    nlinarith
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let MP := (c.originalInternalResponseMatrix P).map c.normalSeries
  have hres' (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : j.val = i.val + r) : PowerSeries.constantCoeff (MP i i) =
        PowerSeries.constantCoeff (MP j j) := by
    rw [c.originalInternal_normal_constant P, c.originalInternal_normal_constant P]
    exact hres i j hij
  have hfac := normalLongPrefixCharge_residue_factor MP δ (d * r - 1) d hd
    (by omega) (show T ≤ originalSelectedCount (hD := hD) P - 1 - (d * r - 1 + 1) by omega) hres'
  have hgrad := c.originalInternal_long_prefix_gradient P r d hn hp T hT J H hH
  dsimp only at hfac
  simp only [MP, c.originalInternal_normal_constant P] at hfac
  simp only [Matrix.map_apply, Nat.add_assoc,
    Nat.sub_add_cancel (show 1 ≤ d * r by omega)] at hfac
  rw [hgrad] at hfac
  exact hfac

end SkewCornerDescent.Matrix.SelectedCoordinate
