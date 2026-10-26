/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalNormalStructure
import SkewCornerDescent.Matrix.ResidueSeriesGeneratorDerivation
import SkewCornerDescent.Matrix.NormalInverseProductJets

/-!
# Complete actual internal diagonal inverse jets

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual source supplies all diagonal unit residues and every short-entry
higher-generator exclusion. Complete inverse products retain each original
normal slope and every repeated position. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual internal diagonal has a produced nonzero normal residue. -/
theorem originalInternal_normal_diagonal_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    PowerSeries.constantCoeff (c.normalSeries (c.originalInternalResponseMatrix P i i)) ≠ 0 := by
  rw [c.normalSeries_constant_apply]
  exact c.originalHessenberg_residue_ne_zero P hB hmax (originalInternalStateIndex P i)

/-- The actual complete inverse diagonal product supplies its full first normal slope sum.
No diagonal residue or inverse-jet formula is assumed by the original consumer. -/
theorem originalInternal_inverse_product_coeff_one {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (s : Finset (Fin (originalSelectedCount (hD := hD) P - 1))) :
    let p := fun i => c.normalSeries (c.originalInternalResponseMatrix P i i)
    PowerSeries.coeff 1 (∏ i ∈ s, (p i)⁻¹) =
      -(∏ i ∈ s, (PowerSeries.constantCoeff (p i))⁻¹) *
        ∑ i ∈ s, PowerSeries.coeff 1 (p i) * (PowerSeries.constantCoeff (p i))⁻¹ := by
  exact normal_inverse_product_coeff_one s _
    (fun i _ => c.originalInternal_normal_diagonal_ne_zero P hB hmax i)

/-- Every actual short internal entry has zero higher-generator derivative at all normal
orders before a complete period window. The original gap geometry supplies the exclusion. -/
theorem originalInternal_normal_entry_short {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) (hij : i ≤ j)
    (hlen : j.val - i.val + 1 < d * r) :
    residueSeriesGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.normalSeries (c.originalInternalResponseMatrix P i j)) = 0 := by
  ext m
  rw [residueSeriesGeneratorDeriv_coeff, map_zero]
  change residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
    (PowerSeries.coeff m (c.normalSeries (c.originalHessenbergResponse P
      (originalInternalStateIndex P i) (originalInternalStateIndex P j)))) = 0
  exact c.originalHessenberg_normalSeries_derivative_below P (NeZero.pos _) hmax H hH _ _
    (by change i.val + 1 ≤ j.val + 1; exact Nat.add_le_add_right hij 1)
    ((c.originalInternalDistance_short_period P r d hp i j hij hlen).trans hheight) m

/-- In particular every complete original diagonal is independent of the fresh high
coefficient at a period length at least two, including all positive normal jets. -/
theorem originalInternal_normal_diagonal_high_zero {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    residueSeriesGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.normalSeries (c.originalInternalResponseMatrix P i i)) = 0 := by
  exact c.originalInternal_normal_entry_short P hmax r d hp H hH hheight i i le_rfl (by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
