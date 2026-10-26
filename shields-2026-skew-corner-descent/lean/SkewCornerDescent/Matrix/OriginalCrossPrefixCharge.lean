/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelfPrefixCharge
import SkewCornerDescent.Matrix.OriginalInternalLongEntryGradient

/-!
# Complete actual directed cross-profile prefixes

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual period geometry supplies the full long-entry gradient at every
prefix start. The right profile keeps its genuine shifted original endpoint;
all inverse couplings and integer Laurent offsets remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete directed cross-profile coefficients at genuine finite interval
starts. The shifted right endpoint is its actual original position, not a
wrapped matrix column or a residue-only proper-core surrogate. -/
noncomputable def originalCrossPrefixCharge {n : ℕ} (P : Profile n) (m : ℕ) (J : ℕ+)
    (T : ℕ) (hT : T ≤ originalSelectedCount (hD := hD) P - 1 - m) : OtherField c.top :=
  ∑ s : Fin T,
    let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨s.val, by have := s.isLt; omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨s.val + m, by have := s.isLt; omega⟩
    let p := c.originalInternalEndpointProfiles P i
    let q := c.originalInternalEndpointProfiles P j
    ((p.1 * q.2).toLaurent).coeff
      (originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) - (J : ℤ)) *
      (c.originalInternalResidue P i)⁻¹

/-- The source supplies every full long-entry high gradient in the weighted
cross-profile prefix. Integer resolving offsets and every original inverse
coupling remain; no local gradient equality is an input. -/
theorem originalInternal_long_prefix_gradient {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (T : ℕ) (hT : T ≤ originalSelectedCount (hD := hD) P - 1 - d * r) (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    (∑ s : Fin T, PowerSeries.constantCoeff (δ (c.normalSeries
      (c.originalInternalResponseMatrix P ⟨s.val, by have := s.isLt; omega⟩
        ⟨s.val + d * r, by have := s.isLt; omega⟩))) *
      (c.originalInternalResidue P ⟨s.val, by have := s.isLt; omega⟩)⁻¹) =
        c.originalCrossPrefixCharge P (d * r) J T hT := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  dsimp only [originalCrossPrefixCharge]
  apply Finset.sum_congr rfl
  intro s _
  let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨s.val, by have := s.isLt; omega⟩
  let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨s.val + d * r, by have := s.isLt; omega⟩
  have he := c.originalInternal_long_entry_local_gradient P r d hn hp i j rfl J H hH
  have hheight : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      P.xi (originalRowSplitEquiv P (.inl (some (originalSelectedEnumeration P
        ⟨i.val, by have := i.isLt; omega⟩)))) -
      P.zeta (originalColSplitEquiv P (.inl (some (originalSelectedEnumeration P
        ⟨i.val + 1, by have := i.isLt; omega⟩)))) := by
    rw [originalHessenbergDistance]
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P
      (⟨i.val, by have := i.isLt; omega⟩ : Fin (originalSelectedCount (hD := hD) P)).succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P
        (⟨i.val + 1, by have := i.isLt; omega⟩ :
          Fin (originalSelectedCount (hD := hD) P)).castSucc))) = _
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hc : PowerSeries.constantCoeff
      (δ (c.normalSeries (c.originalInternalResponseMatrix P i j))) =
      residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
        (c.regularResidue (c.originalInternalResponseMatrix P i j)) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, residueSeriesGeneratorDeriv_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, c.normalSeries_constant_apply]
  rw [hc]
  simpa only [originalInternalEndpointProfiles, hheight, i, j] using
    congrArg (fun x => x * (c.originalInternalResidue P i)⁻¹) he

end SkewCornerDescent.Matrix.SelectedCoordinate
