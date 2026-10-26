/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureFilteredInventory
import SkewCornerDescent.Matrix.OriginalVirtualCycleTransfer

/-!
# Exact filtered virtual closure coefficients on arbitrary actual gaps

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The complete
original two-copy response word gives the filtered cyclic inventory. Replacing its
one central response preserves the actual gap mask and every start. The virtual
factor, source, closure, and central response units are all supplied by geometry.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The exact first-fresh virtual coefficient is one source filtered inventory
plus one complete shifted closure-cycle inventory. No cyclic gap period is assumed. -/
theorem originalVirtualClosure_normalized_log_filtered_cycle {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 2 ≤ j) (hjB : j ≤ originalSelectedCount (hD := hD) P) (M : ℤ)
    (hbound : ∀ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j z ≤ M)
    (K : ℕ+) (hK : c.top < K) (hKeq : (K : ℤ) = (c.top : ℤ) + M) (α : ℚ) :
    let f := c.normalPolynomialSeries P.schur
    let T := c.normalPolynomialSeries Q.schur - PowerSeries.C (α : OtherField c.top) * f ^ 2
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l T) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1)
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff T)⁻¹ * T))) =
      ((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
        (c.originalFilteredIntervalInventory P j K +
          filteredInverseWindowSum
            (completeResponseCycle (c.originalInternalResidue P)
              (c.originalVirtualCentralResponse P Q middle α))
            (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) j M) ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      T (j - 1) := by
  have ht := c.originalVirtualClosure_normalized_log_from_gap_bound P Q v hQ hB hmax
    j hj hjB M hbound K hK hKeq α
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by omega⟩
  let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
  let g := fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)
  have hS : S ≠ 0 := c.originalHessenberg_residue_ne_zero Q hBQ hmaxQ middle
  have hβ : c.residueMap Q.schur ≠ 0 := c.originalSchur_residue_ne_zero Q hBQ hmaxQ
  have hunit := c.originalVirtualClosure_residue_ne_zero P Q v hQ hB hmax α
  have hQinv := c.originalHorizontalClosure_filtered_interval_inventory P Q v hQ hB
    j hj hjB M hbound K hKeq
  have hPlinear := c.originalFilteredIntervalInventory_eq_linear P hB (j - 1) (by omega)
    (by omega) M (by simpa only [show j - 1 + 1 = j by omega] using hbound) K hKeq
  simp only [show j - 1 + 1 = j by omega] at hPlinear
  have hi := filteredInverseWindowSum_complete_replace (c.originalInternalResidue P) S
    (c.originalVirtualCentralResponse P Q middle α) hS g j hjB M
  dsimp only at ht hQinv ⊢
  refine ⟨ht.1, ?_, ht.2.2⟩
  rw [ht.2.1, hQinv, hi, ← hPlinear]
  unfold originalVirtualCentralResponse
  dsimp only [S, middle] at hS ⊢
  field_simp [hS, hβ, hunit]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
