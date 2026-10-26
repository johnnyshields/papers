/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureGapPeriod
import SkewCornerDescent.Matrix.OriginalLinearNormalTransfer

/-!
# Source-period transfer to the actual horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). The literal closure
profile, its component span bound, its cyclic gap period, and its period-length gap sum are
produced from the source. The resulting original full determinant has earlier generator
independence and the exact linear response-window derivative. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual closure is constructed together with its original determinant transfer.
No closure profile, response correspondence, or closure periodicity is supplied as input. -/
theorem originalHorizontalClosure_normalized_log_from_source {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k d : ℕ) (hd : 0 < d) (hdB : d < originalSelectedCount (hD := hD) P)
    (hlen : d + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0) :
    ∃ m : ℕ, ∃ Q : Profile m, ∃ v : ℤ × ℤ,
      originalHorizontalClosure P = translate v Q.cells ∧
      originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P ∧
      let p := c.normalSeries (c.originalHessenbergResponse Q).det
      (∀ l, l < d → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff l p) = 0) ∧
      residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff d
          (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
        ((-1 : OtherField c.top) ^ d * (c.normalCoefficient)⁻¹ ^ d) *
          linearInverseWindowSum (c.originalInternalResidue Q) (d + 1) := by
  obtain ⟨m, Q, v, hQ⟩ := (originalHorizontalClosure_connected P).exists_profile_cells
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by omega⟩
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  have hpQ := c.originalHorizontalClosure_completed_gap_period P Q v hQ r hp
  have hdQ : d < originalSelectedCount (hD := hD) Q := by omega
  have hKQ : (K : ℤ) = (c.top : ℤ) + k • CyclicWindows.windowSum
      (fun z => c.originalCompletedGap Q ((ZMod.finEquiv _).symm z)) 1 r 0 := by
    rw [c.originalHorizontalClosure_completed_gap_window P Q v hQ]
    exact hKeq
  refine ⟨m, Q, v, hQ, hc, ?_, ?_⟩
  · exact (c.originalHessenberg_normalized_log_from_periodic_gaps Q hBQ hmaxQ
      r k d hd hdQ hlen hpQ K hK hKQ).1
  · exact c.originalHessenberg_normalized_log_linear_periodic Q hBQ hmaxQ
      r k d hd hdQ hlen hpQ K hK hKQ

end SkewCornerDescent.Matrix.SelectedCoordinate
