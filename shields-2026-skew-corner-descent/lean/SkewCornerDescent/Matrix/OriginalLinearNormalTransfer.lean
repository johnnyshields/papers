/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalPeriodicNormalTransfer
import SkewCornerDescent.Matrix.OriginalCapNormalization
import SkewCornerDescent.Matrix.HessenbergLinearWindows
import SkewCornerDescent.LinearWindows

/-!
# The genuine normal derivative as the literal internal response word

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
The linear word consists of actual ordered original residues. Its complete inverse windows
are obtained from the full determinant; no response family or endpoint bound is substituted.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Offset products in the actual complete original matrix are exactly the windows
of its actual internal response word, with every indexed occurrence retained. -/
theorem originalInternalResidue_linear_windows {n : ℕ} (P : Profile n)
    (m : ℕ) (hmB : m < originalSelectedCount (hD := hD) P) :
    (∑ s : Fin (originalSelectedCount (hD := hD) P - (m + 1)),
      ∏ l ∈ Finset.Icc
        (⟨s.val + 1, by have := s.isLt; omega⟩ :
          Fin (originalSelectedCount (hD := hD) P + 1))
        ⟨s.val + m + 1, by have := s.isLt; omega⟩,
          (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹) =
      linearInverseWindowSum (c.originalInternalResidue P) (m + 1) := by
  exact hessenberg_internal_interval_inverse_windows hmB
    (fun l => c.regularResidue (c.originalHessenbergResponse P l l))

/-- The actual periodic determinant has the paper's complete linear internal detector,
including the full-length case where the linear start set is empty. Both caps and all
normal-dependent inverse entries have already been handled in the producing assembly. -/
theorem originalHessenberg_normalized_log_linear_periodic {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P)
    (hlen : m + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z)) 1 r 0) :
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      ((-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m) *
        linearInverseWindowSum (c.originalInternalResidue P) (m + 1) := by
  classical
  dsimp only
  rw [c.originalHessenberg_normalized_log_internal_periodic P hB hmax r k m
    hm hmB hlen hp K hK hKeq, hessenberg_internal_interval_sum hmB, ← Finset.mul_sum,
    c.originalInternalResidue_linear_windows P m hmB]

end SkewCornerDescent.Matrix.SelectedCoordinate
