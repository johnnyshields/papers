/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalIntervals
import SkewCornerDescent.Matrix.OriginalCyclicGapIntervals

/-!
# Genuine normal transfer from the actual completed gap period

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The actual endpoint bounds, shorter jets, and unit normalization are produced in this
assembly. Periodicity is a standing assumption of the transfer lemma. Its construction
for the headline theorem and the four-diagram interval cancellation are separate obligations.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The exact periodic actual gap word produces earlier determinant independence and
the full signed inverse-window formula in the original local field. No endpoint-distance
or lower-jet inequality is assumed. Periodicity is the transfer lemma's standing assumption. -/
theorem originalHessenberg_normalized_log_from_periodic_gaps {n : ℕ} (P : Profile n)
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
    (∀ l, l < m → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l p) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
        ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
          if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m ∧
              originalHessenbergDistance (hD := hD) P i j = (K : ℤ) then
            (-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m *
              (∏ l ∈ Finset.Icc i j,
                (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹)
          else 0 := by
  apply c.originalHessenberg_normalized_log_from_length_bound P hB hmax K hK m hm
    hmB.le
  intro i j hij hcost
  rw [hKeq]
  exact c.originalHessenbergDistance_bound_of_periodic_gaps P hB r k m hm hmB hlen hp
    i j hij hcost

/-- The periodic original normal derivative is the complete linear internal sum:
both true-cap endpoint regimes vanish by proved strict geometric bounds. -/
theorem originalHessenberg_normalized_log_internal_periodic {n : ℕ} (P : Profile n)
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
      ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
        ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
          if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m ∧
              0 < (i : ℕ) ∧ (j : ℕ) < originalSelectedCount (hD := hD) P then
            (-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m *
              (∏ l ∈ Finset.Icc i j,
                (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹)
          else 0 := by
  classical
  dsimp only
  rw [(c.originalHessenberg_normalized_log_from_periodic_gaps P hB hmax r k m
    hm hmB hlen hp K hK hKeq).2]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hcost : (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m
  · have he := c.originalHessenbergDistance_eq_cyclic_top_iff P hB m hm hmB
      (k • CyclicWindows.windowSum
        (fun z => c.originalCompletedGap P
          ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z)) 1 r 0)
      (fun s => by
        rw [hlen, CyclicWindows.windowSum_of_zmod_period_multiple _ r hp k s])
      i j hcost.1 hcost.2
    rw [← hKeq] at he
    simp only [he]
  · rw [ite_eq_right (fun h => hcost ⟨h.1, h.2.1⟩),
      ite_eq_right (fun h => hcost ⟨h.1, h.2.1⟩)]

end SkewCornerDescent.Matrix.SelectedCoordinate
