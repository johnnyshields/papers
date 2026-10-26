/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalMarkedLogCoefficient
import SkewCornerDescent.Matrix.OriginalInternalPartitionFirstJet
import SkewCornerDescent.Matrix.NormalMarkedLogOverlap

/-!
# Exact original open-word logarithm after disjoint cancellation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual matrix supplies every diagonal unit and the exact first partition
coefficient. Constant period gradients leave full vertex slopes and overlapping
pair residues. The period-gradient premise is produced by the actual source,
amalgamation, or closure gradient supplier at the consuming assembly.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full actual open-word overlap reduction. The period-entry gradient is DERIVED:
`originalInternal_period_entry_gradient` supplies the source case; the complete
amalgamation and both closure suppliers identify the other actual endpoint intervals. -/
theorem originalInternal_marked_log_overlap {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ))
    (hgradient : let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
      let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
        j.val + 1 = i.val + d * r →
        δ (c.normalSeries (c.originalInternalResponseMatrix P i j)) =
          PowerSeries.C (c.normalCoefficient⁻¹ *
            c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1)))) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let w₀ := fun i => (PowerSeries.constantCoeff (A i i))⁻¹
    let ν := fun i => PowerSeries.coeff 1 (A i i) * w₀ i
    let m := d * r
    let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
    let long := ∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
      if i.val ≤ j.val ∧ j.val - i.val = m then
        δ (A i j) * ∏ k ∈ Finset.Icc i j, (A k k)⁻¹ else 0
    residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (PowerSeries.coeff m (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff A.det)⁻¹ * A.det))) =
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m * PowerSeries.constantCoeff long -
      (-1 : OtherField c.top) ^ (m - 1) * c.normalCoefficient⁻¹ ^ (m - 1) * γ *
        (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
          if j.val - i.val = m - 1 then
            (∏ k ∈ Finset.Icc i j, w₀ k) * ∑ k ∈ Finset.Icc i j, ν k else 0) -
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m * γ *
        (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j, ∑ k, ∑ l,
          if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
            ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
              (∏ s ∈ Finset.Icc i j, w₀ s) *
                (PowerSeries.constantCoeff (A k l) * ∏ s ∈ Finset.Icc k l, w₀ s) else 0) := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
  have hunit (i) : PowerSeries.constantCoeff (A i i) ≠ 0 :=
    c.originalInternal_normal_diagonal_ne_zero P (by omega) hmax i
  have hg (i j) (hij : j.val + 1 = i.val + d * r) : δ (A i j) = PowerSeries.C γ :=
    hgradient i j hij
  have hfirst := c.originalInternal_partition_coeff_one_intervals P hB hmax
  have hlog := c.originalInternal_marked_log_interval_coefficient P hmax r d hn hp J H hH
  have hreduce := normal_marked_log_overlap hn A (fun i j => δ (A i j))
    c.normalCoefficient⁻¹ γ hunit hg hfirst
  dsimp only at hlog hreduce ⊢
  exact hlog.trans hreduce

end SkewCornerDescent.Matrix.SelectedCoordinate
