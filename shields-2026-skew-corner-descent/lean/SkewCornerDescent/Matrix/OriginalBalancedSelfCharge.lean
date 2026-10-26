/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelfPrefixCharge
import SkewCornerDescent.CyclicPeriodicSums

/-!
# Actual weighted self-profile cancellation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The independently periodic completed response cancels all chart-gradient
prefix terms. Complete original self-profile coefficients retain exactly
their onsite normal correction, including selected and lower generators.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- In the identified periodic actual closure, the entire weighted self-profile
charge is exactly its onsite normal correction. All chart-gradient terms cancel
by the source occurrence counts, not by assuming a self-product identity. -/
theorem originalClosure_balanced_self_charge {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b d r : ℕ)
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hshort : d * r < originalSelectedCount (hD := hD) P)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P))) (J : ℕ+) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    b • c.originalSelfPrefixCharge P J (d * r) (by omega) -
      d • c.originalSelfPrefixCharge Q J (originalSelectedCount (hD := hD) P) (by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega) =
      c.residueMap (pderiv J (cellSchur D hD.1)) *
        (b • normalOnsitePrefixCharge ((c.originalInternalResponseMatrix P).map c.normalSeries)
          (d * r) (by omega) -
         d • normalOnsitePrefixCharge ((c.originalInternalResponseMatrix Q).map c.normalSeries)
          (originalSelectedCount (hD := hD) P) (by
            have := NeZero.pos (originalSelectedCount (hD := hD) P)
            omega)) := by
  obtain ⟨hCQ, hcycleQ⟩ := c.originalClosure_normal_residue_cycle P Q z hQ active
  have hBpos := NeZero.pos (originalSelectedCount (hD := hD) P)
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hcQ := hcycleQ hactive
  have hSiQ (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
      c.originalInternalResidue Q i = completeResponseCycle (c.originalInternalResidue P) active
        (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
    have he := hcQ i
    rw [c.originalInternal_normal_constant Q] at he
    exact he
  let S := completeResponseCycle (c.originalInternalResidue P) active
  let f := fun i : ZMod (originalSelectedCount (hD := hD) P) =>
    residueChartDeriv c.top J (S i) * (S i)⁻¹
  have hp : Function.Periodic f (r : ZMod (originalSelectedCount (hD := hD) P)) := by
    intro i
    dsimp only [f, S]
    rw [hresponse i]
  have hbalanced : b • windowSum f 1 (d * r) 0 -
      d • windowSum f 1 (originalSelectedCount (hD := hD) P) 0 = 0 := by
    simpa only [← hB] using balanced_periodic_prefix_sums f r hp b d
  have hPchart : (∑ i : Fin (d * r), residueChartDeriv c.top J
      (c.originalInternalResidue P ⟨i.val, by have := i.isLt; omega⟩) *
        (c.originalInternalResidue P ⟨i.val, by have := i.isLt; omega⟩)⁻¹) =
      windowSum f 1 (d * r) 0 := by
    unfold windowSum
    simp only [nsmul_eq_mul, mul_one, zero_add, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f, S]
    rw [completeResponseCycle_prefix (c.originalInternalResidue P) active
      ⟨i.val, by have := i.isLt; omega⟩]
  have hQchart : (∑ i : Fin (originalSelectedCount (hD := hD) P),
      residueChartDeriv c.top J (c.originalInternalResidue Q
        ⟨i.val, by have := i.isLt; omega⟩) *
        (c.originalInternalResidue Q ⟨i.val, by have := i.isLt; omega⟩)⁻¹) =
      windowSum f 1 (originalSelectedCount (hD := hD) P) 0 := by
    unfold windowSum
    simp only [nsmul_eq_mul, mul_one, zero_add, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hSiQ]
  rw [c.originalSelfPrefixCharge_split P J (d * r),
    c.originalSelfPrefixCharge_split Q J (originalSelectedCount (hD := hD) P), hPchart, hQchart]
  simp only [nsmul_eq_mul] at hbalanced ⊢
  linear_combination hbalanced

end SkewCornerDescent.Matrix.SelectedCoordinate
