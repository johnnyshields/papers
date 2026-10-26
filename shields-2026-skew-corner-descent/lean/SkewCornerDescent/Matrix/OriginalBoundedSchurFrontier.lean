/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSchurAffine

/-!
# Whole-source filtered coefficients from actual gap bounds

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). A bound on
the complete geometric gap cycle supplies every interval bound. The full source
Schur germ retains its removed factor and sign. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original retained interval inventory at one protected distance. -/
noncomputable def originalFilteredIntervalInventory {n : ℕ} (P : Profile n)
    (j : ℕ) (K : ℕ+) : OtherField c.top :=
  ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
    ∑ k : Fin (originalSelectedCount (hD := hD) P + 1),
      if i.val ≤ k.val ∧ k.val - i.val = j - 1 ∧
          originalHessenbergDistance (hD := hD) P i k = (K : ℤ) then
        ∏ l ∈ Finset.Icc i k, (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹
      else 0

/-- A complete cyclic bound supplies the exact filtered coefficient and affine
fresh dependence of the original Schur germ, without a periodicity premise. -/
theorem originalSchur_normalized_log_from_gap_bound {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 2 ≤ j) (hjB : j ≤ originalSelectedCount (hD := hD) P)
    (M : ℤ)
    (hbound : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 j s ≤ M)
    (K : ℕ+) (hK : c.top < K) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    let f := c.normalPolynomialSeries P.schur
    (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l f) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1)
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f))) =
      ((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
        c.originalFilteredIntervalInventory P j K ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      f (j - 1) := by
  have hinterval : ∀ i k : Fin (originalSelectedCount (hD := hD) P + 1), i ≤ k →
      k.val - i.val = j - 1 → originalHessenbergDistance (hD := hD) P i k ≤ (K : ℤ) := by
    intro i k hik hcost
    rw [hKeq]
    apply c.originalHessenbergDistance_bound_of_cyclic_gaps P hB (j - 1) (by omega)
      (by omega) M _ i k hik hcost
    intro z
    have he : j - 1 + 1 = j := by omega
    simpa only [he] using hbound z
  have he := c.originalHessenberg_normalized_log_from_length_bound P hB hmax K hK
    (j - 1) (by omega) (by omega) hinterval
  have hf := c.originalSchur_normalized_log_from_response P hB hmax K hK
    (j - 1) (by omega) he.1
  dsimp only at he hf ⊢
  refine ⟨hf.1, ?_, c.originalSchur_jets_affine_from_length_bound P hB hmax K hK
    (j - 1) (by omega) (by omega) hinterval⟩
  rw [hf.2]
  simpa only [originalFilteredIntervalInventory, Finset.mul_sum, mul_ite, mul_zero] using he.2

end SkewCornerDescent.Matrix.SelectedCoordinate
