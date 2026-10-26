/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureNormalQuotient
import SkewCornerDescent.Matrix.CompleteNormalizedLogCancellation

/-!
# Complete original Schur logarithm and its full removed factor

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both actual orientation signs are retained before normal substitution.
The complete normalized logarithm splits into the whole removed determinant
and the whole retained determinant, with no first-jet independence assumption.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual split and retained endpoint orientations produce their own nonzero
constant scalar in the complete normal determinant factorization. -/
theorem original_normal_removed_factorization {n : ℕ} (P : Profile n) :
    ∃ ε : OtherField c.top, ε ≠ 0 ∧
      PowerSeries.C ε * c.normalPolynomialSeries P.schur =
        c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det *
          c.normalSeries (c.originalHessenbergResponse P).det := by
  classical
  let σh := (originalHessenbergCols (hD := hD) P).symm.trans
    (originalHessenbergRows (hD := hD) P)
  let σs := (originalColSplitEquiv (hD := hD) P).symm.trans
    (originalRowSplitEquiv (hD := hD) P)
  let εh : ℤ := Equiv.Perm.sign σh
  let εs : ℤ := Equiv.Perm.sign σs
  let ε : OtherField c.top := (εh : OtherField c.top) * (εs : OtherField c.top)
  have heh : (εh : OtherField c.top) ≠ 0 :=
    Int.cast_ne_zero.mpr (Units.ne_zero (Equiv.Perm.sign σh))
  have hes : (εs : OtherField c.top) ≠ 0 :=
    Int.cast_ne_zero.mpr (Units.ne_zero (Equiv.Perm.sign σs))
  refine ⟨ε, mul_ne_zero heh hes, ?_⟩
  have h := c.originalHessenbergResponse_local_det P
  rw [originalSplitMatrix_det] at h
  have hn := congrArg c.normalSeries h
  simp only [map_mul, c.normalSeries_polynomial, map_intCast] at hn
  simpa only [ε, εh, εs, σh, σs, map_mul, map_intCast, mul_assoc] using hn

/-- The complete removed and retained normal determinants have nonzero residues.
Their units follow from the actual original Schur residue and signed factorization. -/
theorem original_normal_removed_units {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    PowerSeries.constantCoeff
        (c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det) ≠ 0 ∧
      PowerSeries.constantCoeff (c.normalSeries (c.originalHessenbergResponse P).det) ≠ 0 := by
  obtain ⟨ε, hε, hfactor⟩ := c.original_normal_removed_factorization P
  have hfull : PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur) ≠ 0 := by
    rw [c.normalPolynomialSeries_constant]
    exact c.originalSchur_residue_ne_zero P hB hmax
  have hc := congrArg PowerSeries.constantCoeff hfactor
  simp only [map_mul, PowerSeries.constantCoeff_C] at hc
  have hprod : PowerSeries.constantCoeff
      (c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det) *
      PowerSeries.constantCoeff (c.normalSeries (c.originalHessenbergResponse P).det) ≠ 0 := by
    rw [← hc]
    exact mul_ne_zero hε hfull
  constructor
  · intro hz
    exact hprod (by rw [hz, zero_mul])
  · intro hz
    exact hprod (by rw [hz, mul_zero])

/-- Every normal coefficient of the original normalized Schur logarithm is the
sum of its complete removed and retained logarithms. Unit residues and the
orientation normalization are produced from the actual source. -/
theorem original_normal_log_removed_split {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let full := c.normalPolynomialSeries P.schur
    let removed := c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det
    let retained := c.normalSeries (c.originalHessenbergResponse P).det
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff full)⁻¹ * full) =
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff removed)⁻¹ * removed) +
        PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff retained)⁻¹ * retained) := by
  obtain ⟨ε, hε, hfactor⟩ := c.original_normal_removed_factorization P
  obtain ⟨hremoved, hretained⟩ := c.original_normal_removed_units P hB hmax
  have h := congrArg (fun p : PowerSeries (OtherField c.top) =>
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)) hfactor
  rw [normalized_log_constant_mul _ ε hε,
    normalized_log_mul_complete _ _ hremoved hretained] at h
  exact h

end SkewCornerDescent.Matrix.SelectedCoordinate
