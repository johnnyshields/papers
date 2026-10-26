/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRemovedNormalLog

/-!
# Complete original logarithm comparison after removed-power cancellation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact balance of the actual removed polynomial determinants cancels their
whole normalized logarithms, including every normal jet. The balance premise
is derived by the literal closure and corner-power assembly, not discarded by
first-fresh differentiation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete removed-power balance transfers the entire weighted original Schur
logarithm to the entire actual retained determinant logarithm. The balance is a
derived premise whose geometric producer must be invoked at the assembly boundary. -/
theorem original_normal_log_comparison_of_removed_balance {n m k : ℕ}
    (P : Profile n) (A : Profile m) (Q : Profile k) (b a d : ℕ)
    (hP : 0 < originalSelectedCount (hD := hD) P)
    (hA : 0 < originalSelectedCount (hD := hD) A)
    (hQ : 0 < originalSelectedCount (hD := hD) Q)
    (hmaxP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxA : ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ (c.top : ℕ))
    (hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (hremoved : (originalRemovedMatrix (hD := hD) A).det ^ b =
      (originalRemovedMatrix (hD := hD) P).det ^ a *
        (originalRemovedMatrix (hD := hD) Q).det ^ d) :
    let logNorm := fun p : PowerSeries (OtherField c.top) =>
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)
    b • logNorm (c.normalPolynomialSeries A.schur) -
      a • logNorm (c.normalPolynomialSeries P.schur) -
      d • logNorm (c.normalPolynomialSeries Q.schur) =
    b • logNorm (c.normalSeries (c.originalHessenbergResponse A).det) -
      a • logNorm (c.normalSeries (c.originalHessenbergResponse P).det) -
      d • logNorm (c.normalSeries (c.originalHessenbergResponse Q).det) := by
  have hp := c.original_normal_log_removed_split P hP hmaxP
  have ha := c.original_normal_log_removed_split A hA hmaxA
  have hq := c.original_normal_log_removed_split Q hQ hmaxQ
  have hpunit := (c.original_normal_removed_units P hP hmaxP).1
  have haunit := (c.original_normal_removed_units A hA hmaxA).1
  have hqunit := (c.original_normal_removed_units Q hQ hmaxQ).1
  have hpower := congrArg c.normalPolynomialSeries hremoved
  simp only [map_pow, map_mul] at hpower
  have hcancel := normalized_log_balanced_powers
    (c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) A).det)
    (c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det)
    (c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) Q).det)
    b a d haunit hpunit hqunit hpower
  dsimp only at hp ha hq ⊢
  rw [ha, hp, hq]
  simp only [nsmul_eq_mul] at hcancel ⊢
  linear_combination hcancel

end SkewCornerDescent.Matrix.SelectedCoordinate
