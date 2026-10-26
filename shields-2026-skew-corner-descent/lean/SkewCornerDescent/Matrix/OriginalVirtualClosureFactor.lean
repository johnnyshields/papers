/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.EmptyClosureComplement
import SkewCornerDescent.Matrix.CompleteNormalizedLogCancellation
import SkewCornerDescent.Matrix.OriginalNormalSeries

/-!
# Whole virtual vertical-closure factor

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`cor:row-pencil`). The complementary actual empty closures identify the virtual
factor with the negative vertical Schur function. Constant normalization
retains the entire logarithm at odd as well as even multiplicity. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing

/-- The complete vertical closure represents the negative virtual row-pencil
factor. This identity retains every cell, not only the selected residue. -/
theorem originalVertical_virtual_factor {n q : ℕ} (P : Profile n) (Q : Profile q)
    (z : ℤ × ℤ) (hQ : originalVerticalClosure P = translate z Q.cells) :
    cellSchur (originalHorizontalClosure P) (originalHorizontalClosure_connected P).1 -
      P.schur ^ 2 = -Q.schur := by
  have hV : cellSchur (originalVerticalClosure P) (originalVerticalClosure_connected P).1 =
      Q.schur := by
    rw [cellSchur_congr hQ _ (isSkew_translate z Q.isSkew_cells),
      cellSchur_translate Q.cells Q.isSkew_cells z, cellSchur_cells Q]
  have h := empty_closure_schur_complement P
  rw [hV] at h
  linear_combination h

/-- Exact orientation adjustment preserves the whole comparison logarithm,
including odd closure multiplicities. -/
theorem residue_matched_negative_factor_log {F : Type*} [Field F] [Algebra ℚ F]
    (E f V : PowerSeries F) (κ : F) (b a d : ℕ)
    (hE : PowerSeries.constantCoeff E ≠ 0)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hV : PowerSeries.constantCoeff V ≠ 0)
    (hmatch : PowerSeries.constantCoeff E ^ b =
      κ * (PowerSeries.constantCoeff f ^ a * PowerSeries.constantCoeff (-V) ^ d)) :
    PowerSeries.logOf (PowerSeries.C κ⁻¹ * (E ^ b * (f ^ a * (-V) ^ d)⁻¹)) =
      PowerSeries.logOf (PowerSeries.C (κ * (-1) ^ d)⁻¹ *
        (E ^ b * (f ^ a * V ^ d)⁻¹)) := by
  have hmatch' : PowerSeries.constantCoeff E ^ b =
      (κ * (-1) ^ d) * (PowerSeries.constantCoeff f ^ a *
        PowerSeries.constantCoeff V ^ d) := by
    rw [hmatch, map_neg, ← neg_one_mul (PowerSeries.constantCoeff V), mul_pow]
    ring
  have hneg : PowerSeries.constantCoeff (-V) ≠ 0 := by
    simpa only [map_neg, neg_ne_zero] using hV
  have hlog := normalized_log_constant_mul V (-1) (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
  simp only [map_neg, map_one, neg_one_mul] at hlog
  rw [residue_matched_ratio_log E f (-V) κ b a d hE hf hneg hmatch,
    residue_matched_ratio_log E f V (κ * (-1) ^ d) b a d hE hf hV hmatch',
    map_neg, hlog]

namespace SelectedCoordinate
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual normal chart preserves the whole signed vertical factor. -/
theorem originalVertical_normal_virtual_factor {n q : ℕ} (P : Profile n) (Q : Profile q)
    (z : ℤ × ℤ) (hQ : originalVerticalClosure P = translate z Q.cells) :
    c.normalPolynomialSeries
        (cellSchur (originalHorizontalClosure P) (originalHorizontalClosure_connected P).1 -
          P.schur ^ 2) = -c.normalPolynomialSeries Q.schur := by
  rw [originalVertical_virtual_factor P Q z hQ, map_neg]

end SelectedCoordinate
end SkewCornerDescent.Matrix
