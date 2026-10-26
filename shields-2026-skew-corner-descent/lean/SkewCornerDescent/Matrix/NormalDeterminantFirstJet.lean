/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Complete first determinant jets from the actual residue inverse

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full series matrix is factored using its genuine invertible constant matrix.
Mathlib's determinant trace expansion gives its first coefficient without freezing
any entry, discarding an inverse coupling or assuming a determinant derivative.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F ι : Type*} [CommRing F] [Fintype ι] [DecidableEq ι]

/-- The exact first determinant coefficient keeps the entire constant inverse
and every entry's actual first normal jet.

**Differs from the paper's route.** Mathlib's determinant trace expansion
replaces the first-order interval partition calculation. -/
theorem normal_det_coeff_one (A : Matrix ι ι (PowerSeries F))
    [Invertible (A.map PowerSeries.constantCoeff)] :
    PowerSeries.coeff 1 A.det = (A.map PowerSeries.constantCoeff).det *
      Matrix.trace ((A.map PowerSeries.constantCoeff)⁻¹ * A.map (PowerSeries.coeff 1)) := by
  let A₀ := A.map PowerSeries.constantCoeff
  let B := A₀.map (PowerSeries.C : F →+* PowerSeries F)
  let I := (A₀⁻¹).map (PowerSeries.C : F →+* PowerSeries F)
  let T : Matrix ι ι (PowerSeries F) := Matrix.of fun i j =>
    PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (A i j)
  let M := I * T
  have hBI : B * I = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A₀ (Matrix.isUnit_det_of_invertible A₀)]
    simp
  have hsplit : A = B + (PowerSeries.X : PowerSeries F) • T := by
    ext i j : 1
    change A i j = PowerSeries.C (PowerSeries.constantCoeff (A i j)) +
      PowerSeries.X * PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) (A i j))
    exact (PowerSeries.eq_X_mul_shift_add_const (A i j)).trans (add_comm _ _)
  have hfactor : A = B * (1 + (PowerSeries.X : PowerSeries F) • M) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hBI,
      Matrix.one_mul]
    exact hsplit
  have hz (p : PowerSeries F) : PowerSeries.coeff 1 (p * PowerSeries.X ^ 2) = 0 := by
    rw [mul_comm, PowerSeries.coeff_X_pow_mul']
    norm_num
  conv_lhs => rw [hfactor, Matrix.det_mul, Matrix.det_one_add_smul]
  have hB : B.det = PowerSeries.C A₀.det := by
    exact (RingHom.map_det PowerSeries.C A₀).symm
  rw [hB, PowerSeries.coeff_C_mul]
  simp only [map_add, hz, PowerSeries.coeff_one, Nat.one_ne_zero, ↓reduceIte,
    PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    zero_add, add_zero]
  congr 1
  change PowerSeries.constantCoeff (Matrix.trace M) = _
  simp only [Matrix.trace, Matrix.diag, map_sum, M, Matrix.mul_apply, map_mul,
    Matrix.map_apply, I, T, Matrix.of_apply, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_mk]
  rfl

/-- The first logarithmic slope of the complete determinant uses its full
actual constant inverse. Genuine determinant invertibility supplies the division. -/
theorem normal_det_first_slope {K κ : Type*} [Field K] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ (PowerSeries K)) [Invertible (A.map PowerSeries.constantCoeff)] :
    PowerSeries.coeff 1 A.det * (PowerSeries.constantCoeff A.det)⁻¹ =
      Matrix.trace ((A.map PowerSeries.constantCoeff)⁻¹ * A.map (PowerSeries.coeff 1)) := by
  have hc : PowerSeries.constantCoeff A.det = (A.map PowerSeries.constantCoeff).det :=
    RingHom.map_det PowerSeries.constantCoeff A
  have hu := (Matrix.isUnit_det_of_invertible (A.map PowerSeries.constantCoeff)).ne_zero
  rw [normal_det_coeff_one, hc]
  field_simp [hu]

end SkewCornerDescent.Matrix
