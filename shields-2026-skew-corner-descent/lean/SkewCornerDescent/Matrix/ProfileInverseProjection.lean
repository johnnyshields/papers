/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EndpointVisibleSupport

/-!
# Full endpoint-profile inverse projection

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Dressed generator-entry selectors are the exact endpoint-profile coefficients.
The inverse projection retains every inverse entry and every endpoint weight.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν F : Type*} [Fintype ν] [CommRing F]

/-- The complete incoming profile is the dressed incoming generator selector
at the exact offset, without deleting repeated or zero-valued entries. -/
theorem endpointProfile_dressed_incoming (row col : ν → ℤ) (x p : ℤ)
    (v : ν → F) (j : ν) :
    (endpointProfile (fun i => x - row i) v).coeff (x - col j - p) =
      (if x - col j = p then 1 else 0) -
        ∑ i, if row i - col j = p then v i else 0 := by
  rw [endpointProfile_coeff]
  have hzero : (0 = x - col j - p) ↔ x - col j = p := by omega
  have hindex (i : ν) : (x - row i = x - col j - p) ↔ row i - col j = p := by omega
  simp only [hzero, hindex]

/-- The exact outgoing counterpart uses the full outgoing profile. -/
theorem endpointProfile_dressed_outgoing (row col : ν → ℤ) (y p : ℤ)
    (w : ν → F) (i : ν) :
    (endpointProfile (fun j => col j - y) w).coeff (row i - y - p) =
      (if row i - y = p then 1 else 0) -
        ∑ j, if row i - col j = p then w j else 0 := by
  rw [endpointProfile_coeff]
  have hzero : (0 = row i - y - p) ↔ row i - y = p := by omega
  have hindex (j : ν) : (col j - y = row i - y - p) ↔ row i - col j = p := by omega
  simp only [hzero, hindex]

/-- The complete projected inverse at one actual source position. -/
noncomputable def profileInverseProjection (row col : ν → ℤ) (I : Matrix ν ν F)
    (A B : LaurentPolynomial F) (z : ℤ) : F :=
  ∑ i, ∑ j, A.coeff (z - col i) * I i j * B.coeff (row j - z)

/-- The complete boundary-inverse contraction in the same index order as the
profile projection. -/
theorem boundary_inverse_contraction_sum (L : Matrix Unit ν F) (I : Matrix ν ν F)
    (R : Matrix ν Unit F) :
    (L * I * R) () () = ∑ i, ∑ j, L () i * I i j * R j () := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end SkewCornerDescent.Matrix
