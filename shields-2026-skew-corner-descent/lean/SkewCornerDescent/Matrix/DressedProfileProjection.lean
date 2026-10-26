/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProfileInverseProjection

/-!
# Two-generator dressed contraction as a full profile projection

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The two high entry lengths add to the original endpoint span. Their dressed
boundary contraction is the full inverse projected at the exact intermediate
position, with both complete endpoint profiles retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν F : Type*} [Fintype ν] [CommRing F]

/-- A dressed two-entry contraction is precisely the complete endpoint-profile
projection. The identity uses no diagonal approximation to the inverse. -/
theorem dressed_profile_inverse_projection (row col : ν → ℤ) (x y p q : ℤ)
    (hsum : p + q = x - y) (B : Matrix Unit ν F) (C : Matrix ν Unit F)
    (I : Matrix ν ν F) :
    let E : Matrix Unit ν F := fun _ j => if x - col j = q then 1 else 0
    let D : Matrix ν Unit F := fun i _ => if row i - y = p then 1 else 0
    let EP : Matrix ν ν F := fun i j => if row i - col j = q then 1 else 0
    let DP : Matrix ν ν F := fun i j => if row i - col j = p then 1 else 0
    ((E - B * I * EP) * I * (D - DP * I * C)) () () =
      profileInverseProjection row col I
        (endpointProfile (fun i => x - row i) (fun i => (B * I) () i))
        (endpointProfile (fun i => col i - y) (fun i => (I * C) i ())) (x - q) := by
  classical
  let E : Matrix Unit ν F := fun _ j => if x - col j = q then 1 else 0
  let D : Matrix ν Unit F := fun i _ => if row i - y = p then 1 else 0
  let EP : Matrix ν ν F := fun i j => if row i - col j = q then 1 else 0
  let DP : Matrix ν ν F := fun i j => if row i - col j = p then 1 else 0
  have hleft (j : ν) : (E - B * I * EP) () j =
      (endpointProfile (fun i => x - row i) (fun i => (B * I) () i)).coeff (x - q - col j) := by
    have hoff : x - q - col j = x - col j - q := by omega
    rw [hoff, endpointProfile_dressed_incoming, Matrix.sub_apply, Matrix.mul_apply]
    simp only [E, EP, mul_ite, mul_one, mul_zero]
  have hright (i : ν) : (D - DP * I * C) i () =
      (endpointProfile (fun j => col j - y) (fun j => (I * C) j ())).coeff (row i - (x - q)) := by
    have hoff : row i - (x - q) = row i - y - p := by omega
    rw [hoff, endpointProfile_dressed_outgoing, Matrix.sub_apply, Matrix.mul_assoc,
      Matrix.mul_apply]
    simp only [D, DP, ite_mul, one_mul, zero_mul]
  dsimp only
  rw [boundary_inverse_contraction_sum]
  simp only [profileInverseProjection]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hleft, hright]

end SkewCornerDescent.Matrix
