/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.RatioNormalization
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Formal elbow vectors

The cross-product construction in "The ratio identity alone does not give
Cancellative Leftmost" (`subsec:elbow`) proves `prop:elbow` on an arbitrary
integer grid.  These are formal vectors, not asserted cofactor realizations.
-/

namespace SkewSchurReconstruction

open scoped BigOperators Matrix

/-- The cap-remainder row used in the elbow construction. -/
noncomputable def elbowRemainder (r a : ℕ) (d : ℤ) : CompleteRing :=
  complete ((r : ℤ) + a + d) - complete a * complete ((r : ℤ) + d)

/-- The three coefficients of the elbow vector. -/
noncomputable def elbowCoefficients (d : Fin 3 → ℤ) (r a : ℕ) : Fin 3 → CompleteRing :=
  crossProduct (fun i => complete (d i)) (fun i => elbowRemainder r a (d i))

/-- A finite grid vector with the cross-product coefficients at its three shifts. -/
noncomputable def elbowVector (d : Fin 3 → ℤ) (r a : ℕ) : ℤ →₀ CompleteRing :=
  ∑ i, Finsupp.single (d i) (elbowCoefficients d r a i)

theorem elbowVector_response (d : Fin 3 → ℤ) (r a : ℕ) (k : ℤ) :
    gridResponse (elbowVector d r a) k =
      ∑ i, elbowCoefficients d r a i * complete (k + d i) := by
  rw [elbowVector, gridResponse_sum]
  simp only [gridResponse_single]

/-- Orthogonality to the complete-generator row gives the vanishing zeroth cap. -/
theorem elbowVector_response_zero (d : Fin 3 → ℤ) (r a : ℕ) :
    gridResponse (elbowVector d r a) 0 = 0 := by
  rw [elbowVector_response]
  simpa only [dotProduct, zero_add, mul_comm, elbowCoefficients] using
    dot_self_cross (fun i => complete (d i)) (fun i => elbowRemainder r a (d i))

/-- `prop:elbow`: orthogonality to the remainder row supplies the ratio identity. -/
theorem elbowVector_ratioIdentity (d : Fin 3 → ℤ) (r a : ℕ) :
    RatioIdentity (elbowVector d r a) r a := by
  unfold RatioIdentity
  rw [elbowVector_response, elbowVector_response]
  have h := dot_cross_self (fun i => complete (d i))
    (fun i => elbowRemainder r a (d i))
  change (∑ i, elbowRemainder r a (d i) * elbowCoefficients d r a i) = 0 at h
  simp only [elbowRemainder, sub_mul, Finset.sum_sub_distrib] at h
  rw [← sub_eq_zero, Finset.mul_sum]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- The formal elbow is supported on the stated three-point grid. -/
theorem elbowVector_support (d : Fin 3 → ℤ) (r a : ℕ) :
    (elbowVector d r a).support ⊆ Finset.univ.image d := by
  classical
  intro e he
  by_contra hn
  have hd : ∀ i, d i ≠ e := by
    intro i hi
    exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hz : elbowVector d r a e = 0 := by
    simp [elbowVector, hd]
  exact (Finsupp.mem_support_iff.mp he) hz

end SkewSchurReconstruction
