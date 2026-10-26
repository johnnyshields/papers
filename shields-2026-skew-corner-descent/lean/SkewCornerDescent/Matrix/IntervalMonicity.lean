/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.EndpointProfiles
import Mathlib.Tactic

/-!
# Ordinary endpoint profiles and the retained top coefficient

Supports `shields-2026-skew-corner-descent.tex`, «From response functions to literal copies»
(`sec:one-active`, `lem:profile-derivative`) and «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Strictly interior removed endpoints
produce ordinary profiles with constant term one and derivative one in the retained top.
This does not assert the ordered-path support or the literal recovery theorem. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν K : Type*} [CommRing K] [Fintype ν]

/-- Strict endpoint distances protect the constant coefficient of both full profiles. -/
theorem endpointProfile_mul_coeff_zero (a b : ν → ℤ) (v w : ν → K)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (endpointProfile a v * endpointProfile b w).coeff 0 = 1 := by
  rw [endpointProfile_mul_coeff]
  have hA (i : ν) : a i ≠ 0 := ne_of_gt (ha i)
  have hB (i : ν) : b i ≠ 0 := ne_of_gt (hb i)
  have hAB (i j : ν) : a i + b j ≠ 0 := ne_of_gt (add_pos (ha i) (hb j))
  simp only [ite_true, hA, hB, hAB, ite_false, Finset.sum_const_zero, sub_zero, add_zero]

variable [DecidableEq ν]

/-- The profiles of an actual retained interval are ordinary polynomials, after proving
rather than guessing the sign of every integer endpoint difference. -/
theorem interval_profiles_ordinary (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)]
    (hr : ∀ i, row i < x) (hc : ∀ i, y < col i) :
    leftEndpointProfile x row col =
      (ordinaryEndpointProfile (fun i => (x - row i).toNat)
        (fun i => (intervalIncoming x col * ⅟(intervalMatrix row col)) () i)).toLaurent ∧
    rightEndpointProfile y row col =
      (ordinaryEndpointProfile (fun i => (col i - y).toNat)
        (fun i => (⅟(intervalMatrix row col) * intervalOutgoing y row) i ())).toLaurent := by
  constructor
  · exact endpointProfile_eq_toLaurent_of_nonneg _ _ (fun i => by have := hr i; omega)
  · exact endpointProfile_eq_toLaurent_of_nonneg _ _ (fun i => by have := hc i; omega)

/-- The original retained top has coefficient one even with the complete normal-dependent
inverse. Only the positions of the removed endpoints enter this calculation. -/
theorem generatorDeriv_intervalResponse_top (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] (j : ℕ+)
    (hj : x - y = (j : ℤ)) (hr : ∀ i, row i < x) (hc : ∀ i, y < col i) :
    generatorDeriv j (intervalResponse x y row col) = 1 := by
  rw [generatorDeriv_intervalResponse, hj, sub_self]
  apply endpointProfile_mul_coeff_zero
  · intro i; have := hr i; omega
  · intro i; have := hc i; omega

end SkewCornerDescent.Matrix
