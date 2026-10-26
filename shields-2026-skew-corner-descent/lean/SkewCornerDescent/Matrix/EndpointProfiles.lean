/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Polynomial.Laurent
import SkewCornerDescent.Matrix.OriginalJacobiTrudi

/-!
# Endpoint profiles of the full original Schur complement

Supports local algebraic steps in `shields-2026-skew-corner-descent.tex`, «From response
functions to literal copies» (`sec:one-active`).

The raw derivative identity in `lem:profile-derivative`, with all removed entries retained.
Profiles use integer exponents so that no endpoint difference is silently truncated.
On an actual retained interval, where the removed endpoints lie strictly between its ends,
these are the usual ordinary polynomial profiles.

This module does not prove early recovery of literal endpoint lists. Sorry-free.
-/

open scoped Matrix

namespace SkewCornerDescent.Matrix

open SkewGluing

variable {ν K : Type*} [CommRing K] [Fintype ν]

/-- The profile with specified endpoint distances and full inverse contraction coefficients. -/
noncomputable def endpointProfile (distance : ν → ℤ) (v : ν → K) : LaurentPolynomial K :=
  AddMonoidAlgebra.single (0 : ℤ) (1 : K) -
    ∑ i, AddMonoidAlgebra.single (distance i) (v i)

/-- The ordinary profile for nonnegative endpoint distances. -/
noncomputable def ordinaryEndpointProfile (distance : ν → ℕ) (v : ν → K) : Polynomial K :=
  1 - ∑ i, Polynomial.monomial (distance i) (v i)

/-- The ordinary profile and integer-exponent profile have exactly the same coefficients. -/
theorem toLaurent_ordinaryEndpointProfile (distance : ν → ℕ) (v : ν → K) :
    (ordinaryEndpointProfile distance v).toLaurent =
      endpointProfile (fun i => (distance i : ℤ)) v := by
  simp [ordinaryEndpointProfile, endpointProfile, LaurentPolynomial.single_eq_C_mul_T]

/-- Nonnegative endpoint distances are required before integer subtraction is truncated. -/
theorem endpointProfile_eq_toLaurent_of_nonneg (distance : ν → ℤ) (v : ν → K)
    (hd : ∀ i, 0 ≤ distance i) :
    endpointProfile distance v =
      (ordinaryEndpointProfile (fun i => (distance i).toNat) v).toLaurent := by
  rw [toLaurent_ordinaryEndpointProfile]
  congr 1
  funext i
  exact (Int.toNat_of_nonneg (hd i)).symm

/-- The full product coefficient, including the internal double contraction. -/
theorem endpointProfile_mul_coeff (a b : ν → ℤ) (v w : ν → K) (z : ℤ) :
    (endpointProfile a v * endpointProfile b w).coeff z =
      (if z = 0 then 1 else 0) - ∑ i, (if a i = z then v i else 0) -
        ∑ j, (if b j = z then w j else 0) +
        ∑ i, ∑ j, (if a i + b j = z then v i * w j else 0) := by
  classical
  simp only [endpointProfile, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    AddMonoidAlgebra.single_mul_single, one_mul, mul_one, zero_add, add_zero]
  simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single]
  simp only [Finsupp.finsetSum_apply, Finsupp.sub_apply, Finsupp.single_apply]
  simp only [eq_comm (a := (0 : ℤ))]
  rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun i k => _)]
  abel

variable [DecidableEq ν]

/-- The removed complete original JT block with its actual row and column coordinates. -/
noncomputable def intervalMatrix (row col : ν → ℤ) : Matrix ν ν actualField :=
  fun i j => originalMap (hh (row i - col j))

/-- The incoming original row, including every entry of the removed block. -/
noncomputable def intervalIncoming (x : ℤ) (col : ν → ℤ) : Matrix Unit ν actualField :=
  fun _ i => originalMap (hh (x - col i))

/-- The outgoing original column, including every entry of the removed block. -/
noncomputable def intervalOutgoing (y : ℤ) (row : ν → ℤ) : Matrix ν Unit actualField :=
  fun i _ => originalMap (hh (row i - y))

/-- The actual retained interval response, with its full normal-dependent removed inverse. -/
noncomputable def intervalResponse (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] : actualField :=
  retainedResponse (fun _ _ : Unit => originalMap (hh (x - y)))
    (intervalIncoming x col) (intervalOutgoing y row) (intervalMatrix row col) () ()

/-- Full left endpoint profile of the interval. -/
noncomputable def leftEndpointProfile (x : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] : LaurentPolynomial actualField :=
  endpointProfile (fun i => x - row i)
    (fun i => (intervalIncoming x col * ⅟(intervalMatrix row col)) () i)

/-- Full right endpoint profile of the interval. -/
noncomputable def rightEndpointProfile (y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] : LaurentPolynomial actualField :=
  endpointProfile (fun i => col i - y)
    (fun i => (⅟(intervalMatrix row col) * intervalOutgoing y row) i ())

set_option backward.isDefEq.respectTransparency false in
/-- The original-generator derivative equals the full endpoint-profile product coefficient.
This is the raw identity of `lem:profile-derivative`, not a frozen-residue derivative. -/
theorem generatorDeriv_intervalResponse (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] (j : ℕ+) :
    generatorDeriv j (intervalResponse x y row col) =
      (leftEndpointProfile x row col * rightEndpointProfile y row col).coeff
        (x - y - (j : ℤ)) := by
  classical
  have h := congrFun (congrFun (entryDeriv_retainedResponse (generatorDeriv j)
    (fun _ _ : Unit => originalMap (hh (x - y))) (intervalIncoming x col)
    (intervalOutgoing y row) (intervalMatrix row col)) ()) ()
  change generatorDeriv j (intervalResponse x y row col) = _ at h
  let B := intervalIncoming x col
  let C := intervalOutgoing y row
  let P := intervalMatrix row col
  let Q : Matrix ν ν actualField := ⅟P
  have hL : (entryDeriv (generatorDeriv j) B * (Q * C)) () () =
      ∑ i, if x - col i = (j : ℤ) then (Q * C) i () else 0 := by
    rw [Matrix.mul_apply]
    simp only [B, entryDeriv, intervalIncoming, generatorDeriv_hh,
      ite_mul, one_mul, zero_mul]
  have hR : ((B * Q) * entryDeriv (generatorDeriv j) C) () () =
      ∑ i, if row i - y = (j : ℤ) then (B * Q) () i else 0 := by
    rw [Matrix.mul_apply]
    simp only [C, entryDeriv, intervalOutgoing, generatorDeriv_hh,
      mul_ite, mul_one, mul_zero]
  have hI : ((B * Q) * entryDeriv (generatorDeriv j) P * (Q * C)) () () =
      ∑ i, ∑ k, if row i - col k = (j : ℤ) then
        (B * Q) () i * (Q * C) k () else 0 := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply (M := B * Q) (N := entryDeriv (generatorDeriv j) P),
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [P, entryDeriv, intervalMatrix, generatorDeriv_hh, mul_ite, ite_mul,
      mul_one, mul_zero, zero_mul]
  rw [h, leftEndpointProfile, rightEndpointProfile, endpointProfile_mul_coeff]
  change (entryDeriv (generatorDeriv j) (fun _ _ : Unit => originalMap (hh (x - y))) -
    entryDeriv (generatorDeriv j) B * Q * C -
    B * Q * entryDeriv (generatorDeriv j) C +
    B * Q * entryDeriv (generatorDeriv j) P * Q * C) () () = _
  rw [Matrix.mul_assoc (entryDeriv (generatorDeriv j) B) Q C,
    Matrix.mul_assoc (B * Q * entryDeriv (generatorDeriv j) P) Q C]
  simp only [Matrix.add_apply, Matrix.sub_apply, hL, hR, hI, entryDeriv,
    generatorDeriv_hh]
  have hz : (x - y - (j : ℤ) = 0) ↔ x - y = (j : ℤ) := by omega
  have hl (i : ν) : (x - row i = x - y - (j : ℤ)) ↔ row i - y = (j : ℤ) := by
    omega
  have hr (i : ν) : (col i - y = x - y - (j : ℤ)) ↔ x - col i = (j : ℤ) := by
    omega
  have hi (i k : ν) : (x - row i + (col k - y) = x - y - (j : ℤ)) ↔
      row i - col k = (j : ℤ) := by omega
  simp only [hz, hl, hr, hi]
  abel

end SkewCornerDescent.Matrix
