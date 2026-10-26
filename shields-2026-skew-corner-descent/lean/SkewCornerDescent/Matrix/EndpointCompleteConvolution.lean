/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.BetaEndpointPolynomial

/-!
# Complete generator convolution of the actual incoming endpoint polynomial

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The finite incoming profile convolves with the complete original generator
sequence by its literal row distances. At every actual removed column the
full inverse equation makes this convolution zero. Negative original
indices are zero before natural subtraction can truncate them. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing
open scoped BigOperators
variable {R ν : Type*}

section
variable [CommRing R] [Fintype ν]

/-- The full finite endpoint polynomial convolves with the original
complete generators, retaining all positions and negative-index zeros. -/
theorem ordinaryEndpointProfile_complete_convolution (φ : Lambda →+* R)
    (distance : ν → ℕ) (weight : ν → R) (w : ℕ) :
    (∑ j ∈ Finset.range (w+1), (ordinaryEndpointProfile distance weight).coeff j *
      φ (hh ((w : ℤ) - (j : ℤ)))) =
      φ (hh (w : ℤ)) - ∑ i, weight i * φ (hh ((w : ℤ) - (distance i : ℤ))) := by
  classical
  have hsingle (d : ℕ) (a : R) :
      (∑ j ∈ Finset.range (w+1), (if d = j then a else 0) *
        φ (hh ((w : ℤ) - (j : ℤ)))) = a * φ (hh ((w : ℤ) - (d : ℤ))) := by
    by_cases hd : d ≤ w
    · rw [Finset.sum_eq_single d]
      · rw [ite_eq_left rfl]
      · intro j hj hjd
        rw [ite_eq_right (Ne.symm hjd), zero_mul]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr (by omega)))
    · have hneg : (w : ℤ) - (d : ℤ) < 0 := by omega
      rw [hh_of_neg hneg, map_zero, mul_zero]
      apply Finset.sum_eq_zero
      intro j hj
      have hne : d ≠ j := by have h := Finset.mem_range.mp hj; omega
      rw [ite_eq_right hne, zero_mul]
  have hconst : (∑ j ∈ Finset.range (w+1), (if j = 0 then (1 : R) else 0) *
      φ (hh ((w : ℤ) - (j : ℤ)))) = φ (hh (w : ℤ)) := by
    simpa only [eq_comm, Nat.cast_zero, sub_zero, one_mul] using hsingle 0 1
  simp only [ordinaryEndpointProfile, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, hconst, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hsingle (distance i) (weight i)

end

section
variable [Field R] [Fintype ν] [DecidableEq ν]

/-- The complete actual inverse equation forces the incoming convolution
to vanish at each genuine removed column coordinate. -/
theorem betaEndpointLeftPolynomial_column_convolution (φ : Lambda →+* R)
    (row col : ν → ℤ) (x : ℤ) [Invertible (vertexBetaMatrix φ row col)]
    (hrow : ∀ i, row i ≤ x) (k : ν) (w : ℕ) (hw : (w : ℤ) = x - col k) :
    (∑ j ∈ Finset.range (w+1), (betaEndpointLeftPolynomial φ row col x).coeff j *
      φ (hh ((w : ℤ) - (j : ℤ)))) = 0 := by
  let M := vertexBetaMatrix φ row col
  let V := vertexOutgoing φ col x
  let v := fun i => (V * M⁻¹) () i
  have hprod : (V * M⁻¹) * M = V :=
    Matrix.nonsing_inv_mul_cancel_right M V (Matrix.isUnit_det_of_invertible M)
  have hcol := congrArg (fun T : Matrix Unit ν R => T () k) hprod
  change (∑ i, v i * φ (hh (row i-col k))) = φ (hh (x-col k)) at hcol
  rw [betaEndpointLeftPolynomial, ordinaryEndpointProfile_complete_convolution]
  have he (i : ν) : (w : ℤ) - ((x-row i).toNat : ℤ) = row i-col k := by
    rw [Int.toNat_of_nonneg (by have := hrow i; omega), hw]
    ring
  change φ (hh (w : ℤ)) - ∑ i, v i * φ (hh ((w : ℤ) - ((x-row i).toNat : ℤ))) = 0
  simp_rw [he]
  rw [hw, hcol, sub_self]

end

end SkewCornerDescent.Matrix
