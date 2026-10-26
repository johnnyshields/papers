/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.EndpointCompleteConvolution

/-!
# Incoming coefficients recovered from their complete original prefix

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The strictly earlier incoming coefficients determine one recurrence value.
A genuine removed column supplies the full inverse equation identifying
the next coefficient with that value. Nonzero profile coefficients also
supply their actual finite row-distance witnesses. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing
open scoped BigOperators
variable {R ν : Type*}

section
variable [CommRing R]

/-- The complete-generator recurrence value computed from the strictly earlier incoming prefix. -/
noncomputable def completePrefixRecurrenceValue (φ : Lambda →+* R)
    (A : Polynomial R) (w : ℕ) : R :=
  -(∑ j ∈ Finset.range w, A.coeff j * φ (hh ((w : ℤ) - (j : ℤ))))

/-- Matching actual earlier coefficients give the same complete prefix recurrence value. -/
theorem completePrefixRecurrenceValue_congr (φ : Lambda →+* R)
    (A B : Polynomial R) (w : ℕ) (hjet : ∀ j, j < w → A.coeff j = B.coeff j) :
    completePrefixRecurrenceValue φ A w = completePrefixRecurrenceValue φ B w := by
  unfold completePrefixRecurrenceValue
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hjet j (Finset.mem_range.mp hj)]

/-- An absent positive original distance contributes no incoming profile coefficient. -/
theorem ordinary_profile_coeff_of_no_distance [Fintype ν] (distance : ν → ℕ)
    (weight : ν → R) (w : ℕ) (hw : 0 < w) (hno : ∀ i, distance i ≠ w) :
    (ordinaryEndpointProfile distance weight).coeff w = 0 := by
  classical
  have hs : (∑ i, if distance i = w then weight i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (hno i)
  simp only [ordinaryEndpointProfile, Polynomial.coeff_sub, Polynomial.coeff_one,
    ite_eq_right (ne_of_gt hw), Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    hs, sub_self]

/-- A nonzero positive incoming coefficient supplies an actual original row-distance witness. -/
theorem ordinary_profile_nonzero_coefficient_support [Fintype ν] (distance : ν → ℕ)
    (weight : ν → R) (w : ℕ) (hw : 0 < w)
    (hcoeff : (ordinaryEndpointProfile distance weight).coeff w ≠ 0) :
    ∃ i, distance i = w := by
  by_contra hn
  have hno : ∀ i, distance i ≠ w := by simpa only [not_exists] using hn
  exact hcoeff (ordinary_profile_coeff_of_no_distance distance weight w hw hno)

end

section
variable [Field R] [Fintype ν] [DecidableEq ν]

/-- Every genuine original column recovers its incoming coefficient from
the strictly earlier complete prefix, with the full inverse retained. -/
theorem betaEndpointLeftPolynomial_column_coefficient (φ : Lambda →+* R)
    (row col : ν → ℤ) (x : ℤ) [Invertible (vertexBetaMatrix φ row col)]
    (hrow : ∀ i, row i ≤ x) (k : ν) (w : ℕ) (hw : (w : ℤ) = x - col k) :
    (betaEndpointLeftPolynomial φ row col x).coeff w =
      completePrefixRecurrenceValue φ (betaEndpointLeftPolynomial φ row col x) w := by
  have hc := betaEndpointLeftPolynomial_column_convolution φ row col x hrow k w hw
  rw [Finset.sum_range_succ] at hc
  simp only [sub_self, hh_zero, map_one, mul_one] at hc
  unfold completePrefixRecurrenceValue
  calc
    (betaEndpointLeftPolynomial φ row col x).coeff w =
        (betaEndpointLeftPolynomial φ row col x).coeff w -
          ((∑ j ∈ Finset.range w, (betaEndpointLeftPolynomial φ row col x).coeff j *
            φ (hh ((w : ℤ) - (j : ℤ)))) + (betaEndpointLeftPolynomial φ row col x).coeff w) := by
      rw [hc, sub_zero]
    _ = _ := by ring

end

end SkewCornerDescent.Matrix
