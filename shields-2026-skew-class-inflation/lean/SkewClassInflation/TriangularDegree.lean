/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Nonvanishing at a new linear polynomial variable

The leading-degree step of `lem:triangular-substitution` in
`shields-2026-skew-class-inflation.tex`.  A polynomial whose coefficients
are independent of a variable cannot vanish at an element of variable
degree one.  The argument works in every characteristic.  Sorry-free.
-/

namespace SkewClassInflation

open scoped BigOperators

/-- A new degree-one variable satisfies no nonzero polynomial with old coefficients. -/
theorem eval_ne_zero_of_new_variable {σ K : Type*} [CommRing K] [IsDomain K]
    (x : σ) (y : MvPolynomial σ K) (hy : y.degreeOf x = 1)
    (p : Polynomial (MvPolynomial σ K)) (hp : p ≠ 0)
    (hcoeff : ∀ i, (p.coeff i).degreeOf x = 0) : p.eval y ≠ 0 := by
  classical
  by_cases hd : p.natDegree = 0
  · rw [Polynomial.eval_eq_sum_range, hd, Finset.sum_range_one, pow_zero, mul_one]
    have hc := Polynomial.leadingCoeff_ne_zero.mpr hp
    simpa only [Polynomial.leadingCoeff, hd] using hc
  have hdp : 0 < p.natDegree := by omega
  have hy0 : y ≠ 0 := MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [hy]; decide)
  let L := p.coeff p.natDegree * y ^ p.natDegree
  let R := ∑ i ∈ Finset.range p.natDegree, p.coeff i * y ^ i
  have hlead : (p.coeff p.natDegree) ≠ 0 := by
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hL : L.degreeOf x = p.natDegree := by
    rw [MvPolynomial.degreeOf_mul_eq hlead (pow_ne_zero _ hy0), hcoeff,
      MvPolynomial.degreeOf_pow_eq x y _ hy0, hy, zero_add, mul_one]
  have hR : R.degreeOf x < p.natDegree := by
    have hb := MvPolynomial.degreeOf_sum_le x (Finset.range p.natDegree)
      (fun i => p.coeff i * y ^ i)
    apply lt_of_le_of_lt hb
    apply (Finset.sup_lt_iff (by omega)).mpr
    intro i hi
    have hm := MvPolynomial.degreeOf_mul_le x (p.coeff i) (y ^ i)
    have hh := MvPolynomial.degreeOf_pow_le x y i
    rw [hcoeff, zero_add] at hm
    rw [hy, mul_one] at hh
    have hir : i < p.natDegree := Finset.mem_range.mp hi
    omega
  have he : p.eval y = L + R := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_comm]
  have hdegree : (p.eval y).degreeOf x = p.natDegree := by
    rw [he, MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (hL ▸ hR), hL]
  exact MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [hdegree]; omega)

end SkewClassInflation
