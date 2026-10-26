/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalSeriesSupport

/-!
# Affine first-fresh normal jets

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Earlier
jets lie in the lower-generator field; a first fresh jet is affine in the protected
generator. Products and full formal inverse jets preserve this property at positive
order. Applications to rational fractions still supply their actual unit residues.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F]

/-- Affine dependence on one generator with both coefficients in a fixed subfield. -/
def affineOver (S : Subfield F) (x y : F) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, y = a + b * x

/-- A lower value is affine with zero slope. -/
theorem affineOver_of_mem (S : Subfield F) (x : F) {y : F} (hy : y ∈ S) :
    affineOver S x y :=
  ⟨y, hy, 0, S.zero_mem, by simp⟩

/-- Addition retains both lower coefficients. -/
theorem affineOver_add (S : Subfield F) (x : F) {y z : F}
    (hy : affineOver S x y) (hz : affineOver S x z) : affineOver S x (y + z) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  obtain ⟨c, hc, d, hd, rfl⟩ := hz
  exact ⟨a + c, S.add_mem ha hc, b + d, S.add_mem hb hd, by ring⟩

/-- Multiplying by a lower scalar does not create a quadratic term. -/
theorem affineOver_mul_of_left_mem (S : Subfield F) (x : F) {y z : F}
    (hy : y ∈ S) (hz : affineOver S x z) : affineOver S x (y * z) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact ⟨y * a, S.mul_mem hy ha, y * b, S.mul_mem hy hb, by ring⟩

/-- The right scalar form retains the same affine contract. -/
theorem affineOver_mul_of_right_mem (S : Subfield F) (x : F) {y z : F}
    (hy : affineOver S x y) (hz : z ∈ S) : affineOver S x (y * z) := by
  rw [mul_comm]
  exact affineOver_mul_of_left_mem S x hz hy

/-- Every finite sum of affine values remains affine over the same lower field. -/
theorem affineOver_sum {ι : Type*} (S : Subfield F) (x : F) (s : Finset ι) (y : ι → F)
    (hy : ∀ i ∈ s, affineOver S x (y i)) : affineOver S x (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using affineOver_of_mem S x S.zero_mem
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact affineOver_add S x (hy i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hy j (Finset.mem_insert_of_mem hj)))

/-- Earlier normal coefficients are lower; the first fresh coefficient is affine. -/
def jetsAffineOver (S : Subfield F) (x : F) (p : PowerSeries F) (h : ℕ) : Prop :=
  (∀ n, n < h → PowerSeries.coeff n p ∈ S) ∧ affineOver S x (PowerSeries.coeff h p)

/-- Integral determinant signs preserve the lower and affine jet contracts. -/
theorem jetsAffineOver_zsmul (S : Subfield F) (x : F) {p : PowerSeries F} {h : ℕ}
    (hp : jetsAffineOver S x p h) (z : ℤ) : jetsAffineOver S x (z • p) h := by
  constructor
  · intro n hn
    rw [map_zsmul, zsmul_eq_mul]
    exact S.mul_mem (S.intCast_mem z) (hp.1 n hn)
  · rw [map_zsmul, zsmul_eq_mul]
    exact affineOver_mul_of_left_mem S x (S.intCast_mem z) hp.2

/-- At positive order a convolution has at most one first-fresh factor. -/
theorem jetsAffineOver_mul (S : Subfield F) (x : F) {p q : PowerSeries F} {h : ℕ}
    (hh : 0 < h) (hp : jetsAffineOver S x p h) (hq : jetsAffineOver S x q h) :
    jetsAffineOver S x (p * q) h := by
  constructor
  · intro n hn
    rw [PowerSeries.coeff_mul]
    apply S.sum_mem
    intro j hj
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
    exact S.mul_mem (hp.1 j.1 (by omega)) (hq.1 j.2 (by omega))
  · rw [PowerSeries.coeff_mul]
    apply affineOver_sum
    intro j hj
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
    by_cases hl : j.1 = h
    · rw [hl]
      exact affineOver_mul_of_right_mem S x hp.2 (hq.1 j.2 (by omega))
    · by_cases hr : j.2 = h
      · rw [hr]
        exact affineOver_mul_of_left_mem S x (hp.1 j.1 (by omega)) hq.2
      · exact affineOver_of_mem S x
          (S.mul_mem (hp.1 j.1 (by omega)) (hq.1 j.2 (by omega)))

/-- All inverse jets below the fresh order remain lower; the fresh inverse jet is
still affine. This is a formal-series statement, not a nonvanishing certificate. -/
theorem jetsAffineOver_inv (S : Subfield F) (x : F) {p : PowerSeries F} {h : ℕ}
    (hh : 0 < h) (hp : jetsAffineOver S x p h) : jetsAffineOver S x p⁻¹ h := by
  have h0 : PowerSeries.constantCoeff p ∈ S := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hp.1 0 hh
  have hinv : ∀ n, n < h → PowerSeries.coeff n p⁻¹ ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rw [PowerSeries.coeff_inv]
      split_ifs with hz
      · exact S.inv_mem h0
      · apply S.mul_mem (S.neg_mem (S.inv_mem h0))
        apply S.sum_mem
        intro j hj
        split_ifs with hsmall
        · have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
          exact S.mul_mem (hp.1 j.1 (by omega)) (ih j.2 hsmall (by omega))
        · exact S.zero_mem
  refine ⟨hinv, ?_⟩
  rw [PowerSeries.coeff_inv, ite_eq_right (ne_of_gt hh)]
  apply affineOver_mul_of_left_mem S x (S.neg_mem (S.inv_mem h0))
  apply affineOver_sum
  intro j hj
  split_ifs with hsmall
  · have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
    by_cases hfresh : j.1 = h
    · rw [hfresh]
      exact affineOver_mul_of_right_mem S x hp.2 (hinv j.2 hsmall)
    · exact affineOver_of_mem S x
        (S.mul_mem (hp.1 j.1 (by omega)) (hinv j.2 hsmall))
  · exact affineOver_of_mem S x S.zero_mem

end SkewCornerDescent.Matrix
