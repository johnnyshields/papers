/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueLowerBounds

/-!
# Polynomial intersection with the original lower rational field

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Membership in a lower rational field forces
an original polynomial to use only its lower generators. Rational corrections can therefore
be cleared by their actual lower denominator without losing their polynomial support.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- Every lower-field fraction has a numerator and nonzero denominator in the lower
polynomial algebra. -/
theorem lowerGeneratorField_fraction {K : ℕ+} {x : actualField}
    (hx : x ∈ lowerGeneratorField K) :
    ∃ a ∈ supported ℚ {j : ℕ+ | j < K}, ∃ b ∈ supported ℚ {j : ℕ+ | j < K},
      b ≠ 0 ∧ x = originalMap a / originalMap b := by
  let S := supported ℚ {j : ℕ+ | j < K}
  change x ∈ Subfield.closure _ at hx
  induction hx using Subfield.closure_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine ⟨X j.val, (X_mem_supported (R := ℚ)).mpr j.property, 1, S.one_mem, one_ne_zero, ?_⟩
      rw [map_one, div_one]
  | one =>
      exact ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, by rw [map_one, div_one]⟩
  | @add x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, hb0, rfl⟩ := ihx
      obtain ⟨d, hd, e, he, he0, rfl⟩ := ihy
      refine ⟨a * e + d * b, S.add_mem (S.mul_mem ha he) (S.mul_mem hd hb),
        b * e, S.mul_mem hb he, mul_ne_zero hb0 he0, ?_⟩
      rw [map_add, map_mul, map_mul, map_mul]
      have hmb : originalMap b ≠ 0 := by simpa only [ne_eq, originalMap_eq_zero] using hb0
      have hme : originalMap e ≠ 0 := by simpa only [ne_eq, originalMap_eq_zero] using he0
      field_simp [hmb, hme]
  | @neg x _ ih =>
      obtain ⟨a, ha, b, hb, hb0, rfl⟩ := ih
      exact ⟨-a, S.neg_mem ha, b, hb, hb0, by rw [map_neg, neg_div]⟩
  | @inv x _ ih =>
      obtain ⟨a, ha, b, hb, hb0, rfl⟩ := ih
      by_cases ha0 : a = 0
      · subst a
        exact ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, by
          rw [map_zero, zero_div, inv_zero, zero_div]⟩
      · exact ⟨b, hb, a, ha, ha0, inv_div _ _⟩
  | @mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, hb0, rfl⟩ := ihx
      obtain ⟨d, hd, e, he, he0, rfl⟩ := ihy
      refine ⟨a * d, S.mul_mem ha hd, b * e, S.mul_mem hb he, mul_ne_zero hb0 he0, ?_⟩
      rw [map_mul, map_mul, div_mul_div_comm]

/-- Lower polynomial support gives the corresponding strict natural span bound. -/
theorem polynomialSpan_lt_of_supported {K : ℕ+} {p : Lambda}
    (hp : p ∈ supported ℚ {j : ℕ+ | j < K}) : polynomialSpan p < (K : ℕ) := by
  apply Finset.sup_lt_iff K.property |>.mpr
  intro j hj
  exact mem_supported.mp hp hj

/-- A polynomial lying in the lower rational field already lies in the lower polynomial
algebra; field membership cannot hide a higher original generator. -/
theorem originalMap_mem_lower_iff {K : ℕ+} {p : Lambda} :
    originalMap p ∈ lowerGeneratorField K ↔ p ∈ supported ℚ {j : ℕ+ | j < K} := by
  constructor
  · intro hp
    by_cases hp0 : p = 0
    · rw [hp0]
      exact Subalgebra.zero_mem _
    obtain ⟨a, ha, b, hb, hb0, he⟩ := lowerGeneratorField_fraction hp
    have hmb : originalMap b ≠ 0 := by simpa only [ne_eq, originalMap_eq_zero] using hb0
    have hm : p * b = a := originalMap_injective (by
      rw [map_mul, he, div_mul_cancel₀ _ hmb])
    have hspan := polynomialSpan_lt_of_supported ha
    rw [← hm, polynomialSpan_mul p b hp0 hb0] at hspan
    apply mem_supported.mpr
    intro j hj
    change (j : ℕ) < (K : ℕ)
    exact lt_of_le_of_lt (Finset.le_sup hj) (lt_of_le_of_lt (le_max_left _ _) hspan)
  · intro hp
    exact supported_map_mem_subfield originalMap (lowerGeneratorField K) {j : ℕ+ | j < K}
      (fun j hj => Subfield.subset_closure ⟨⟨j, hj⟩, rfl⟩) hp

end SkewCornerDescent.Matrix
