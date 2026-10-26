/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.EndpointPrefixRecurrence

/-!
# Produced binary first-profile differences at a fixed actual baseline

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Identical strictly earlier coefficients give one common complete-prefix
recurrence value. Actual zero-or-recurrence coefficient alternatives and
a genuine first disagreement then produce a nonzero amplitude and binary
differences, normalized to bit zero at the prescribed actual baseline.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing

private theorem two_value_difference_bits {F I : Type*} [AddGroup F]
    (value : I → F) (base : I) (η0 : F)
    (hcases : ∀ i, value i = 0 ∨ value i = η0)
    (hne : ∃ i, value i ≠ value base) :
    ∃ η : F, η ≠ 0 ∧ (η = η0 ∨ η = -η0) ∧
      ∃ bits : I → Bool, bits base = false ∧
        ∀ i, value i-value base = if bits i then η else 0 := by
  classical
  have hη : η0 ≠ 0 := by
    intro hzero
    have hall (i : I) : value i = 0 := by
      rcases hcases i with h | h
      · exact h
      · exact h.trans hzero
    obtain ⟨i,hi⟩ := hne
    exact hi ((hall i).trans (hall base).symm)
  rcases hcases base with hbase | hbase
  · let bits := fun i => decide (value i = η0)
    refine ⟨η0, hη, Or.inl rfl, bits, ?_, ?_⟩
    · simp [bits, hbase, Ne.symm hη]
    · intro i
      rcases hcases i with hi | hi
      · simp [bits, hi, hbase, Ne.symm hη]
      · simp [bits, hi, hbase]
  · let bits := fun i => decide (value i = 0)
    refine ⟨-η0, neg_ne_zero.mpr hη, Or.inr rfl, bits, ?_, ?_⟩
    · simp [bits, hbase, hη]
    · intro i
      rcases hcases i with hi | hi
      · simp [bits, hi, hbase]
      · simp [bits, hi, hbase, hη]

/-- Common complete earlier prefixes and the produced two-value coefficient
alternatives give a nonzero binary difference from the actual baseline. -/
theorem polynomial_prefix_binary_differences {F I : Type*} [CommRing F]
    (φ : Lambda →+* F) (A : I → Polynomial F) (base : I) (w : ℕ)
    (hprefix : ∀ i j, j < w → (A i).coeff j = (A base).coeff j)
    (hcases : ∀ i, (A i).coeff w = 0 ∨
      (A i).coeff w = completePrefixRecurrenceValue φ (A i) w)
    (hne : ∃ i, (A i).coeff w ≠ (A base).coeff w) :
    ∃ η : F, η ≠ 0 ∧
      (η = completePrefixRecurrenceValue φ (A base) w ∨
        η = -completePrefixRecurrenceValue φ (A base) w) ∧
      ∃ bits : I → Bool, bits base = false ∧
        ∀ i, (A i).coeff w-(A base).coeff w = if bits i then η else 0 := by
  have hc (i : I) : (A i).coeff w = 0 ∨
      (A i).coeff w = completePrefixRecurrenceValue φ (A base) w := by
    rcases hcases i with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (completePrefixRecurrenceValue_congr φ (A i) (A base) w (hprefix i)))
  exact two_value_difference_bits (fun i => (A i).coeff w) base
    (completePrefixRecurrenceValue φ (A base) w) hc hne

end SkewCornerDescent.Matrix
