/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.LowerResponses
import SkewCornerDescent.Matrix.ComponentIntervals
import SkewCornerDescent.RationalPoles
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.Algebra.Algebra.Rat

/-!
# Protected generators in the original rational field

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:residue-classifier`). A retained top generator is transcendental
over all lower generators. Complete triangular responses preserve that transcendence.
The residue-field identification and the ordered interval classifier are separate obligations.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

noncomputable local instance : Algebra ℚ actualField := OreLocalization.instAlgebra

/-- The original complete-homogeneous generators remain algebraically independent in
 their fraction field; no new presentation of symmetric functions is introduced. -/
theorem original_generators_independent :
    AlgebraicIndependent ℚ (fun j : ℕ+ => originalMap (MvPolynomial.X j)) := by
  let f : Lambda →ₐ[ℚ] actualField :=
    { originalMap with commutes' := RingHom.map_rat_algebraMap originalMap }
  exact (MvPolynomial.algebraicIndependent_X ℕ+ ℚ).map'
    (f := f) originalMap_injective

private theorem lower_adjoin_eq (K : ℕ+) :
    (IntermediateField.adjoin ℚ
      (Set.range (fun j : {j : ℕ+ // j < K} => originalMap (MvPolynomial.X j.1)))).toSubfield =
      lowerGeneratorField K := by
  rw [IntermediateField.adjoin_toSubfield]
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro z (⟨q, rfl⟩ | hz)
    · have hq : algebraMap ℚ actualField q = (q : actualField) := by
        simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ actualField) q
      rw [hq]
      exact SubfieldClass.ratCast_mem (lowerGeneratorField K) q
    · exact Subfield.subset_closure hz
  · exact Subfield.closure_mono Set.subset_union_right

/-- The retained generator is transcendental over the entire lower rational subfield,
 including rational functions rather than merely lower polynomials. -/
theorem original_generator_transcendental (K : ℕ+) :
    Transcendental (lowerGeneratorField K) (originalMap (MvPolynomial.X K)) := by
  have h := original_generators_independent.transcendental_adjoin
    (s := {j : ℕ+ | j < K}) (i := K) (by simp)
  have hs : ((fun j : ℕ+ => originalMap (MvPolynomial.X j)) '' {j : ℕ+ | j < K}) =
      Set.range (fun j : {j : ℕ+ // j < K} => originalMap (MvPolynomial.X j.1)) := by
    ext z
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
  rw [hs] at h
  have h' := IntermediateField.transcendental_adjoin_iff.mpr h
  change Transcendental
    (IntermediateField.adjoin ℚ
      (Set.range (fun j : {j : ℕ+ // j < K} => originalMap (MvPolynomial.X j.1)))).toSubfield
    (originalMap (MvPolynomial.X K)) at h'
  rwa [lower_adjoin_eq K] at h'

/-- Adding any complete lower rational correction cannot destroy the protected top. -/
theorem triangular_transcendental (K : ℕ+) (A : actualField)
    (hA : A ∈ lowerGeneratorField K) :
    Transcendental (lowerGeneratorField K) (originalMap (MvPolynomial.X K) + A) := by
  let a : lowerGeneratorField K := ⟨A, hA⟩
  have h := (original_generator_transcendental K).aeval
    (Polynomial.X + Polynomial.C a)
    (by simp) (by simp)
  simpa [a, Subfield.algebraMap_ofSubfield] using h

/-- A full interval response, with the unmodified inverse correction, is transcendental
over the lower rational field at its geometric retained top. -/
theorem intervalResponse_transcendental {ν : Type*} [Fintype ν] [DecidableEq ν]
    (x y : ℤ) (row col : ν → ℤ) [Invertible (intervalMatrix row col)] (K : ℕ+)
    (hK : x - y = (K : ℤ)) (hr : ∀ i, row i < x) (hc : ∀ i, y < col i) :
    Transcendental (lowerGeneratorField K) (intervalResponse x y row col) := by
  obtain ⟨A, hA, heq, _⟩ := intervalResponse_triangular x y row col K hK hr hc
  rw [heq]
  exact triangular_transcendental K A hA

/-- Dividing a protected response by any nonzero lower rational factor preserves its
transcendence. This includes the complete product of the two true caps once their tops
have been placed strictly below the closure top. -/
theorem triangular_quotient_transcendental (K : ℕ+) (A F : actualField)
    (hA : A ∈ lowerGeneratorField K) (hF : F ∈ lowerGeneratorField K) (hF0 : F ≠ 0) :
    Transcendental (lowerGeneratorField K) ((originalMap (MvPolynomial.X K) + A) / F) := by
  let a : lowerGeneratorField K := ⟨A, hA⟩
  let f : lowerGeneratorField K := ⟨F, hF⟩
  have hf : f ≠ 0 := fun h => hF0 (congrArg Subtype.val h)
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have h := (original_generator_transcendental K).aeval
    (Polynomial.C f⁻¹ * Polynomial.X + Polynomial.C (a / f))
    (by rw [Polynomial.natDegree_linear hfi]; exact one_ne_zero)
    (by rw [Polynomial.leadingCoeff_linear hfi]; exact mem_nonZeroDivisors_of_ne_zero hfi)
  have he : Polynomial.aeval (originalMap (MvPolynomial.X K))
      (Polynomial.C f⁻¹ * Polynomial.X + Polynomial.C (a / f)) =
      (originalMap (MvPolynomial.X K) + A) / F := by
    simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
      Polynomial.aeval_X, map_inv₀, map_div₀, Subfield.algebraMap_ofSubfield]
    change F⁻¹ * originalMap (MvPolynomial.X K) + A / F =
      (originalMap (MvPolynomial.X K) + A) / F
    ring
  rwa [he] at h

/-- A response lies below every strictly greater retained top. -/
theorem triangular_mem_larger_lowerField {K L : ℕ+} (hKL : K < L)
    (A : actualField) (hA : A ∈ lowerGeneratorField K) :
    originalMap (MvPolynomial.X K) + A ∈ lowerGeneratorField L := by
  apply (lowerGeneratorField L).add_mem
  · exact Subfield.subset_closure ⟨⟨K, hKL⟩, rfl⟩
  · exact lowerGeneratorField_mono hKL.le hA

/-- Responses with distinct protected tops cannot be equal as full rational functions. -/
theorem triangular_ne_of_top_lt {K L : ℕ+} (hKL : K < L)
    (A B : actualField) (hA : A ∈ lowerGeneratorField K)
    (hB : B ∈ lowerGeneratorField L) :
    originalMap (MvPolynomial.X K) + A ≠ originalMap (MvPolynomial.X L) + B := by
  intro he
  have hz := triangular_mem_larger_lowerField hKL A hA
  rw [he] at hz
  have halg := isAlgebraic_algebraMap (A := actualField)
    (⟨originalMap (MvPolynomial.X L) + B, hz⟩ : lowerGeneratorField L)
  exact triangular_transcendental L B hB (by
    simpa [Subfield.algebraMap_ofSubfield] using halg)

/-- The actual connected component supplies its own inverse and top bounds for the
protected-coordinate theorem. -/
theorem componentResponse_transcendental {n : ℕ} (P : Profile n) :
    Transcendental (lowerGeneratorField P.topVar) (componentResponse P) := by
  let := componentIntervalInverse P
  rw [componentResponse_eq_intervalResponse P]
  obtain ⟨hr, hc⟩ := componentInterval_endpoint_bounds P
  apply intervalResponse_transcendental _ _ _ _ _ _ hr hc
  rw [P.zeta_last, sub_zero]
  exact P.topVar_coe.symm

/-- With a genuine protected closure coordinate, a nonzero rational class inventory
cannot have zero inverse-response detector, even when all lower corrections depend on
the same original generators. -/
theorem protected_pole_detector_ne_zero (K : ℕ+) (A F : actualField)
    (hA : A ∈ lowerGeneratorField K) (hF : F ∈ lowerGeneratorField K) (hF0 : F ≠ 0)
    (s : Finset ℚ) (c : ℚ → ℚ) (hc : ∑ a ∈ s, c a ≠ 0) :
    ∑ a ∈ s, c a • (F * ((originalMap (MvPolynomial.X K) + A) / F -
      algebraMap ℚ actualField a))⁻¹ ≠ 0 := by
  have hx := triangular_quotient_transcendental K A F hA hF hF0
  have hxQ : Transcendental ℚ ((originalMap (MvPolynomial.X K) + A) / F) :=
    hx.restrictScalars (algebraMap ℚ (lowerGeneratorField K)).injective
  exact RationalPoles.scaled_pole_sum_ne_zero _ F hxQ hF0 s c hc

end SkewCornerDescent.Matrix
