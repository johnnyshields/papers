/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResiduePolynomialBand
import SkewCornerDescent.TriangularPrimes
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Faithful higher-coordinate polynomial presentation of the actual residue

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`).

The coefficient field is the actual strict lower residue field. Its surviving higher
original generators are algebraically independent over that field, so polynomial
responses are represented injectively without introducing independent response variables.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

noncomputable local instance higherResidueRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Original higher indices surviving the selected prime relation. -/
abbrev ResidueHigherIndex (N : ℕ+) := {j : ℕ+ // N < j}

/-- Polynomial higher coordinates over the complete actual lower rational field. -/
abbrev ResidueHigherPolynomial (N : ℕ+) :=
  MvPolynomial (ResidueHigherIndex N) (residueLowerField N N)

/-- The higher coordinates retain algebraic independence after adjoining all lower fractions. -/
theorem residue_higher_generators_independent (N : ℕ+) :
    AlgebraicIndependent (residueLowerField N N)
      (fun j : ResidueHigherIndex N => residueGenerator N ⟨j.val, ne_of_gt j.prop⟩) := by
  let s : Set {j : ℕ+ // j ≠ N} := {j | j.val < N}
  let t : Set {j : ℕ+ // j ≠ N} := {j | N < j.val}
  have hdis : Disjoint s t := by
    rw [Set.disjoint_left]
    intro j hs ht
    change j.val < N at hs
    change N < j.val at ht
    exact lt_asymm hs ht
  have h := (residue_generators_independent N).adjoin_of_disjoint hdis
  have h' := IntermediateField.algebraicIndependent_adjoin_iff.mpr h
  let f : ResidueHigherIndex N → t := fun j => ⟨⟨j.val, ne_of_gt j.prop⟩, j.prop⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun z : t => z.val.val) hij
  exact h'.comp f hf

/-- Evaluation into the unchanged original residue field, not into a surrogate chart. -/
noncomputable def residueHigherEval (N : ℕ+) :
    ResidueHigherPolynomial N →ₐ[residueLowerField N N] OtherField N :=
  MvPolynomial.aeval (fun j => residueGenerator N ⟨j.val, ne_of_gt j.prop⟩)

/-- Higher-coordinate polynomial equality is faithful to the actual residue field. -/
theorem residueHigherEval_injective (N : ℕ+) : Function.Injective (residueHigherEval N) :=
  residue_higher_generators_independent N

/-- Every actual polynomial-band element has a higher-coordinate representative below its top. -/
theorem residuePolynomialBand_representative (N K : ℕ+) {A : OtherField N}
    (hA : A ∈ residuePolynomialBand N K) :
    ∃ p : ResidueHigherPolynomial N,
      (∀ j ∈ p.vars, j.val < K) ∧ residueHigherEval N p = A := by
  classical
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    rcases hA with hlow | ⟨j, hjN, hjK, rfl⟩
    · refine ⟨C ⟨A, hlow⟩, ?_, ?_⟩
      · intro j hj
        simp only [vars_C, Finset.notMem_empty] at hj
      · simp only [residueHigherEval, aeval_C, Subfield.algebraMap_ofSubfield]
        rfl
    · let j' : ResidueHigherIndex N := ⟨j.val, hjN⟩
      refine ⟨X j', ?_, ?_⟩
      · intro i hi
        rw [vars_X, Finset.mem_singleton] at hi
        subst i
        exact hjK
      · simp only [residueHigherEval, aeval_X]
        rfl
  | algebraMap q =>
    refine ⟨C ⟨(q : OtherField N), SubfieldClass.ratCast_mem _ q⟩, ?_, ?_⟩
    · intro j hj
      simp only [vars_C, Finset.notMem_empty] at hj
    · simp only [residueHigherEval, aeval_C, Subfield.algebraMap_ofSubfield]
      exact (map_ratCast (algebraMap ℚ (OtherField N)) q).symm
  | add A B _ _ hA hB =>
    obtain ⟨p, hp, he⟩ := hA
    obtain ⟨q, hq, hf⟩ := hB
    refine ⟨p + q, ?_, by rw [map_add, he, hf]⟩
    intro j hj
    rcases Finset.mem_union.mp (vars_add_subset p q hj) with hj | hj
    · exact hp j hj
    · exact hq j hj
  | mul A B _ _ hA hB =>
    obtain ⟨p, hp, he⟩ := hA
    obtain ⟨q, hq, hf⟩ := hB
    refine ⟨p * q, ?_, by rw [map_mul, he, hf]⟩
    intro j hj
    rcases Finset.mem_union.mp (vars_mul p q hj) with hj | hj
    · exact hp j hj
    · exact hq j hj

end SkewCornerDescent.Matrix
