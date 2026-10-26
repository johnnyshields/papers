/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueHigherPolynomial

/-!
# Actual retained responses as prime polynomial classes

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`).

Primeness is in the actual polynomial algebra of surviving higher generators over the
lower residue field, not in its fraction field. Complete original endpoint elimination
produces each correction and its support; the injective polynomial presentation transports
the resulting prime back to that algebra.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

noncomputable local instance actualPrimeRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- The actual polynomial algebra inside the unchanged residue field. -/
noncomputable def actualResiduePolynomialAlgebra (N : ℕ+) :
    Subalgebra (residueLowerField N N) (OtherField N) := (residueHigherEval N).range

/-- The faithful polynomial presentation, restricted to its actual algebraic range. -/
noncomputable def actualResiduePolynomialEquiv (N : ℕ+) :
    ResidueHigherPolynomial N ≃ₐ[residueLowerField N N] actualResiduePolynomialAlgebra N :=
  AlgEquiv.ofInjective (residueHigherEval N) (residueHigherEval_injective N)

/-- A complete original retained response has a produced prime representative at its literal top. -/
theorem residue_monic_prime (N K : ℕ+) (hNK : N < K) {A : OtherField N}
    (hA : A ∈ residuePolynomialBand N K) :
    ∃ S : actualResiduePolynomialAlgebra N,
      (S : OtherField N) = residueGenerator N ⟨K, ne_of_gt hNK⟩ + A ∧ Prime S := by
  obtain ⟨p, hp, he⟩ := residuePolynomialBand_representative N K hA
  let j : ResidueHigherIndex N := ⟨K, hNK⟩
  have hsupport : ∀ i ∈ p.vars, i < j := hp
  let e := actualResiduePolynomialEquiv N
  refine ⟨e (X j + p), ?_, ?_⟩
  · change residueHigherEval N (X j + p) = _
    rw [map_add, he]
    simp only [residueHigherEval, aeval_X]
    rfl
  · exact (MulEquiv.prime_iff e).mpr (monicTriangularPolynomial_prime hsupport)

/-- Monic associates in the actual polynomial algebra have equal tops and full corrections. -/
theorem actualResidue_monic_associated_iff (N : ℕ+)
    {a b : ResidueHigherPolynomial N} {K J : ResidueHigherIndex N}
    (ha : ∀ i ∈ a.vars, i < K) (hb : ∀ i ∈ b.vars, i < J) :
    Associated (actualResiduePolynomialEquiv N (X K + a))
      (actualResiduePolynomialEquiv N (X J + b)) ↔ K = J ∧ a = b := by
  constructor
  · intro h
    have hp := Associated.map (actualResiduePolynomialEquiv N).symm h
    simp only [AlgEquiv.symm_apply_apply] at hp
    exact (monicTriangularPolynomial_associated_iff ha hb).mp hp
  · rintro ⟨rfl, rfl⟩
    exact Associated.refl _

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Primeness of the full actual retained residue, with no response-correction binder. -/
theorem originalLocalResponse_residue_prime {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ S : actualResiduePolynomialAlgebra c.top,
      (S : OtherField c.top) = c.regularResidue (c.originalLocalResponse P b d) ∧ Prime S := by
  obtain ⟨A, hA, he⟩ := c.originalLocalResponse_residue_polynomial P b d K hNK hK hmax
  obtain ⟨S, hS, hprime⟩ := residue_monic_prime c.top K hNK hA
  refine ⟨S, ?_, hprime⟩
  rw [hS, he, c.residueMap_other K (ne_of_gt hNK)]
  rfl

end SelectedCoordinate
end SkewCornerDescent.Matrix
