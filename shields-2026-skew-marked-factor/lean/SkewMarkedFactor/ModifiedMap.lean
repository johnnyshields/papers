/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.WeightedJacobiTrudi
import SkewMarkedFactor.OrdinaryAction

/-!
# The modified composition algebra map

«The algebra map and the weighted operator» (`eq:algebra-map`) of
`shields-2026-skew-marked-factor.tex`.
`Ψ_η` is the algebra homomorphism of `Λ = ℚ[h₁, h₂, …]` with `Ψ_η(h_j) = A^{j-1} b_j`, where
`A = s_W` and `b_j` is the Schur function of the composite of a row of `j` cells.
Covariance of a derivation with `Ψ_η` is checked on generators.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The composite of a one-row outer of `j` cells. -/
def rowComposite (η : MarkedInner) (j : ℕ) : Diagram := η.compose (skewOf [j] [])

/-- The value `Ψ_η(h_j) = A^{j-1} b_j` on the `j`-th generator. -/
def modifiedGen (η : MarkedInner) (j : ℕ+) : Lambda :=
  normalizerRow η ^ ((j : ℕ) - 1) * cellSchur (rowComposite η j)

/-- **The modified composition algebra map** `Ψ_η` (`eq:algebra-map`), defined on the free
complete generators. -/
def compositionMap (η : MarkedInner) : Lambda →ₐ[ℚ] Lambda := aeval (modifiedGen η)

@[simp] theorem compositionMap_X (η : MarkedInner) (j : ℕ+) :
    compositionMap η (X j) = modifiedGen η j := aeval_X _ _

/-- Covariance on the generators `h_j` extends to the whole ring: if the derivations `D` and `E`
satisfy `D Ψ(h_j) = c Ψ(E h_j)` for every `j`, then `D Ψ(f) = c Ψ(E f)` for every `f`. -/
theorem intertwine_of_generators (Ψ : Lambda →ₐ[ℚ] Lambda) (D E : Derivation ℚ Lambda Lambda)
    (c : Lambda) (h : ∀ j : ℕ+, D (Ψ (X j)) = c * Ψ (E (X j))) (f : Lambda) :
    D (Ψ f) = c * Ψ (E f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Derivation.map_algebraMap,
      Derivation.map_algebraMap, map_zero, mul_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg, mul_add]
  | mul_X f j hf =>
    have e1 : D (Ψ (f * X j)) = Ψ f * D (Ψ (X j)) + Ψ (X j) * D (Ψ f) := by
      rw [map_mul, Derivation.leibniz]; simp only [smul_eq_mul]
    have e2 : E (f * X j) = f * E (X j) + X j * E f := by
      rw [Derivation.leibniz]; simp only [smul_eq_mul]
    rw [e1, e2, hf, h, map_add, map_mul, map_mul]
    ring

end SkewMarkedFactor
