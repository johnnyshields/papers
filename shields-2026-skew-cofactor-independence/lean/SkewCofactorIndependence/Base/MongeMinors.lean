/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/MongeMinors.lean
import SkewCofactorIndependence.Base.MongeAssignments
import SkewCofactorIndependence.Base.GeneratorProducts
import Vendor.AlgebraicCombinatorics.DeterminantsBasic

/-!
# Strict-Monge minors in the free complete-generator ring

Formalizes «Strict-Monge uncrossing» (`sec:geometry`, `thm:monge-minor`)
of `shields-2026-skew-boundary-reconstruction.tex`.  The assignment theorem produces
strict inequalities between all surviving permutation terms; polynomial initial forms
then show that the increasing term survives with its unit coefficient.  Sorry-free.
-/

namespace SkewCofactorIndependence.Base

open scoped BigOperators

variable {n : ℕ}

/-- A square Jacobi--Trudi staircase with explicit row and column coordinates. -/
noncomputable def staircaseMatrix (A d : Fin n → ℤ) : Matrix (Fin n) (Fin n) CompleteRing :=
  Matrix.of fun i j => complete (d j - A i)

/-- The actual signed polynomial term of a row-to-column permutation. -/
noncomputable def permutationTerm (A d : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : CompleteRing :=
  Equiv.Perm.sign σ • ∏ i, complete (d (σ i) - A i)

/-- The shared determinant convention is the manuscript's row-to-column expansion. -/
theorem staircase_det_expansion (A d : Fin n → ℤ) :
    (staircaseMatrix A d).det = ∑ σ, permutationTerm A d σ := by
  simpa only [staircaseMatrix, Matrix.of_apply, permutationTerm] using
    AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook (staircaseMatrix A d)

/-- Feasible signed terms are homogeneous at their matching cost. -/
theorem permutationTerm_homogeneous (w : ConvexWeight) (A d : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (hf : matchingFeasible A d σ) :
    MvPolynomial.IsWeightedHomogeneous w.generatorWeight (permutationTerm A d σ)
      (matchingCost w A d σ) := by
  have hprod := complete_prod_convex_homogeneous Finset.univ
    (fun i => d (σ i) - A i) w (fun i _ => sub_nonneg.mpr (hf i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [permutationTerm, hs, matchingCost] using hprod
  · simpa [permutationTerm, hs, matchingCost] using hprod.neg

/-- A feasible term is nonzero even when some matched complete index is zero. -/
theorem permutationTerm_ne_zero (A d : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (hf : matchingFeasible A d σ) : permutationTerm A d σ ≠ 0 := by
  have hprod := complete_prod_ne_zero Finset.univ (fun i => d (σ i) - A i)
    (fun i _ => sub_nonneg.mpr (hf i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [permutationTerm, hs] using hprod
  · simpa [permutationTerm, hs] using hprod

/-- A nonfeasible matching contributes exactly zero to the determinant expansion. -/
theorem permutationTerm_eq_zero (A d : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (hf : ¬ matchingFeasible A d σ) : permutationTerm A d σ = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hf
  have hz : complete (d (σ i) - A i) = 0 := complete_of_neg (by omega)
  unfold permutationTerm
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, smul_zero]

/-- Exact valuation of a surviving signed permutation term. -/
theorem permutationTerm_valuation (w : ConvexWeight) (A d : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (hf : matchingFeasible A d σ) :
    monomialValuation w.generatorWeight (permutationTerm A d σ) =
      (matchingCost w A d σ : WithTop ℝ) :=
  monomialValuation_eq_of_homogeneous (permutationTerm_ne_zero A d σ hf)
    (permutationTerm_homogeneous w A d σ hf)

/-- The full initial-form conclusion of `thm:monge-minor`. -/
theorem monge_minor_initialForm (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : ∀ i, A i ≤ d i) :
    initialForm w.generatorWeight (staircaseMatrix A d).det =
      ∏ i, complete (d i - A i) := by
  classical
  let e : Equiv.Perm (Fin n) := Equiv.refl _
  have he : matchingFeasible A d e := hf
  have hterm := permutationTerm_ne_zero A d e he
  have hmin : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), σ ≠ e →
      monomialValuation w.generatorWeight (permutationTerm A d e) <
        monomialValuation w.generatorWeight (permutationTerm A d σ) := by
    intro σ _ hσ
    rw [permutationTerm_valuation w A d e he]
    by_cases hfeas : matchingFeasible A d σ
    · rw [permutationTerm_valuation w A d σ hfeas]
      exact WithTop.coe_lt_coe.mpr (identity_cost_lt_matching w hA hd hfeas hσ)
    · rw [permutationTerm_eq_zero A d σ hfeas, monomialValuation_zero]
      exact WithTop.coe_lt_top _
  rw [staircase_det_expansion]
  rw [(initialForm_sum_unique Finset.univ (permutationTerm A d)
    (Finset.mem_univ e) hterm hmin).1]
  rw [initialForm_eq_of_homogeneous hterm (permutationTerm_homogeneous w A d e he)]
  simp [permutationTerm, e]

/-- The increasing determinant term cannot be cancelled by the higher terms. -/
theorem monge_minor_ne_zero (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : ∀ i, A i ≤ d i) :
    (staircaseMatrix A d).det ≠ 0 := by
  intro hz
  have hi := monge_minor_initialForm w hA hd hf
  rw [hz, initialForm_zero] at hi
  exact complete_prod_ne_zero Finset.univ (fun i => d i - A i)
    (fun i _ => sub_nonneg.mpr (hf i)) hi.symm

/-- If the increasing matching is not feasible, no permutation term survives. -/
theorem monge_minor_eq_zero_of_infeasible (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : ¬ ∀ i, A i ≤ d i) :
    (staircaseMatrix A d).det = 0 := by
  classical
  rw [staircase_det_expansion]
  apply Finset.sum_eq_zero
  intro σ _
  apply permutationTerm_eq_zero
  intro hσ
  exact hf ((matching_feasible_iff_identity w hA hd).mp ⟨σ, hσ⟩)

/-- Nonvanishing is exactly feasibility of the increasing matching. -/
theorem monge_minor_ne_zero_iff (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d) :
    (staircaseMatrix A d).det ≠ 0 ↔ ∀ i, A i ≤ d i := by
  constructor
  · intro h
    by_contra hf
    exact h (monge_minor_eq_zero_of_infeasible w hA hd hf)
  · exact monge_minor_ne_zero w hA hd

end SkewCofactorIndependence.Base
