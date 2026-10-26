-- TODO-COPIED: skew-cofactor-independence/lean/SkewCofactorIndependence/Base/MongeInitialCoefficients.lean
/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/MongeInitialCoefficients.lean
import SkewCofactorIndependence.Base.MongeMinors
import SkewCofactorIndependence.Base.GeneratorMonomials

/-!
# The unit coefficient of the increasing determinant term

The coefficient conclusion of `thm:monge-minor` in
«Strict-Monge geometry of cofactor actions» (`sec:geometry`) of
`shields-2026-skew-boundary-reconstruction.tex`.  Zero complete indices contribute
no variable to the exponent vector, but retain their unit factors.  Sorry-free.
-/

namespace SkewCofactorIndependence.Base

open scoped BigOperators

/-- Generator indices of the increasing matching, including zero indices. -/
def increasingIndexList {n : ℕ} (A d : Fin n → ℤ) : List ℕ :=
  List.ofFn fun i => (d i - A i).toNat

/-- The increasing product is one monomial with coefficient one. -/
theorem increasing_product_eq_monomial {n : ℕ} (A d : Fin n → ℤ)
    (hf : ∀ i, A i ≤ d i) :
    (∏ i, complete (d i - A i)) =
      MvPolynomial.monomial (exponentVector (increasingIndexList A d)) 1 := by
  have hx : ∀ i, ((d i - A i).toNat : ℤ) = d i - A i := by
    intro i
    have h := hf i
    omega
  calc
    (∏ i, complete (d i - A i)) =
        ((increasingIndexList A d).map (fun k : ℕ => complete (k : ℤ))).prod := by
      simp only [increasingIndexList, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
      apply Finset.prod_congr rfl
      intro i _
      rw [hx i]
    _ = _ := prod_complete_eq_monomial _

/-- The initial polynomial has precisely the unit coefficient asserted in `thm:monge-minor`. -/
theorem monge_minor_initial_coefficient (w : ConvexWeight) {n : ℕ} (A d : Fin n → ℤ)
    (hA : StrictMono A) (hd : StrictMono d) (hf : ∀ i, A i ≤ d i) :
    (initialForm w.generatorWeight (staircaseMatrix A d).det).coeff
      (exponentVector (increasingIndexList A d)) = 1 := by
  rw [monge_minor_initialForm w hA hd hf, increasing_product_eq_monomial A d hf]
  simp

end SkewCofactorIndependence.Base
