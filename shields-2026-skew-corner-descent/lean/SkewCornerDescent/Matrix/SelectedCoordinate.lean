/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalDerivation
import SkewGluing.CofactorAssembly

/-!
# Affine normal coordinates produced by connected diagrams

Formalizes the selected-prime coordinate used in `shields-2026-skew-corner-descent.tex`,
«Equal windows and the determinant defect» (`sec:normal-chart`) and the chain rule in
«From response functions to literal copies» (`sec:one-active`, `lem:profile-derivative`).
The coefficient and lower remainder are produced from the actual corner expansion,
not assumed as analytic input. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- Data of an actual connected prime expressed in its geometric top generator. -/
structure SelectedCoordinate (D : Diagram) (hD : IsConnectedSkew D) where
  top : ℕ+
  span_eq : (top : ℕ) = span D
  coefficient : Lambda
  remainder : Lambda
  coefficient_ne_zero : coefficient ≠ 0
  coefficient_lower : coefficient ∈ supported ℚ {j : ℕ+ | j < top}
  remainder_lower : remainder ∈ supported ℚ {j : ℕ+ | j < top}
  prime_eq : cellSchur D hD.1 = affineCoordinate top coefficient remainder

/-- A connected diagram supplies a genuine affine normal coordinate with a nonzero lower top
cofactor. No assumption about a producer is left in the interface. -/
theorem exists_selectedCoordinate {D : Diagram} (hD : IsConnectedSkew D) :
    Nonempty (SelectedCoordinate D hD) := by
  obtain ⟨n, P, v, hp⟩ := hD.exists_profile_cells
  obtain ⟨R, hR, he⟩ := P.schur_corner_integralRemainder
  let a : Lambda := (-1) ^ n *
    cellSchur (diagramInterior P.cells) P.isSkew_cells.interior
  have ha : a ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero n (by simp))
    rw [← P.minorDet_eq_interiorSchur]
    exact P.minor_ne_zero
  have haL : a ∈ supported ℚ {j : ℕ+ | j < P.topVar} := by
    apply Subalgebra.mul_mem
    · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) n
    · rw [← map_integralCellSchur]
      apply mem_supported.mpr
      intro j hj
      exact (mem_supported.mp P.integralInterior_mem_below) (vars_map _ _ hj)
  have hRL : map (Int.castRingHom ℚ) R ∈ supported ℚ {j : ℕ+ | j < P.topVar} := by
    apply mem_supported.mpr
    intro j hj
    exact (mem_supported.mp hR) (vars_map _ _ hj)
  refine ⟨⟨P.topVar, ?_, a, map (Int.castRingHom ℚ) R, ha, haL, hRL, ?_⟩⟩
  · rw [hp, span_translate, P.span_cells_eq_topVar]
  · rw [cellSchur_eq_profile hD P v hp, he]
    simp only [affineCoordinate, a]
    ring

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The selected coordinate is the actual connected prime, not a surrogate polynomial. -/
theorem irreducible : Irreducible (affineCoordinate c.top c.coefficient c.remainder) := by
  rw [← c.prime_eq]
  exact irreducible_cellSchur hD

/-- The actual selected coefficient omits its top generator. -/
theorem top_notMem_coefficient : c.top ∉ c.coefficient.vars := by
  intro h
  exact (lt_irrefl c.top) ((mem_supported.mp c.coefficient_lower) h)

/-- The actual selected remainder omits its top generator. -/
theorem top_notMem_remainder : c.top ∉ c.remainder.vars := by
  intro h
  exact (lt_irrefl c.top) ((mem_supported.mp c.remainder_lower) h)

/-- Every nonzero lower polynomial is regular at the actual selected prime divisor. -/
theorem not_dvd_lower {f : Lambda} (hf : f ≠ 0)
    (hl : f ∈ supported ℚ {j : ℕ+ | j < c.top}) :
    ¬ cellSchur D hD.1 ∣ f := by
  intro hd
  have hbound := polynomialSpan_le_of_dvd hf hd
  rw [polynomialSpan_cellSchur hD, ← c.span_eq] at hbound
  have hlow : polynomialSpan f ≤ (c.top : ℕ) - 1 := by
    apply Finset.sup_le
    intro j hj
    have hlt := mem_supported.mp hl hj
    change (j : ℕ) < (c.top : ℕ) at hlt
    omega
  have hp := c.top.pos
  omega

/-- The nonzero top cofactor is a unit at the selected divisor, not just in the generic field. -/
theorem not_dvd_coefficient : ¬ cellSchur D hD.1 ∣ c.coefficient :=
  c.not_dvd_lower c.coefficient_ne_zero c.coefficient_lower

/-- The normal derivation of the actual selected prime is one. -/
theorem normalDeriv_prime :
    normalDeriv c.top c.coefficient (originalMap (cellSchur D hD.1)) = 1 := by
  rw [c.prime_eq]
  exact normalDeriv_affineCoordinate _ _ _ c.coefficient_ne_zero
    c.top_notMem_coefficient c.top_notMem_remainder

/-- Lower chart derivatives hold the actual selected prime fixed. -/
theorem fixedNormalDeriv_prime (j : ℕ+) :
    fixedNormalDeriv c.top j c.coefficient c.remainder
      (originalMap (cellSchur D hD.1)) = 0 := by
  rw [c.prime_eq]
  exact fixedNormalDeriv_affineCoordinate _ _ _ _ c.coefficient_ne_zero
    c.top_notMem_coefficient c.top_notMem_remainder

/-- The complete endpoint derivative identities with the actual selected prime. Both derivatives
retain every entry of the original removed inverse. -/
theorem interval_derivative_identities {ν : Type*} [Fintype ν] [DecidableEq ν]
    (x y : ℤ) (row col : ν → ℤ) [Invertible (intervalMatrix row col)] (j : ℕ+) :
    generatorDeriv j (intervalResponse x y row col) =
        (leftEndpointProfile x row col * rightEndpointProfile y row col).coeff
          (x - y - (j : ℤ)) ∧
      originalMap c.coefficient * normalDeriv c.top c.coefficient
          (intervalResponse x y row col) =
        (leftEndpointProfile x row col * rightEndpointProfile y row col).coeff
          (x - y - (c.top : ℤ)) ∧
      generatorDeriv j (intervalResponse x y row col) =
        fixedNormalDeriv c.top j c.coefficient c.remainder (intervalResponse x y row col) +
          normalDeriv c.top c.coefficient (intervalResponse x y row col) *
            generatorDeriv j (originalMap (cellSchur D hD.1)) := by
  refine ⟨generatorDeriv_intervalResponse x y row col j,
    normalDeriv_intervalResponse _ _ c.coefficient_ne_zero x y row col, ?_⟩
  rw [c.prime_eq]
  simpa only [mul_comm] using
    generatorDeriv_eq_fixed_add_normal c.top j c.coefficient c.remainder
      (intervalResponse x y row col)

end SelectedCoordinate
end SkewCornerDescent.Matrix
