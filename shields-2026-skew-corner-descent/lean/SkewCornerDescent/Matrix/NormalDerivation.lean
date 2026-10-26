/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.EndpointProfiles

/-!
# Normal and fixed-normal derivations in the original field

Supports local algebraic steps in `shields-2026-skew-corner-descent.tex`, «From response
functions to literal copies» (`sec:one-active`).

The chain-rule part of `lem:profile-derivative` for an affine original coordinate
`a * h_N + c`, with `a,c` independent of `h_N` and `a ≠ 0`. All derivations remain on
`FractionRing SkewGluing.Lambda`. The normal derivation sends this coordinate to one;
the fixed-normal lower derivations annihilate it and retain their original lower-generator
values. Thus neither the original derivative nor the normal-dependent inverse is replaced
by a scalar surrogate.

Producing `a,c` from the selected characteristic-independent cofactor, and identifying
this coordinate with the selected prime, are separate obligations. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- An affine coordinate in an original complete-homogeneous generator. -/
noncomputable def affineCoordinate (N : ℕ+) (a c : Lambda) : Lambda :=
  a * MvPolynomial.X N + c

/-- The normal derivation of the actual rational field for an affine coordinate. -/
noncomputable def normalDeriv (N : ℕ+) (a : Lambda) : Derivation ℚ actualField actualField :=
  (originalMap a)⁻¹ • generatorDeriv N

/-- The original lower derivative adjusted to hold the affine normal coordinate fixed. -/
noncomputable def fixedNormalDeriv (N j : ℕ+) (a c : Lambda) :
    Derivation ℚ actualField actualField :=
  generatorDeriv j - generatorDeriv j (originalMap (affineCoordinate N a c)) •
    normalDeriv N a

/-- Independence from `h_N` proves the normal-coordinate derivative, rather than assuming it. -/
theorem generatorDeriv_affineCoordinate (N : ℕ+) (a c : Lambda)
    (ha : N ∉ a.vars) (hc : N ∉ c.vars) :
    generatorDeriv N (originalMap (affineCoordinate N a c)) = originalMap a := by
  rw [generatorDeriv_originalMap]
  simp [affineCoordinate, MvPolynomial.pderiv_eq_zero_of_notMem_vars ha,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hc]

/-- The genuine normal derivative of the original affine coordinate is one. -/
theorem normalDeriv_affineCoordinate (N : ℕ+) (a c : Lambda) (ha0 : a ≠ 0)
    (ha : N ∉ a.vars) (hc : N ∉ c.vars) :
    normalDeriv N a (originalMap (affineCoordinate N a c)) = 1 := by
  have hmap : originalMap a ≠ 0 := by simpa using ha0
  simp [normalDeriv, generatorDeriv_affineCoordinate N a c ha hc, hmap]

/-- Fixed-normal lower derivations actually annihilate the original affine coordinate. -/
theorem fixedNormalDeriv_affineCoordinate (N j : ℕ+) (a c : Lambda) (ha0 : a ≠ 0)
    (ha : N ∉ a.vars) (hc : N ∉ c.vars) :
    fixedNormalDeriv N j a c (originalMap (affineCoordinate N a c)) = 0 := by
  simp [fixedNormalDeriv, normalDeriv_affineCoordinate N a c ha0 ha hc]

/-- Normal differentiation fixes each distinct original lower generator. -/
theorem normalDeriv_X_of_ne (N j : ℕ+) (a : Lambda) (hj : j ≠ N) :
    normalDeriv N a (originalMap (MvPolynomial.X j)) = 0 := by
  simp [normalDeriv, hj]

/-- The fixed-normal lower derivatives keep the original lower-generator coordinate values. -/
theorem fixedNormalDeriv_X_of_ne (N j k : ℕ+) (a c : Lambda) (hk : k ≠ N) :
    fixedNormalDeriv N j a c (originalMap (MvPolynomial.X k)) =
      if k = j then 1 else 0 := by
  simp only [fixedNormalDeriv, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul,
    normalDeriv_X_of_ne N k a hk, mul_zero, sub_zero]
  exact generatorDeriv_X j k

/-- The raw/chart correction is taken in the original rational field. -/
theorem generatorDeriv_eq_fixed_add_normal (N j : ℕ+) (a c : Lambda) (f : actualField) :
    generatorDeriv j f = fixedNormalDeriv N j a c f +
      generatorDeriv j (originalMap (affineCoordinate N a c)) * normalDeriv N a f := by
  simp [fixedNormalDeriv]

/-- The exact top-generator normal identity, without specializing away inverse entries. -/
theorem mul_normalDeriv (N : ℕ+) (a : Lambda) (ha0 : a ≠ 0) (f : actualField) :
    originalMap a * normalDeriv N a f = generatorDeriv N f := by
  have hmap : originalMap a ≠ 0 := by simpa using ha0
  simp [normalDeriv, hmap]

/-- Full normal endpoint-profile identity, valid for the original complete removed matrix. -/
theorem normalDeriv_intervalResponse (N : ℕ+) (a : Lambda) (ha0 : a ≠ 0)
    {ν : Type*} [Fintype ν] [DecidableEq ν] (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] :
    originalMap a * normalDeriv N a (intervalResponse x y row col) =
      (leftEndpointProfile x row col * rightEndpointProfile y row col).coeff
        (x - y - (N : ℤ)) := by
  rw [mul_normalDeriv N a ha0, generatorDeriv_intervalResponse]

/-- Full fixed-normal lower endpoint-profile identity with its original affine correction. -/
theorem fixedNormalDeriv_intervalResponse (N j : ℕ+) (a c : Lambda)
    {ν : Type*} [Fintype ν] [DecidableEq ν] (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] :
    fixedNormalDeriv N j a c (intervalResponse x y row col) =
      (leftEndpointProfile x row col * rightEndpointProfile y row col).coeff
        (x - y - (j : ℤ)) -
        generatorDeriv j (originalMap (affineCoordinate N a c)) *
          normalDeriv N a (intervalResponse x y row col) := by
  change generatorDeriv j (intervalResponse x y row col) - _ = _
  rw [generatorDeriv_intervalResponse]
  simp

end SkewCornerDescent.Matrix
