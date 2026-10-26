/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BetaEndpointPolynomial

/-!
# Naturality of full beta endpoint polynomials

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A coefficient homomorphism transports the complete inverse whenever the source
matrix is invertible. No matrix entry or endpoint weight is discarded.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

variable {R S ν : Type*} [CommRing R] [CommRing S] [Fintype ν] [DecidableEq ν]

/-- A coefficient homomorphism transports the whole inverse of an invertible beta matrix. -/
theorem beta_inverse_map (φ : Lambda →+* R) (f : R →+* S) (row col : ν → ℤ)
    [Invertible (vertexBetaMatrix φ row col)] :
    ((vertexBetaMatrix φ row col)⁻¹).map f =
      (vertexBetaMatrix (f.comp φ) row col)⁻¹ := by
  let inv := Invertible.map f.mapMatrix (vertexBetaMatrix φ row col)
  let := inv
  have h := map_invOf f.mapMatrix (vertexBetaMatrix φ row col)
  let inv' := inv
  change Invertible ((vertexBetaMatrix φ row col).map f) at inv'
  let := inv'
  change (⅟(vertexBetaMatrix φ row col)).map f =
    ⅟((vertexBetaMatrix φ row col).map f) at h
  simp only [Matrix.invOf_eq_nonsing_inv] at h
  have hm : (vertexBetaMatrix φ row col).map f =
      vertexBetaMatrix (f.comp φ) row col := by
    ext i j : 1
    rfl
  rw [hm] at h
  exact h

/-- The full incoming polynomial commutes with a coefficient homomorphism. -/
theorem betaEndpointLeftPolynomial_map (φ : Lambda →+* R) (f : R →+* S)
    (row col : ν → ℤ) (x : ℤ) [Invertible (vertexBetaMatrix φ row col)] :
    (betaEndpointLeftPolynomial φ row col x).map f =
      betaEndpointLeftPolynomial (f.comp φ) row col x := by
  have hi := beta_inverse_map φ f row col
  unfold betaEndpointLeftPolynomial ordinaryEndpointProfile
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_sum,
    Polynomial.map_monomial]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change f (∑ j, φ (hh (x - col j)) * (vertexBetaMatrix φ row col)⁻¹ j i) =
    ∑ j, f (φ (hh (x - col j))) * (vertexBetaMatrix (f.comp φ) row col)⁻¹ j i
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  exact congrArg (fun z : S => f (φ (hh (x - col j))) * z)
    (congrFun (congrFun hi j) i)

/-- The full outgoing polynomial commutes with the same coefficient homomorphism. -/
theorem betaEndpointRightPolynomial_map (φ : Lambda →+* R) (f : R →+* S)
    (row col : ν → ℤ) (y : ℤ) [Invertible (vertexBetaMatrix φ row col)] :
    (betaEndpointRightPolynomial φ row col y).map f =
      betaEndpointRightPolynomial (f.comp φ) row col y := by
  have hi := beta_inverse_map φ f row col
  unfold betaEndpointRightPolynomial ordinaryEndpointProfile
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_sum,
    Polynomial.map_monomial]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change f (∑ j, (vertexBetaMatrix φ row col)⁻¹ i j * φ (hh (row j - y))) =
    ∑ j, (vertexBetaMatrix (f.comp φ) row col)⁻¹ i j * f (φ (hh (row j - y)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  exact congrArg (fun z : S => z * f (φ (hh (row j - y))))
    (congrFun (congrFun hi i) j)

end SkewCornerDescent.Matrix
