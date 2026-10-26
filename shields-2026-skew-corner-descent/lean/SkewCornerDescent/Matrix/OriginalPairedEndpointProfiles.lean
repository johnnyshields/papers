/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles
import SkewCornerDescent.Matrix.BetaEndpointPolynomial

/-!
# Full endpoint profiles under a complete original paired copy

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`,
`prop:normal-interface`.  A whole actual interval equivalence transports
both complete endpoint polynomials, preserving every inverse weight and
original exponent, not merely visible coefficients or their scalar product.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A complete original paired endpoint copy transports both full endpoint
polynomials, not only their visible jets or their scalar product. -/
theorem original_interval_endpoint_polynomials_of_copy {n m : ℕ} (P : Profile n) (Q : Profile m)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (a' b' : OriginalSelectedBlocks (hD := hD) Q) (shift : ℤ)
    (e : OriginalResponseInterval (hD := hD) P (some a) (some b) ≃
      OriginalResponseInterval (hD := hD) Q (some a') (some b'))
    (he : ∀ p, originalResponseRows Q (e p).1.1 = originalResponseRows P p.1.1 + shift ∧
      originalResponseCols Q (e p).1.1 = originalResponseCols P p.1.1 + shift)
    (hx : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) + shift)
    (hy : Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) =
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) + shift) :
    c.originalResidueLeftEndpointPolynomial P (some a) (some b) =
        c.originalResidueLeftEndpointPolynomial Q (some a') (some b') ∧
      c.originalResidueRightEndpointPolynomial P (some a) (some b) =
        c.originalResidueRightEndpointPolynomial Q (some a') (some b') := by
  classical
  let rowP := fun p : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
    originalResponseRows P p.1.1
  let colP := fun p : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
    originalResponseCols P p.1.1
  let rowQ := fun q : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
    originalResponseRows Q q.1.1
  let colQ := fun q : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
    originalResponseCols Q q.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  change x' = x + shift at hx
  change y' = y + shift at hy
  have hr : rowQ = fun q => rowP (e.symm q) + shift := by
    funext q
    simpa only [rowP, rowQ, Equiv.apply_symm_apply] using (he (e.symm q)).1
  have hc : colQ = fun q => colP (e.symm q) + shift := by
    funext q
    simpa only [colP, colQ, Equiv.apply_symm_apply] using (he (e.symm q)).2
  have hL : betaEndpointLeftPolynomial c.residueMap rowQ colQ x' =
      betaEndpointLeftPolynomial c.residueMap rowP colP x := by
    rw [hr, hc, hx]
    exact (betaEndpointLeftPolynomial_translate c.residueMap
      (rowP ∘ e.symm) (colP ∘ e.symm) x shift).trans
      (betaEndpointLeftPolynomial_equiv c.residueMap rowP colP x e.symm)
  have hR : betaEndpointRightPolynomial c.residueMap rowQ colQ y' =
      betaEndpointRightPolynomial c.residueMap rowP colP y := by
    rw [hr, hc, hy]
    exact (betaEndpointRightPolynomial_translate c.residueMap
      (rowP ∘ e.symm) (colP ∘ e.symm) y shift).trans
      (betaEndpointRightPolynomial_equiv c.residueMap rowP colP y e.symm)
  let := c.originalResponseResidueIntervalInverse P (some a) (some b)
  let := c.originalResponseResidueIntervalInverse Q (some a') (some b')
  constructor
  · simpa only [originalResidueLeftEndpointPolynomial, residueIntervalLeftPolynomial,
      betaEndpointLeftPolynomial, Matrix.invOf_eq_nonsing_inv, rowP, colP, rowQ, colQ, x, x']
      using hL.symm
  · simpa only [originalResidueRightEndpointPolynomial, residueIntervalRightPolynomial,
      betaEndpointRightPolynomial, Matrix.invOf_eq_nonsing_inv, rowP, colP, rowQ, colQ, y, y']
      using hR.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
