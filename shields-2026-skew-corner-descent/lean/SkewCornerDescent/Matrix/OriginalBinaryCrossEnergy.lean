/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCrossProfileEnergy
import SkewCornerDescent.BinaryProfileEnergy

/-!
# Binary transition energy for complete original inverse profiles

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Equal actual response functions supply all needed self-product jets.
Baseline-normalized first differences then identify the complete directed
cross-minus-self coefficient with the actual binary transition count.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing BinaryTransitions
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The genuine complete original cross-minus-self coefficient equals one
half the squared produced amplitude times the cyclic transition count. -/
theorem original_cross_profile_binary_energy {n s : ℕ} [NeZero s]
    (P : Profile n)
    (b d : ZMod s → Option (OriginalSelectedBlocks (hD := hD) P))
    (i₀ : ZMod s) (K w : ℕ) (hw : 0 < w)
    (hhigh : (c.top : ℕ) + w < K)
    (hK : ∀ i, P.xi (originalRowSplitEquiv (hD := hD) P (.inl (b i))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (d i))) = (K : ℤ))
    (hS : ∀ i, c.regularResidue (c.originalLocalResponse P (b i) (d i)) =
      c.regularResidue (c.originalLocalResponse P (b i₀) (d i₀)))
    (hmatch : ∀ i k, k < w →
      (c.originalResidueLeftEndpointPolynomial P (b i) (d i)).coeff k =
      (c.originalResidueLeftEndpointPolynomial P (b (i + 1)) (d (i + 1))).coeff k)
    (η : OtherField c.top) (bits : ZMod s → Bool)
    (hbits : ∀ i, (c.originalResidueLeftEndpointPolynomial P (b i) (d i)).coeff w -
      (c.originalResidueLeftEndpointPolynomial P (b i₀) (d i₀)).coeff w =
        if bits i then η else 0) :
    ∑ i, (c.originalResidueLeftEndpointPolynomial P (b i) (d i) *
      c.originalResidueRightEndpointPolynomial P (b (i+1)) (d (i+1)) -
      c.originalResidueLeftEndpointPolynomial P (b i) (d i) *
      c.originalResidueRightEndpointPolynomial P (b i) (d i)).coeff (2*w) =
      (1/2 : OtherField c.top) * η^2 * (transitionCount bits 1 : OtherField c.top) := by
  have he := c.original_cross_profile_energy P b d (Equiv.addRight 1) i₀ K w hw
    hhigh hK hS hmatch
  have hb := binary_profile_square_sum
    (fun i => (c.originalResidueLeftEndpointPolynomial P (b i) (d i)).coeff w)
    ((c.originalResidueLeftEndpointPolynomial P (b i₀) (d i₀)).coeff w) η bits hbits
  simpa [mul_assoc] using
    he.trans (congrArg (fun x => (1/2 : OtherField c.top) * x) hb)

end SkewCornerDescent.Matrix.SelectedCoordinate
