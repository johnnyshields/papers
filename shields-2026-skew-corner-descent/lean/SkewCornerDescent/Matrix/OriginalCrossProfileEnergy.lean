/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProfileSelfJets
import SkewCornerDescent.DirectedCrossProfileEnergy

/-!
# Directed energy from complete original endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual equal response functions produce the self-product jets. The full
endpoint polynomials are then coerced to profile series for the directed
energy calculation; these are not normal-parameter germs. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal actual responses and aligned heights produce the complete self-product
jets used by directed energy, rather than assuming those jets as extra data. -/
theorem original_cross_profile_energy {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Profile n)
    (b d : ι → Option (OriginalSelectedBlocks (hD := hD) P))
    (σ : Equiv.Perm ι) (i₀ : ι) (K w : ℕ) (hw : 0 < w)
    (hhigh : (c.top : ℕ) + w < K)
    (hK : ∀ i, P.xi (originalRowSplitEquiv (hD := hD) P (.inl (b i))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (d i))) = (K : ℤ))
    (hS : ∀ i, c.regularResidue (c.originalLocalResponse P (b i) (d i)) =
      c.regularResidue (c.originalLocalResponse P (b i₀) (d i₀)))
    (hmatch : ∀ i k, k < w →
      (c.originalResidueLeftEndpointPolynomial P (b i) (d i)).coeff k =
      (c.originalResidueLeftEndpointPolynomial P (b (σ i)) (d (σ i))).coeff k) :
    ∑ i, (c.originalResidueLeftEndpointPolynomial P (b i) (d i) *
      c.originalResidueRightEndpointPolynomial P (b (σ i)) (d (σ i)) -
      c.originalResidueLeftEndpointPolynomial P (b i) (d i) *
      c.originalResidueRightEndpointPolynomial P (b i) (d i)).coeff (2 * w) =
      (1/2 : OtherField c.top) * ∑ i,
        ((c.originalResidueLeftEndpointPolynomial P (b i) (d i)).coeff w -
          (c.originalResidueLeftEndpointPolynomial P (b (σ i)) (d (σ i))).coeff w)^2 := by
  let f := fun i => c.originalResidueLeftEndpointPolynomial P (b i) (d i)
  let g := fun i => c.originalResidueRightEndpointPolynomial P (b i) (d i)
  have hself : ∀ i k, k ≤ w → (f i * g i).coeff k = (f i₀ * g i₀).coeff k :=
    c.original_self_profile_family_jets P b d i₀ K w hhigh hK hS
  have hf0 : ∀ i, PowerSeries.constantCoeff (f i : PowerSeries (OtherField c.top)) = 1 := by
    intro i
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using
      c.originalResidueLeftEndpointPolynomial_coeff_zero P (b i) (d i)
  have hg0 : PowerSeries.constantCoeff (g i₀ : PowerSeries (OtherField c.top)) = 1 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using
      c.originalResidueRightEndpointPolynomial_coeff_zero P (b i₀) (d i₀)
  have he := directed_cross_profile_energy
    (fun i => (f i : PowerSeries (OtherField c.top)))
    (fun i => (g i : PowerSeries (OtherField c.top))) σ w hw
    ((f i₀ * g i₀ : Polynomial (OtherField c.top)) : PowerSeries (OtherField c.top))
    (by rw [Polynomial.coe_mul, map_mul, hf0, hg0, one_mul]) hf0
    (by simpa only [Polynomial.coeff_coe] using hmatch)
    (by simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using hself)
  simpa only [f, g, ← Polynomial.coe_mul, ← Polynomial.coe_sub, Polynomial.coeff_coe] using he

/-- Complete actual cross-minus-self profile coefficients vanish below twice
the first incoming-profile discrepancy. Every common self jet is produced
from actual equal responses; no weighted cancellation is an input. -/
theorem original_cross_profile_sum_low {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Profile n) (b d : ι → Option (OriginalSelectedBlocks (hD := hD) P))
    (σ : Equiv.Perm ι) (i₀ : ι) (K w : ℕ) (hw : 0 < w)
    (hhigh : (c.top : ℕ) + w < K)
    (hK : ∀ i, P.xi (originalRowSplitEquiv (hD := hD) P (.inl (b i))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (d i))) = (K : ℤ))
    (hS : ∀ i, c.regularResidue (c.originalLocalResponse P (b i) (d i)) =
      c.regularResidue (c.originalLocalResponse P (b i₀) (d i₀)))
    (hmatch : ∀ i k, k < w →
      (c.originalResidueLeftEndpointPolynomial P (b i) (d i)).coeff k =
      (c.originalResidueLeftEndpointPolynomial P (b (σ i)) (d (σ i))).coeff k)
    (k : ℕ) (hk : k < 2 * w) :
    ∑ i, (c.originalResidueLeftEndpointPolynomial P (b i) (d i) *
      c.originalResidueRightEndpointPolynomial P (b (σ i)) (d (σ i)) -
      c.originalResidueLeftEndpointPolynomial P (b i) (d i) *
      c.originalResidueRightEndpointPolynomial P (b i) (d i)).coeff k = 0 := by
  let f := fun i => c.originalResidueLeftEndpointPolynomial P (b i) (d i)
  let g := fun i => c.originalResidueRightEndpointPolynomial P (b i) (d i)
  have hself : ∀ i l, l ≤ w → (f i * g i).coeff l = (f i₀ * g i₀).coeff l :=
    c.original_self_profile_family_jets P b d i₀ K w hhigh hK hS
  have hf0 : ∀ i, PowerSeries.constantCoeff (f i : PowerSeries (OtherField c.top)) = 1 := by
    intro i
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using
      c.originalResidueLeftEndpointPolynomial_coeff_zero P (b i) (d i)
  have he := directed_cross_profile_sum_low
    (fun i => (f i : PowerSeries (OtherField c.top)))
    (fun i => (g i : PowerSeries (OtherField c.top))) σ w hw
    ((f i₀ * g i₀ : Polynomial (OtherField c.top)) : PowerSeries (OtherField c.top)) hf0
    (by simpa only [Polynomial.coeff_coe] using hmatch)
    (by simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using hself) k hk
  simpa only [f, g, ← Polynomial.coe_mul, ← Polynomial.coe_sub, Polynomial.coeff_coe] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
