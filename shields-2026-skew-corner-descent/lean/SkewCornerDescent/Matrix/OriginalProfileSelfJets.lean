/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelfProfileJets

/-!
# Produced self-product jets for actual equal-response families

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original equal responses and aligned heights supply every common low
self-product jet through the first incoming-profile discrepancy.
The resolving generator is proved above the selected span. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal actual residue responses and aligned original heights supply the
complete common self-product jets for a whole profile family. -/
theorem original_self_profile_family_jets {n : ℕ} {ι : Type*}
    (P : Profile n) (b d : ι → Option (OriginalSelectedBlocks (hD := hD) P))
    (i₀ : ι) (K w : ℕ) (hhigh : (c.top : ℕ) + w < K)
    (hK : ∀ i, P.xi (originalRowSplitEquiv (hD := hD) P (.inl (b i))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (d i))) = (K : ℤ))
    (hS : ∀ i, c.regularResidue (c.originalLocalResponse P (b i) (d i)) =
      c.regularResidue (c.originalLocalResponse P (b i₀) (d i₀))) :
    ∀ i k, k ≤ w →
      (c.originalResidueLeftEndpointPolynomial P (b i) (d i) *
        c.originalResidueRightEndpointPolynomial P (b i) (d i)).coeff k =
      (c.originalResidueLeftEndpointPolynomial P (b i₀) (d i₀) *
        c.originalResidueRightEndpointPolynomial P (b i₀) (d i₀)).coeff k := by
  intro i k hk
  let j : ℕ+ := ⟨K - k, by omega⟩
  have hj : c.top < j := by
    change (c.top : ℕ) < K - k
    omega
  have hkP : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (b i))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (d i))) - (j : ℤ) = (k : ℤ) := by
    rw [hK]
    change (K : ℤ) - ((K - k : ℕ) : ℤ) = (k : ℤ)
    omega
  have hkQ : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (b i₀))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (d i₀))) - (j : ℤ) = (k : ℤ) := by
    rw [hK]
    change (K : ℤ) - ((K - k : ℕ) : ℤ) = (k : ℤ)
    omega
  exact c.original_self_profile_coeff_eq_of_residue_eq P P
    (b i) (d i) (b i₀) (d i₀) j hj k hkP hkQ (hS i)

end SkewCornerDescent.Matrix.SelectedCoordinate
