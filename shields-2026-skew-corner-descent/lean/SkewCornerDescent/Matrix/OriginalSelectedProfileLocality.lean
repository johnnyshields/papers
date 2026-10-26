/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedPrefixProfiles
import SkewCornerDescent.Matrix.OriginalSelectedSuffixProfiles

/-!
# Full local endpoint products inside long original retained intervals

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete long inverse supplies the actual local cross-profile coefficient
through both local heights, including all selected boundary strips.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full local incoming and outgoing profiles determine every product coefficient
through both local heights. Their local intervals may overlap or be disjoint. -/
theorem original_selected_cross_profile_coeff {n : ℕ} (P : Profile n)
    (b d e t : OriginalSelectedBlocks (hD := hD) P)
    (hleft : b.val ≤ d.val ∧ d.val ≤ t.val)
    (hright : b.val ≤ e.val ∧ e.val ≤ t.val)
    (k : ℕ)
    (hkleft : (k : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))))
    (hkright : (k : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some e))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))) :
    (c.originalResidueLeftEndpointPolynomial P (some b) (some t) *
      c.originalResidueRightEndpointPolynomial P (some b) (some t)).coeff k =
    (c.originalResidueLeftEndpointPolynomial P (some b) (some d) *
      c.originalResidueRightEndpointPolynomial P (some e) (some t)).coeff k := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hpl : (p.1 : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) := by omega
  have hpr : (p.2 : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some e))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t))) := by omega
  rw [c.original_left_profile_selected_prefix_coeff P b d t hleft p.1 hpl,
    c.original_right_profile_selected_suffix_coeff P b e t hright p.2 hpr]

/-- A higher-generator derivative of the actual long residue response is the
coefficient of the complete local cross-profile product, not of proper cores alone. -/
theorem original_long_response_local_gradient {n : ℕ} (P : Profile n)
    (b d e t : OriginalSelectedBlocks (hD := hD) P)
    (hleft : b.val ≤ d.val ∧ d.val ≤ t.val)
    (hright : b.val ≤ e.val ∧ e.val ≤ t.val)
    (H : ℕ+) (hH : c.top < H) (k : ℕ)
    (hdegree : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t))) - (H : ℤ) = (k : ℤ))
    (hkleft : (k : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))))
    (hkright : (k : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some e))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.regularResidue (c.originalLocalResponse P (some b) (some t))) =
    (c.originalResidueLeftEndpointPolynomial P (some b) (some d) *
      c.originalResidueRightEndpointPolynomial P (some e) (some t)).coeff k := by
  rw [c.originalLocalResponse_residue_profile_gradient P (some b) (some t) H hH, hdegree]
  have hn (f : Polynomial (OtherField c.top)) : f.toLaurent.coeff (k : ℤ) = f.coeff k := by
    change (Finsupp.mapDomain (fun z : ℕ => (z : ℤ)) f.toFinsupp.coeff) (k : ℤ) = _
    exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k
  rw [hn]
  exact c.original_selected_cross_profile_coeff P b d e t hleft hright k hkleft hkright

/-- Integer-offset locality includes the zero regime below degree zero. In that
regime the Laurent coefficient vanishes; it is never replaced by a constant term
through truncated natural subtraction. -/
theorem original_long_response_local_gradient_laurent {n : ℕ} (P : Profile n)
    (b d e t : OriginalSelectedBlocks (hD := hD) P)
    (hleft : b.val ≤ d.val ∧ d.val ≤ t.val)
    (hright : b.val ≤ e.val ∧ e.val ≤ t.val)
    (H : ℕ+) (hH : c.top < H) (w : ℤ)
    (hdegree : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t))) - (H : ℤ) = w)
    (hwleft : w ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))))
    (hwright : w ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some e))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.regularResidue (c.originalLocalResponse P (some b) (some t))) =
    ((c.originalResidueLeftEndpointPolynomial P (some b) (some d) *
      c.originalResidueRightEndpointPolynomial P (some e) (some t)).toLaurent).coeff w := by
  by_cases hw : 0 ≤ w
  · let k := w.toNat
    have hk : (k : ℤ) = w := Int.toNat_of_nonneg hw
    have hnat (f : Polynomial (OtherField c.top)) :
        f.toLaurent.coeff (k : ℤ) = f.coeff k := by
      change (Finsupp.mapDomain (fun z : ℕ => (z : ℤ)) f.toFinsupp.coeff) (k : ℤ) = _
      exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k
    rw [← hk, hnat]
    exact c.original_long_response_local_gradient P b d e t hleft hright H hH k
      (hdegree.trans hk.symm) (by rw [hk]; exact hwleft) (by rw [hk]; exact hwright)
  · have hneg (f : Polynomial (OtherField c.top)) : f.toLaurent.coeff w = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rw [LaurentPolynomial.support_coeff_toLaurent]
      intro h
      obtain ⟨k, _, he⟩ := Finset.mem_map.mp h
      change (k : ℤ) = w at he
      omega
    rw [c.originalLocalResponse_residue_profile_gradient P (some b) (some t) H hH,
      hdegree, hneg, hneg]

end SkewCornerDescent.Matrix.SelectedCoordinate
