/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalLowStrips
import SkewCornerDescent.Matrix.OriginalSelectedCoreCoordinates

/-!
# Complete normal original boundary strips equal their actual proper cores

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual source index equivalences and beta translation identify both whole strip
profiles at every normal order. No normal matching or constant-jet premise is supplied.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original first-strip normal polynomial is its own literal proper core. -/
theorem original_normal_left_strip_eq_core {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (hupper : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P d) :
    let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    c.originalNormalLeftStripPolynomial P b d = c.selectedCoreNormalLeftPolynomial Q := by
  classical
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  let τ := P.zeta (interiorBlockLast P b.val.val).castSucc
  let row := fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1
  let col := fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseCols P i.1.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  let e := (finCongr (originalRemovedSize_selected P b).symm).trans
    (originalLeftStripSourceEquiv P b d hupper)
  have hrow : row ∘ e = fun i : Fin (interiorBlockLength P b.val.val) => Q.xi i.succ + τ := by
    funext i
    exact original_selected_core_row_coordinate P b i
  have hcol : col ∘ e = fun i : Fin (interiorBlockLength P b.val.val) => Q.zeta i.castSucc + τ := by
    funext i
    exact original_selected_core_col_coordinate P b i
  have hx : x = Q.xi 0 + τ := original_selected_core_retained_row P b
  have hp := (betaEndpointLeftPolynomial_equiv c.normalPolynomialSeries row col x e).symm
  have ht := betaEndpointLeftPolynomial_translate c.normalPolynomialSeries
    (fun i : Fin (interiorBlockLength P b.val.val) => Q.xi i.succ)
    (fun i => Q.zeta i.castSucc) (Q.xi 0) τ
  conv_rhs at hp => rw [hrow, hcol, hx]
  exact hp.trans ht

/-- The complete original last-strip normal polynomial is its own literal proper core. -/
theorem original_normal_right_strip_eq_core {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (hlower : originalResponseLowerCut P b < (interiorBlock P d.val.val : ℤ)) :
    let Q := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
    c.originalNormalRightStripPolynomial P b d = c.selectedCoreNormalRightPolynomial Q := by
  classical
  let Q := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
  let τ := P.zeta (interiorBlockLast P d.val.val).castSucc
  let row := fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1
  let col := fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseCols P i.1.1.1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  let e := (finCongr (originalRemovedSize_selected P d).symm).trans
    (originalRightStripSourceEquiv P b d hlower)
  have hrow : row ∘ e = fun i : Fin (interiorBlockLength P d.val.val) => Q.xi i.succ + τ := by
    funext i
    exact original_selected_core_row_coordinate P d i
  have hcol : col ∘ e = fun i : Fin (interiorBlockLength P d.val.val) => Q.zeta i.castSucc + τ := by
    funext i
    exact original_selected_core_col_coordinate P d i
  have hy : y = Q.zeta (Fin.last (interiorBlockLength P d.val.val)) + τ := by
    rw [Q.zeta_last, zero_add]
    exact congrArg P.zeta (originalColSplitEquiv_selected P d)
  have hp := (betaEndpointRightPolynomial_equiv c.normalPolynomialSeries row col y e).symm
  have ht := betaEndpointRightPolynomial_translate c.normalPolynomialSeries
    (fun i : Fin (interiorBlockLength P d.val.val) => Q.xi i.succ)
    (fun i => Q.zeta i.castSucc) (Q.zeta (Fin.last (interiorBlockLength P d.val.val))) τ
  conv_rhs at hp => rw [hrow, hcol, hy]
  exact hp.trans ht

/-- The complete original incoming profile through selected-span endpoint degree is
constant in the normal variable and equals its own actual source-selected core. -/
theorem original_normal_left_profile_low_core {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (hupper : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P d)
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalNormalLeftEndpointPolynomial P (some b) d).coeff k =
      PowerSeries.C ((c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm).coeff k) := by
  rw [c.original_normal_left_profile_low_strip P b d k hk,
    c.original_normal_left_strip_eq_core P b d hupper,
    c.selected_core_normal_left_polynomial _ (originalSelectedProfile_schur P b).symm,
    Polynomial.coeff_map]

/-- The symmetric full original outgoing low core has the same all-normal-order identity. -/
theorem original_normal_right_profile_low_core {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (hlower : originalResponseLowerCut P b < (interiorBlock P d.val.val : ℤ))
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalNormalRightEndpointPolynomial P b (some d)).coeff k =
      PowerSeries.C ((c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm).coeff k) := by
  rw [c.original_normal_right_profile_low_strip P b d k hk,
    c.original_normal_right_strip_eq_core P b d hlower,
    c.selected_core_normal_right_polynomial _ (originalSelectedProfile_schur P d).symm,
    Polynomial.coeff_map]

/-- The full original low mixed profile product is exactly the constant normal series
of its two own proper cores. Every complete source inverse and unit jet remains on the left. -/
theorem original_normal_profile_product_low_cores {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalNormalLeftEndpointPolynomial P (some b) (some d) *
      c.originalNormalRightEndpointPolynomial P (some b) (some d)).coeff k =
      PowerSeries.C ((c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm *
        c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm).coeff k) := by
  have hu : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P (some d) := by
    change (interiorBlock P b.val.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1
    omega
  have hl : originalResponseLowerCut P (some b) < (interiorBlock P d.val.val : ℤ) := by
    change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P d.val.val : ℤ)
    omega
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [c.original_normal_left_profile_low_core P b (some d) hu i (by omega),
    c.original_normal_right_profile_low_core P (some b) d hl j (by omega), map_mul]

end SkewCornerDescent.Matrix.SelectedCoordinate
