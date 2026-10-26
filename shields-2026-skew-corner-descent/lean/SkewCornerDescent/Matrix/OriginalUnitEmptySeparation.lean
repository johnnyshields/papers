/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEmptyOutgoingTop
import SkewCornerDescent.Matrix.ResidueProtectedTop

/-!
# Original profile coefficients distinguish full blocks from empty pivots

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
At a common endpoint distance, protected top recognition separates every row
or column of a positive-span unit component from a literal empty pivot.
All coefficient models and nonzero extreme cofactors are source-produced.
The comparison is in the unchanged original residue field. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At one common visible distance, a full positive-span unit-component row
cannot have the same original incoming profile coefficient as an empty pivot.
Their actual protected tops, not numerical specializations, distinguish them. -/
theorem original_incoming_unit_row_ne_empty {n m : ℕ} (P : Profile n) (Q : Profile m)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P (some a) < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : Fin (interiorBlockLength P u.val + 1))
    (a' : OriginalSelectedBlocks (hD := hD) Q)
    (d' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (k : OriginalResponseInterval (hD := hD) Q (some a') d')
    (hempty : Q.xi k.1.1.1.val.succ = Q.zeta k.1.1.1.val.castSucc)
    (hdistance :
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
          originalResponseRows P (originalIntervalUnitIndex P (some a) d u hs hu j).1.1 =
        Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
          originalResponseRows Q k.1.1) :
    (c.originalResidueLeftEndpointPolynomial P (some a) d).coeff
        (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
          originalResponseRows P (originalIntervalUnitIndex P (some a) d u hs hu j).1.1).toNat ≠
      (c.originalResidueLeftEndpointPolynomial Q (some a') d').coeff
        (Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
          originalResponseRows Q k.1.1).toNat := by
  obtain ⟨J, hJe, hJ, α, hα, hα0, R, hR, hvalue⟩ :=
    c.original_interval_incoming_protected_top P a d u hs hne hu hmax j
  obtain ⟨K, hKe, hK, T, hT, hvalueQ⟩ :=
    c.original_empty_interval_incoming_top Q a' d' k hempty
  have hp := c.original_left_profile_coeff_at_row P (some a) d
    (originalIntervalUnitIndex P (some a) d u hs hu j)
  have hq := c.original_left_profile_coeff_at_row Q (some a') d' k
  dsimp only at hJe hKe hvalue hvalueQ hp hq
  intro heq
  rw [hp, hq] at heq
  have hv := neg_inj.mp heq
  rw [hvalue, hvalueQ] at hv
  have hv' : residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * α + R =
      residueGenerator c.top ⟨K, ne_of_gt hK⟩ * 1 + T := by
    simpa only [mul_one] using hv
  have hJK := c.residue_protected_affine_top_unique J K hJ hK α R 1 T
    hα hα0 hR (residueLowerField c.top K).one_mem
    (one_ne_zero : (1 : OtherField c.top) ≠ 0) hT hv'
  have hc := congrArg (fun t : ℕ+ => (t : ℤ)) hJK
  have hr := (original_unit_component_beta P u hs hne j).1
  change originalResponseRows P (originalIntervalUnitIndex P (some a) d u hs hu j).1.1 =
    (interiorBlockProfile P u.val hne).xi j + originalComponentTau P u at hr
  have hp0 := (interiorBlockProfile P u.val hne).xi_pos j
  have hqrow := (originalEmptyBlock_remaining_endpoints Q k.1.1.1 hempty k.1.1.2).1
  change originalResponseRows Q k.1.1 = Q.xi k.1.1.1.val.succ at hqrow
  rw [hr, hqrow] at hdistance
  omega

/-- The exact outgoing analogue distinguishes a positive-span unit-component
column from a literal empty pivot at the same endpoint distance. -/
theorem original_outgoing_unit_col_ne_empty {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P (some d))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : Fin (interiorBlockLength P u.val + 1))
    (b' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (d' : OriginalSelectedBlocks (hD := hD) Q)
    (k : OriginalResponseInterval (hD := hD) Q b' (some d'))
    (hempty : Q.xi k.1.1.1.val.succ = Q.zeta k.1.1.1.val.castSucc)
    (hdistance : originalResponseCols P (originalIntervalUnitIndex P b (some d) u hs hu j).1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) =
      originalResponseCols Q k.1.1 -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some d')))) :
    (c.originalResidueRightEndpointPolynomial P b (some d)).coeff
        (originalResponseCols P (originalIntervalUnitIndex P b (some d) u hs hu j).1.1 -
          P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))).toNat ≠
      (c.originalResidueRightEndpointPolynomial Q b' (some d')).coeff
        (originalResponseCols Q k.1.1 -
          Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some d')))).toNat := by
  obtain ⟨J, hJe, hJ, α, hα, hα0, R, hR, hvalue⟩ :=
    c.original_interval_outgoing_protected_top P b d u hs hne hu hmax j
  obtain ⟨K, hKe, hK, T, hT, hvalueQ⟩ :=
    c.original_empty_interval_outgoing_top Q b' d' k hempty
  have hp := c.original_right_profile_coeff_at_col P b (some d)
    (originalIntervalUnitIndex P b (some d) u hs hu j)
  have hq := c.original_right_profile_coeff_at_col Q b' (some d') k
  dsimp only at hJe hKe hvalue hvalueQ hp hq
  intro heq
  rw [hp, hq] at heq
  have hv := neg_inj.mp heq
  rw [hvalue, hvalueQ] at hv
  have hv' : residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * α + R =
      residueGenerator c.top ⟨K, ne_of_gt hK⟩ * 1 + T := by
    simpa only [mul_one, mul_comm α] using hv
  have hJK := c.residue_protected_affine_top_unique J K hJ hK α R 1 T
    hα hα0 hR (residueLowerField c.top K).one_mem
    (one_ne_zero : (1 : OtherField c.top) ≠ 0) hT hv'
  have hc := congrArg (fun t : ℕ+ => (t : ℤ)) hJK
  have hpcol := (original_unit_component_beta P u hs hne j).2
  change originalResponseCols P (originalIntervalUnitIndex P b (some d) u hs hu j).1.1 =
    (interiorBlockProfile P u.val hne).zeta j + originalComponentTau P u at hpcol
  have hz := (interiorBlockProfile P u.val hne).zeta_strictAnti.antitone (Fin.zero_le j)
  have hpos := (interiorBlockProfile P u.val hne).r_pos 0
  have hrel := (interiorBlockProfile P u.val hne).xi_sub_zeta 0
  have hqcol := (originalEmptyBlock_remaining_endpoints Q k.1.1.1 hempty k.1.1.2).2
  change originalResponseCols Q k.1.1 = Q.zeta k.1.1.1.val.castSucc at hqcol
  rw [← hempty] at hqcol
  rw [hpcol, hqcol] at hdistance
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
