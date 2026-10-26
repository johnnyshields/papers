/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles
import SkewCornerDescent.Matrix.OriginalSelectedStripBounds
import SkewCornerDescent.Matrix.OrderedProfileLocality

/-!
# Low actual endpoint profiles belong to their selected boundary strips

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Actual
ordered locality identifies the full incoming or outgoing coefficients in the
boundary strip. Every other original position starts strictly beyond the selected
span, including literal h-zero vertices. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The pruned actual residue interval inherits original block triangularity. -/
theorem originalResponseInterval_residue_blockTriangular {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    (vertexBetaMatrix c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)).BlockTriangular
        (fun i => (interiorBlock P i.1.1.1.val : ℤ)) := by
  exact (c.originalResponse_residue_blockTriangular P).submatrix.submatrix

/-- The prefix consisting of the original first selected boundary strip. -/
abbrev OriginalLeftStripIndex {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) :=
  {i : OriginalResponseInterval (hD := hD) P (some b) d //
    (interiorBlock P i.1.1.1.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1}

/-- The selected-strip inverse is produced from the full original interval. -/
@[instance_reducible]
noncomputable def originalLeftStripResidueInverse {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
      (fun i => originalResponseCols P i.1.1.1)) := by
  let := c.originalResponseResidueIntervalInverse P (some b) d
  exact (c.originalResponseInterval_residue_blockTriangular P (some b) d).invertibleToBlock _

/-- Ordinary incoming polynomial of the actual original selected boundary strip. -/
noncomputable def originalLeftStripEndpointPolynomial {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) : Polynomial (OtherField c.top) :=
  letI := c.originalLeftStripResidueInverse P b d
  c.residueIntervalLeftPolynomial
    (fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
    (fun i => originalResponseCols P i.1.1.1)
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))

/-- Through selected-span degree, the complete actual incoming profile is
exactly the selected-strip profile. Both the strip inverse and the exclusion of
all later original rows are supplied by the source geometry. -/
theorem original_left_profile_low_strip {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalResidueLeftEndpointPolynomial P (some b) d).coeff k =
      (c.originalLeftStripEndpointPolynomial P b d).coeff k := by
  classical
  let := c.originalResponseResidueIntervalInverse P (some b) d
  let := c.originalLeftStripResidueInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P (some b) d =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P (some b) d =>
    originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun i : OriginalResponseInterval (hD := hD) P (some b) d =>
    (interiorBlock P i.1.1.1.val : ℤ)
  let cut := (interiorBlock P b.val.val : ℤ) + 1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  have htri : M.BlockTriangular label :=
    c.originalResponseInterval_residue_blockTriangular P (some b) d
  have hweights (i : OriginalLeftStripIndex (hD := hD) P b d) :
      (vertexOutgoing c.residueMap col x * ⅟M) () i.1 =
        (vertexOutgoing c.residueMap (fun j : OriginalLeftStripIndex (hD := hD) P b d =>
          col j.1) x * ⅟(vertexBetaMatrix c.residueMap
            (fun j : OriginalLeftStripIndex (hD := hD) P b d => row j.1)
            (fun j => col j.1))) () i := by
    simp only [Matrix.mul_apply, vertexOutgoing, Matrix.of_apply, Matrix.invOf_eq_nonsing_inv]
    exact incoming_inverse_prefix (fun j => c.residueMap (hh (x - col j))) M label htri cut i.1 i.2
  have habsent (i : OriginalResponseInterval (hD := hD) P (some b) d)
      (hi : ¬label i < cut) : (x - row i).toNat ≠ k := by
    have hlt : interiorBlock P b.val.val < interiorBlock P i.1.1.1.val := by
      dsimp only [label, cut] at hi
      omega
    have h := c.original_row_distance_gt_top_of_later_block P b i.1.1 hlt
    change (c.top : ℤ) < x - row i at h
    exact ne_of_gt (hk.trans_lt (Int.lt_toNat.mpr h))
  simp only [originalResidueLeftEndpointPolynomial, originalLeftStripEndpointPolynomial,
    residueIntervalLeftPolynomial, ordinaryEndpointProfile, Polynomial.coeff_sub,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply congrArg (fun z : OtherField c.top =>
    (1 : Polynomial (OtherField c.top)).coeff k - z)
  apply Finset.sum_congr_set {i | label i < cut}
  · intro i hi
    split_ifs
    · exact hweights ⟨i, hi⟩
    · rfl
  · intro i hi
    exact ite_eq_right (habsent i hi)

/-- The suffix consisting of the original last selected boundary strip. -/
abbrev OriginalRightStripIndex {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) :=
  {i : OriginalResponseInterval (hD := hD) P b (some d) //
    (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P i.1.1.1.val : ℤ)}

/-- The original last-strip inverse is produced by transposed ordered locality. -/
@[instance_reducible]
noncomputable def originalRightStripResidueInverse {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
      (fun i => originalResponseCols P i.1.1.1)) := by
  let := c.originalResponseResidueIntervalInverse P b (some d)
  have htri := c.originalResponseInterval_residue_blockTriangular P b (some d)
  let inv := htri.transpose.invertibleToBlock
    (OrderDual.toDual ((interiorBlock P d.val.val : ℤ) - 1))
  change Invertible (Matrix.transpose (vertexBetaMatrix c.residueMap
    (fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
    (fun i => originalResponseCols P i.1.1.1))) at inv
  let := inv
  exact Matrix.invertibleOfInvertibleTranspose _

/-- Ordinary outgoing polynomial of the actual original last selected strip. -/
noncomputable def originalRightStripEndpointPolynomial {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) : Polynomial (OtherField c.top) :=
  letI := c.originalRightStripResidueInverse P b d
  c.residueIntervalRightPolynomial
    (fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
    (fun i => originalResponseCols P i.1.1.1)
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))))

/-- Through selected-span degree, the full actual outgoing profile is exactly
the last selected-strip profile, with all earlier original columns excluded
by their produced strict source distances. -/
theorem original_right_profile_low_strip {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalResidueRightEndpointPolynomial P b (some d)).coeff k =
      (c.originalRightStripEndpointPolynomial P b d).coeff k := by
  classical
  let := c.originalResponseResidueIntervalInverse P b (some d)
  let := c.originalRightStripResidueInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
    originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
    (interiorBlock P i.1.1.1.val : ℤ)
  let cut := (interiorBlock P d.val.val : ℤ) - 1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  have htri : M.BlockTriangular label :=
    c.originalResponseInterval_residue_blockTriangular P b (some d)
  have hweights (i : OriginalRightStripIndex (hD := hD) P b d) :
      (⅟M * vertexIncoming c.residueMap row y) i.1 () =
        (⅟(vertexBetaMatrix c.residueMap
            (fun j : OriginalRightStripIndex (hD := hD) P b d => row j.1)
            (fun j => col j.1)) *
          vertexIncoming c.residueMap
            (fun j : OriginalRightStripIndex (hD := hD) P b d => row j.1) y) i () := by
    simp only [Matrix.mul_apply, vertexIncoming, Matrix.of_apply, Matrix.invOf_eq_nonsing_inv]
    exact outgoing_inverse_suffix (fun j => c.residueMap (hh (row j - y))) M label htri cut i.1 i.2
  have habsent (i : OriginalResponseInterval (hD := hD) P b (some d))
      (hi : ¬cut < label i) : (col i - y).toNat ≠ k := by
    have hlt : interiorBlock P i.1.1.1.val < interiorBlock P d.val.val := by
      dsimp only [label, cut] at hi
      omega
    have h := c.original_col_distance_gt_top_of_earlier_block P d i.1.1 hlt
    change (c.top : ℤ) < col i - y at h
    exact ne_of_gt (hk.trans_lt (Int.lt_toNat.mpr h))
  simp only [originalResidueRightEndpointPolynomial, originalRightStripEndpointPolynomial,
    residueIntervalRightPolynomial, ordinaryEndpointProfile, Polynomial.coeff_sub,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply congrArg (fun z : OtherField c.top =>
    (1 : Polynomial (OtherField c.top)).coeff k - z)
  apply Finset.sum_congr_set {i | cut < label i}
  · intro i hi
    split_ifs
    · exact hweights ⟨i, hi⟩
    · rfl
  · intro i hi
    exact ite_eq_right (habsent i hi)

/-- If both actual proper boundary-strip profiles agree, any nonzero
discrepancy of the complete original profiles occurs strictly beyond the selected
span. No low-profile agreement is supplied as a separate hypothesis. -/
theorem original_profile_discrepancy_gt_top {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (hleft : c.originalLeftStripEndpointPolynomial P b (some d) =
      c.originalLeftStripEndpointPolynomial Q b' (some d'))
    (hright : c.originalRightStripEndpointPolynomial P (some b) d =
      c.originalRightStripEndpointPolynomial Q (some b') d')
    (w : ℕ)
    (hdiff :
      (c.originalResidueLeftEndpointPolynomial P (some b) (some d)).coeff w ≠
        (c.originalResidueLeftEndpointPolynomial Q (some b') (some d')).coeff w ∨
      (c.originalResidueRightEndpointPolynomial P (some b) (some d)).coeff w ≠
        (c.originalResidueRightEndpointPolynomial Q (some b') (some d')).coeff w) :
    (c.top : ℕ) < w := by
  by_contra hn
  have hw : w ≤ (c.top : ℕ) := Nat.le_of_not_gt hn
  rcases hdiff with hdiff | hdiff
  · rw [c.original_left_profile_low_strip P b (some d) w hw,
      c.original_left_profile_low_strip Q b' (some d') w hw, hleft] at hdiff
    exact hdiff rfl
  · rw [c.original_right_profile_low_strip P (some b) d w hw,
      c.original_right_profile_low_strip Q (some b') d' w hw, hright] at hdiff
    exact hdiff rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
