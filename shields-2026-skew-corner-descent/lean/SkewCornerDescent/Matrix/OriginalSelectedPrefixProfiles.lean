/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles
import SkewCornerDescent.Matrix.OrderedProfileLocality
import SkewCornerDescent.Matrix.OriginalSelectedStripBounds

/-!
# Full-height locality of the complete left endpoint profile

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). For retained
original intervals `b ≤ d ≤ t`, the coefficient of the complete incoming endpoint
profile of `(b, t)` at every degree `k ≤ x - y` equals that of `(b, d)`, where
`x` is the incoming selected row and `y` the outgoing selected column of `d`.
Every removed row of a block after `d` lies strictly below `y`, so it cannot reach
degree `k`. The complete original inverse restricted to the prefix through `d` is
the complete inverse of the `(b, d)` interval. No inverse coupling is dropped.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Coefficient formula of an ordinary endpoint profile at a natural degree. -/
private theorem selectedPrefix_ordinary_coeff {ν F : Type*} [Fintype ν] [CommRing F]
    (dist : ν → ℕ) (v : ν → F) (k : ℕ) :
    (ordinaryEndpointProfile dist v).coeff k =
      (if k = 0 then 1 else 0) - ∑ i, if dist i = k then v i else 0 := by
  simp [ordinaryEndpointProfile, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_one]

/-- A removed row of a block strictly after the selected block `d` lies strictly below
the outgoing selected column of `d`. -/
private theorem selectedPrefix_row_lt_of_later {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hlt : interiorBlock P d.val.val < interiorBlock P j.1.val) :
    originalResponseRows P j <
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) := by
  have he := interior_block_endpoint_separation P (originalRemovedRow (hD := hD) P j.1 j.2)
    (interiorBlockLast P d.val.val)
    (by rw [originalRemovedRow_block, interiorBlockLast_label]; exact hlt)
  rw [originalColSplitEquiv_selected]
  exact he

/-- The retained interval `(b, d)` is exactly the subtype of the retained interval `(b, t)`
whose blocks lie below the upper cutoff of `d`. -/
private noncomputable def selectedPrefixEquiv {n : ℕ} (P : Profile n)
    (b t : Option (OriginalSelectedBlocks (hD := hD) P)) (d : OriginalSelectedBlocks (hD := hD) P)
    (hcut : originalResponseUpperCut P (some d) ≤ originalResponseUpperCut P t) :
    OriginalResponseInterval (hD := hD) P b (some d) ≃
      {i : OriginalResponseInterval (hD := hD) P b t //
        (interiorBlock P i.1.1.1.val : ℤ) < originalResponseUpperCut P (some d)} where
  toFun z := ⟨⟨⟨z.1.1, lt_of_lt_of_le z.1.2 hcut⟩, z.2⟩, z.1.2⟩
  invFun w := ⟨⟨w.1.1.1, w.2⟩, w.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Abstract transfer of the complete ordered inverse. The full inverse coefficient of
a prefix index uses only the prefix block (`incoming_inverse_prefix`), and the prefix
block of the larger matrix is the complete inverse of the smaller matrix, reindexed. -/
private theorem selectedPrefix_transfer {ν μ F α : Type*} [Fintype ν] [DecidableEq ν]
    [Fintype μ] [DecidableEq μ] [LinearOrder α] [CommRing F]
    (M : Matrix ν ν F) [Invertible M] (Mμ : Matrix μ μ F)
    (lab : ν → α) (hM : M.BlockTriangular lab) (cut : α)
    (e : μ ≃ {i : ν // lab i < cut})
    (hMμ : Mμ = (M.toBlock (fun i => lab i < cut) (fun i => lab i < cut)).submatrix e e)
    (r : ν → F) (s : μ → F) (hr : ∀ j, s j = r (e j).1)
    (dist : ν → ℕ) (dist' : μ → ℕ) (hdist : ∀ z, dist' z = dist (e z).1)
    (k : ℕ) (hvan : ∀ i, ¬ lab i < cut → dist i = k → False) :
    ∑ i, (if dist i = k then ∑ j, r j * M⁻¹ j i else 0) =
      ∑ z, (if dist' z = k then ∑ j, s j * Mμ⁻¹ j z else 0) := by
  have hsplit : ∑ i, (if dist i = k then ∑ j, r j * M⁻¹ j i else 0) =
      (∑ i : {i : ν // lab i < cut}, (if dist i.1 = k then ∑ j, r j * M⁻¹ j i.1 else 0)) +
        ∑ i : {i : ν // ¬ lab i < cut}, (if dist i.1 = k then ∑ j, r j * M⁻¹ j i.1 else 0) :=
    (Fintype.sum_subtype_add_sum_subtype (fun i => lab i < cut)
      (fun i => if dist i = k then ∑ j, r j * M⁻¹ j i else 0)).symm
  have hzero : ∑ i : {i : ν // ¬ lab i < cut},
      (if dist i.1 = k then ∑ j, r j * M⁻¹ j i.1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (hvan i.1 i.2)]
  have hWV : ∀ z : μ, (∑ j, s j * Mμ⁻¹ j z) = ∑ i, r i * M⁻¹ i (e z).1 := by
    intro z
    rw [incoming_inverse_prefix r M lab hM cut (e z).1 (e z).2]
    have hinv : ∀ j z', Mμ⁻¹ j z' =
        (M.toBlock (fun i => lab i < cut) (fun i => lab i < cut))⁻¹ (e j) (e z') := by
      intro j z'
      rw [hMμ, Matrix.inv_submatrix_equiv, Matrix.submatrix_apply]
    calc ∑ j, s j * Mμ⁻¹ j z
        = ∑ j, r (e j).1 *
            (M.toBlock (fun i => lab i < cut) (fun i => lab i < cut))⁻¹ (e j) (e z) :=
          Finset.sum_congr rfl fun j _ => by rw [hr j, hinv j z]
      _ = ∑ w : {i : ν // lab i < cut}, r w.1 *
            (M.toBlock (fun i => lab i < cut) (fun i => lab i < cut))⁻¹ w (e z) :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hsplit, hzero, add_zero]
  symm
  apply Fintype.sum_equiv e _ _
  intro z
  simp only [hdist z, hWV z]

/-- Full-height locality of the complete left endpoint profile. For a genuine block order
`b ≤ d ≤ t` of selected original blocks and every degree `k` not exceeding the local
height `x - y`, the coefficient of the `(b, t)` profile equals that of the `(b, d)` profile.
No bound on `k` by the selected span is assumed. -/
theorem original_left_profile_selected_prefix_coeff {n : ℕ} (P : Profile n)
    (b d t : OriginalSelectedBlocks (hD := hD) P) (hord : b.val ≤ d.val ∧ d.val ≤ t.val)
    (k : ℕ)
    (hk : (k : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) :
    (c.originalResidueLeftEndpointPolynomial P (some b) (some t)).coeff k =
      (c.originalResidueLeftEndpointPolynomial P (some b) (some d)).coeff k := by
  have hdt : interiorBlock P d.val.val ≤ interiorBlock P t.val.val :=
    interiorBlock_mono P (show d.val.val ≤ t.val.val from hord.2)
  have hcut : originalResponseUpperCut P (some d) ≤ originalResponseUpperCut P (some t) := by
    change (interiorBlock P d.val.val : ℤ) + 1 ≤ (interiorBlock P t.val.val : ℤ) + 1
    omega
  have hMt : (vertexBetaMatrix c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
        originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)).BlockTriangular
        (fun i => (interiorBlock P i.1.1.1.val : ℤ)) := by
    intro i j hij
    have hfull := c.originalResponse_residue_blockTriangular P
    exact hfull (i := i.1.1) (j := j.1.1) hij
  have hvan : ∀ i : OriginalResponseInterval (hD := hD) P (some b) (some t),
      ¬ ((interiorBlock P i.1.1.1.val : ℤ) < originalResponseUpperCut P (some d)) →
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        originalResponseRows P i.1.1).toNat = k → False := by
    intro i hi h1
    have h' : ¬ ((interiorBlock P i.1.1.1.val : ℤ) <
        (interiorBlock P d.val.val : ℤ) + 1) := hi
    have hlt : interiorBlock P d.val.val < interiorBlock P i.1.1.1.val := by
      omega
    have hrow := selectedPrefix_row_lt_of_later P d i.1.1 hlt
    have hpos : 0 ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        originalResponseRows P i.1.1 := by
      omega
    have h2 := Int.toNat_of_nonneg hpos
    rw [h1] at h2
    omega
  unfold originalResidueLeftEndpointPolynomial residueIntervalLeftPolynomial
  dsimp only
  rw [selectedPrefix_ordinary_coeff, selectedPrefix_ordinary_coeff]
  congr 1
  let := c.originalResponseResidueIntervalInverse P (some b) (some t)
  have key := selectedPrefix_transfer
    (M := vertexBetaMatrix c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
        originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1))
    (Mμ := vertexBetaMatrix c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
        originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1))
    (lab := fun i : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
      (interiorBlock P i.1.1.1.val : ℤ))
    (hM := hMt) (cut := originalResponseUpperCut P (some d))
    (e := selectedPrefixEquiv P (some b) (some t) d hcut)
    (hMμ := Matrix.ext fun _ _ => rfl)
    (r := fun j : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
      c.residueMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        originalResponseCols P j.1.1)))
    (s := fun j : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      c.residueMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        originalResponseCols P j.1.1)))
    (hr := fun _ => rfl)
    (dist := fun i : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        originalResponseRows P i.1.1).toNat)
    (dist' := fun z : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        originalResponseRows P z.1.1).toNat)
    (hdist := fun _ => rfl)
    (k := k) (hvan := hvan)
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.mul_apply, vertexOutgoing, Matrix.of_apply]
  exact key

end SkewCornerDescent.Matrix.SelectedCoordinate
