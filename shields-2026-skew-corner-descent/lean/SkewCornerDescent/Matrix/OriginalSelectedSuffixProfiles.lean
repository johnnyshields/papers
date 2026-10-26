/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueLowStrips

/-!
# Full-height suffix locality of actual right endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). For nested
original selected blocks `b ≤ d ≤ t`, the outgoing endpoint profile of the retained
interval `(b, t)` and that of `(d, t)` agree in every coefficient up to the local
selected-to-selected height `xi(d) - zeta(t)`. The complete retained suffix of the
`(b, t)` inverse is the complete inverse of `(d, t)`, transported along an exact index
equivalence; every inverse coupling inside the suffix is kept. No top-degree bound is
assumed.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A finite sum supported on a subtype is the sum over that subtype, transported along
an equivalence onto the target index type. -/
theorem selectedSuffix_sum_eq_of_zero_off {ι κ β : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid β] (p : ι → Prop) (e : {i // p i} ≃ κ)
    (f : ι → β) (g : κ → β) (hf : ∀ i, ¬ p i → f i = 0)
    (hfg : ∀ x : {i // p i}, f x.1 = g (e x)) :
    ∑ i, f i = ∑ j, g j := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype p f]
  have h0 : ∑ i : {i // ¬ p i}, f i.1 = 0 := Finset.sum_eq_zero (fun i _ => hf i.1 i.2)
  rw [h0, add_zero]
  exact Fintype.sum_equiv e (fun x => f x.1) g hfg

set_option backward.isDefEq.respectTransparency false in
/-- The complete suffix row of an inverse, transported along an exact identification of
the suffix block with another matrix. The inverse coupling inside the suffix is the full
block of the inverse, never its diagonal. -/
theorem selectedSuffix_inverse_transport {ν κ α F : Type*} [Fintype ν] [DecidableEq ν]
    [Fintype κ] [DecidableEq κ] [LinearOrder α] [CommRing F]
    (M : Matrix ν ν F) [Invertible M] (M' : Matrix κ κ F) (b : ν → α)
    (hM : M.BlockTriangular b) (cut : α) (e : {j : ν // cut < b j} ≃ κ)
    (hN : M.toBlock (fun i => cut < b i) (fun i => cut < b i) = M'.submatrix e e)
    (cv : ν → F) (cv' : κ → F) (hc : ∀ j : {j : ν // cut < b j}, cv j.1 = cv' (e j))
    (x : {j : ν // cut < b j}) :
    ∑ j, M⁻¹ x.1 j * cv j = ∑ j, M'⁻¹ (e x) j * cv' j := by
  rw [outgoing_inverse_suffix cv M b hM cut x.1 x.2]
  change (∑ j : {j : ν // cut < b j},
    (M.toBlock (fun i => cut < b i) (fun i => cut < b i))⁻¹ x j * cv j.1) = _
  have hinv : (M.toBlock (fun i => cut < b i) (fun i => cut < b i))⁻¹ =
      M'⁻¹.submatrix e e := by
    rw [hN, Matrix.inv_submatrix_equiv]
  calc
    _ = ∑ j : {j : ν // cut < b j}, M'⁻¹ (e x) (e j) * cv j.1 := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z : F => z * cv j.1) (congrFun (congrFun hinv x) j)
    _ = _ := Fintype.sum_equiv e _ _ (fun j => by rw [hc j])

/-- Coefficient form of the outgoing residue endpoint polynomial over an arbitrary
interval, with the complete residue inverse. -/
theorem selectedSuffix_residueRight_coeff_sum {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (y : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)] (k : ℕ) :
    (c.residueIntervalRightPolynomial row col y).coeff k =
      (1 : Polynomial (OtherField c.top)).coeff k -
        ∑ i, if (col i - y).toNat = k then
          ((vertexBetaMatrix c.residueMap row col)⁻¹ *
            vertexIncoming c.residueMap row y) i ()
        else 0 := by
  simp only [residueIntervalRightPolynomial, ordinaryEndpointProfile, Polynomial.coeff_sub,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Matrix.invOf_eq_nonsing_inv]

/-- The actual outgoing profile of the retained interval `(b, d)` in coefficient-sum
form over the complete original residue inverse. -/
theorem originalSelectedSuffix_residueRight_coeff {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℕ) :
    (c.originalResidueRightEndpointPolynomial P b d).coeff k =
      (1 : Polynomial (OtherField c.top)).coeff k -
        ∑ i : OriginalResponseInterval (hD := hD) P b d,
          if (originalResponseCols (hD := hD) P i.1.1 -
              P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))).toNat = k then
            ((vertexBetaMatrix c.residueMap
                (fun i : OriginalResponseInterval (hD := hD) P b d =>
                  originalResponseRows (hD := hD) P i.1.1)
                (fun i => originalResponseCols (hD := hD) P i.1.1))⁻¹ *
              vertexIncoming c.residueMap
                (fun i : OriginalResponseInterval (hD := hD) P b d =>
                  originalResponseRows (hD := hD) P i.1.1)
                (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))) i ()
          else 0 := by
  let := c.originalResponseResidueIntervalInverse P b d
  exact c.selectedSuffix_residueRight_coeff_sum
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows (hD := hD) P i.1.1)
    (fun i => originalResponseCols (hD := hD) P i.1.1)
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))) k

/-- A removed column in a strictly earlier block lies strictly above the selected row
of `d`, by the actual selected endpoint distance. -/
theorem originalSelectedSuffix_row_lt_col {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hlt : interiorBlock P j.1.val < interiorBlock P d.val.val) :
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some d))) <
      originalResponseCols (hD := hD) P j := by
  have he := interior_block_endpoint_separation P d.val.val
    (originalRemovedCol (hD := hD) P j.1 j.2)
    (by rw [originalRemovedCol_block]; exact hlt)
  change P.xi d.val.val.succ < originalResponseCols P j at he
  simpa only [originalRowSplitEquiv_selected] using he

/-- Full-height suffix equality. Through the whole local interval height
`xi(d) - zeta(t)`, the actual right endpoint profile of `(b, t)` equals that of `(d, t)`.
Retained entries of `(b, t)` outside the suffix `(d, t)` lie in earlier blocks and their
columns sit strictly above `xi(d)`, so they contribute to no coefficient up to that
height. The suffix weights are the complete inverse block, transported by an exact
index equivalence. -/
theorem original_right_profile_selected_suffix_coeff {n : ℕ} (P : Profile n)
    (b d t : OriginalSelectedBlocks (hD := hD) P)
    (hord : b.val ≤ d.val ∧ d.val ≤ t.val)
    (k : ℕ)
    (hk : (k : ℤ) ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some d))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))) :
    (c.originalResidueRightEndpointPolynomial P (some b) (some t)).coeff k =
      (c.originalResidueRightEndpointPolynomial P (some d) (some t)).coeff k := by
  let := c.originalResponseResidueIntervalInverse P (some b) (some t)
  have hblockZ : (interiorBlock P b.val.val : ℤ) ≤ (interiorBlock P d.val.val : ℤ) := by
    exact_mod_cast interiorBlock_mono P hord.1
  rw [c.originalSelectedSuffix_residueRight_coeff P (some b) (some t) k,
    c.originalSelectedSuffix_residueRight_coeff P (some d) (some t) k]
  congr 1
  -- The suffix of the `(b, t)` interval at the cut of `d` is exactly the `(d, t)` interval.
  let e : {x : OriginalResponseInterval (hD := hD) P (some b) (some t) //
      (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P x.1.1.1.val : ℤ)} ≃
      OriginalResponseInterval (hD := hD) P (some d) (some t) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun w => ⟨⟨w.1, lt_of_le_of_lt
        (show (interiorBlock P b.val.val : ℤ) - 1 ≤ (interiorBlock P d.val.val : ℤ) - 1 by
          omega) w.2⟩, w.2⟩
      left_inv := fun x => rfl
      right_inv := fun w => rfl }
  have hN : (vertexBetaMatrix c.residueMap
      (fun x : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
        originalResponseRows (hD := hD) P x.1.1)
      (fun x => originalResponseCols (hD := hD) P x.1.1)).toBlock
        (fun x => (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P x.1.1.1.val : ℤ))
        (fun x => (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P x.1.1.1.val : ℤ)) =
      (vertexBetaMatrix c.residueMap
        (fun x : OriginalResponseInterval (hD := hD) P (some d) (some t) =>
          originalResponseRows (hD := hD) P x.1.1)
        (fun x => originalResponseCols (hD := hD) P x.1.1)).submatrix e e := by
    ext i j
    rfl
  -- Earlier-block retained entries are excluded by the local height.
  have absent : ∀ x : OriginalResponseInterval (hD := hD) P (some b) (some t),
      ¬ ((interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P x.1.1.1.val : ℤ)) →
        ¬ ((originalResponseCols (hD := hD) P x.1.1 -
          P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))).toNat = k) := by
    intro x hx hcond
    have hlt : interiorBlock P x.1.1.1.val < interiorBlock P d.val.val := by
      have h' : (interiorBlock P x.1.1.1.val : ℤ) < (interiorBlock P d.val.val : ℤ) := by
        omega
      exact_mod_cast h'
    have hcol := originalSelectedSuffix_row_lt_col P d x.1.1 hlt
    have hk' : (k : ℤ) < originalResponseCols (hD := hD) P x.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t))) := by
      omega
    exact (ne_of_gt (Int.lt_toNat.mpr hk')) hcond
  -- Suffix weights of `(b, t)` coincide with those of `(d, t)`.
  have hv : ∀ x : {x : OriginalResponseInterval (hD := hD) P (some b) (some t) //
      (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P x.1.1.1.val : ℤ)},
      ((vertexBetaMatrix c.residueMap
          (fun i : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
            originalResponseRows (hD := hD) P i.1.1)
          (fun i => originalResponseCols (hD := hD) P i.1.1))⁻¹ *
        vertexIncoming c.residueMap
          (fun i : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
            originalResponseRows (hD := hD) P i.1.1)
          (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t))))) x.1 () =
      ((vertexBetaMatrix c.residueMap
          (fun i : OriginalResponseInterval (hD := hD) P (some d) (some t) =>
            originalResponseRows (hD := hD) P i.1.1)
          (fun i => originalResponseCols (hD := hD) P i.1.1))⁻¹ *
        vertexIncoming c.residueMap
          (fun i : OriginalResponseInterval (hD := hD) P (some d) (some t) =>
            originalResponseRows (hD := hD) P i.1.1)
          (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t))))) (e x) () := by
    intro x
    simp only [Matrix.mul_apply, vertexIncoming, Matrix.of_apply]
    refine selectedSuffix_inverse_transport _ _ _
      (c.originalResponseInterval_residue_blockTriangular P (some b) (some t)) _ e hN _ _ ?_ x
    intro j
    rfl
  refine selectedSuffix_sum_eq_of_zero_off
    (fun x : OriginalResponseInterval (hD := hD) P (some b) (some t) =>
      (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P x.1.1.1.val : ℤ))
    e _ _ ?_ ?_
  · intro x hx
    exact ite_eq_right (absent x hx)
  · intro x
    dsimp only
    by_cases h : (originalResponseCols (hD := hD) P x.1.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))).toNat = k
    · have h2 : (originalResponseCols (hD := hD) P (e x).1.1 -
          P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))).toNat = k := h
      rw [ite_eq_left h, ite_eq_left h2, hv x]
    · have h2 : ¬ (originalResponseCols (hD := hD) P (e x).1.1 -
          P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some t)))).toNat = k := h
      rw [ite_eq_right h, ite_eq_right h2]

end SkewCornerDescent.Matrix.SelectedCoordinate
