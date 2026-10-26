/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEmptyIncomingTop

/-!
# Protected full outgoing coefficients of actual empty pivots

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual original block order produces the complete suffix inverse, including
the unit pivot itself. Exact unit-boundary transpose duality supplies its
monic protected outgoing coordinate and the full endpoint coefficient with
leading coefficient minus one. No inverse match is a hypothesis. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A literal empty pivot in a selected-end interval has its actual monic
protected outgoing coordinate, with its full genuine suffix inverse retained. -/
theorem original_empty_interval_outgoing_top {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (k : OriginalResponseInterval (hD := hD) P b (some d))
    (hempty : P.xi k.1.1.1.val.succ = P.zeta k.1.1.1.val.castSucc) :
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
    let m := P.xi k.1.1.1.val.succ
    let row := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
      originalResponseCols P i.1.1
    ∃ J : ℕ+, (J : ℤ) = m - y ∧ ∃ hJ : c.top < J,
      ∃ R ∈ residueLowerField c.top J,
        ((vertexBetaMatrix c.residueMap row col)⁻¹ * vertexIncoming c.residueMap row y) k () =
          residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  classical
  let ν := OriginalResponseInterval (hD := hD) P b (some d)
  let u := k.1.1.1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  let m := P.xi u.val.succ
  let row := fun i : ν => originalResponseRows P i.1.1
  let col := fun i : ν => originalResponseCols P i.1.1
  have hkrow : row k = m := (originalEmptyBlock_remaining_endpoints P u hempty k.1.1.2).1
  have hkcol : col k = m :=
    ((originalEmptyBlock_remaining_endpoints P u hempty k.1.1.2).2).trans hempty.symm
  have hs : ¬ originalBlockSelected (hD := hD) P u :=
    not_dvd_originalEmptyBlock (hD := hD) P u.val hempty
  have hud : interiorBlock P u.val < interiorBlock P d.val.val := by
    have hl := k.1.2
    change (interiorBlock P u.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1 at hl
    have hn : u ≠ d.val := by intro he; exact hs (he.symm ▸ d.property)
    have hne : interiorBlock P u.val ≠ interiorBlock P d.val.val := by
      intro he
      exact hn ((originalBlocks_label_strictMono P).injective he)
    omega
  have hHigh := c.original_col_distance_gt_top_of_earlier_block P d k.1.1 hud
  change (c.top : ℤ) < col k - y at hHigh
  rw [hkcol] at hHigh
  let J := higherIndexFromInteger c.top (m - y) hHigh
  have hJe : (J.val : ℤ) = m - y := higherIndexFromInteger_coe _ _ _
  let M := vertexBetaMatrix c.residueMap row col
  let := c.originalResponseResidueIntervalInverse P b (some d)
  let label := fun i : ν => (i.1.1.1.val.val : ℤ)
  let cut := label k - 1
  have hM : M.BlockTriangular label := by
    intro i j hij
    apply c.originalResponse_residue_blockTriangular P
    have hblock : j.1.1.1 < i.1.1.1 := by
      change j.1.1.1.val.val < i.1.1.1.val.val
      change (j.1.1.1.val.val : ℤ) < (i.1.1.1.val.val : ℤ) at hij
      exact_mod_cast hij
    have h := originalBlocks_label_strictMono P hblock
    change (interiorBlock P j.1.1.1.val : ℤ) < (interiorBlock P i.1.1.1.val : ℤ)
    exact_mod_cast h
  let μ := {i : ν // cut < label i}
  let N := M.toBlock (fun i => cut < label i) (fun i => cut < label i)
  let : Invertible N.transpose := hM.transpose.invertibleToBlock (OrderDual.toDual cut)
  let : Invertible N := Matrix.invertibleOfInvertibleTranspose N
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : μ => row i.val) (fun i : μ => col i.val)) := by
    change Invertible N
    infer_instance
  let kk : μ := ⟨k, by dsimp only [cut]; omega⟩
  have hcol (i : μ) : y < col i.val :=
    originalResponse_col_gt P (some d) i.val.1.1 i.val.1.2
  have hrow (i : μ) : row i.val ≤ m := by
    by_cases he : i.val.1.1.1 = u
    · have hi : P.xi i.val.1.1.1.val.succ = P.zeta i.val.1.1.1.val.castSucc := he.symm ▸ hempty
      have hr := (originalEmptyBlock_remaining_endpoints P i.val.1.1.1 hi i.val.1.1.2).1
      change row i.val = P.xi i.val.1.1.1.val.succ at hr
      rw [he] at hr
      exact le_of_eq hr
    · have hne : i.val.1.1.1.val.val ≠ u.val.val := by
        intro h
        exact he (Subtype.ext (Fin.ext h))
      have hlt : u < i.val.1.1.1 := by
        have hp := i.property
        change u.val.val < i.val.1.1.1.val.val
        change (u.val.val : ℤ) - 1 < (i.val.1.1.1.val.val : ℤ) at hp
        omega
      have hh := original_remaining_beta_separated (hD := hD) P i.val.1.1.1 u hlt
        i.val.1.1.2 k.1.1.2
      change row i.val < col k at hh
      rw [hkcol] at hh
      exact hh.le
  have hrowinj : Function.Injective row := by
    intro i j he
    exact Subtype.ext (Subtype.ext (original_response_rows_injective (hD := hD) P he))
  obtain ⟨R, hR, hvalue⟩ := c.protected_unit_outgoing
    (fun i : μ => row i.val) (fun i : μ => col i.val) m y kk hkrow hkcol
    (by intro i j he; exact Subtype.ext (hrowinj he)) hrow hcol J.val J.property hJe
  refine ⟨J.val, hJe, J.property, R, hR, ?_⟩
  rw [Matrix.mul_apply] at hvalue ⊢
  change (∑ i : ν, M⁻¹ k i * c.residueMap (hh (row i - y))) = _ + R
  rw [outgoing_inverse_suffix _ M label hM cut k (by dsimp only [cut]; omega)]
  exact hvalue

/-- The actual full outgoing profile coefficient has protected leading
coefficient minus one at a literal empty pivot's own positive distance. -/
theorem original_empty_right_profile_top {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (k : OriginalResponseInterval (hD := hD) P b (some d))
    (hempty : P.xi k.1.1.1.val.succ = P.zeta k.1.1.1.val.castSucc) :
    ∃ J : ℕ+, (J : ℤ) = P.xi k.1.1.1.val.succ -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) ∧
      ∃ hJ : c.top < J, ∃ R ∈ residueLowerField c.top J,
        (c.originalResidueRightEndpointPolynomial P b (some d)).coeff J =
          -residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  obtain ⟨J, hJe, hJ, R, hR, hvalue⟩ :=
    c.original_empty_interval_outgoing_top P b d k hempty
  refine ⟨J, hJe, hJ, -R, (residueLowerField c.top J).neg_mem hR, ?_⟩
  have hcoeff := c.original_right_profile_coeff_at_col P b (some d) k
  have hc := (originalEmptyBlock_remaining_endpoints P k.1.1.1 hempty k.1.1.2).2
  have hdegree :
      (originalResponseCols P k.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))).toNat = (J : ℕ) := by
    change (P.zeta (originalRemovedCol P k.1.1.1 k.1.1.2).castSucc - _).toNat = _
    rw [hc, ← hempty, ← hJe]
    simp
  dsimp only at hcoeff hvalue
  rw [hdegree, hvalue] at hcoeff
  simpa only [neg_add] using hcoeff

end SkewCornerDescent.Matrix.SelectedCoordinate
