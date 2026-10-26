/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleProfileCoefficients
import SkewCornerDescent.Matrix.OriginalWindowUnitBlocks
import SkewCornerDescent.Matrix.OriginalIntervalProtectedTops
import SkewCornerDescent.Matrix.ProtectedUnitBoundary

/-!
# Protected full incoming coefficients of actual empty pivots

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The actual empty block retains one unit pivot. Complete original block order
produces its genuine prefix inverse, all lower-generator support, and its
monic protected incoming coordinate. The corresponding full endpoint-profile
coefficient has leading coefficient minus one. No inverse entry or positive
component realization is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A literal empty pivot in a selected-start interval has its actual monic
protected incoming coordinate. The complete earlier-block inverse is retained;
no positive-span component or supplied inverse match is used. -/
theorem original_empty_interval_incoming_top {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (k : OriginalResponseInterval (hD := hD) P (some a) d)
    (hempty : P.xi k.1.1.1.val.succ = P.zeta k.1.1.1.val.castSucc) :
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    let m := P.xi k.1.1.1.val.succ
    let row := fun i : OriginalResponseInterval (hD := hD) P (some a) d =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P (some a) d =>
      originalResponseCols P i.1.1
    ∃ J : ℕ+, (J : ℤ) = x - m ∧ ∃ hJ : c.top < J,
      ∃ R ∈ residueLowerField c.top J,
        (vertexOutgoing c.residueMap col x * (vertexBetaMatrix c.residueMap row col)⁻¹) () k =
          residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  classical
  let ν := OriginalResponseInterval (hD := hD) P (some a) d
  let u := k.1.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let m := P.xi u.val.succ
  let row := fun i : ν => originalResponseRows P i.1.1
  let col := fun i : ν => originalResponseCols P i.1.1
  have hkrow : row k = m := (originalEmptyBlock_remaining_endpoints P u hempty k.1.1.2).1
  have hkcol : col k = m :=
    ((originalEmptyBlock_remaining_endpoints P u hempty k.1.1.2).2).trans hempty.symm
  have hs : ¬ originalBlockSelected (hD := hD) P u :=
    not_dvd_originalEmptyBlock (hD := hD) P u.val hempty
  have hab : interiorBlock P a.val.val < interiorBlock P u.val := by
    have hl := k.2
    change (interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P u.val : ℤ) at hl
    have hn : a.val ≠ u := by intro he; exact hs (he ▸ a.property)
    have hne : interiorBlock P a.val.val ≠ interiorBlock P u.val := by
      intro he
      exact hn ((originalBlocks_label_strictMono P).injective he)
    omega
  have hHigh := c.original_row_distance_gt_top_of_later_block P a k.1.1 hab
  change (c.top : ℤ) < x - row k at hHigh
  rw [hkrow] at hHigh
  let J := higherIndexFromInteger c.top (x - m) hHigh
  have hJe : (J.val : ℤ) = x - m := higherIndexFromInteger_coe _ _ _
  let M := vertexBetaMatrix c.residueMap row col
  let := c.originalResponseResidueIntervalInverse P (some a) d
  let label := fun i : ν => i.1.1.1.val.val
  let cut := label k + 1
  have hM : M.BlockTriangular label := by
    intro i j hij
    apply c.originalResponse_residue_blockTriangular P
    have hblock : j.1.1.1 < i.1.1.1 := hij
    have h := originalBlocks_label_strictMono P hblock
    change (interiorBlock P j.1.1.1.val : ℤ) < (interiorBlock P i.1.1.1.val : ℤ)
    exact_mod_cast h
  let μ := {i : ν // label i < cut}
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : μ => row i.val) (fun i : μ => col i.val)) := by
    change Invertible (M.toBlock (fun i => label i < cut) (fun i => label i < cut))
    exact hM.invertibleToBlock cut
  let kk : μ := ⟨k, Nat.lt_succ_self _⟩
  have hrow (i : μ) : row i.val < x := originalResponse_row_lt P (some a) i.val.1.1 i.val.2
  have hcol (i : μ) : m ≤ col i.val := by
    by_cases he : i.val.1.1.1 = u
    · have hi : P.xi i.val.1.1.1.val.succ = P.zeta i.val.1.1.1.val.castSucc := he.symm ▸ hempty
      have hc := (originalEmptyBlock_remaining_endpoints P i.val.1.1.1 hi i.val.1.1.2).2
      change col i.val = P.zeta i.val.1.1.1.val.castSucc at hc
      rw [he, ← hempty] at hc
      exact le_of_eq hc.symm
    · have hne : i.val.1.1.1.val.val ≠ u.val.val := by
        intro h
        exact he (Subtype.ext (Fin.ext h))
      have hlt : i.val.1.1.1 < u := by
        have hp := i.property
        change i.val.1.1.1.val.val < u.val.val
        change i.val.1.1.1.val.val < u.val.val + 1 at hp
        omega
      have hh := original_remaining_beta_separated (hD := hD) P u i.val.1.1.1 hlt
        k.1.1.2 i.val.1.1.2
      change row k < col i.val at hh
      rw [hkrow] at hh
      exact hh.le
  have hcolinj : Function.Injective col := by
    intro i j he
    exact Subtype.ext (Subtype.ext (original_response_cols_injective (hD := hD) P he))
  obtain ⟨R, hR, hvalue⟩ := c.protected_unit_incoming
    (fun i : μ => row i.val) (fun i : μ => col i.val) x m kk hkrow hkcol
    (by intro i j he; exact Subtype.ext (hcolinj he)) hrow hcol J.val J.property hJe
  refine ⟨J.val, hJe, J.property, R, hR, ?_⟩
  rw [Matrix.mul_apply] at hvalue ⊢
  change (∑ i : ν, c.residueMap (hh (x - col i)) * M⁻¹ i k) = _ + R
  rw [incoming_inverse_prefix _ M label hM cut k (Nat.lt_succ_self _)]
  exact hvalue

/-- A literal empty pivot has a nonzero protected leading term in its complete
incoming endpoint polynomial, at its actual original positive distance. -/
theorem original_empty_left_profile_top {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (k : OriginalResponseInterval (hD := hD) P (some a) d)
    (hempty : P.xi k.1.1.1.val.succ = P.zeta k.1.1.1.val.castSucc) :
    ∃ J : ℕ+, (J : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        P.xi k.1.1.1.val.succ ∧
      ∃ hJ : c.top < J, ∃ R ∈ residueLowerField c.top J,
        (c.originalResidueLeftEndpointPolynomial P (some a) d).coeff J =
          -residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  obtain ⟨J, hJe, hJ, R, hR, hvalue⟩ :=
    c.original_empty_interval_incoming_top P a d k hempty
  refine ⟨J, hJe, hJ, -R, (residueLowerField c.top J).neg_mem hR, ?_⟩
  have hcoeff := c.original_left_profile_coeff_at_row P (some a) d k
  have hr := (originalEmptyBlock_remaining_endpoints P k.1.1.1 hempty k.1.1.2).1
  have hdegree :
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        originalResponseRows P k.1.1).toNat = (J : ℕ) := by
    change (_ - P.xi (originalRemovedRow P k.1.1.1 k.1.1.2).succ).toNat = _
    rw [hr, ← hJe]
    simp
  dsimp only at hcoeff hvalue
  rw [hdegree, hvalue] at hcoeff
  simpa only [neg_add] using hcoeff

end SkewCornerDescent.Matrix.SelectedCoordinate
