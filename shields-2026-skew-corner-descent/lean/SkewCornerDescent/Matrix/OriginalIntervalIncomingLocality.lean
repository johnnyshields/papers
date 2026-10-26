/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalUnitEquivalence
import SkewCornerDescent.Matrix.OrderedProfileLocality

/-!
# Actual retained incoming coefficients in complete prefix coordinates

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The original interval's triangular block order removes only later blocks.
The proved full prefix/current equivalence then identifies every retained inverse
entry with the ordered component consumer, including all earlier couplings.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full original interval incoming value at a current-component row is exactly
its complete ordered prefix/current value. No inverse-entry equality is assumed. -/
theorem original_interval_incoming_prefix_value {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d)
    (x : ℤ) (j : Fin (interiorBlockLength P u.val + 1)) :
    let row := fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseCols P i.1.1
    (vertexOutgoing c.residueMap col x * (vertexBetaMatrix c.residueMap row col)⁻¹)
      () (originalIntervalUnitIndex P b d u hs hu j) =
    (vertexOutgoing c.residueMap
      (Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
        originalResponseCols P i.1.1.1)
        (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u)) x *
      (vertexBetaMatrix c.residueMap
        (Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
          originalResponseRows P i.1.1.1)
          (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u))
        (Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
          originalResponseCols P i.1.1.1)
          (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u)))⁻¹)
      () (.inr j) := by
  classical
  let row := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun i : OriginalResponseInterval (hD := hD) P b d => i.1.1.1.val.val
  let k := originalIntervalUnitIndex P b d u hs hu j
  let := c.originalResponseResidueIntervalInverse P b d
  have hM : M.BlockTriangular label := by
    intro i l hil
    apply c.originalResponse_residue_blockTriangular P
    have hblock : l.1.1.1 < i.1.1.1 := hil
    have h := originalBlocks_label_strictMono P hblock
    change (interiorBlock P l.1.1.1.val : ℤ) < (interiorBlock P i.1.1.1.val : ℤ)
    exact_mod_cast h
  let cut := u.val.val + 1
  have hk : label k < cut := Nat.lt_succ_self _
  let e := (originalIntervalUnitPrefixEquiv P b d u hs hu).trans
    (Equiv.subtypeEquivRight (fun i => show i.1.1.1 ≤ u ↔ label i < cut from by
      change i.1.1.1.val.val ≤ u.val.val ↔ i.1.1.1.val.val < u.val.val + 1
      omega))
  let N := M.toBlock (fun i => label i < cut) (fun i => label i < cut)
  have hmat : N.submatrix e e = M.submatrix
      (originalIntervalUnitPrefixIndex P b d u hs hu)
      (originalIntervalUnitPrefixIndex P b d u hs hu) := by
    ext i l
    rfl
  have hcol (i) : col (e i).val =
      Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
        originalResponseCols P i.1.1.1)
        (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u) i := by
    cases i with
    | inl i => rfl
    | inr i => exact (original_unit_component_beta P u hs hne i).2
  rw [Matrix.mul_apply]
  change (∑ i, c.residueMap (hh (x - col i)) * M⁻¹ i k) = _
  rw [incoming_inverse_prefix _ M label hM cut k hk]
  have he := Fintype.sum_equiv e
    (fun i => c.residueMap (hh (x - col (e i).val)) * N⁻¹ (e i) ⟨k, hk⟩)
    (fun i => c.residueMap (hh (x - col i.val)) * N⁻¹ i ⟨k, hk⟩)
    (fun _ => rfl)
  rw [← he]
  have hpoint : e (.inr j) = ⟨k, hk⟩ := Subtype.ext rfl
  rw [← hpoint]
  have hinv := Matrix.inv_submatrix_equiv N e e
  have hshape := c.original_interval_unit_prefix_matrix P b d u hs hne hu
  change M.submatrix _ _ = _ at hshape
  rw [← hmat] at hshape
  apply Finset.sum_congr rfl
  intro i _
  rw [hcol]
  have hi := congrFun (congrFun hinv i) (.inr j)
  change (N.submatrix e e)⁻¹ i (.inr j) = N⁻¹ (e i) (e (.inr j)) at hi
  rw [← hi, hshape]
  rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
