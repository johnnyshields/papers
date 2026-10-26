/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalUnitEquivalence
import SkewCornerDescent.Matrix.OrderedProfileLocality

/-!
# Actual retained outgoing coefficients in complete suffix coordinates

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The actual block order removes only earlier blocks. The complete current/suffix
bijection identifies the remaining inverse with its ordered consumer, retaining
all later-block couplings and excluding unrelated exterior source blocks.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full actual outgoing value equals the complete current/suffix value.
The original interval supplies triangularity and every retained index. -/
theorem original_interval_outgoing_suffix_value {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d)
    (y : ℤ) (j : Fin (interiorBlockLength P u.val + 1)) :
    let row := fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseCols P i.1.1
    ((vertexBetaMatrix c.residueMap row col)⁻¹ * vertexIncoming c.residueMap row y)
      (originalIntervalUnitIndex P b d u hs hu j) () =
    ((vertexBetaMatrix c.residueMap
      (Sum.elim (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u)
        (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u =>
          originalResponseRows P i.1.1.1))
      (Sum.elim (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u)
        (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u =>
          originalResponseCols P i.1.1.1)))⁻¹ *
      vertexIncoming c.residueMap
        (Sum.elim (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u)
          (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u =>
            originalResponseRows P i.1.1.1)) y) (.inl j) () := by
  classical
  let row := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun i : OriginalResponseInterval (hD := hD) P b d => (i.1.1.1.val.val : ℤ)
  let k := originalIntervalUnitIndex P b d u hs hu j
  let := c.originalResponseResidueIntervalInverse P b d
  have hM : M.BlockTriangular label := by
    intro i l hil
    dsimp only [label] at hil
    apply c.originalResponse_residue_blockTriangular P
    have hblock : l.1.1.1 < i.1.1.1 := by
      change l.1.1.1.val.val < i.1.1.1.val.val
      exact_mod_cast hil
    have h := originalBlocks_label_strictMono P hblock
    change (interiorBlock P l.1.1.1.val : ℤ) < (interiorBlock P i.1.1.1.val : ℤ)
    exact_mod_cast h
  let cut := (u.val.val : ℤ) - 1
  have hk : cut < label k := by
    change (u.val.val : ℤ) - 1 < (u.val.val : ℤ)
    omega
  let e := (originalIntervalUnitSuffixEquiv P b d u hs hu).trans
    (Equiv.subtypeEquivRight (fun i => show u ≤ i.1.1.1 ↔ cut < label i from by
      change u.val.val ≤ i.1.1.1.val.val ↔ (u.val.val : ℤ) - 1 < (i.1.1.1.val.val : ℤ)
      omega))
  let N := M.toBlock (fun i => cut < label i) (fun i => cut < label i)
  have hmat : N.submatrix e e = M.submatrix
      (originalIntervalUnitSuffixIndex P b d u hs hu)
      (originalIntervalUnitSuffixIndex P b d u hs hu) := by
    ext i l
    rfl
  have hrow (i) : row (e i).val =
      Sum.elim (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u)
        (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u =>
          originalResponseRows P i.1.1.1) i := by
    cases i with
    | inl i => exact (original_unit_component_beta P u hs hne i).1
    | inr i => rfl
  rw [Matrix.mul_apply]
  change (∑ i, M⁻¹ k i * c.residueMap (hh (row i - y))) = _
  rw [outgoing_inverse_suffix _ M label hM cut k hk]
  have he := Fintype.sum_equiv e
    (fun i => N⁻¹ ⟨k, hk⟩ (e i) * c.residueMap (hh (row (e i).val - y)))
    (fun i => N⁻¹ ⟨k, hk⟩ i * c.residueMap (hh (row i.val - y)))
    (fun _ => rfl)
  rw [← he]
  have hpoint : e (.inl j) = ⟨k, hk⟩ := Subtype.ext rfl
  rw [← hpoint]
  have hinv := Matrix.inv_submatrix_equiv N e e
  have hshape := c.original_interval_unit_suffix_matrix P b d u hs hne hu
  change M.submatrix _ _ = _ at hshape
  rw [← hmat] at hshape
  apply Finset.sum_congr rfl
  intro i _
  rw [hrow]
  have hi := congrFun (congrFun hinv (.inl j)) i
  change (N.submatrix e e)⁻¹ (.inl j) i = N⁻¹ (e (.inl j)) (e i) at hi
  rw [← hi, hshape]
  rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
