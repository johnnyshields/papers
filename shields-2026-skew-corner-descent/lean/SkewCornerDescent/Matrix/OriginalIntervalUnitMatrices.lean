/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalUnitComponents
import SkewCornerDescent.Matrix.OrderedComponentProfileTops

/-!
# Complete original interval prefix/current and current/suffix matrix bridges

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The actual retained interval supplies every index of its known prefix and suffix.
Literal full component coordinates identify both complete matrices; source-produced
separation and inverses supply the combined inverse. No exterior block is imported.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual interval indices of the known prefix followed by the complete current component. -/
def originalIntervalUnitPrefixIndex {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    OriginalIntervalUnitPrefix (hD := hD) P b d u ⊕ Fin (interiorBlockLength P u.val + 1) →
      OriginalResponseInterval (hD := hD) P b d :=
  Sum.elim Subtype.val (originalIntervalUnitIndex P b d u hs hu)

/-- Actual interval indices of the complete current component followed by its known suffix. -/
def originalIntervalUnitSuffixIndex {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    Fin (interiorBlockLength P u.val + 1) ⊕ OriginalIntervalUnitSuffix (hD := hD) P b d u →
      OriginalResponseInterval (hD := hD) P b d :=
  Sum.elim (originalIntervalUnitIndex P b d u hs hu) Subtype.val

/-- The complete actual prefix/current interval submatrix has the exact ordered consumer shape. -/
theorem original_interval_unit_prefix_matrix {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    (vertexBetaMatrix c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)).submatrix
        (originalIntervalUnitPrefixIndex P b d u hs hu)
        (originalIntervalUnitPrefixIndex P b d u hs hu) =
    vertexBetaMatrix c.residueMap
      (Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
        originalResponseRows P i.1.1.1)
        (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u))
      (Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
        originalResponseCols P i.1.1.1)
        (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u)) := by
  have hx i := (original_unit_component_beta P u hs hne i).1
  have hz i := (original_unit_component_beta P u hs hne i).2
  ext i j : 1
  cases i <;> cases j <;>
    simp only [vertexBetaMatrix, Matrix.of_apply, Matrix.submatrix_apply,
      originalIntervalUnitPrefixIndex, Sum.elim_inl, Sum.elim_inr,
      originalIntervalUnitIndex, originalResponseRows, originalResponseCols, hx, hz]

/-- The complete actual current/suffix submatrix has the exact dual consumer shape. -/
theorem original_interval_unit_suffix_matrix {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    (vertexBetaMatrix c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)).submatrix
        (originalIntervalUnitSuffixIndex P b d u hs hu)
        (originalIntervalUnitSuffixIndex P b d u hs hu) =
    vertexBetaMatrix c.residueMap
      (Sum.elim (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u)
        (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u => originalResponseRows P i.1.1.1))
      (Sum.elim (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u)
        (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u =>
          originalResponseCols P i.1.1.1)) := by
  have hx i := (original_unit_component_beta P u hs hne i).1
  have hz i := (original_unit_component_beta P u hs hne i).2
  ext i j : 1
  cases i <;> cases j <;>
    simp only [vertexBetaMatrix, Matrix.of_apply, Matrix.submatrix_apply,
      originalIntervalUnitSuffixIndex, Sum.elim_inl, Sum.elim_inr,
      originalIntervalUnitIndex, originalResponseRows, originalResponseCols, hx, hz]

/-- The source-produced actual prefix inverse and full nonselected component inverse
supply the complete combined inverse, with all cross-component entries retained. -/
@[instance_reducible]
def originalIntervalUnitPrefixCurrentInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ) :
    Invertible (vertexBetaMatrix c.residueMap
      (Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
        originalResponseRows P i.1.1.1)
        (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u))
      (Sum.elim (fun i : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
        originalResponseCols P i.1.1.1)
        (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u))) := by
  let := c.originalIntervalUnitPrefixInverse P b d u
  exact c.orderedComponentPrefixInverse (interiorBlockProfile P u.val hne)
    (original_unit_component_schur_ne P u hs hne) _ _ (originalComponentTau P u)
    (fun i j => original_interval_unit_prefix_separation P b d u hs hne i j)

/-- The dual combined inverse is supplied by the actual suffix and current full component. -/
@[instance_reducible]
def originalIntervalUnitCurrentSuffixInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ) :
    Invertible (vertexBetaMatrix c.residueMap
      (Sum.elim (fun i => (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u)
        (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u => originalResponseRows P i.1.1.1))
      (Sum.elim (fun i => (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u)
        (fun i : OriginalIntervalUnitSuffix (hD := hD) P b d u =>
          originalResponseCols P i.1.1.1))) := by
  let := c.originalIntervalUnitSuffixInverse P b d u
  exact c.orderedComponentSuffixInverse (interiorBlockProfile P u.val hne)
    (original_unit_component_schur_ne P u hs hne) _ _ (originalComponentTau P u)
    (fun j i => original_interval_unit_suffix_separation P b d u hs hne i j)

end SkewCornerDescent.Matrix.SelectedCoordinate
