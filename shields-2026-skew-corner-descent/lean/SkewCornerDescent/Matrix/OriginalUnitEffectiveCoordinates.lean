/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitComponentInverse
import SkewCornerDescent.Matrix.OrderedComponentRowRecovery

/-!
# Effective coordinates from complete actual unit-component endpoint matrices

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The original component supplies the literal beta lists, separation, Schur mismatch,
and genuine prefix/suffix inverse. The protected-distance condition remains explicit
until the chosen endpoint's geometric distance producer supplies it. Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Incoming coefficients of the complete actual prefix/current matrix expand in the
full effective coordinates. Every matrix, inverse and component comparison is produced. -/
theorem original_unit_effective_incoming {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ) (x : ℤ)
    (hhigh : ∀ k, (c.top : ℤ) < x -
      ((interiorBlockProfile P b.val hne).zeta k + originalComponentTau P b))
    (j : Fin (interiorBlockLength P b.val + 1)) :
    let Q := interiorBlockProfile P b.val hne
    let row := fun i : OriginalUnitPrefix (hD := hD) P b => originalRemainingRowBeta P i.val
    let col := fun i : OriginalUnitPrefix (hD := hD) P b => originalRemainingColBeta P i.val
    let cols := Sum.elim col (fun i => Q.zeta i + originalComponentTau P b)
    let M := ((originalRemovedMatrix (hD := hD) P).map c.residueMap).submatrix
      (originalUnitPrefixIndex P b hs) (originalUnitPrefixIndex P b hs)
    letI := c.originalUnitPrefixInverse P b
    (vertexOutgoing c.residueMap cols x * M⁻¹) () (.inr j) =
      ∑ k, c.effectiveIncomingCoordinate row col x
        (higherIndexFromInteger c.top (x - (Q.zeta k + originalComponentTau P b)) (hhigh k)) *
          ((jtMatrix Q.xi Q.zeta).map c.residueMap)⁻¹ k j := by
  classical
  dsimp only
  rw [original_unit_prefix_matrix c.residueMap P b hs hne]
  let := c.originalUnitPrefixInverse P b
  have key := c.ordered_component_effective_incoming
    (interiorBlockProfile P b.val hne) (original_unit_component_schur_ne P b hs hne)
    (fun i : OriginalUnitPrefix (hD := hD) P b => originalRemainingRowBeta P i.val)
    (fun i : OriginalUnitPrefix (hD := hD) P b => originalRemainingColBeta P i.val)
    x (originalComponentTau P b)
    (fun i k => original_unit_prefix_separation P b hs hne i k) hhigh j
  simpa only [Matrix.invOf_eq_nonsing_inv] using key

/-- Outgoing coefficients of the complete actual current/suffix matrix use every later
coupling. The suffix inverse is produced from complete original blocks. -/
theorem original_unit_effective_outgoing {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ) (y : ℤ)
    (hhigh : ∀ k, (c.top : ℤ) <
      (interiorBlockProfile P b.val hne).xi k + originalComponentTau P b - y)
    (i : Fin (interiorBlockLength P b.val + 1)) :
    let Q := interiorBlockProfile P b.val hne
    let row := fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingRowBeta P j.val
    let col := fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingColBeta P j.val
    let rows := Sum.elim (fun j => Q.xi j + originalComponentTau P b) row
    let M := ((originalRemovedMatrix (hD := hD) P).map c.residueMap).submatrix
      (originalUnitSuffixIndex P b hs) (originalUnitSuffixIndex P b hs)
    letI := c.originalUnitSuffixInverse P b
    (M⁻¹ * vertexIncoming c.residueMap rows y) (.inl i) () =
      ∑ k, ((jtMatrix Q.xi Q.zeta).map c.residueMap)⁻¹ i k *
        c.effectiveOutgoingCoordinate row col y
          (higherIndexFromInteger c.top (Q.xi k + originalComponentTau P b - y) (hhigh k)) := by
  classical
  dsimp only
  rw [original_unit_suffix_matrix c.residueMap P b hs hne]
  let := c.originalUnitSuffixInverse P b
  have key := c.ordered_component_effective_outgoing
    (interiorBlockProfile P b.val hne) (original_unit_component_schur_ne P b hs hne)
    (fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingRowBeta P j.val)
    (fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingColBeta P j.val)
    y (originalComponentTau P b)
    (fun j k => original_unit_suffix_separation P b hs hne k j) hhigh i
  simpa only [Matrix.invOf_eq_nonsing_inv] using key

end SkewCornerDescent.Matrix.SelectedCoordinate
