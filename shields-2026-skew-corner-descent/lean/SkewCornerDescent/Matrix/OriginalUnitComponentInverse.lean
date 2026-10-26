/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitComponentOrder
import SkewCornerDescent.Matrix.OriginalRemovalRegularity
import SkewCornerDescent.Matrix.BlockSubsetInverse

/-!
# Genuine inverses of original unit-component prefixes and suffixes

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Complete-block restriction of the actual removed matrix supplies each endpoint inverse.
The component's nonselection supplies its nonzero residue determinant; no inverse,
Schur mismatch, or diagonal regularity premise is added by the caller. Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Nonselection of the actual component rules out equality to the selected Schur prime. -/
theorem original_unit_component_schur_ne {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ) :
    cellSchur D hD.1 ≠ (interiorBlockProfile P b.val hne).schur := by
  intro he
  apply hs
  unfold originalBlockSelected
  rw [interior_block_det_eq_profile P b.val hne, ← he]

/-- The original full residue matrix supplies triangularity in canonical component order. -/
theorem original_removed_residue_triangular {n : ℕ} (P : Profile n) :
    ((originalRemovedMatrix (hD := hD) P).map c.residueMap).BlockTriangular Sigma.fst := by
  intro i j hij
  change c.residueMap (originalRemovedMatrix (hD := hD) P i j) = 0
  rw [originalRemovedMatrix_blockTriangular_fst P hij, map_zero]

/-- Genuine inverse of the entire original prefix, including all cross-component entries. -/
@[instance_reducible]
def originalUnitPrefixInverse {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun j : OriginalUnitPrefix (hD := hD) P b => originalRemainingRowBeta P j.val)
      (fun j : OriginalUnitPrefix (hD := hD) P b => originalRemainingColBeta P j.val)) := by
  letI := c.originalRemovedResidueInverse P
  exact blockTriangularKeptInverse ((originalRemovedMatrix (hD := hD) P).map c.residueMap)
    Sigma.fst (c.original_removed_residue_triangular P) (fun d => d < b)

/-- Genuine inverse of the entire original suffix, not a diagonal-only substitute. -/
@[instance_reducible]
def originalUnitSuffixInverse {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingRowBeta P j.val)
      (fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingColBeta P j.val)) := by
  letI := c.originalRemovedResidueInverse P
  exact blockTriangularKeptInverse ((originalRemovedMatrix (hD := hD) P).map c.residueMap)
    Sigma.fst (c.original_removed_residue_triangular P) (fun d => b < d)

end SkewCornerDescent.Matrix.SelectedCoordinate
