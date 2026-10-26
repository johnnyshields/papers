/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BlockSubsetInverse
import SkewCornerDescent.Matrix.OriginalPrivateEndpointSeparation
import SkewCornerDescent.Matrix.OriginalWindowResponseIntervals

/-!
# Actual interval inverses after retaining complete original blocks

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The unchanged source supplies the full interval inverse and its canonical
triangular block order. Every retained diagonal remains invertible, including
empty blocks and complete nonrow units. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every complete-block selection from the actual original interval receives
its own genuine inverse. No determinant or inverse-entry premise is supplied. -/
@[instance_reducible]
noncomputable def originalIntervalKeptBlockInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (keep : OriginalBlocks P → Prop) [DecidablePred keep] :
    letI := c.originalResponseResidueIntervalInverse P b d
    let row := fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseCols P i.1.1
    Invertible ((vertexBetaMatrix c.residueMap row col).toBlock
      (fun i => keep i.1.1.1) (fun i => keep i.1.1.1)) := by
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseCols P i.1.1
  let label := fun i : OriginalResponseInterval (hD := hD) P b d => i.1.1.1
  have hM : (vertexBetaMatrix c.residueMap row col).BlockTriangular label := by
    intro i j hij
    apply c.originalResponse_residue_blockTriangular P
    dsimp only
    have h := originalBlocks_label_strictMono P hij
    exact_mod_cast h
  exact blockTriangularKeptInverse (vertexBetaMatrix c.residueMap row col) label hM keep

/-- Removing the one actual private unit retains complete original blocks and
therefore produces the full old inverse required by the insertion formula. -/
@[instance_reducible]
noncomputable def originalIntervalWithoutPrivateUnitInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (u : OriginalResponseInterval (hD := hD) P b d)
    (hunit : originalResponseRows P u.1.1 = k ∧ originalResponseCols P u.1.1 = k) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun i : {i : OriginalResponseInterval (hD := hD) P b d //
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
          originalResponseRows P i.val.1.1)
      (fun i : {i : OriginalResponseInterval (hD := hD) P b d //
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
          originalResponseCols P i.val.1.1)) := by
  classical
  let a : OriginalBlocks P := u.1.1.1
  let keep := fun t : OriginalBlocks P => t ≠ a
  have hp (i : OriginalResponseInterval (hD := hD) P b d) :
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k) ↔
        keep i.1.1.1 := by
    constructor
    · intro hi he
      apply hi
      have he' := originalRemaining_private_unit_block_singleton P k hcur hprev
        u.1.1 hunit i.1.1 (congrArg (fun t : OriginalBlocks P => interiorBlock P t.val) he)
      rw [he']
      exact hunit
    · intro hi he
      apply hi
      have he' := originalRemaining_private_unit_unique P k i.1.1 u.1.1 he hunit
      exact congrArg (fun j : OriginalRemainingIndices (hD := hD) P => j.1) he'
  let e : {i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} ≃
      {i : OriginalResponseInterval (hD := hD) P b d // keep i.1.1.1} :=
    Equiv.subtypeEquivRight hp
  let := c.originalResponseResidueIntervalInverse P b d
  let := c.originalIntervalKeptBlockInverse P b d keep
  let row := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d =>
    originalResponseCols P i.1.1
  let M := (vertexBetaMatrix c.residueMap row col).toBlock
    (fun i => keep i.1.1.1) (fun i => keep i.1.1.1)
  have he : vertexBetaMatrix c.residueMap
      (fun i => originalResponseRows P i.val.1.1)
      (fun i => originalResponseCols P i.val.1.1) = M.submatrix e e := by
    apply Matrix.ext
    intro i j
    rfl
  rw [he]
  exact Matrix.submatrixEquivInvertible M e e

end SkewCornerDescent.Matrix.SelectedCoordinate
