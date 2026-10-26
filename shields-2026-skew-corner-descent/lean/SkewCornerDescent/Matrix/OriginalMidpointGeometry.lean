/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNonmidpointInterval
import SkewCornerDescent.Matrix.OriginalIntervalBlockSubsetInverse

/-!
# Genuine original geometry and inverse after midpoint removal

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Removing a literal midpoint vertex retains complete original blocks.
The source supplies the punctured matrix inverse and strict separation of
every remaining original row and column to one side of that vertex.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Midpoint removal retains or excludes a whole original block, not selected
entries of a genuine inverse.  An empty block has just one original coordinate. -/
theorem original_interval_midpoint_block_iff {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (q : OriginalResponseInterval (hD := hD) P (some a) (some b)) :
    originalIntervalMidpointVertex P a b q ↔
      P.xi q.1.1.1.val.succ = P.zeta q.1.1.1.val.castSucc ∧
        2 * P.xi q.1.1.1.val.succ =
          P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) +
            P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hr := (originalEmptyBlock_remaining_endpoints P q.1.1.1 h.1 q.1.1.2).1
    have hm := h.2
    change 2 * P.xi (originalRemovedRow P q.1.1.1 q.1.1.2).succ = _ at hm
    rwa [hr] at hm
  · intro h
    refine ⟨h.1, ?_⟩
    have hr := (originalEmptyBlock_remaining_endpoints P q.1.1.1 h.1 q.1.1.2).1
    change 2 * P.xi (originalRemovedRow P q.1.1.1 q.1.1.2).succ = _
    rw [hr]
    exact h.2

/-- If a midpoint vertex exists, its entire block is exactly the exception
removed from the recovered interval. -/
theorem original_nonmidpoint_iff_block_ne {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p : OriginalResponseInterval (hD := hD) P (some a) (some b))
    (hp : originalIntervalMidpointVertex P a b p)
    (q : OriginalResponseInterval (hD := hD) P (some a) (some b)) :
    ¬ originalIntervalMidpointVertex P a b q ↔ q.1.1.1 ≠ p.1.1.1 := by
  constructor
  · intro hq he
    apply hq
    apply (original_interval_midpoint_block_iff P a b q).mpr
    rw [he]
    exact (original_interval_midpoint_block_iff P a b p).mp hp
  · intro hne hq
    have he := original_interval_midpoint_unique P a b p q hp hq
    exact hne (congrArg (fun j : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
      j.1.1.1) he.symm)

/-- Every other actual retained point lies wholly on one strict side of a
literal midpoint vertex, in both original coordinates. -/
theorem original_midpoint_remaining_separation {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p q : OriginalResponseInterval (hD := hD) P (some a) (some b))
    (hp : originalIntervalMidpointVertex P a b p)
    (hq : ¬ originalIntervalMidpointVertex P a b q) :
    (originalResponseRows P q.1.1 < originalResponseRows P p.1.1 ∧
      originalResponseCols P q.1.1 < originalResponseRows P p.1.1) ∨
    (originalResponseRows P p.1.1 < originalResponseRows P q.1.1 ∧
      originalResponseRows P p.1.1 < originalResponseCols P q.1.1) := by
  have hne := (original_nonmidpoint_iff_block_ne P a b p hp q).mp hq
  have hpcoord := original_interval_midpoint_coordinates P a b p hp
  rcases lt_trichotomy q.1.1.1 p.1.1.1 with h | h | h
  · have hr := original_remaining_row_block_strict P q.1.1.1 p.1.1.1 h q.1.1.2 p.1.1.2
    have hc := original_remaining_col_block_strict P q.1.1.1 p.1.1.1 h q.1.1.2 p.1.1.2
    change originalResponseRows P p.1.1 < originalResponseRows P q.1.1 at hr
    change originalResponseCols P p.1.1 < originalResponseCols P q.1.1 at hc
    exact Or.inr ⟨hr, hpcoord ▸ hc⟩
  · exact (hne h).elim
  · have hr := original_remaining_row_block_strict P p.1.1.1 q.1.1.1 h p.1.1.2 q.1.1.2
    have hc := original_remaining_col_block_strict P p.1.1.1 q.1.1.1 h p.1.1.2 q.1.1.2
    change originalResponseRows P q.1.1 < originalResponseRows P p.1.1 at hr
    change originalResponseCols P q.1.1 < originalResponseCols P p.1.1 at hc
    exact Or.inl ⟨hr, hpcoord ▸ hc⟩

variable (c : SelectedCoordinate D hD)

/-- The whole recovered nonmidpoint interval has its own genuine inverse,
produced by retaining complete original blocks. -/
@[instance_reducible]
noncomputable def originalNonmidpointIntervalInverse {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1)
      (fun q : OriginalNonmidpointInterval P a b => originalResponseCols P q.1.1.1)) := by
  classical
  let keep := fun u : OriginalBlocks P => ¬ (P.xi u.val.succ = P.zeta u.val.castSucc ∧
    2 * P.xi u.val.succ = P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) +
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))))
  have hp (q : OriginalResponseInterval (hD := hD) P (some a) (some b)) :
      ¬ originalIntervalMidpointVertex P a b q ↔ keep q.1.1.1 :=
    not_congr (original_interval_midpoint_block_iff P a b q)
  let e : OriginalNonmidpointInterval P a b ≃
      {q : OriginalResponseInterval (hD := hD) P (some a) (some b) // keep q.1.1.1} :=
    Equiv.subtypeEquivRight hp
  let := c.originalResponseResidueIntervalInverse P (some a) (some b)
  let := c.originalIntervalKeptBlockInverse P (some a) (some b) keep
  let row := fun q : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
    originalResponseRows P q.1.1
  let col := fun q : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
    originalResponseCols P q.1.1
  let M := (vertexBetaMatrix c.residueMap row col).toBlock
    (fun q => keep q.1.1.1) (fun q => keep q.1.1.1)
  have he : vertexBetaMatrix c.residueMap
      (fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1)
      (fun q : OriginalNonmidpointInterval P a b => originalResponseCols P q.1.1.1) =
      M.submatrix e e := by
    ext i j
    rfl
  rw [he]
  exact Matrix.submatrixEquivInvertible M e e

end SkewCornerDescent.Matrix.SelectedCoordinate
