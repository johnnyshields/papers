/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalMidpointGeometry
import SkewCornerDescent.Matrix.OriginalPrivateUnitResponse

/-!
# Reinsert the genuine original midpoint vertex

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The recovered interval and its unique actual midpoint pivot enumerate the
whole original interval.  Full affine beta transport identifies the actual
residue response with the complete unit-insertion correction.  Both inverses
and strict separation are produced, without extra private-cut hypotheses.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The full actual interval consists of the recovered part and its unique
literal midpoint vertex.  The map retains every original position. -/
noncomputable def originalIntervalMidpointEquiv {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p : OriginalResponseInterval (hD := hD) P (some a) (some b))
    (hp : originalIntervalMidpointVertex P a b p) :
    (OriginalNonmidpointInterval P a b ⊕ Unit) ≃
      OriginalResponseInterval (hD := hD) P (some a) (some b) := by
  let m := originalResponseRows P p.1.1
  have hpcol : originalResponseCols P p.1.1 = m :=
    (original_interval_midpoint_coordinates P a b p hp).symm
  have he (q : OriginalResponseInterval (hD := hD) P (some a) (some b)) :
      originalIntervalMidpointVertex P a b q ↔
        originalResponseRows P q.1.1 = m ∧ originalResponseCols P q.1.1 = m := by
    constructor
    · intro hq
      have hqp := original_interval_midpoint_unique P a b q p hq hp
      rw [hqp]
      exact ⟨rfl, hpcol⟩
    · intro hq
      have hqp : q = p := Subtype.ext (Subtype.ext (original_response_rows_injective P hq.1))
      exact hqp.symm ▸ hp
  let e : OriginalNonmidpointInterval P a b ≃
      {q : OriginalResponseInterval (hD := hD) P (some a) (some b) //
        ¬ (originalResponseRows P q.1.1 = m ∧ originalResponseCols P q.1.1 = m)} :=
    Equiv.subtypeEquivRight (fun q => not_congr (he q))
  exact (Equiv.sumCongr e (Equiv.refl Unit)).trans
    (originalIntervalPrivateUnitEquiv P (some a) (some b) m p ⟨rfl, hpcol⟩)

variable (c : SelectedCoordinate D hD)

/-- Reinsert the actual original midpoint vertex into the complete recovered
interval.  Both inverses, strict geometric separation and every coupling are
source-produced; no private-cut singleton hypothesis is added. -/
theorem original_interval_midpoint_response {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p : OriginalResponseInterval (hD := hD) P (some a) (some b))
    (hp : originalIntervalMidpointVertex P a b p) :
    letI := c.originalNonmidpointIntervalInverse P a b
    let row := fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1
    let col := fun q : OriginalNonmidpointInterval P a b => originalResponseCols P q.1.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
    let m := originalResponseRows P p.1.1
    c.regularResidue (c.originalLocalResponse P (some a) (some b)) =
      vertexBetaResponse c.residueMap row col x y -
        vertexBetaResponse c.residueMap row col x m *
          vertexBetaResponse c.residueMap row col m y := by
  classical
  let row := fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1
  let col := fun q : OriginalNonmidpointInterval P a b => originalResponseCols P q.1.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let m := originalResponseRows P p.1.1
  let := c.originalNonmidpointIntervalInverse P a b
  let := c.originalResponseResidueIntervalInverse P (some a) (some b)
  have hsep (q) : (row q < m ∧ col q < m) ∨ (m < row q ∧ m < col q) :=
    original_midpoint_remaining_separation P a b p q.1 hp q.2
  let e := originalIntervalMidpointEquiv P a b p hp
  let row' := Sum.elim row (fun _ : Unit => m)
  let col' := Sum.elim col (fun _ : Unit => m)
  let := vertexBetaUnitInverse c.residueMap row col m hsep
  have hr (i) : originalResponseRows P (e i).1.1 = row' i := by
    rcases i with i | i
    · rfl
    · cases i
      rfl
  have hc (i) : originalResponseCols P (e i).1.1 = col' i := by
    rcases i with i | i
    · rfl
    · cases i
      exact (original_interval_midpoint_coordinates P a b p hp).symm
  have hcopy := vertexBetaResponse_affine_reindex c.residueMap e row' col'
    (fun i => originalResponseRows P i.1.1) (fun i => originalResponseCols P i.1.1) x y 0
    (fun i => by simpa only [add_zero] using hr i)
    (fun i => by simpa only [add_zero] using hc i)
  simp only [add_zero] at hcopy
  have hfull := c.originalLocalResponse_residue_pruned P (some a) (some b)
  change c.regularResidue (c.originalLocalResponse P (some a) (some b)) =
    vertexBetaResponse c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
        originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1) x y at hfull
  dsimp only
  rw [hfull, ← hcopy]
  exact vertexBetaResponse_unit_insert c.residueMap row col m x y hsep

/-- In the absence of a literal midpoint pivot the reconstructed interval
is the whole actual interval, so its response is unchanged. -/
theorem original_interval_without_midpoint_response {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (hnone : ∀ p : OriginalResponseInterval (hD := hD) P (some a) (some b),
      ¬ originalIntervalMidpointVertex P a b p) :
    letI := c.originalNonmidpointIntervalInverse P a b
    c.regularResidue (c.originalLocalResponse P (some a) (some b)) =
      vertexBetaResponse c.residueMap
        (fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1)
        (fun q : OriginalNonmidpointInterval P a b => originalResponseCols P q.1.1.1)
        (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))))
        (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))) := by
  classical
  let := c.originalNonmidpointIntervalInverse P a b
  let := c.originalResponseResidueIntervalInverse P (some a) (some b)
  let e : OriginalNonmidpointInterval P a b ≃
      OriginalResponseInterval (hD := hD) P (some a) (some b) :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, hnone p⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcopy := vertexBetaResponse_affine_reindex c.residueMap e
    (fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1)
    (fun q => originalResponseCols P q.1.1.1)
    (fun q => originalResponseRows P q.1.1) (fun q => originalResponseCols P q.1.1)
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))))
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))) 0
    (fun _ => by simp only [add_zero]; rfl) (fun _ => by simp only [add_zero]; rfl)
  simp only [add_zero] at hcopy
  have hfull := c.originalLocalResponse_residue_pruned P (some a) (some b)
  exact hfull.trans hcopy.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
