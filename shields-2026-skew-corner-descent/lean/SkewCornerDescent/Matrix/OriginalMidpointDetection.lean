/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalMidpointInsertion
import SkewCornerDescent.Matrix.MidpointBetaResponseDetection

/-!
# Actual original response detects its midpoint vertex

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The complete source midpoint insertion is nonzero above the selected span.
Its protected generator, both actual inverses and every geometric condition
are produced from the original interval, not taken as compatibility inputs.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual full residue response differs from that of its recovered
punctured interval whenever the literal midpoint vertex is present.
The resolving index, both complete inverses and all geometric bounds are
produced from the actual source and its interval height. -/
theorem original_midpoint_response_ne_punctured {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p : OriginalResponseInterval (hD := hD) P (some a) (some b))
    (hp : originalIntervalMidpointVertex P a b p)
    (hK : 2 * (c.top : ℤ) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))) :
    letI := c.originalNonmidpointIntervalInverse P a b
    c.regularResidue (c.originalLocalResponse P (some a) (some b)) ≠
      vertexBetaResponse c.residueMap
        (fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1)
        (fun q : OriginalNonmidpointInterval P a b => originalResponseCols P q.1.1.1)
        (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))))
        (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))) := by
  classical
  let row := fun q : OriginalNonmidpointInterval P a b => originalResponseRows P q.1.1.1
  let col := fun q : OriginalNonmidpointInterval P a b => originalResponseCols P q.1.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let m := originalResponseRows P p.1.1
  let := c.originalNonmidpointIntervalInverse P a b
  have hm : 2 * m = x + y := hp.2
  have hx (q) : row q < x := originalResponse_row_lt P (some a) q.1.1.1 q.1.2
  have hy (q) : y < col q := originalResponse_col_gt P (some b) q.1.1.1 q.1.1.2
  have hsep (q) : (row q < m ∧ col q < m) ∨ (m < row q ∧ m < col q) :=
    original_midpoint_remaining_separation P a b p q.1 hp q.2
  have hxmpos : 0 < x - m := by
    have hh := originalResponse_row_lt P (some a) p.1.1 p.2
    change m < x at hh
    omega
  let J : ℕ+ := ⟨(x - m).toNat, by omega⟩
  have hxm : x - m = (J : ℤ) := by
    dsimp only [J]
    exact (Int.toNat_of_nonneg hxmpos.le).symm
  have hmy : m - y = (J : ℤ) := by omega
  have hJ : c.top < J := by
    have hh : (c.top : ℤ) < (J : ℤ) := by
      change 2 * (c.top : ℤ) < x - y at hK
      omega
    exact_mod_cast hh
  have hne := c.midpoint_vertex_beta_response_ne row col m x y J hJ hsep hx hy hxm hmy
  have hins := vertexBetaResponse_unit_insert c.residueMap row col m x y hsep
  dsimp only at hne hins ⊢
  rw [hins] at hne
  rw [c.original_interval_midpoint_response P a b p hp]
  exact hne

end SkewCornerDescent.Matrix.SelectedCoordinate
