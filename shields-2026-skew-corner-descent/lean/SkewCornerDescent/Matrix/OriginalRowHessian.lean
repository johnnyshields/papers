/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRowProjection
import SkewCornerDescent.Matrix.OriginalEndpointInjection

/-!
# Actual all-row response mixed jets have the three integer values

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The full source mixed jet counts at most two literal unit vertices. A coincident
square counts one position twice. Every bound comes from complete original
endpoint injection and the all-row component hypothesis. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual original response mixed jet is zero, minus one or minus two;
at a coincident square its normalized value is zero or minus one. No
inverse-entry or vertex-count premise is supplied. -/
theorem original_row_response_hessian_bound {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hsum : (p : ℤ) + (q : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) :
    ∃ k : ℕ, k ≤ (if p = q then 1 else 2) ∧
      residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
        (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
          (c.regularResidue (c.originalLocalResponse P (some b) (some d)))) =
        -(if p = q then 2 else 1 : OtherField c.top) * (k : OtherField c.top) := by
  classical
  let ν := OriginalResponseInterval (hD := hD) P (some b) (some d)
  let row := fun i : ν => originalResponseRows P i.1.1
  let col := fun i : ν => originalResponseCols P i.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  let count := fun z : ℤ => (Finset.univ.filter (fun i : ν => row i = z ∧ col i = z)).card
  have hcount (z) : count z ≤ 1 := original_interval_unit_vertex_count_le_one P (some b) (some d) z
  have h := c.originalLocalResponse_hessian_projection P (some b) (some d) p q hp hq hsum
  let := c.originalResponseResidueIntervalInverse P (some b) (some d)
  dsimp only at h
  rw [c.original_interval_row_projection_count P b d horder hmax hrows,
    c.original_interval_row_projection_count P b d horder hmax hrows] at h
  change residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalLocalResponse P (some b) (some d)))) =
    -(count (x - (q : ℤ)) : OtherField c.top) - (count (x - (p : ℤ)) : OtherField c.top) at h
  by_cases he : p = q
  · subst q
    refine ⟨count (x - (p : ℤ)), ?_, ?_⟩
    · simpa only [ite_true] using hcount (x - (p : ℤ))
    · rw [ite_eq_left rfl, h]
      ring
  · refine ⟨count (x - (q : ℤ)) + count (x - (p : ℤ)), ?_, ?_⟩
    · rw [ite_eq_right he]
      have ha := hcount (x - (q : ℤ))
      have hb := hcount (x - (p : ℤ))
      omega
    · rw [ite_eq_right he, h, Nat.cast_add]
      ring

end SkewCornerDescent.Matrix.SelectedCoordinate
