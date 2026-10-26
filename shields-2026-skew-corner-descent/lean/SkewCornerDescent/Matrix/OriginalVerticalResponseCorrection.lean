/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateUnitResponse
import SkewCornerDescent.Matrix.OriginalClosureJoinVectors

/-!
# Exact full response correction for the literal vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The actual vertical join unit and its complete nonunit beta match produce
the full response relation to the literal horizontal reference. Both complete
effective cut responses remain; no mixed-jet identity substitutes for the
full rational function. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original vertical response equals its actual horizontal
reference minus the two complete effective responses through the actual cut. -/
theorem originalVerticalClosure_response_correction {n m s : ℕ}
    (P : Profile n) (V : Profile m) (H : Profile s) (v w : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    let bV := originalVerticalClosureSelectedCopy P V v hV true b
    let dV := originalVerticalClosureSelectedCopy P V v hV false d
    let bH := originalHorizontalClosureSelectedCopy P H w hH true b
    let dH := originalHorizontalClosureSelectedCopy P H w hH false d
    letI := c.originalResponseResidueIntervalInverse H (some bH) (some dH)
    let row := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
      originalResponseRows H i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
      originalResponseCols H i.1.1
    let x := H.xi (originalRowSplitEquiv (hD := hD) H (.inl (some bH)))
    let y := H.zeta (originalColSplitEquiv (hD := hD) H (.inl (some dH)))
    c.regularResidue (c.originalLocalResponse V (some bV) (some dV)) =
      c.regularResidue (c.originalLocalResponse H (some bH) (some dH)) -
        vertexBetaResponse c.residueMap row col x (P.xi 0) *
          vertexBetaResponse c.residueMap row col (P.xi 0) y := by
  classical
  intro bV dV bH dH
  let rowH := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
    originalResponseRows H i.1.1
  let colH := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
    originalResponseCols H i.1.1
  let rowV := fun i : {i : OriginalResponseInterval (hD := hD) V (some bV) (some dV) //
    ¬ (originalResponseRows V i.1.1 = P.xi 0 ∧ originalResponseCols V i.1.1 = P.xi 0)} =>
      originalResponseRows V i.val.1.1
  let colV := fun i : {i : OriginalResponseInterval (hD := hD) V (some bV) (some dV) //
    ¬ (originalResponseRows V i.1.1 = P.xi 0 ∧ originalResponseCols V i.1.1 = P.xi 0)} =>
      originalResponseCols V i.val.1.1
  have hpriv := originalVerticalClosure_profile_join_private P V v hV
  obtain ⟨u, hu, _⟩ := c.originalVerticalClosure_join_interval_unit P V v hV b d
  let := c.originalIntervalWithoutPrivateUnitInverse V (some bV) (some dV) (P.xi 0)
    hpriv.1 hpriv.2 u hu
  let := c.originalResponseResidueIntervalInverse H (some bH) (some dH)
  obtain ⟨e, he⟩ := c.originalClosures_join_nonunit_vectors P V H v w hV hH b d
  have copy (x y : ℤ) : vertexBetaResponse c.residueMap rowH colH x y =
      vertexBetaResponse c.residueMap rowV colV x y := by
    have hc := vertexBetaResponse_affine_reindex c.residueMap e.symm rowH colH rowV colV
      x y 0 (fun i => by simpa only [add_zero] using (he i).1)
      (fun i => by simpa only [add_zero] using (he i).2)
    simpa only [add_zero] using hc
  have hxV := (c.originalVerticalClosure_retained_endpoints P V v hV true b).1
  have hxH := (originalHorizontalClosure_retained_endpoints P H w hH true b).1
  have hyV := (c.originalVerticalClosure_retained_endpoints P V v hV false d).2
  have hyH := (originalHorizontalClosure_retained_endpoints P H w hH false d).2
  simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte,
    sub_zero, add_zero, add_sub_cancel_right] at hxV hxH hyV hyH
  have hx : V.xi (originalRowSplitEquiv (hD := hD) V (.inl (some bV))) =
      H.xi (originalRowSplitEquiv (hD := hD) H (.inl (some bH))) := hxV.trans hxH.symm
  have hy : V.zeta (originalColSplitEquiv (hD := hD) V (.inl (some dV))) =
      H.zeta (originalColSplitEquiv (hD := hD) H (.inl (some dH))) := hyV.trans hyH.symm
  have h := c.originalInterval_private_unit_response V (some bV) (some dV) (P.xi 0)
    hpriv.1 hpriv.2 u hu
  dsimp only at h
  rw [hx, hy, ← copy, ← copy, ← copy] at h
  have hbase := c.originalLocalResponse_residue_pruned H (some bH) (some dH)
  change c.regularResidue (c.originalLocalResponse H (some bH) (some dH)) =
    vertexBetaResponse c.residueMap rowH colH
      (H.xi (originalRowSplitEquiv (hD := hD) H (.inl (some bH))))
      (H.zeta (originalColSplitEquiv (hD := hD) H (.inl (some dH)))) at hbase
  dsimp only
  rw [← hbase] at h
  exact h

end SkewCornerDescent.Matrix.SelectedCoordinate
