/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowIntervals
import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles
import SkewCornerDescent.Matrix.BetaEndpointPolynomial
import SkewCornerDescent.Matrix.OriginalWindowRows

/-!
# Full endpoint profiles under complete literal-window translation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`lem:early-recovery`). Whole remaining-index equivalences transport every
inverse entry, endpoint exponent, proper selected strip, and empty unit vertex.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete literal windows preserve both full original endpoint polynomials.
The inverse equivalence and all endpoint shifts are produced from actual cells;
no profile equality or matrix matching is supplied as an assumption. -/
theorem originalEndpointProfiles_literal_window_translate {n m : ℕ}
    (P : Profile n) (Q : Profile m) (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhiq : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P lo hi b.val) (hd : originalBlockInWindow P lo hi d.val)
    (hb' : originalBlockInWindow Q (lo + q) (hi + q) b'.val)
    (hd' : originalBlockInWindow Q (lo + q) (hi + q) d'.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val)
    (he' : translate v (interiorBlockCells P d.val.val) = interiorBlockCells Q d'.val.val) :
    c.originalResidueLeftEndpointPolynomial Q (some b') (some d') =
      c.originalResidueLeftEndpointPolynomial P (some b) (some d) ∧
    c.originalResidueRightEndpointPolynomial Q (some b') (some d') =
      c.originalResidueRightEndpointPolynomial P (some b) (some d) := by
  obtain ⟨e, hend⟩ := originalLiteralWindow_retained_interval_equiv (hD := hD)
    P Q lo hi q v hv hwindow hlo hloq hhi hhiq b d b' d' hb hd hb' hd' he he'
  let rowP := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseRows (hD := hD) P i.1.1
  let colP := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseCols (hD := hD) P i.1.1
  let rowQ := fun i : OriginalResponseInterval (hD := hD) Q (some b') (some d') =>
    originalResponseRows (hD := hD) Q i.1.1
  let colQ := fun i : OriginalResponseInterval (hD := hD) Q (some b') (some d') =>
    originalResponseCols (hD := hD) Q i.1.1
  let xP := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  let yP := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  let xQ := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some b')))
  let yQ := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some d')))
  have hr : rowQ = fun i => rowP (e.symm i) + q := by
    funext i
    simpa only [rowP, rowQ, Equiv.apply_symm_apply] using (hend (e.symm i)).1
  have hc : colQ = fun i => colP (e.symm i) + q := by
    funext i
    simpa only [colP, colQ, Equiv.apply_symm_apply] using (hend (e.symm i)).2
  have hx : xQ = xP + q := by
    have h := (c.originalSelected_translated_endpoints P Q b b' v he).1
    rw [hv] at h
    simpa only [xP, xQ, originalRowSplitEquiv_selected] using h
  have hy : yQ = yP + q := by
    have h := (c.originalSelected_translated_endpoints P Q d d' v he').2
    rw [hv] at h
    simpa only [yP, yQ, originalColSplitEquiv_selected] using h
  have hL : betaEndpointLeftPolynomial c.residueMap rowQ colQ xQ =
      betaEndpointLeftPolynomial c.residueMap rowP colP xP := by
    rw [hr, hc, hx]
    exact (betaEndpointLeftPolynomial_translate c.residueMap
      (rowP ∘ e.symm) (colP ∘ e.symm) xP q).trans
      (betaEndpointLeftPolynomial_equiv c.residueMap rowP colP xP e.symm)
  have hR : betaEndpointRightPolynomial c.residueMap rowQ colQ yQ =
      betaEndpointRightPolynomial c.residueMap rowP colP yP := by
    rw [hr, hc, hy]
    exact (betaEndpointRightPolynomial_translate c.residueMap
      (rowP ∘ e.symm) (colP ∘ e.symm) yP q).trans
      (betaEndpointRightPolynomial_equiv c.residueMap rowP colP yP e.symm)
  let := c.originalResponseResidueIntervalInverse P (some b) (some d)
  let := c.originalResponseResidueIntervalInverse Q (some b') (some d')
  constructor
  · simpa only [originalResidueLeftEndpointPolynomial, residueIntervalLeftPolynomial,
      betaEndpointLeftPolynomial, Matrix.invOf_eq_nonsing_inv, rowP, colP, rowQ, colQ, xP, xQ]
      using hL
  · simpa only [originalResidueRightEndpointPolynomial, residueIntervalRightPolynomial,
      betaEndpointRightPolynomial, Matrix.invOf_eq_nonsing_inv, rowP, colP, rowQ, colQ, yP, yQ]
      using hR

end SkewCornerDescent.Matrix.SelectedCoordinate
