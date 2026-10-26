/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLaurentSelfJet
import SkewCornerDescent.Matrix.OriginalCompletedGapEndpoints
import SkewCornerDescent.Matrix.OriginalInternalPeriodEntryGradient

/-!
# Complete actual internal self-profile correction

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual consecutive selected endpoints supply both full profile polynomials.
Their positive completed gap produces the normal-jet alignment, and the
Laurent raw/chart correction retains every resolving offset. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both complete residue endpoint polynomials at an actual internal state. -/
noncomputable def originalInternalEndpointProfiles {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    Polynomial (OtherField c.top) × Polynomial (OtherField c.top) :=
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  (c.originalResidueLeftEndpointPolynomial P (some (E a)) (some (E b)),
    c.originalResidueRightEndpointPolynomial P (some (E a)) (some (E b)))

/-- The complete actual internal self-profile correction is valid at every
resolving generator, including the selected one and negative Laurent offsets.
The positive source gap supplies the normal-jet alignment internally. -/
theorem originalInternal_self_chart_correction {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (j : ℕ+) :
    let p := c.originalInternalEndpointProfiles P i
    ((p.1 * p.2).toLaurent).coeff
      (originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) - (j : ℤ)) =
      residueChartDeriv c.top j (c.originalInternalResidue P i) +
        c.residueMap (pderiv j (cellSchur D hD.1)) *
          PowerSeries.coeff 1 (c.normalSeries (c.originalInternalResponseMatrix P i i)) := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let K := P.xi (originalRowSplitEquiv P (.inl (some (E a)))) -
    P.zeta (originalColSplitEquiv P (.inl (some (E b))))
  have hgap : c.originalCompletedGap P a = K - (c.top : ℤ) :=
    c.originalCompletedGap_internal_endpoints P a (by dsimp only [a]; have := i.isLt; omega)
  have hg0 : 0 ≤ c.originalCompletedGap P a := by
    have hg := c.originalCompletedGap_gt_top P a
    have hp := c.top.pos
    omega
  let l := (c.originalCompletedGap P a).toNat
  have hl : K - (c.top : ℤ) = (l : ℤ) := by
    rw [← hgap]
    exact (Int.toNat_of_nonneg hg0).symm
  have he := c.originalLocalResponse_raw_chart_laurent_first_jet P
    (some (E a)) (some (E b)) j l hl
  have hheight : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) = K := by
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))) = K
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hentry : c.originalInternalResponseMatrix P i i =
      c.originalLocalResponse P (some (E a)) (some (E b)) :=
    c.originalInternalResponseMatrix_selected_entry P i i
  rw [← hentry] at he
  change _ = residueChartDeriv c.top j (c.originalInternalResidue P i) + _ at he
  simpa only [originalInternalEndpointProfiles, a, b, E, hheight] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
