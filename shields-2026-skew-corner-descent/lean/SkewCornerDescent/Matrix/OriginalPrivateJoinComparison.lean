/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureJoinProjection
import SkewCornerDescent.Matrix.OriginalEqualWindowCapProjection
import SkewCornerDescent.Matrix.OriginalOrdinaryPrivateCapLocalization

/-!
# Actual private-source contraction versus its literal horizontal reference

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Equal whole windows identify the complete retained cap with the actual
horizontal closure, not a formal scalar replacement. The sole difference is
the unit at an ordinary vertical cut. All inverse matches are produced.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Below the lower private cut, the actual source contraction differs from
its literal horizontal reference by exactly the actual vertical unit indicator. -/
theorem originalPrivateJoin_comparison_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v w : ℤ × ℤ) (q : ℤ) (hv : content v = q)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevcut : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (b d first last : OriginalSelectedBlocks (hD := hD) P)
    (hdwindow : ∀ x ∈ interiorBlockCells P d.val.val,
      0 ≤ content x ∧ content x < P.xi 0 - q)
    (he : translate v (interiorBlockCells P d.val.val) = interiorBlockCells P first.val.val)
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = P.xi 0 - q) (hp : content prev = P.xi 0 - q - 1)
    (hb : P.xi 0 - q < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < P.xi 0 - q)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : z ≤ P.xi 0 - q)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0)
    (hA0 : A.coeff 0 = 1) (hT0 : T.coeff 0 = 1) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalIntervalInverseProjection Q
          (some (originalHorizontalClosureSelectedCopy P Q w hQ true last))
          (some (originalHorizontalClosureSelectedCopy P Q w hQ false first)) A T (z + q) +
        if z = P.xi 0 - q ∧ cur.2 = prev.2 then 1 else 0 := by
  rw [c.originalOrdinaryPrivate_lower_cap_projection P b d (P.xi 0 - q) cur prev
    hcur hprev hc hp hcutLq hprevcut hb hd A T z hz hA hT hA0 hT0,
    c.originalEqualWindow_lower_cap_projection P q v hv hwindow hcutq hcutLq
      d first hdwindow he A T z,
    c.originalHorizontalClosure_join_projection_lower P Q w hQ last first A T
      (z + q) (by omega) hA hT]

/-- Above the upper private cut, the same comparison uses the complete
lower cap and the actual span-minus-window displacement of the reference. -/
theorem originalPrivateJoin_comparison_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v w : ℤ × ℤ) (q : ℤ) (hv : content v = q)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevcut : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (b d first last : OriginalSelectedBlocks (hD := hD) P)
    (hlastwindow : ∀ x ∈ interiorBlockCells P last.val.val,
      0 ≤ content x ∧ content x < P.xi 0 - q)
    (he : translate v (interiorBlockCells P last.val.val) = interiorBlockCells P b.val.val)
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = q) (hp : content prev = q - 1)
    (hb : q < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < q)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : q ≤ z)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0)
    (hA0 : A.coeff 0 = 1) (hT0 : T.coeff 0 = 1) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalIntervalInverseProjection Q
          (some (originalHorizontalClosureSelectedCopy P Q w hQ true last))
          (some (originalHorizontalClosureSelectedCopy P Q w hQ false first)) A T
          (z + P.xi 0 - q) +
        if z = q ∧ cur.2 = prev.2 then 1 else 0 := by
  have hcap := c.originalEqualWindow_upper_cap_projection P q v hv hwindow hcutq hcutLq
    last b hlastwindow he A T (z - q)
  simp only [sub_add_cancel] at hcap
  rw [c.originalOrdinaryPrivate_upper_cap_projection P b d q cur prev
    hcur hprev hc hp hcutq hprevcut hb hd A T z hz hA hT hA0 hT0, hcap,
    c.originalHorizontalClosure_join_projection_upper P Q w hQ last first A T
      (z + P.xi 0 - q) (by omega) hA hT]
  rw [show z + P.xi 0 - q - P.xi 0 = z - q by omega]

end SkewCornerDescent.Matrix.SelectedCoordinate
