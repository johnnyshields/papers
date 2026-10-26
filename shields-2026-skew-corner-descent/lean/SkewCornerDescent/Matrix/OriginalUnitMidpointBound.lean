/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitProtectedPositions

/-!
# At most one actual full unit component straddles an endpoint midpoint

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The complete original component order strictly separates each later greatest
row from every earlier least column. This rules out two midpoint-straddling
components without a supplied separation or interval-disjointness premise.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- At most one nonempty complete original nonselected component can straddle
any given content position. Empty pivots are not classified as positive-span components. -/
theorem original_unit_midpoint_unique {n : ℕ} (P : Profile n) (b d : OriginalBlocks P)
    (hb : ¬ originalBlockSelected (hD := hD) P b)
    (hd : ¬ originalBlockSelected (hD := hD) P d)
    (hbne : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hdne : P.zeta d.val.castSucc < P.xi d.val.succ) (m : ℤ)
    (hbl : originalComponentTau P b < m)
    (hbr : m < (interiorBlockProfile P b.val hbne).xi 0 + originalComponentTau P b)
    (hdl : originalComponentTau P d < m)
    (hdr : m < (interiorBlockProfile P d.val hdne).xi 0 + originalComponentTau P d) :
    b = d := by
  rcases lt_trichotomy b d with hbd | he | hdb
  · have h := original_remaining_beta_separated (hD := hD) P d b hbd
      (originalUnitIndex P d hd 0) (originalUnitIndex P b hb (Fin.last _))
    change P.xi (originalRemovedRow P d (originalUnitIndex P d hd 0)).succ <
      P.zeta (originalRemovedCol P b (originalUnitIndex P b hb (Fin.last _))).castSucc at h
    rw [(original_unit_component_beta P d hd hdne 0).1,
      (original_unit_component_beta P b hb hbne (Fin.last _)).2,
      (interiorBlockProfile P b.val hbne).zeta_last, zero_add] at h
    omega
  · exact he
  · have h := original_remaining_beta_separated (hD := hD) P b d hdb
      (originalUnitIndex P b hb 0) (originalUnitIndex P d hd (Fin.last _))
    change P.xi (originalRemovedRow P b (originalUnitIndex P b hb 0)).succ <
      P.zeta (originalRemovedCol P d (originalUnitIndex P d hd (Fin.last _))).castSucc at h
    rw [(original_unit_component_beta P b hb hbne 0).1,
      (original_unit_component_beta P d hd hdne (Fin.last _)).2,
      (interiorBlockProfile P d.val hdne).zeta_last, zero_add] at h
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
