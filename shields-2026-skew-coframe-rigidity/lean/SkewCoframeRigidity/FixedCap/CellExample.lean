/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.SpliceExample

/-!
# The same-cell cap: flags and hypotheses

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Rigidity with the same literal cap»
(`sec:fixed-caps`, `ex:same-cell-cap`, `fig:cell-splice`).  The one-cell cap and the equal-function
hooks `(2,1)` and `(2,2)/(1)` are connected and normalized, and the `00`-splices have exactly the
full lists `(4,1)/(1,0)` and `(4,2)/(2,0)` of the example.  Sorry-free.
-/

namespace SkewCoframeRigidity

open SkewCofactorIndependence

theorem cellCap_isNorm : IsNorm cellCap := rfl

theorem hookA_isNorm : IsNorm hookA := rfl

theorem hookB_isNorm : IsNorm hookB := rfl

theorem cellCap_connected : cellCap.Connected :=
  ⟨by norm_num, fun i hi => by omega⟩

theorem hookA_connected : hookA.Connected := by
  refine ⟨by norm_num, fun i hi => ?_⟩
  have : i = 0 := by ext; simp only [Fin.val_zero]; omega
  subst this
  simp [hookA]

theorem hookB_connected : hookB.Connected := by
  refine ⟨by norm_num, fun i hi => ?_⟩
  have : i = 0 := by ext; simp only [Fin.val_zero]; omega
  subst this
  simp [hookB]

theorem cellSplice_A_row : (splice cellCap hookA cellCap_isNorm hookA_isNorm).row = ![4, 1] := by
  funext i
  fin_cases i <;> simp [splice, spliceRow, cellCap, hookA]

theorem cellSplice_A_col : (splice cellCap hookA cellCap_isNorm hookA_isNorm).col = ![1, 0] := by
  funext i
  fin_cases i <;> simp [splice, spliceCol, cellCap, hookA]

theorem cellSplice_B_row : (splice cellCap hookB cellCap_isNorm hookB_isNorm).row = ![4, 2] := by
  funext i
  fin_cases i <;> simp [splice, spliceRow, cellCap, hookB]

theorem cellSplice_B_col : (splice cellCap hookB cellCap_isNorm hookB_isNorm).col = ![2, 0] := by
  funext i
  fin_cases i <;> simp [splice, spliceCol, cellCap, hookB]

end SkewCoframeRigidity
