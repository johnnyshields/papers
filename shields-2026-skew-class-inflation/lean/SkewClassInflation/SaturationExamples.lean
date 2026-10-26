/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationChains
import SkewClassInflation.SaturationRibbonReduction
import SkewClassInflation.SharpExamples

/-!
# Non-vacuity witnesses for the general separated-inner domain

The merger-coincidence example in `sec:examples` and the zero-inner-gap
boundary of `eq:saturation-domain` in
`shields-2026-skew-class-inflation.tex`.  Each witness inhabits the full
standing domain and uses the actual repeated-power and source-chain
constructors.  No rigidity or cardinality assertion is inferred from
these individual configurations.  Sorry-free.
-/

namespace SkewClassInflation

/-- A separated inner whose merger length already occurs as an interior row length. -/
def collidingInner : SaturationInner where
  k := 2
  k_pos := by decide
  r := ![4, 7, 5]
  c := 1
  d := 2
  c_lt_d := by decide
  first_bound := by decide
  last_bound := by decide
  interior_bound i hi hl := by fin_cases i <;> simp_all

/-- The parameter domain really includes a coincident merger and interior row value. -/
theorem colliding_inner_merger : collidingInner.merger = collidingInner.r 1 := by decide

/-- The actual overlapped power retains all three coincident internal row positions. -/
theorem colliding_inner_power_rows :
    (collidingInner.power 2 (by decide)).r = ![4, 7, 7, 7, 5] := by
  funext i
  fin_cases i <;> rfl

/-- The actual larger-seam source keeps the coincident rows in their original ordered blocks. -/
theorem colliding_inner_source_rows :
    (collidingInner.diagram outerOneTwo (by decide)).2.r = ![4, 7, 5, 4, 7, 7, 7, 5] := by
  funext i
  fin_cases i <;> rfl

/-- The distinguished joining seam is separate from all of the repeated inner gaps. -/
theorem colliding_inner_source_gaps :
    (collidingInner.diagram outerOneTwo (by decide)).2.g = ![1, 1, 2, 1, 1, 1, 1] := by
  funext i
  fin_cases i <;> rfl

/-- A complete separated-inner witness with zero inner gaps. -/
def zeroGapInner : SaturationInner where
  k := 1
  k_pos := by decide
  r := ![4, 5]
  c := 0
  d := 1
  c_lt_d := by decide
  first_bound := by decide
  last_bound := by decide
  interior_bound i hi hl := by fin_cases i <;> simp_all

/-- The full zero-gap parameter regime produces its actual ordinary near-concatenated power. -/
theorem zero_gap_inner_power_rows : (zeroGapInner.power 2 (by decide)).r = ![4, 8, 5] := by
  funext i
  fin_cases i <;> rfl

/-- The zero-gap source has an actual Hessenberg proof on the complete standing domain. -/
theorem zero_gap_inner_source_thick :
    SkewJacobiNegative.Staircase.Thick (zeroGapInner.diagram outerOneTwo (by decide)).2 :=
  zeroGapInner.diagram_thick outerOneTwo (by decide)

end SkewClassInflation
