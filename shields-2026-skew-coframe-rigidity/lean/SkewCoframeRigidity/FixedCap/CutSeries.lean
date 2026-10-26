/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.CutAlgebra
import SkewCoframeRigidity.FixedCap.Deriv
import SkewCoframeRigidity.Coframe.Coherent
import SkewCoframeRigidity.Coframe.Algebra
import SkewCoframeRigidity.FixedCap.CapPoly

/-!
# Series supported on the columns of a diagram

For a diagram `D`, a power series supported on its column positions is determined by its
coefficients there, and the coefficients of `H · U` at the row positions are the proper matrix
applied to that vector.  With a cut of `D` this gives the leading and trailing uniqueness
statements used in the descent in the proof of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex`.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- `U` has all its coefficients on the column positions `colPos D j` with `P j`. -/
def SuppCols (D : BetaDiagram (n + 1)) (P : Fin n → Prop) (U : PowerSeries CohField) : Prop :=
  ∀ s, (∀ j, P j → colPos D j ≠ s) → PowerSeries.coeff s U = 0

/-- A cut of `D` at `q`: every row with index `≥ q` lies strictly below every column with index
`< q`. -/
def CutAt (D : BetaDiagram (n + 1)) (q : ℕ) : Prop :=
  ∀ i j : Fin n, q ≤ i.val → j.val < q → D.row i.succ < D.col j.castSucc

theorem SuppCols.mono {D : BetaDiagram (n + 1)} {P Q : Fin n → Prop} (h : ∀ j, P j → Q j)
    {U : PowerSeries CohField} (hU : SuppCols D P U) : SuppCols D Q U :=
  fun s hs => hU s fun j hj => hs j (h j hj)

theorem SuppCols.apply_not {D : BetaDiagram (n + 1)} {P : Fin n → Prop}
    {U : PowerSeries CohField} (hU : SuppCols D P U) {j : Fin n} (hj : ¬ P j) :
    PowerSeries.coeff (colPos D j) U = 0 :=
  hU _ fun j' hj' he => hj (by rwa [← colPos_injective D he])

theorem coeff_eq_sum_colPos {D : BetaDiagram (n + 1)} {U : PowerSeries CohField}
    (hU : SuppCols D (fun _ => True) U) (s : ℕ) :
    PowerSeries.coeff s U =
      ∑ j, if colPos D j = s then PowerSeries.coeff (colPos D j) U else 0 := by
  by_cases h : ∃ j, colPos D j = s
  · obtain ⟨j, rfl⟩ := h
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [if_neg (fun he => hi (colPos_injective D he))]
    · simp
  · push Not at h
    rw [hU s fun j _ => h j, Finset.sum_eq_zero]
    intro j _
    rw [if_neg (h j)]

theorem uniPoly_colVec_eq (D : BetaDiagram (n + 1)) {U : PowerSeries CohField}
    (hU : SuppCols D (fun _ => True) U) :
    (uniPoly (fun j => PowerSeries.coeff (colPos D j) U) (colPos D) : PowerSeries CohField) =
      1 + U := by
  ext s
  rw [Polynomial.coeff_coe, uniPoly_coeff, map_add, PowerSeries.coeff_one,
    coeff_eq_sum_colPos hU s]

/-- The coefficients of `H · U` at the row positions are the proper matrix applied to the
coefficients of `U` at the column positions. -/
theorem coeff_rowPos_supp (D : BetaDiagram (n + 1)) {U : PowerSeries CohField}
    (hU : SuppCols D (fun _ => True) U) (i : Fin n) :
    PowerSeries.coeff (rowPos D i) (letterSeries * U) =
      (properMatrixOf cohLetters D *ᵥ fun j => PowerSeries.coeff (colPos D j) U) i := by
  have h := coeff_rowPos cohLetters D (fun j => PowerSeries.coeff (colPos D j) U) i
  rw [uniPoly_colVec_eq D hU, mul_add, mul_one, map_add] at h
  have e : topVecOf cohLetters D i =
      PowerSeries.coeff (rowPos D i) (PowerSeries.mk cohLetters) := by
    unfold topVecOf
    rw [PowerSeries.coeff_mk, ← letterOf_natCast cohLetters (rowPos D i), rowPos_cast D]
  rw [e] at h
  exact add_left_cancel h

theorem eq_zero_of_colVec_zero {D : BetaDiagram (n + 1)} {U : PowerSeries CohField}
    (hU : SuppCols D (fun _ => True) U) (h : ∀ j, PowerSeries.coeff (colPos D j) U = 0) :
    U = 0 := by
  ext s
  rw [coeff_eq_sum_colPos hU s, map_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [h j, ite_self]

theorem lowerZero_of_cutAt {D : BetaDiagram (n + 1)} {q : ℕ} (hq : CutAt D q) :
    LowerZero (properMatrixOf cohLetters D) q := fun i j hi hj => by
  have := hq i j hi hj
  simp only [properMatrixOf, Matrix.of_apply]
  exact letterOf_neg_eq _ (by omega)

/-- **Leading uniqueness.**  A series on the columns left of a cut whose product with `H`
vanishes at the leading rows is zero. -/
theorem lead_inj_series {D : BetaDiagram (n + 1)} (hD : D.Connected) {q : ℕ} (hq : CutAt D q)
    {U : PowerSeries CohField} (hU : SuppCols D (fun j => j.val < q) U)
    (h : ∀ i : Fin n, i.val < q → PowerSeries.coeff (rowPos D i) (letterSeries * U) = 0) :
    U = 0 := by
  have hU' := hU.mono (P := fun j => j.val < q) (Q := fun _ => True) (fun _ _ => trivial)
  refine eq_zero_of_colVec_zero hU' ?_
  have := lead_inj (properDet_cohLetters_ne_zero hD) (lowerZero_of_cutAt hq)
    (fun j => PowerSeries.coeff (colPos D j) U)
    (fun j hj => hU.apply_not (by omega))
    (fun i hi => by rw [← coeff_rowPos_supp D hU' i]; exact h i hi)
  exact fun j => congrFun this j

/-- **Trailing uniqueness.**  A series on the columns right of a cut whose product with `H`
vanishes at the trailing rows is zero. -/
theorem trail_inj_series {D : BetaDiagram (n + 1)} (hD : D.Connected) {q : ℕ} (hq : CutAt D q)
    {U : PowerSeries CohField} (hU : SuppCols D (fun j => q ≤ j.val) U)
    (h : ∀ i : Fin n, q ≤ i.val → PowerSeries.coeff (rowPos D i) (letterSeries * U) = 0) :
    U = 0 := by
  have hU' := hU.mono (P := fun j => q ≤ j.val) (Q := fun _ => True) (fun _ _ => trivial)
  refine eq_zero_of_colVec_zero hU' ?_
  have := trail_inj (properDet_cohLetters_ne_zero hD) (lowerZero_of_cutAt hq)
    (fun j => PowerSeries.coeff (colPos D j) U)
    (fun j hj => hU.apply_not (by omega))
    (fun i hi => by rw [← coeff_rowPos_supp D hU' i]; exact h i hi)
  exact fun j => congrFun this j

end SkewCoframeRigidity.FixedCap
