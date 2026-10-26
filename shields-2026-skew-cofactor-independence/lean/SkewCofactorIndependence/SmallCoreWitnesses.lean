/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.FirstVariations
import SkewCofactorIndependence.SymmetricCofactors

/-!
# Small actual dense cores

The base core in `ex:dilation-ray` and the symmetric dense core used in the
concluding limitation of `shields-2026-skew-cofactor-independence.tex`.
The coordinates, cofactors, and unit polynomials are literal determinants.
Sorry-free.
-/

namespace SkewCofactorIndependence

/-- The nonsymmetric dense core with beta lists `(4,2)` and `(1,0)`. -/
def dilationRayCore : BetaDiagram 2 where
  row := ![4, 2]
  col := ![1, 0]
  row_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  col_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  row_nonempty := by intro i; fin_cases i <;> norm_num

/-- The base core really lies in the dense class. -/
theorem dilationRayCore_dense : dilationRayCore.Dense := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [dilationRayCore]

/-- The base coordinates are normalized as in the manuscript. -/
theorem dilationRayCore_normalized : dilationRayCore.Normalized := by
  intro hn
  norm_num [dilationRayCore]

/-- The base core is not fixed by rotation. -/
theorem dilationRayCore_nonsymmetric : ¬ dilationRayCore.Symmetric := by
  rintro ⟨c, hrow, hcol⟩
  have h0 := hrow 0
  have h1 := hrow 1
  norm_num [dilationRayCore] at h0 h1
  omega

/-- The four actual complementary determinants, with their original site signs. -/
theorem dilationRayCore_cofactor (i j : Fin 2) :
    dilationRayCore.cofactor i j =
      (![![complete 2, -complete 1], ![-complete 4, complete 3]] i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [BetaDiagram.cofactor, BetaDiagram.matrix, dilationRayCore,
      Fin.succAbove]

set_option backward.isDefEq.respectTransparency false in
/-- The literal single available first-variation polynomial in the example. -/
theorem dilationRayCore_unit_three :
    dilationRayCore.unitVariation 3 =
      complete 1 * complete 2 ^ 2 - complete 1 ^ 2 * complete 3 := by
  unfold BetaDiagram.unitVariation
  rw [Fin.sum_univ_two]
  simp_rw [dilationRayCore_cofactor]
  norm_num [dilationRayCore, StrictTriangularPaths.positiveGap]
  rw [Fin.sum_univ_two]
  norm_num
  ring

/-- The symmetric dense core with beta lists `(4,3)` and `(1,0)`. -/
def symmetricDenseCore : BetaDiagram 2 where
  row := ![4, 3]
  col := ![1, 0]
  row_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  col_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  row_nonempty := by intro i; fin_cases i <;> norm_num

/-- Density is checked on the actual four sites. -/
theorem symmetricDenseCore_dense : symmetricDenseCore.Dense := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [symmetricDenseCore]

/-- Reflection uses the actual center four. -/
theorem symmetricDenseCore_symmetric : symmetricDenseCore.Symmetric := by
  refine ⟨4, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [symmetricDenseCore]
  · intro i
    fin_cases i <;> norm_num [symmetricDenseCore]

/-- Its actual signed cofactors span exactly three rational dimensions. -/
theorem symmetricDenseCore_rank :
    Module.finrank ℚ (LinearMap.range (cofactorRelationMap symmetricDenseCore)) = 3 := by
  simpa using symmetric_cofactor_rank symmetricDenseCore
    symmetricDenseCore_dense symmetricDenseCore_symmetric

end SkewCofactorIndependence
