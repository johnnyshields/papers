/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MixedExample
import SkewMarkedFactor.ModifiedMap

/-!
# The modified map on the mixed example

«Explicit formulas and examples» (`sec:examples`, `eq:mixed-example`) of
`shields-2026-skew-marked-factor.tex`: `Φ(h₂) = h₁ P` and `Φ(e₂) = -s_{(3,2,1)}`.
-/

set_option maxRecDepth 4096

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The column domino. -/
def mixedExampleColumn : Diagram := skewOf [1, 1] []

/-- The composite of the column domino: the supplemental singleton fills the missing cell. -/
theorem mixedExampleColumn_composite :
    mixedExampleMark.compose mixedExampleColumn = translate (0, -1) (skewOf [3, 2, 1] []) := by
  decide +kernel

/-- The row profile of the staircase `(3,2,1)`. -/
def staircaseProfile : Profile 2 where
  r := ![3, 2, 1]
  g := ![1, 0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

theorem staircase_cells : skewOf [3, 2, 1] [] = translate (0, -2) staircaseProfile.cells := by
  decide +kernel

/-- The Jacobi–Trudi determinant of the staircase. -/
theorem staircase_schur : cellSchur (skewOf [3, 2, 1] []) =
    X 1 * X 2 * X 3 - X 3 ^ 2 - X 1 ^ 2 * X 4 + X 1 * X 5 := by
  rw [staircase_cells, cellSchur_translate, cellSchur_cells, Profile.schur, Matrix.det_fin_three]
  norm_num [Profile.xi, Profile.zeta, staircaseProfile, Fin.sum_univ_succ, hh, hPos]
  ring

theorem mixedExample_rowComposite_two :
    rowComposite mixedExampleMark 2 = mixedExampleParent := rfl

theorem mixedExample_rowComposite_one :
    rowComposite mixedExampleMark 1 = mixedExampleInner := by
  unfold rowComposite mixedExampleMark mixedExampleInner
  decide +kernel

/-- `Φ(h₂) = h₁ P`. -/
theorem mixedExample_Phi_h2 :
    compositionMap mixedExampleMark (X 2) = X 1 * cellSchur mixedExampleParent := by
  rw [compositionMap_X]
  unfold modifiedGen
  rw [show ((2 : ℕ+) : ℕ) = 2 from rfl, mixedExampleMark_normalizers.1,
    mixedExample_rowComposite_two]
  simp

/-- `Φ(e₂) = -s_{(3,2,1)}`, with the sign carried by the lower vertical end. -/
theorem mixedExample_Phi_e2 :
    compositionMap mixedExampleMark (elem 2) = -cellSchur (skewOf [3, 2, 1] []) := by
  have h1 : compositionMap mixedExampleMark (X 1) = X 1 * X 2 - X 3 := by
    rw [compositionMap_X]
    unfold modifiedGen
    rw [show ((1 : ℕ+) : ℕ) = 1 from rfl, mixedExample_rowComposite_one, mixedExampleInner_schur]
    simp
  rw [elem_two, map_sub, map_pow, h1, mixedExample_Phi_h2, mixedExampleParent_schur,
    staircase_schur]
  ring

end SkewMarkedFactor
