/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseFivePlacements

/-!
# Mixed third-label regimes

The actual five-row profiles and collected coefficient in `ex:mixed-stratum`
of `shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative.StaircaseMixedStratum

open Gluing HessenbergExpansion StaircaseFiveFamilies

/-- Parameters of the displayed mixed-regime pair. -/
def parameters : ContactParameters where
  a := 1
  b := 3
  d := 1
  d_nonneg := by decide
  a_pos := by decide
  b_gt := by decide

/-- The first actual profile has row word `(2,4,4,4,5)` and gap word `(1,1,1,2)`. -/
def firstProfile : Profile 4 := m3F parameters

/-- The second actual profile has row word `(2,4,5,4,4)` and gap word `(1,2,1,1)`. -/
def secondProfile : Profile 4 := m3H parameters

/-- Prefix, suffix, and largest three-row interval labels of a five-row profile. -/
def labelData (P : Profile 4) : ℤ × ℤ × ℤ :=
  (P.xi 0-P.zeta 3, P.xi 1-P.zeta 4,
    max (P.xi 0-P.zeta 2) (max (P.xi 1-P.zeta 3) (P.xi 2-P.zeta 4)))

private theorem first_thick : Staircase.Thick firstProfile := by
  unfold Staircase.Thick
  decide

private theorem second_thick : Staircase.Thick secondProfile := by
  unfold Staircase.Thick
  decide

/-- Both sides are actual full Schur determinants. -/
theorem schur_eq : firstProfile.toBetaDiagram.schur = secondProfile.toBetaDiagram.schur :=
  m3_schur_eq parameters

/-- The two equal functions occur in different third-label regimes. -/
theorem label_values : labelData firstProfile = (11,13,10) ∧
    labelData secondProfile = (11,13,11) := by decide

/-- The coefficient at the third supported generator on the first side. -/
theorem first_third_coefficient :
    MvPolynomial.pderiv (11 : ℕ+) firstProfile.toBetaDiagram.schur =
      -complete 5*complete 1^3 := by
  rw [Profile.toBetaDiagram_schur,schur_interval firstProfile first_thick.hessenberg]
  change MvPolynomial.pderiv (11 : ℕ+) (interval hh 2 4 4 4 5 1 1 1 2) = _
  simp only [interval,← complete_eq_hh,map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
    Staircase.residual_pderiv_complete]
  norm_num
  ring

/-- The positive and negative coincident third-label terms are retained before collection. -/
theorem second_third_terms :
    MvPolynomial.pderiv (11 : ℕ+) secondProfile.toBetaDiagram.schur =
      -complete 1^2*complete 2*complete 4+
        complete 1^2*complete 2*complete 4-complete 5*complete 1^3 := by
  rw [Profile.toBetaDiagram_schur,schur_interval secondProfile second_thick.hessenberg]
  change MvPolynomial.pderiv (11 : ℕ+) (interval hh 2 4 5 4 4 1 2 1 1) = _
  simp only [interval,← complete_eq_hh,map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
    Staircase.residual_pderiv_complete]
  norm_num
  ring

/-- Collecting the coincident terms gives exactly the coefficient on the other side. -/
theorem second_third_coefficient :
    MvPolynomial.pderiv (11 : ℕ+) secondProfile.toBetaDiagram.schur =
      -complete 5*complete 1^3 := by
  rw [second_third_terms]
  ring

/-- Full equality, both actual label regimes, and the common collected coefficient. -/
theorem mixed_stratum_example :
    firstProfile.toBetaDiagram.schur = secondProfile.toBetaDiagram.schur ∧
      labelData firstProfile = (11,13,10) ∧ labelData secondProfile = (11,13,11) ∧
      MvPolynomial.pderiv (11 : ℕ+) firstProfile.toBetaDiagram.schur = -complete 5*complete 1^3 ∧
      MvPolynomial.pderiv (11 : ℕ+) secondProfile.toBetaDiagram.schur = -complete 5*complete 1^3 :=
  ⟨schur_eq,label_values.1,label_values.2,first_third_coefficient,second_third_coefficient⟩

end SkewJacobiNegative.StaircaseMixedStratum
