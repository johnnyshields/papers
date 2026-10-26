/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.NonDenseResonance
import SkewJacobiNegative.SixRowBoundaryQuartets

/-!
# The resonance component inside the eight-negative quartet

Actual coordinate and cofactor correspondence in `prop:nondense-resonance`.
The three-row component is related by a proved motion, not identified by
its polynomial degree.
-/
namespace SkewJacobiNegative.NonDenseResonance
open Gluing
set_option backward.isDefEq.respectTransparency false

def quartetParameters (p : Parameters) : SixRowBoundary.Parameters where
  q := p.q
  b := p.b
  g := p.g
  q_pos := by exact_mod_cast p.q_pos
  q_le_b := by exact_mod_cast p.q_lt_b.le
  b_lt_g := by exact_mod_cast p.b_lt_g

theorem quartet_s (p : Parameters) : (quartetParameters p).s = (p.s : ℤ) := by
  have hb := p.q_lt_b.le
  simp only [quartetParameters, SixRowBoundary.Parameters.s, Parameters.s,
    Int.ofNat_sub hb]

/-- The half-turn of the actual corner component is the resonance diagram,
up to the common beta-list translation. -/
theorem quartet_core_rotation (p : Parameters) :
    (diagram p).TranslationEquivalent (quartetParameters p).coreEight.rotate := by
  refine ⟨(p.b : ℤ) + 2*p.g, ?_, ?_⟩ <;> intro i
  all_goals fin_cases i
  all_goals simp [diagram, profile, Profile.toBetaDiagram, Profile.xi, Profile.zeta,
    Fin.sum_univ_succ, BetaDiagram.rotate, SixRowBoundary.Parameters.coreEight,
    quartetParameters, Fin.rev, Parameters.s, Int.ofNat_sub p.q_lt_b.le]
  all_goals ring

/-- Both actual eight-negative parents have precisely the same corner
coefficient, with its reducible two-singleton factor retained. -/
theorem quartet_corner_coefficient (p : Parameters) (e : Bool) :
    ((quartetParameters p).diagram (if e then .h8 else .f8)).cornerCoefficient =
      -(h p.s ^ 2 * (diagram p).schur) := by
  rw [SixRowBoundary.Parameters.corner_eight_coefficient]
  have hc := (quartet_core_rotation p).schur_eq
  rw [BetaDiagram.rotate_schur] at hc
  rw [← hc, quartet_s]
  rfl

/-- The two orders are genuinely different even though their nonlinear
component has the same Schur polynomial. -/
theorem quartet_component_orders (p : Parameters) :
    let P := quartetParameters p
    let hs : 0 < P.s := by
      rw [quartet_s]
      exact_mod_cast (show 0 < p.s from by
        have := p.q_lt_b; simp [Parameters.s]; omega)
    ((P.sourceDecomposition .f8 hs).components.map Sigma.fst) = [1,3,1] ∧
      ((P.sourceDecomposition .h8 hs).components.map Sigma.fst) = [3,1,1] := by
  dsimp only
  exact ⟨SixRowBoundary.Parameters.source_component_rows _ _ _,
    SixRowBoundary.Parameters.source_component_rows _ _ _⟩

end SkewJacobiNegative.NonDenseResonance
