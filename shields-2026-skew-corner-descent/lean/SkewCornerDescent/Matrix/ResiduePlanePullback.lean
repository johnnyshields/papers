/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueRationalLabels
import SkewCornerDescent.PlanePolynomial
import SkewCornerDescent.TriangularDivisors

/-!
# Actual residue-plane polynomial pullbacks

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Rational labels are derived from divisors
of the denominator-cleared plane numerator over the actual lower residue field.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

noncomputable local instance clearedPlaneRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- A linear response divisor of the cleared numerator has a rational label.
**Differs from the paper's route.** Evaluating at the response root and excluding new
algebraic constants proves linearity directly, without constructing irreducibility
of the entire plane pullback over the lower field. -/
theorem residue_plane_cleared_linear_divisor (N K : ℕ+) {A B F : OtherField N}
    (hA : A ∈ residueLowerField N K) (hB : B ∈ residueLowerField N K)
    (hF : F ∈ residueLowerField N K) (hF0 : F ≠ 0) {p : Polynomial ℚ}
    (hp : Irreducible p)
    (hd : Polynomial.X + Polynomial.C B ∣ clearedPlanePolynomial p A F) :
    p.natDegree = 1 ∧ ∃ c : ℚ, p.IsRoot c ∧ B = A - (c : OtherField N) * F := by
  have hz : (A - B) / F ∈ residueLowerField N K :=
    (residueLowerField N K).div_mem ((residueLowerField N K).sub_mem hA hB) hF
  have hr : Polynomial.aeval ((A - B) / F) p = 0 := by
    have h := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (x := -B) hd
      (by simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        neg_add_cancel])
    rw [clearedPlanePolynomial_eval p A F (-B) hF0, neg_add_eq_sub] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hF0)
  obtain ⟨hdeg, c, hc, hroot⟩ := residueLowerField_irreducible_root N K hz hp hr
  refine ⟨hdeg, c, hroot, ?_⟩
  have hcF : (c : OtherField N) * F = A - B := (eq_div_iff hF0).mp hc
  rw [hcF]
  ring

end SkewCornerDescent.Matrix
