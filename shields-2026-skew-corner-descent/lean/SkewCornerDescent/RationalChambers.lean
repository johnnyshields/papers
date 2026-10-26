/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularChambers
import SkewCornerDescent.PolynomialChambers

/-!
# Regular rational triangular chambers

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Nonzero lower denominators are avoided before higher coordinates are chosen. Every rational
monic triangular response then has the chosen sign, and squared-denominator clearing exhibits
both sign domains as nonempty open polynomial chambers.

Sorry-free.
-/

namespace SkewCornerDescent

/-- The literal real specialization of a monic response with a lower correction denominator. -/
noncomputable def rationalTriangularResponse (J : ℕ) (p q : MvPolynomial ℕ ℝ)
    (x : ℕ → ℝ) : ℝ :=
  x J + MvPolynomial.eval x p / MvPolynomial.eval x q

/-- A supported polynomial's value only sees the specified lower coordinates. -/
theorem eval_polynomial_eq_of_agree_below (p : MvPolynomial ℕ ℝ) (J : ℕ)
    (hp : ∀ j ∈ p.vars, j < J) (x y : ℕ → ℝ) (hxy : ∀ j, j < J → x j = y j) :
    MvPolynomial.eval x p = MvPolynomial.eval y p := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro j hj _
  exact hxy j (hp j hj)

/-- Rational corrections with strictly lower numerators and denominators remain triangular. -/
theorem rational_correction_locality (top : ℕ) (p q : MvPolynomial ℕ ℝ)
    (hp : ∀ j ∈ p.vars, j < top) (hq : ∀ j ∈ q.vars, j < top)
    (x y : ℕ → ℝ) (hxy : ∀ j, j < top → x j = y j) :
    MvPolynomial.eval x p / MvPolynomial.eval x q =
      MvPolynomial.eval y p / MvPolynomial.eval y q := by
  rw [eval_polynomial_eq_of_agree_below p top hp x y hxy,
    eval_polynomial_eq_of_agree_below q top hq x y hxy]

/-- Either sign is attainable for a finite rational triangular family with regular denominators. -/
theorem exists_signed_rational_triangular_family {ι : Type*} [Finite ι]
    (top : ι → ℕ) (p q : ι → MvPolynomial ℕ ℝ) (N : ℕ)
    (htop : ∀ i, N ≤ top i) (hp : ∀ i j, j ∈ (p i).vars → j < top i)
    (hq : ∀ i j, j ∈ (q i).vars → j < N) (hq0 : ∀ i, q i ≠ 0)
    (positive : Bool) :
    ∃ x : ℕ → ℝ, (∀ i, MvPolynomial.eval x (q i) ≠ 0) ∧
      ∀ i, responseSign positive (rationalTriangularResponse (top i) (p i) (q i) x) := by
  obtain ⟨base, _, hbase⟩ := exists_finite_polynomials_ne_zero_on_open q hq0
    Set.univ isOpen_univ ⟨fun _ => 0, Set.mem_univ _⟩
  obtain ⟨x, hx, hs⟩ := exists_signed_triangular_assignment top
    (fun i x => MvPolynomial.eval x (p i) / MvPolynomial.eval x (q i)) N htop
    (fun i x y hxy => rational_correction_locality (top i) (p i) (q i) (hp i)
      (fun j hj => lt_of_lt_of_le (hq i j hj) (htop i)) x y hxy) base positive
  refine ⟨x, ?_, hs⟩
  intro i
  rw [eval_polynomial_eq_of_agree_below (q i) N (hq i) x base hx]
  exact hbase i

/-- Positive squared-denominator clearing preserves either strict sign. -/
theorem responseSign_div_iff_cleared (positive : Bool) (a b c : ℝ) (hc : c ≠ 0) :
    responseSign positive (a + b / c) ↔ responseSign positive ((a * c + b) * c) := by
  have he : (a + b / c) * c ^ 2 = (a * c + b) * c := by field_simp
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  rw [← he]
  cases positive
  · change a + b / c < 0 ↔ (a + b / c) * c ^ 2 < 0
    constructor
    · intro h
      exact mul_neg_of_neg_of_pos h hc2
    · intro h
      by_contra hh
      have := mul_nonneg (le_of_not_gt hh) hc2.le
      linarith
  · change 0 < a + b / c ↔ 0 < (a + b / c) * c ^ 2
    exact (mul_pos_iff_of_pos_right hc2).symm

/-- The sign-equivalent polynomial obtained by positive squared-denominator clearing. -/
noncomputable def clearedTriangularResponse (J : ℕ) (p q : MvPolynomial ℕ ℝ) :
    MvPolynomial ℕ ℝ :=
  (MvPolynomial.X J * q + p) * q

/-- The rational sign chamber is nonempty and open, with every denominator explicitly nonzero. -/
theorem rational_triangular_chamber {ι : Type*} [Finite ι]
    (top : ι → ℕ) (p q : ι → MvPolynomial ℕ ℝ) (N : ℕ)
    (htop : ∀ i, N ≤ top i) (hp : ∀ i j, j ∈ (p i).vars → j < top i)
    (hq : ∀ i j, j ∈ (q i).vars → j < N) (hq0 : ∀ i, q i ≠ 0)
    (positive : Bool) :
    IsOpen {x : ℕ → ℝ | ∀ i, MvPolynomial.eval x (q i) ≠ 0 ∧
      responseSign positive (MvPolynomial.eval x (clearedTriangularResponse (top i) (p i) (q i)))} ∧
    ({x : ℕ → ℝ | ∀ i, MvPolynomial.eval x (q i) ≠ 0 ∧
      responseSign positive (MvPolynomial.eval x (clearedTriangularResponse (top i) (p i) (q i)))} :
      Set (ℕ → ℝ)).Nonempty := by
  constructor
  · simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply (isOpen_ne.preimage (q i).continuous_eval).inter
    have hcont := (clearedTriangularResponse (top i) (p i) (q i)).continuous_eval
    cases positive
    · exact isOpen_lt hcont continuous_const
    · exact isOpen_lt continuous_const hcont
  · obtain ⟨x, hx, hs⟩ := exists_signed_rational_triangular_family top p q N htop hp hq hq0 positive
    refine ⟨x, fun i => ⟨hx i, ?_⟩⟩
    simp only [clearedTriangularResponse, map_mul, map_add, MvPolynomial.eval_X]
    exact (responseSign_div_iff_cleared positive _ _ _ (hx i)).mp (hs i)

end SkewCornerDescent
