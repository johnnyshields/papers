/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.RationalChambers

/-!
# Separating a pair inside a simultaneous positive chamber

Supports `shields-2026-skew-corner-descent.tex` (`lem:two-support`,
`cor:one-positive-short`). A nonzero cleared difference is avoided inside the
nonempty open monic-positive chamber. The result uses one common assignment for
all dependent response functions, never independent response variables. Sorry-free.
-/

namespace SkewCornerDescent

/-- One common positive assignment separates two distinct rational responses.
The full lower denominator family remains regular at that assignment. -/
theorem exists_positive_rational_family_separated {ι : Type*} [Finite ι]
    (top : ι → ℕ) (p q : ι → MvPolynomial ℕ ℝ) (N : ℕ)
    (htop : ∀ i, N ≤ top i) (hp : ∀ i j, j ∈ (p i).vars → j < top i)
    (hq : ∀ i j, j ∈ (q i).vars → j < N) (hq0 : ∀ i, q i ≠ 0)
    (a b : ι)
    (hdiff : (MvPolynomial.X (top a) * q a + p a) * q b -
      (MvPolynomial.X (top b) * q b + p b) * q a ≠ 0) :
    ∃ x : ℕ → ℝ, (∀ i, MvPolynomial.eval x (q i) ≠ 0) ∧
      (∀ i, 0 < rationalTriangularResponse (top i) (p i) (q i) x) ∧
      rationalTriangularResponse (top a) (p a) (q a) x ≠
        rationalTriangularResponse (top b) (p b) (q b) x := by
  obtain ⟨hopen, hnonempty⟩ := rational_triangular_chamber top p q N htop hp hq hq0 true
  let difference := (MvPolynomial.X (top a) * q a + p a) * q b -
    (MvPolynomial.X (top b) * q b + p b) * q a
  obtain ⟨x, hx, hvalue⟩ := exists_polynomial_ne_zero_on_open difference hdiff _ hopen hnonempty
  have hden : ∀ i, MvPolynomial.eval x (q i) ≠ 0 := fun i => (hx i).1
  have hpositive : ∀ i, 0 < rationalTriangularResponse (top i) (p i) (q i) x := by
    intro i
    have hsign := (hx i).2
    simp only [clearedTriangularResponse, map_mul, map_add, MvPolynomial.eval_X] at hsign
    exact (responseSign_div_iff_cleared true _ _ _ (hden i)).mpr hsign
  refine ⟨x, hden, hpositive, ?_⟩
  intro heq
  unfold rationalTriangularResponse at heq
  field_simp [hden a, hden b] at heq
  apply hvalue
  simp only [difference, map_sub, map_mul, map_add, MvPolynomial.eval_X]
  linear_combination heq

end SkewCornerDescent
