/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.NonVNormalization

/-!
# Finite caps cannot be replaced by complete hatted marks

Formalizes `shields-2026-skew-corner-descent.tex` (`rem:comparison-v`).
The actual legal non-V family has a finite cap product different from the
square of its full hatted-mark function. The actual one-copy row cofactor
already rejects that replacement. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- The actual first-generator cap square differs from the full second-generator hat square. -/
theorem first_second_generator_squares_ne : hh 1 ^ 2 ≠ hh 2 ^ 2 := by
  intro he
  let φ : Lambda →+* ℚ := eval₂Hom (RingHom.id ℚ) (fun j : ℕ+ => if j = 1 then 1 else 0)
  have h := congrArg φ he
  change φ ((X (1 : ℕ+) : Lambda) ^ 2) = φ ((X (2 : ℕ+) : Lambda) ^ 2) at h
  norm_num [φ] at h

/-- Every legal member of the actual non-V family rejects the proposed
replacement of its two finite caps by two full hatted marks. -/
theorem nonVMark_finite_caps_ne_two_hats (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).normalTheta (nonVMark_isLegal k hk) ≠
      (nonVMark k).normalB (nonVMark_isLegal k hk) ^ 2 := by
  rw [nonVMark_normalTheta k hk, nonVMark_normalB k hk]
  exact first_second_generator_squares_ne

/-- The complete actual one-copy row cofactor is already a counterexample
within the legal domain; no asymptotic or incomplete cap model is used. -/
theorem nonVMark_one_row_cofactor_ne_two_hats (k : ℕ) (hk : 3 ≤ k) :
    cellSchur (diagramInterior ((nonVMark k).compose (horizontalRow 1)))
      ((nonVMark_isLegal k hk).isConnectedSkew_compose_horizontalRow_all (by decide)).1.interior ≠
        (nonVMark k).normalB (nonVMark_isLegal k hk) ^ 2 := by
  rw [nonVMark_row_cofactor k hk (by decide : 1 ≤ 1), nonVMark_normalB k hk]
  simp only [Nat.sub_self, pow_zero, mul_one]
  exact first_second_generator_squares_ne

end SkewCornerDescent
