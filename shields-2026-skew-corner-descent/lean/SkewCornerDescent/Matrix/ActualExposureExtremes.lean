/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualExposureCaps
import SkewCornerDescent.Matrix.TrueCapExposureTops

/-!
# Exposed extremes in actual simultaneous chambers

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

At every point of either simultaneous chamber, an extreme anchor root zeros its own
response and leaves every other factor strictly signed and regular. The designated
true-cap responses retain a positive product.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

/-- An extreme anchor exposes one actual represented class and signs every remaining factor. -/
theorem simultaneousActualChamber_exposed_extreme {ι : Type*} [Finite ι]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → OtherPolynomial N)
    (hp : ∀ i j, j ∈ (realResiduePolynomial N (p i)).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (realResiduePolynomial N (q i)).vars → j < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool)
    (x : ℕ → ℝ) (hx : x ∈ simultaneousActualChamber N K top p q positive) :
    ∃ a : {i : ι // top i = K},
      let y := anchorAssignment (K : ℕ)
        (rationalAnchorRoot (fun a => realResiduePolynomial N (p a.val))
          (fun a => realResiduePolynomial N (q a.val))) a x
      rationalTriangularResponse (K : ℕ) (realResiduePolynomial N (p a.val))
        (realResiduePolynomial N (q a.val)) y = 0 ∧
      (∀ i, MvPolynomial.eval y (realResiduePolynomial N (q i)) ≠ 0) ∧
      ∀ i, i ≠ a.val → responseSign positive
        (rationalTriangularResponse (top i : ℕ) (realResiduePolynomial N (p i))
          (realResiduePolynomial N (q i)) y) := by
  exact simultaneousRealChamber_exposed_extreme N K hNK top
    (fun i => realResiduePolynomial N (p i)) (fun i => realResiduePolynomial N (q i))
    hp hq hanchor positive x hx

end SkewCornerDescent.Matrix.SelectedCoordinate
