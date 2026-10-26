/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualSimultaneousChambers
import SkewCornerDescent.ExposureLabels

/-!
# Cap signs in actual simultaneous response chambers

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Every designated off-anchor response retains its sign at all anchor roots. In particular,
two actual cap responses have positive product in either prescribed-sign chamber.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

/-- Both designated cap responses have the chamber sign and positive product at every root. -/
theorem simultaneousActualChamber_cap_product_pos {ι : Type*}
    (N K : ℕ+) (top : ι → ℕ+) (p q : ι → OtherPolynomial N) (positive : Bool)
    (left right : ι) (hl : top left ≠ K) (hr : top right ≠ K)
    (x : ℕ → ℝ) (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (a : {i : ι // top i = K}) :
    let y := anchorAssignment (K : ℕ)
      (rationalAnchorRoot (fun a => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val))) a x
    let L := rationalTriangularResponse (top left : ℕ)
      (realResiduePolynomial N (p left)) (realResiduePolynomial N (q left)) y
    let Q := rationalTriangularResponse (top right : ℕ)
      (realResiduePolynomial N (p right)) (realResiduePolynomial N (q right)) y
    responseSign positive L ∧ responseSign positive Q ∧ 0 < L * Q := by
  have hL := (hx.2.2 a ⟨left, hl⟩).2
  have hQ := (hx.2.2 a ⟨right, hr⟩).2
  exact ⟨hL, hQ, signed_cap_product_pos positive hL hQ⟩

/-- Every point of the actual simultaneous chamber has pairwise distinct anchor roots. -/
theorem simultaneousActualChamber_roots_injective {ι : Type*}
    (N K : ℕ+) (top : ι → ℕ+) (p q : ι → OtherPolynomial N) (positive : Bool)
    (x : ℕ → ℝ) (hx : x ∈ simultaneousActualChamber N K top p q positive) :
    Function.Injective (fun a : {i : ι // top i = K} =>
      rationalAnchorRoot (fun a => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val)) a x) := by
  exact simultaneousRealChamber_roots_injective K top
    (fun i => realResiduePolynomial N (p i)) (fun i => realResiduePolynomial N (q i))
    positive x hx

end SkewCornerDescent.Matrix.SelectedCoordinate
