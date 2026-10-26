/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposedWindowPoles
import SkewCornerDescent.CoordinatePolynomials
import SkewCornerDescent.ExposedRootOrders
import SkewCornerDescent.RealResponseSlices

/-!
# Exact pole orders on actual exposed coordinate slices

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
The exposed anchor is produced from the actual simultaneous response chamber. Its numerator
is proved to have a simple root, and every other factor is regular there. The resulting exact
maximal pole retains every dependence on the shared generators. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- The actual response chamber supplies the simple anchor, regular denominators and common
off-anchor sign on the faithful coordinate slice. -/
theorem simultaneousActualChamber_exposed_slice {ι : Type*} [Finite ι]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → OtherPolynomial N)
    (hp : ∀ i k, k ∈ (realResiduePolynomial N (p i)).vars → k < (top i : ℕ))
    (hq : ∀ i k, k ∈ (realResiduePolynomial N (q i)).vars → k < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive) :
    ∃ a : {i : ι // top i = K},
      let r := rationalAnchorRoot
        (fun a : {i : ι // top i = K} => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val)) a x
      let slice := coordinatePolynomial (K : ℕ) x
      let num := fun i => slice (exposedResponseNumerator N top p q i)
      let den := fun i => slice (exposedResponseDenominator N q i)
      Polynomial.eval r (num a.val) = 0 ∧
        Polynomial.rootMultiplicity r (num a.val) = 1 ∧
        (∀ i, 0 < Polynomial.eval r (den i)) ∧
        (∀ i, i ≠ a.val → 0 < (if positive then 1 else -1) *
          Polynomial.eval r (num i)) := by
  exact simultaneousRealChamber_exposed_slice N K hNK top
    (fun i => realResiduePolynomial N (p i)) (fun i => realResiduePolynomial N (q i))
    hp hq hanchor positive x hx

/-- The actual chamber supplies an exposed coordinate slice with exact maximal-window pole
order. Neither a simple-root certificate nor an off-anchor regularity premise is assumed. -/
theorem simultaneousActualChamber_cyclic_root_orders {ι G : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommGroup G] [Fintype G]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → OtherPolynomial N)
    (hp : ∀ i k, k ∈ (realResiduePolynomial N (p i)).vars → k < (top i : ℕ))
    (hq : ∀ i k, k ∈ (realResiduePolynomial N (q i)).vars → k < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (word : G → ι) (step : G) (j : ℕ) :
    ∃ a : {i : ι // top i = K},
      let r := rationalAnchorRoot
        (fun a : {i : ι // top i = K} => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val)) a x
      let slice := coordinatePolynomial (K : ℕ) x
      let num := fun i => slice (exposedResponseNumerator N top p q i)
      let den := fun i => slice (exposedResponseDenominator N q i)
      let count := fun Y i => windowSum (classMask word Y) step j i
      let bound := maximalClassWindowCount word step j
      let numerator := clearedPoleSum Finset.univ (num a.val) (bound a.val) (count a.val)
        (fun i => den a.val ^ count a.val i * ∏ Y ∈ Finset.univ.erase a.val,
          num Y ^ (bound Y - count Y i) * den Y ^ count Y i)
      let denominator := num a.val ^ bound a.val *
        ∏ Y ∈ Finset.univ.erase a.val, num Y ^ bound Y
      numerator ≠ 0 ∧ Polynomial.rootMultiplicity r numerator = 0 ∧
        denominator ≠ 0 ∧ Polynomial.rootMultiplicity r denominator = bound a.val := by
  obtain ⟨a, h⟩ := simultaneousActualChamber_exposed_slice
    N K hNK top p q hp hq hanchor positive x hx
  exact ⟨a, cyclic_inverse_window_root_orders word step j a.val _ _ _
    (if positive then 1 else -1) h.1 h.2.1 h.2.2.1 h.2.2.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
