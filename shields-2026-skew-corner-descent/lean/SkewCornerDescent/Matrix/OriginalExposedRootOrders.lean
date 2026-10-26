/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposedRootOrders

/-!
# Original-matrix producers of exact exposed cyclic pole orders

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
Complete original elimination supplies one faithful family of response representatives and
both exposed chambers. Their coordinate slices have exact maximal-window denominator orders
and nonvanishing leading numerators. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- The original-matrix family closes the chamber, simple-root and cyclic-count producers
without carrying any of their conclusions as hypotheses. -/
theorem originalResponses_cyclic_root_orders {D : Diagram} {hD : IsConnectedSkew D}
    (c : SelectedCoordinate D hD) {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [Fintype G]
    (n : ι → ℕ) (P : ∀ i, Profile (n i))
    (b d : ∀ i, Option (OriginalSelectedBlocks (hD := hD) (P i)))
    (top : ι → ℕ+) (htop : ∀ i, c.top < top i)
    (hindices : ∀ i, (P i).xi (originalRowSplitEquiv (hD := hD) (P i) (.inl (b i))) -
      (P i).zeta (originalColSplitEquiv (hD := hD) (P i) (.inl (d i))) = (top i : ℤ))
    (hmax : ∀ i C, C ∈ edgeComponents (diagramInterior (P i).cells) →
      span C ≤ (c.top : ℕ))
    (K : ℕ+) (hanchor : ∃ i, top i = K)
    (hdistinct : ∀ i l, top i = K → top l = K → i ≠ l →
      c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) ≠
        c.regularResidue (c.originalLocalResponse (P l) (b l) (d l)))
    (word : G → ι) (step : G) (j : ℕ) :
    ∃ p q : ι → OtherPolynomial c.top,
      (∀ i, c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) =
        residueGenerator c.top ⟨top i, ne_of_gt (htop i)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p i) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i)) ∧
      ∀ positive : Bool, ∃ x ∈ simultaneousActualChamber c.top K top p q positive,
        ∃ a : {i : ι // top i = K},
        let r := rationalAnchorRoot
          (fun a : {i : ι // top i = K} => realResiduePolynomial c.top (p a.val))
          (fun a => realResiduePolynomial c.top (q a.val)) a x
        let slice := coordinatePolynomial (K : ℕ) x
        let num := fun i => slice (exposedResponseNumerator c.top top p q i)
        let den := fun i => slice (exposedResponseDenominator c.top q i)
        let count := fun Y i => windowSum (classMask word Y) step j i
        let bound := maximalClassWindowCount word step j
        let numerator := clearedPoleSum Finset.univ (num a.val) (bound a.val) (count a.val)
          (fun i => den a.val ^ count a.val i * ∏ Y ∈ Finset.univ.erase a.val,
            num Y ^ (bound Y - count Y i) * den Y ^ count Y i)
        let denominator := num a.val ^ bound a.val *
          ∏ Y ∈ Finset.univ.erase a.val, num Y ^ bound Y
        numerator ≠ 0 ∧ Polynomial.rootMultiplicity r numerator = 0 ∧
          denominator ≠ 0 ∧ Polynomial.rootMultiplicity r denominator = bound a.val := by
  classical
  obtain ⟨p, q, hp, hq, he, hchamber⟩ :=
    c.originalResponses_simultaneous_chambers n P b d top htop hindices hmax
      K hanchor hdistinct
  have hNK : c.top ≤ K := by
    obtain ⟨i, hi⟩ := hanchor
    exact (htop i).le.trans_eq hi
  refine ⟨p, q, he, ?_⟩
  intro positive
  obtain ⟨x, hx⟩ := (hchamber positive).2
  obtain ⟨a, ha⟩ := simultaneousActualChamber_cyclic_root_orders c.top K hNK top p q
    hp hq hanchor positive x hx word step j
  exact ⟨x, hx, a, ha⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
