/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposedRootOrders
import SkewCornerDescent.ExposedForwardValuation

/-!
# Exact cyclic valuations produced from original responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
Original elimination, the two actual response chambers and the simple coordinate slice
compose with the full cyclic clearing identity. No pole-order certificate is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial CyclicWindows PhaseInventory WithZero
open scoped BigOperators

/-- One actual exposed slice supplies exact reciprocal and forward valuations for every
window length. All lengths use the same anchor and unchanged dependent responses. -/
theorem simultaneousActualChamber_cyclic_valuation {ι G : Type*} [Finite ι]
    [DecidableEq ι] [AddCommGroup G] [Fintype G]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → OtherPolynomial N)
    (hp : ∀ i k, k ∈ (realResiduePolynomial N (p i)).vars → k < (top i : ℕ))
    (hq : ∀ i k, k ∈ (realResiduePolynomial N (q i)).vars → k < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (word : G → ι) (step : G) :
    ∃ a : {i : ι // top i = K},
      let r := rationalAnchorRoot
        (fun a : {i : ι // top i = K} => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val)) a x
      let slice := coordinatePolynomial (K : ℕ) x
      let num := fun i => slice (exposedResponseNumerator N top p q i)
      let den := fun i => slice (exposedResponseDenominator N q i)
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      ∀ j : ℕ,
        (exposedRootIdeal r).valuation (RatFunc ℝ)
            (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) =
          exp (maximalClassWindowCount word step j a.val : ℤ) ∧
        (exposedRootIdeal r).valuation (RatFunc ℝ)
            (∑ i, windowProduct (response ∘ word) step j i) =
          exp (-(minimalClassWindowCount word step j a.val : ℤ)) := by
  obtain ⟨a, h⟩ := simultaneousActualChamber_exposed_slice
    N K hNK top p q hp hq hanchor positive x hx
  refine ⟨a, fun j => ?_⟩
  exact ⟨cyclic_inverse_window_valuation word step j a.val _ _ _
      (if positive then 1 else -1) h.1 h.2.1 h.2.2.1 h.2.2.2,
    cyclic_forward_window_valuation word step j a.val _ _ _
      (if positive then 1 else -1) h.1 h.2.1 h.2.2.1 h.2.2.2⟩

/-- Complete original matrices produce faithful residue representatives and both exposed
cyclic valuations. All regularity, simple-root and noncancellation premises are discharged. -/
theorem originalResponses_cyclic_valuations {D : Diagram} {hD : IsConnectedSkew D}
    (c : SelectedCoordinate D hD) {ι G : Type*} [Finite ι] [DecidableEq ι]
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
    (word : G → ι) (step : G) :
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
        let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
          algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
        ∀ j : ℕ,
          (exposedRootIdeal r).valuation (RatFunc ℝ)
              (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) =
            exp (maximalClassWindowCount word step j a.val : ℤ) ∧
          (exposedRootIdeal r).valuation (RatFunc ℝ)
              (∑ i, windowProduct (response ∘ word) step j i) =
            exp (-(minimalClassWindowCount word step j a.val : ℤ)) := by
  let := Fintype.ofFinite ι
  obtain ⟨p, q, hp, hq, he, hchamber⟩ :=
    c.originalResponses_simultaneous_chambers n P b d top htop hindices hmax
      K hanchor hdistinct
  have hNK : c.top ≤ K := by
    obtain ⟨i, hi⟩ := hanchor
    exact (htop i).le.trans_eq hi
  refine ⟨p, q, he, ?_⟩
  intro positive
  obtain ⟨x, hx⟩ := (hchamber positive).2
  obtain ⟨a, ha⟩ := simultaneousActualChamber_cyclic_valuation c.top K hNK top p q
    hp hq hanchor positive x hx word step
  exact ⟨x, hx, a, ha⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
