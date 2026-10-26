/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFaithfulSlices
import SkewCornerDescent.Matrix.OriginalExposedValuations
import SkewCornerDescent.Matrix.ActualResiduePrimes
import SkewCornerDescent.SignedClosurePole
import SkewCornerDescent.InactiveExposedPoles

/-!
# Actual response-prime valuations on the unchanged original residue field

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
The exposed chamber contains a faithful assignment, so its coordinate slice
extends to the whole original fraction field. Pulling back the normalized
root valuation therefore gives a genuine original-field valuation. The
selected original response is a produced prime, has order one, and every
nonzero off-coordinate polynomial is a unit. Complete cyclic pole orders
are identified by this full field map, not by a finite specialization.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial CyclicWindows PhaseInventory WithZero
open scoped BigOperators

set_option maxHeartbeats 1200000 in
-- The actual polynomial representatives, full field map and cyclic valuation share dependent indices.
/-- Complete original matrices produce a response-prime valuation of the
unchanged original field whose cyclic orders equal the certified exposed
root orders. All coordinate regularity and leading terms are produced.

**Differs from the paper's route.** A Baire-generic point inside the exposed
chamber makes the coordinate slice injective on the whole source field,
so the root valuation pulls back through a genuine field map. -/
theorem originalResponses_response_prime_valuations {D : Diagram} {hD : IsConnectedSkew D}
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
    (hdistinct : ∀ i j, top i = K → top j = K → i ≠ j →
      c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) ≠
        c.regularResidue (c.originalLocalResponse (P j) (b j) (d j)))
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
      ∃ φ : OtherField c.top →+* RatFunc ℝ,
        (∀ f : OtherPolynomial c.top,
          φ (algebraMap (OtherPolynomial c.top) (OtherField c.top) f) =
            originalCoordinateSlice c.top K x f) ∧
        let v := ((exposedRootIdeal r).valuation (RatFunc ℝ)).comap φ
        let response := fun i => c.regularResidue (c.originalLocalResponse (P i) (b i) (d i))
        (∃ SX : actualResiduePolynomialAlgebra c.top,
          (SX : OtherField c.top) = response a.val ∧ Prime SX) ∧
        (∀ f : OtherPolynomial c.top, f ≠ 0 →
          (K : ℕ) ∉ (realResiduePolynomial c.top f).vars →
            v (algebraMap (OtherPolynomial c.top) (OtherField c.top) f) = 1) ∧
        v (response a.val) = exp (-1 : ℤ) ∧
        (∀ i, i ≠ a.val → v (response i) = 1) ∧
        (∀ e : ι → ℤ,
          (e a.val = 0 → v (∑ i, (e i : OtherField c.top) * (response i)⁻¹) ≤ 1) ∧
          (e a.val ≠ 0 → v (∑ i, (e i : OtherField c.top) * (response i)⁻¹) =
            exp (1 : ℤ))) ∧
        ∀ j : ℕ,
          v (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) =
            exp (maximalClassWindowCount word step j a.val : ℤ) ∧
          v (∑ i, windowProduct (response ∘ word) step j i) =
            exp (-(minimalClassWindowCount word step j a.val : ℤ)) := by
  classical
  obtain ⟨p, q, hp, hq, he, hchamber⟩ :=
    c.originalResponses_simultaneous_chambers n P b d top htop hindices hmax K hanchor hdistinct
  have hNK : c.top ≤ K := by
    obtain ⟨i, hi⟩ := hanchor
    exact (htop i).le.trans_eq hi
  refine ⟨p, q, he, ?_⟩
  intro positive
  obtain ⟨x, hx, hxfaithful⟩ := exists_faithful_original_coordinate_slice c.top K
    (simultaneousActualChamber c.top K top p q positive)
    (hchamber positive).1 (hchamber positive).2
  obtain ⟨a, hroot, hsimple, hden, hsign⟩ :=
    simultaneousActualChamber_exposed_slice c.top K hNK top p q hp hq hanchor positive x hx
  let r := rationalAnchorRoot
    (fun a : {i : ι // top i = K} => realResiduePolynomial c.top (p a.val))
    (fun a => realResiduePolynomial c.top (q a.val)) a x
  let num := fun i => coordinatePolynomial (K : ℕ) x
    (exposedResponseNumerator c.top top p q i)
  let den := fun i => coordinatePolynomial (K : ℕ) x (exposedResponseDenominator c.top q i)
  let response := fun i => c.regularResidue (c.originalLocalResponse (P i) (b i) (d i))
  let φ := originalCoordinateFieldSlice c.top K x hxfaithful
  let v := ((exposedRootIdeal r).valuation (RatFunc ℝ)).comap φ
  have hmap (i : ι) : φ (response i) =
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (num i) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den i) := by
    have hq0 : q i ≠ 0 := by
      intro hz
      have hd := hden i
      simp only [exposedResponseDenominator, hz, map_zero, zero_pow (by decide : 2 ≠ 0),
        Polynomial.eval_zero] at hd
      exact lt_irrefl 0 hd
    have hn := originalExposedNumerator_fraction c.top top p q
      (fun i => ne_of_gt (htop i)) i hq0
    have hs : response i =
        algebraMap (OtherPolynomial c.top) (OtherField c.top)
          (originalExposedNumerator c.top top p q (fun i => ne_of_gt (htop i)) i) /
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i ^ 2) :=
      (he i).trans hn.symm
    rw [hs, map_div₀]
    simp only [φ, num, den, originalCoordinateFieldSlice_algebraMap, originalCoordinateSlice,
      RingHom.comp_apply, real_originalExposedNumerator, exposedResponseDenominator, map_pow]
  dsimp only [response] at hmap
  have hn0 : num a.val ≠ 0 := by
    intro hz
    have hs : Polynomial.rootMultiplicity r (num a.val) = 1 := hsimple
    rw [hz, Polynomial.rootMultiplicity_zero] at hs
    exact Nat.zero_ne_one hs
  have hd0 : den a.val ≠ 0 := by
    intro hz
    have hd : 0 < Polynomial.eval r (den a.val) := hden a.val
    rw [hz, Polynomial.eval_zero] at hd
    exact lt_irrefl 0 hd
  have hregular (i : ι) (hi : i ≠ a.val) : Polynomial.eval r (num i) ≠ 0 := by
    intro hz
    have hs : 0 < (if positive then 1 else -1) * Polynomial.eval r (num i) := hsign i hi
    rw [hz, mul_zero] at hs
    exact lt_irrefl 0 hs
  have hsum (e : ι → ℤ) :
      φ (∑ i, (e i : OtherField c.top) * (response i)⁻¹) =
        ∑ i, RatFunc.C (e i : ℝ) * algebraMap (Polynomial ℝ) (RatFunc ℝ) (den i) /
          algebraMap (Polynomial ℝ) (RatFunc ℝ) (num i) := by
    simp only [map_sum, map_mul, map_intCast, map_inv₀, response, hmap, inv_div,
      mul_div_assoc]
  refine ⟨x, hx, a, φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact originalCoordinateFieldSlice_algebraMap c.top K x hxfaithful f
  · exact c.originalLocalResponse_residue_prime (P a.val) (b a.val) (d a.val)
      (top a.val) (htop a.val) (hindices a.val) (hmax a.val)
  · intro f hf hnot
    exact originalCoordinateFieldSlice_off_coordinate_unit c.top K x hxfaithful r f hf hnot
  · change (exposedRootIdeal r).valuation (RatFunc ℝ) (φ (response a.val)) = _
    rw [hmap, map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      exposedRoot_intValuation r _ hn0, exposedRoot_intValuation r _ hd0]
    have hdorder : Polynomial.rootMultiplicity r (den a.val) = 0 :=
      Polynomial.rootMultiplicity_eq_zero
        (show Polynomial.eval r (den a.val) ≠ 0 from ne_of_gt (hden a.val))
    rw [show Polynomial.rootMultiplicity r (num a.val) = 1 from hsimple, hdorder]
    simp only [Nat.cast_one, Nat.cast_zero, neg_zero, exp_zero, div_one]
  · intro i hi
    change (exposedRootIdeal r).valuation (RatFunc ℝ) (φ (response i)) = 1
    rw [hmap]
    exact exposedRoot_regular_fraction r (num i) (den i) (hregular i hi) (ne_of_gt (hden i))
  · intro e
    constructor
    · intro he0
      change (exposedRootIdeal r).valuation (RatFunc ℝ)
        (φ (∑ i, (e i : OtherField c.top) * (response i)⁻¹)) ≤ 1
      rw [hsum]
      simpa only [inv_div, mul_div_assoc] using
        inactive_labelSum_valuation_le_one num den (fun i => (e i : ℝ)) a.val r
          (fun i => ne_of_gt (hden i)) hregular (by exact_mod_cast he0)
    · intro hene
      change (exposedRootIdeal r).valuation (RatFunc ℝ)
        (φ (∑ i, (e i : OtherField c.top) * (response i)⁻¹)) = exp (1 : ℤ)
      rw [hsum]
      exact signedInverseResponses_pole num den (fun i => (e i : ℝ)) a.val r
        hroot hsimple hregular (ne_of_gt (hden a.val)) (by exact_mod_cast hene)
  · intro j
    constructor
    · have hv := cyclic_inverse_window_valuation word step j a.val num den r
        (if positive then 1 else -1) hroot hsimple hden hsign
      simpa only [v, Valuation.comap_apply, map_sum, map_inv₀, windowProduct, map_prod,
        Function.comp_apply, hmap] using hv
    · have hv := cyclic_forward_window_valuation word step j a.val num den r
        (if positive then 1 else -1) hroot hsimple hden hsign
      simpa only [v, Valuation.comap_apply, map_sum, windowProduct, map_prod,
        Function.comp_apply, hmap] using hv

end SkewCornerDescent.Matrix.SelectedCoordinate
