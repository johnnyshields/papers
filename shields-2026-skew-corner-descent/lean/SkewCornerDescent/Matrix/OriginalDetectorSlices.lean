/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalExposedPolynomials

/-!
# Original residue-field identities on produced regular slices

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `lem:peeling`).
The unchanged original response representatives supply regularity before each complete detector
identity is specialized. All classes, couplings, cyclic starts and repeated wraps are retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows
open scoped BigOperators

/-- An actual chamber supplies every regularity premise needed to specialize the original short
identity. No numerator or denominator nonvanishing is an additional binder.

**Differs from the paper's route.** Specializes a cleared finite detector identity rather than
transporting the original residue-prime valuation. -/
theorem originalChamber_shortDetector_zero_slice {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α]
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hanchor : ∃ a, top a = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (word : G → α) (e : α → ℤ) (step : G) (j prefixLength : ℕ) (start : G) (s m : ℕ)
    (hzero :
      let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
        algebraMap (OtherPolynomial N) (OtherField N) (p a) /
          algebraMap (OtherPolynomial N) (OtherField N) (q a)
      (s : OtherField N) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        (m : OtherField N) * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ a, (e a : OtherField N) * (response a)⁻¹) = 0) :
    let response := fun a => algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a)) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a))
    RatFunc.C (s : ℝ) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
      RatFunc.C (m : ℝ) * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
        (∑ a, RatFunc.C (e a : ℝ) * (response a)⁻¹) = 0 := by
  classical
  let source := algebraMap (OtherPolynomial N) (OtherField N)
  let φ := originalCoordinateSlice N K x
  let num := originalExposedNumerator N top p q htop
  let den := fun a => q a ^ 2
  obtain ⟨hnφ, hdφ⟩ := originalCoordinateSlice_regular N K hNK top p q htop hp hq
    hanchor positive x hx
  have hn (a : α) : num a ≠ 0 := by
    intro hz
    exact hnφ a (by change φ (num a) = 0; rw [hz, map_zero])
  have hd (a : α) : den a ≠ 0 := by
    intro hz
    exact hdφ a (by change φ (den a) = 0; rw [hz, map_zero])
  have hq0 (a : α) : q a ≠ 0 := by
    intro hz
    exact hd a (by simp only [den, hz, zero_pow (by decide : 2 ≠ 0)])
  have hsource :
      let response := fun a => source (num a) / source (den a)
      source (s : OtherPolynomial N) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        source (m : OtherPolynomial N) *
          (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ a, source (e a : OtherPolynomial N) * (response a)⁻¹) = 0 := by
    simpa only [source, num, den, originalExposedNumerator_fraction N top p q htop _ (hq0 _),
      map_natCast, map_intCast] using hzero
  have h := shortDetector_zero_specialize source φ (IsFractionRing.injective _ _)
    num den word (fun a => (e a : OtherPolynomial N)) step j prefixLength start
    (s : OtherPolynomial N) (m : OtherPolynomial N)
    (fun a => (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hn a))
    (fun a => (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hd a)) hnφ hdφ hsource
  simpa only [φ, num, den, originalCoordinateSlice, RingHom.comp_apply,
    real_originalExposedNumerator, map_pow, exposedResponseDenominator,
    map_natCast, map_intCast] using h

/-- The actual chamber also specializes the complete cross-multiplied full-period identity.
The original source fractions and the coordinate response family are identified by a proved bridge.

**Differs from the paper's route.** Uses finite common-denominator specialization, with
regularity produced from the actual exposed chamber. -/
theorem originalChamber_fullDetector_zero_slice {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α]
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hanchor : ∃ a, top a = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (word : G → α) (e : α → ℤ) (step : G)
    (fullLength periodLength prefixLength k : ℕ) (start : G) (scalar : ℕ)
    (hzero :
      let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
        algebraMap (OtherPolynomial N) (OtherField N) (p a) /
          algebraMap (OtherPolynomial N) (OtherField N) (q a)
      (scalar : OtherField N) *
          (windowProduct (response ∘ word) step periodLength start) ^ (k - 1) *
          windowProduct (response ∘ word) step prefixLength start -
        (∑ a, (e a : OtherField N) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) step fullLength i) = 0) :
    let response := fun a => algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a)) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a))
    RatFunc.C (scalar : ℝ) *
        (windowProduct (response ∘ word) step periodLength start) ^ (k - 1) *
        windowProduct (response ∘ word) step prefixLength start -
      (∑ a, RatFunc.C (e a : ℝ) * (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) step fullLength i) = 0 := by
  classical
  let source := algebraMap (OtherPolynomial N) (OtherField N)
  let φ := originalCoordinateSlice N K x
  let num := originalExposedNumerator N top p q htop
  let den := fun a => q a ^ 2
  obtain ⟨hnφ, hdφ⟩ := originalCoordinateSlice_regular N K hNK top p q htop hp hq
    hanchor positive x hx
  have hn (a : α) : num a ≠ 0 := by
    intro hz
    exact hnφ a (by change φ (num a) = 0; rw [hz, map_zero])
  have hd (a : α) : den a ≠ 0 := by
    intro hz
    exact hdφ a (by change φ (den a) = 0; rw [hz, map_zero])
  have hq0 (a : α) : q a ≠ 0 := by
    intro hz
    exact hd a (by simp only [den, hz, zero_pow (by decide : 2 ≠ 0)])
  have hsource :
      let response := fun a => source (num a) / source (den a)
      source (scalar : OtherPolynomial N) *
          (windowProduct (response ∘ word) step periodLength start) ^ (k - 1) *
          windowProduct (response ∘ word) step prefixLength start -
        (∑ a, source (e a : OtherPolynomial N) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) step fullLength i) = 0 := by
    simpa only [source, num, den, originalExposedNumerator_fraction N top p q htop _ (hq0 _),
      map_natCast, map_intCast] using hzero
  have h := fullDetector_zero_specialize source φ (IsFractionRing.injective _ _)
    num den word (fun a => (e a : OtherPolynomial N)) step fullLength periodLength prefixLength k
    start (scalar : OtherPolynomial N)
    (fun a => (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hn a))
    (fun a => (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hd a)) hnφ hdφ hsource
  simpa only [φ, num, den, originalCoordinateSlice, RingHom.comp_apply,
    real_originalExposedNumerator, map_pow, exposedResponseDenominator,
    map_natCast, map_intCast] using h

end SkewCornerDescent.Matrix
