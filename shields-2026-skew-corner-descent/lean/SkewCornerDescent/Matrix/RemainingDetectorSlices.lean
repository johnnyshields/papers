/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.RemainingResponseRepresentatives

/-!
# Original detectors on remaining-family chambers

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
Finite inactive masks preserve the original dependent zero identities. A chamber of the
remaining actual family then specializes those identities with every replaced coordinate
taking the chamber sign. All literal positions, cyclic starts and wraps remain present.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- Finite inactive replacement and actual specialization compose for the complete short
identity. Both original-field nonvanishing and slice regularity are produced.

**Differs from the paper's route.** Specializes the preserved finite zero identity rather
than transporting valuations on the original residue field. -/
theorem remainingActualChamber_shortDetector_zero {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α]
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0)
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive)
    (word : G → α) (e : α → ℤ) (step : G)
    (j prefixLength : ℕ) (start : G) (s m : ℕ)
    (he : ∀ a ∈ S, e a = 0)
    (hcount : ∀ a ∈ S, ∀ i, windowSum (classMask word a) step j i =
      windowSum (classMask word a) step prefixLength start)
    (hzero :
      let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
        algebraMap (OtherPolynomial N) (OtherField N) (p a) /
          algebraMap (OtherPolynomial N) (OtherField N) (q a)
      (s : OtherField N) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        (m : OtherField N) * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ a, (e a : OtherField N) * (response a)⁻¹) = 0) :
    let original := fun a => algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a)) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a))
    let response := replaceResponses S original (fun _ => RatFunc.C (if positive then 1 else -1))
    RatFunc.C (s : ℝ) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
      RatFunc.C (m : ℝ) * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
        (∑ a, RatFunc.C (e a : ℝ) * (response a)⁻¹) = 0 := by
  classical
  let source := algebraMap (OtherPolynomial N) (OtherField N)
  let φ := originalCoordinateSlice N K x
  let original := fun a => residueGenerator N ⟨top a, htop a⟩ + source (p a) / source (q a)
  let replacement : α → OtherField N := fun _ => if positive then 1 else -1
  let labels : α → OtherField N := fun a => (e a : OtherField N)
  have hsource := (shortDetector_replace_zero_iff word original replacement labels step
    j prefixLength start (s : OtherField N) (m : OtherField N) S
    (originalMonicResponse_ne_zero N top p q htop hNtop hp hq hq0)
    (by intro a ha; cases positive <;> simp only [replacement, Bool.false_eq_true,
      ite_false, ite_true, neg_ne_zero] <;> norm_num)
    (by intro a ha; simp only [labels, he a ha, Int.cast_zero]) hcount).mp hzero
  obtain ⟨num, den, hsourceRep, hnmap, hdmap, hnφ, hdφ⟩ :=
    remainingActualChamber_response_representatives S N K hNK top p q htop hp hq
      hanchor positive x hx
  have hn (a : α) : source (num a) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    intro hz
    exact hnφ a (by rw [hz, map_zero])
  have hd (a : α) : source (den a) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    intro hz
    exact hdφ a (by rw [hz, map_zero])
  have hsource' :
      let response := fun a => source (num a) / source (den a)
      source (s : OtherPolynomial N) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        source (m : OtherPolynomial N) *
          (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ a, source (e a : OtherPolynomial N) * (response a)⁻¹) = 0 := by
    simpa only [source, map_natCast, map_intCast, hsourceRep, labels] using hsource
  have htarget := shortDetector_zero_specialize source φ (IsFractionRing.injective _ _)
    num den word (fun a => (e a : OtherPolynomial N)) step j prefixLength start
    (s : OtherPolynomial N) (m : OtherPolynomial N) hn hd hnφ hdφ hsource'
  have htargetEq : (fun a => φ (num a) / φ (den a)) =
      replaceResponses S (fun a => algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a)) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ)
          (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a)))
        (fun _ => RatFunc.C (if positive then 1 else -1)) := by
    funext a
    rw [hnmap, hdmap]
    by_cases ha : a ∈ S <;> simp only [replaceResponses, ha, ite_true, ite_false, div_one]
  have htargetPoint (a : α) := congrFun htargetEq a
  simpa only [map_natCast, map_intCast, htargetPoint] using htarget

/-- Finite inactive replacement and actual specialization also preserve the complete
forward identity, including its whole-cycle power.

**Differs from the paper's route.** Specializes a finite cleared identity through the
actual remaining-family chamber, without extending its map to the whole residue field. -/
theorem remainingActualChamber_fullDetector_zero {α : Type*}
    [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0)
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive)
    (word : ZMod n → α) (e : α → ℤ) (m prefixLength k scalar : ℕ)
    (he : ∀ a ∈ S, e a = 0)
    (hcount : ∀ a ∈ S, ∀ i, windowSum (classMask word a) 1 m i =
      windowSum (classMask word a) 1 prefixLength 0)
    (hzero :
      let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
        algebraMap (OtherPolynomial N) (OtherField N) (p a) /
          algebraMap (OtherPolynomial N) (OtherField N) (q a)
      (scalar : OtherField N) * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 prefixLength 0 -
        (∑ a, (e a : OtherField N) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0) :
    let original := fun a => algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a)) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a))
    let response := replaceResponses S original (fun _ => RatFunc.C (if positive then 1 else -1))
    RatFunc.C (scalar : ℝ) * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 prefixLength 0 -
      (∑ a, RatFunc.C (e a : ℝ) * (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0 := by
  classical
  let source := algebraMap (OtherPolynomial N) (OtherField N)
  let φ := originalCoordinateSlice N K x
  let original := fun a => residueGenerator N ⟨top a, htop a⟩ + source (p a) / source (q a)
  let replacement : α → OtherField N := fun _ => if positive then 1 else -1
  let labels : α → OtherField N := fun a => (e a : OtherField N)
  have hsource := (fullDetector_replace_zero_iff word original replacement labels
    m prefixLength k (scalar : OtherField N) S
    (originalMonicResponse_ne_zero N top p q htop hNtop hp hq hq0)
    (by intro a ha; cases positive <;> simp only [replacement, Bool.false_eq_true,
      ite_false, ite_true, neg_ne_zero] <;> norm_num)
    (by intro a ha; simp only [labels, he a ha, Int.cast_zero]) hcount).mp hzero
  obtain ⟨num, den, hsourceRep, hnmap, hdmap, hnφ, hdφ⟩ :=
    remainingActualChamber_response_representatives S N K hNK top p q htop hp hq
      hanchor positive x hx
  have hn (a : α) : source (num a) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    intro hz
    exact hnφ a (by rw [hz, map_zero])
  have hd (a : α) : source (den a) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    intro hz
    exact hdφ a (by rw [hz, map_zero])
  have hsource' :
      let response := fun a => source (num a) / source (den a)
      source (scalar : OtherPolynomial N) *
          (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 prefixLength 0 -
        (∑ a, source (e a : OtherPolynomial N) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0 := by
    simpa only [source, map_natCast, map_intCast, hsourceRep, labels] using hsource
  have htarget := fullDetector_zero_specialize source φ (IsFractionRing.injective _ _)
    num den word (fun a => (e a : OtherPolynomial N)) 1 ((k - 1) * n + m) n prefixLength k
    0 (scalar : OtherPolynomial N) hn hd hnφ hdφ hsource'
  have htargetEq : (fun a => φ (num a) / φ (den a)) =
      replaceResponses S (fun a => algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a)) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ)
          (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a)))
        (fun _ => RatFunc.C (if positive then 1 else -1)) := by
    funext a
    rw [hnmap, hdmap]
    by_cases ha : a ∈ S <;> simp only [replaceResponses, ha, ite_true, ite_false, div_one]
  have htargetPoint (a : α) := congrFun htargetEq a
  simpa only [map_natCast, map_intCast, htargetPoint] using htarget

end SkewCornerDescent.Matrix
