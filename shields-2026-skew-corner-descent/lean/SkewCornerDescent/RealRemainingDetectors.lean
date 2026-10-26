/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealResponseRegularity

/-!
# Finite inactive replacements and real detector specialization

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-general`).
Every finite inactive replacement preserves the complete source identity. The remaining
real chamber produces regular representatives before specialization; no homomorphism on
the entire source fraction field is asserted. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- The complete short zero identity survives finite inactive replacement and specialization
through a real remaining-family chamber.

**Differs from the paper's route.** Clears the finite dependent detector expression before
specializing, rather than transporting valuations through the source fraction field. -/
theorem remainingRealChamber_shortDetector_zero {G α F : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [Field F]
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (hqφ : ∀ i, φ (q i) ≠ 0)
    (hresponse : ∀ i, φ (X (top i : ℕ)) + φ (p i) / φ (q i) ≠ 0)
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive)
    (word : G → α) (e : α → ℤ) (step : G)
    (j prefixLength : ℕ) (start : G) (s m : ℕ)
    (he : ∀ a ∈ S, e a = 0)
    (hcount : ∀ a ∈ S, ∀ i, windowSum (classMask word a) step j i =
      windowSum (classMask word a) step prefixLength start)
    (hzero :
      let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
      (s : F) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        (m : F) * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ a, (e a : F) * (response a)⁻¹) = 0) :
    let original := fun a => realCoordinateSlice K x (realResponseNumerator top p q a) /
      realCoordinateSlice K x (q a ^ 2)
    let response := replaceResponses S original (fun _ => RatFunc.C (if positive then 1 else -1))
    RatFunc.C (s : ℝ) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
      RatFunc.C (m : ℝ) * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
        (∑ a, RatFunc.C (e a : ℝ) * (response a)⁻¹) = 0 := by
  classical
  let original := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
  let replacement : α → F := fun _ => if positive then 1 else -1
  let labels : α → F := fun a => (e a : F)
  have hsource := (shortDetector_replace_zero_iff word original replacement labels step
    j prefixLength start (s : F) (m : F) S hresponse
    (by intro a ha; cases positive <;> simp only [replacement, Bool.false_eq_true,
      ite_false, ite_true, neg_ne_zero] <;> norm_num)
    (by intro a ha; simp only [labels, he a ha, Int.cast_zero]) hcount).mp hzero
  obtain ⟨num, den, hsourceRep, hnρ, hdρ, hnumSlice, hdenSlice⟩ :=
    remainingRealChamber_representatives φ S N K hNK top p q hp hq hqφ
      hanchor positive x hx
  have hn (a : α) : φ (num a) ≠ 0 := by
    apply (map_ne_zero_iff _ hφ).mpr
    intro hz
    exact hnρ a (by rw [hz, map_zero])
  have hd (a : α) : φ (den a) ≠ 0 := by
    apply (map_ne_zero_iff _ hφ).mpr
    intro hz
    exact hdρ a (by rw [hz, map_zero])
  have hsource' :
      let response := fun a => φ (num a) / φ (den a)
      φ (s : MvPolynomial ℕ ℝ) * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        φ (m : MvPolynomial ℕ ℝ) *
          (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ a, φ (e a : MvPolynomial ℕ ℝ) * (response a)⁻¹) = 0 := by
    simpa only [map_natCast, map_intCast, hsourceRep, original, replacement, labels] using hsource
  have htarget := shortDetector_zero_specialize φ (realCoordinateSlice K x) hφ
    num den word (fun a => (e a : MvPolynomial ℕ ℝ)) step j prefixLength start
    (s : MvPolynomial ℕ ℝ) (m : MvPolynomial ℕ ℝ) hn hd hnρ hdρ hsource'
  have htargetPoint (a : α) :
      realCoordinateSlice K x (num a) / realCoordinateSlice K x (den a) =
        replaceResponses S
          (fun a => realCoordinateSlice K x (realResponseNumerator top p q a) /
            realCoordinateSlice K x (q a ^ 2))
          (fun _ => RatFunc.C (if positive then 1 else -1)) a := by
    simp only [realCoordinateSlice, RingHom.comp_apply, hnumSlice, hdenSlice]
    by_cases ha : a ∈ S <;> simp only [replaceResponses, ha, ite_true, ite_false,
      RatFunc.algebraMap_C, map_one, div_one]
  simpa only [map_natCast, map_intCast, htargetPoint] using htarget

/-- The complete forward identity, including every whole-cycle power, survives the same
finite replacement and real specialization.

**Differs from the paper's route.** Specializes a finite cleared expression on the produced
remaining chamber, rather than a valuation on the full source field. -/
theorem remainingRealChamber_fullDetector_zero {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] {n : ℕ} [NeZero n]
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (hqφ : ∀ i, φ (q i) ≠ 0)
    (hresponse : ∀ i, φ (X (top i : ℕ)) + φ (p i) / φ (q i) ≠ 0)
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive)
    (word : ZMod n → α) (e : α → ℤ) (m prefixLength k scalar : ℕ)
    (he : ∀ a ∈ S, e a = 0)
    (hcount : ∀ a ∈ S, ∀ i, windowSum (classMask word a) 1 m i =
      windowSum (classMask word a) 1 prefixLength 0)
    (hzero :
      let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
      (scalar : F) * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 prefixLength 0 -
        (∑ a, (e a : F) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0) :
    let original := fun a => realCoordinateSlice K x (realResponseNumerator top p q a) /
      realCoordinateSlice K x (q a ^ 2)
    let response := replaceResponses S original (fun _ => RatFunc.C (if positive then 1 else -1))
    RatFunc.C (scalar : ℝ) * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 prefixLength 0 -
      (∑ a, RatFunc.C (e a : ℝ) * (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0 := by
  classical
  let original := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
  let replacement : α → F := fun _ => if positive then 1 else -1
  let labels : α → F := fun a => (e a : F)
  have hsource := (fullDetector_replace_zero_iff word original replacement labels
    m prefixLength k (scalar : F) S hresponse
    (by intro a ha; cases positive <;> simp only [replacement, Bool.false_eq_true,
      ite_false, ite_true, neg_ne_zero] <;> norm_num)
    (by intro a ha; simp only [labels, he a ha, Int.cast_zero]) hcount).mp hzero
  obtain ⟨num, den, hsourceRep, hnρ, hdρ, hnumSlice, hdenSlice⟩ :=
    remainingRealChamber_representatives φ S N K hNK top p q hp hq hqφ
      hanchor positive x hx
  have hn (a : α) : φ (num a) ≠ 0 := by
    apply (map_ne_zero_iff _ hφ).mpr
    intro hz
    exact hnρ a (by rw [hz, map_zero])
  have hd (a : α) : φ (den a) ≠ 0 := by
    apply (map_ne_zero_iff _ hφ).mpr
    intro hz
    exact hdρ a (by rw [hz, map_zero])
  have hsource' :
      let response := fun a => φ (num a) / φ (den a)
      φ (scalar : MvPolynomial ℕ ℝ) * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 prefixLength 0 -
        (∑ a, φ (e a : MvPolynomial ℕ ℝ) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0 := by
    simpa only [map_natCast, map_intCast, hsourceRep, original, replacement, labels] using hsource
  have htarget := fullDetector_zero_specialize φ (realCoordinateSlice K x) hφ
    num den word (fun a => (e a : MvPolynomial ℕ ℝ)) 1 ((k - 1) * n + m) n
    prefixLength k 0 (scalar : MvPolynomial ℕ ℝ) hn hd hnρ hdρ hsource'
  have htargetPoint (a : α) :
      realCoordinateSlice K x (num a) / realCoordinateSlice K x (den a) =
        replaceResponses S
          (fun a => realCoordinateSlice K x (realResponseNumerator top p q a) /
            realCoordinateSlice K x (q a ^ 2))
          (fun _ => RatFunc.C (if positive then 1 else -1)) a := by
    simp only [realCoordinateSlice, RingHom.comp_apply, hnumSlice, hdenSlice]
    by_cases ha : a ∈ S <;> simp only [replaceResponses, ha, ite_true, ite_false,
      RatFunc.algebraMap_C, map_one, div_one]
  simpa only [map_natCast, map_intCast, htargetPoint] using htarget

end SkewCornerDescent
