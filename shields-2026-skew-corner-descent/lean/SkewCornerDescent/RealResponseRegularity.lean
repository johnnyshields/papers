/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealResponseSlices
import SkewCornerDescent.RegularDetectorSpecialization
import SkewCornerDescent.FiniteInactiveReplacement
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Regular polynomial representatives of real triangular responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-general`).
A real simultaneous chamber supplies nonzero slice representatives before any finite
zero-identity transfer. Square normalization is identified with the original monic
fraction over every field receiving the polynomial ring. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows

/-- The real coordinate slice maps polynomials into the univariate rational-function field. -/
noncomputable def realCoordinateSlice (K : ℕ+) (x : ℕ → ℝ) :
    MvPolynomial ℕ ℝ →+* RatFunc ℝ :=
  (algebraMap (Polynomial ℝ) (RatFunc ℝ)).comp (coordinatePolynomial (K : ℕ) x)

/-- Square normalization represents the complete monic fraction under a regular polynomial map. -/
theorem realResponseNumerator_fraction_map {ι F : Type*} [Field F]
    (φ : MvPolynomial ℕ ℝ →+* F) (top : ι → ℕ+)
    (p q : ι → MvPolynomial ℕ ℝ) (i : ι) (hq : φ (q i) ≠ 0) :
    φ (realResponseNumerator top p q i) / φ (q i ^ 2) =
      φ (X (top i : ℕ)) + φ (p i) / φ (q i) := by
  simp only [realResponseNumerator, map_mul, map_add, map_pow]
  field_simp

/-- The top derivative of a triangular numerator is its nonzero denominator.
Thus the complete source response cannot vanish under a faithful polynomial map. -/
theorem real_triangular_source_ne_zero {F : Type*} [Field F]
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (K : ℕ) (p q : MvPolynomial ℕ ℝ)
    (hp : ∀ j ∈ p.vars, j < K) (hq : ∀ j ∈ q.vars, j < K) (hq0 : q ≠ 0) :
    φ (X K) + φ p / φ q ≠ 0 := by
  have hpK : K ∉ p.vars := fun h => (lt_irrefl K) (hp K h)
  have hqK : K ∉ q.vars := fun h => (lt_irrefl K) (hq K h)
  have hraw : X K * q + p ≠ 0 := by
    intro hz
    have he := congrArg (pderiv K) hz
    simp only [map_add, pderiv_mul, pderiv_X_self,
      pderiv_eq_zero_of_notMem_vars hpK, pderiv_eq_zero_of_notMem_vars hqK,
      map_zero, one_mul, mul_zero, add_zero] at he
    exact hq0 he
  have hqφ : φ q ≠ 0 := (map_ne_zero_iff _ hφ).mpr hq0
  have he : φ (X K) + φ p / φ q = φ (X K * q + p) / φ q := by
    simp only [map_add, map_mul]
    field_simp
  rw [he]
  exact div_ne_zero ((map_ne_zero_iff _ hφ).mpr hraw) hqφ

/-- Every source numerator and square denominator is regular on the produced coordinate
slice. The exposed numerator may evaluate to zero at its root, but is not the zero polynomial. -/
theorem realCoordinateSlice_regular {ι : Type*} [Finite ι]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K top p q positive) :
    (∀ i, realCoordinateSlice K x (realResponseNumerator top p q i) ≠ 0) ∧
      (∀ i, realCoordinateSlice K x (q i ^ 2) ≠ 0) := by
  obtain ⟨a, _, hsimple, hden, hsign⟩ := simultaneousRealChamber_exposed_slice
    N K hNK top p q hp hq hanchor positive x hx
  dsimp only at hsimple hden hsign
  constructor
  · intro i
    apply RatFunc.algebraMap_ne_zero
    intro hz
    by_cases hi : i = a.val
    · subst i
      rw [hz, Polynomial.rootMultiplicity_zero] at hsimple
      exact Nat.zero_ne_one hsimple
    · have h := hsign i hi
      rw [hz, Polynomial.eval_zero, mul_zero] at h
      exact (lt_irrefl 0) h
  · intro i
    apply RatFunc.algebraMap_ne_zero
    intro hz
    have h := hden i
    rw [hz, Polynomial.eval_zero] at h
    exact (lt_irrefl 0) h

/-- One real chamber proves regularity of the original source fractions under every faithful
polynomial embedding. These nonzero premises are derived, not assumed by the assembly. -/
theorem simultaneousRealChamber_source_regular {ι F : Type*} [Finite ι] [Field F]
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K top p q positive) :
    (∀ i, φ (q i) ≠ 0) ∧
      (∀ i, φ (X (top i : ℕ)) + φ (p i) / φ (q i) ≠ 0) := by
  obtain ⟨hn, hd⟩ := realCoordinateSlice_regular N K hNK top p q hp hq
    hanchor positive x hx
  have hq0 (i : ι) : q i ≠ 0 := by
    intro hz
    exact hd i (by rw [hz, zero_pow (by decide), map_zero])
  have hqφ (i : ι) : φ (q i) ≠ 0 := (map_ne_zero_iff _ hφ).mpr (hq0 i)
  refine ⟨hqφ, ?_⟩
  intro i
  rw [← realResponseNumerator_fraction_map φ top p q i (hqφ i)]
  apply div_ne_zero
  · apply (map_ne_zero_iff _ hφ).mpr
    intro hz
    exact hn i (by rw [hz, map_zero])
  · rw [map_pow]
    exact pow_ne_zero 2 (hqφ i)

/-- Inactive replacements have regular source and slice polynomial representatives;
remaining classes keep their full actual triangular fractions. -/
theorem remainingRealChamber_representatives {α F : Type*} [Finite α] [Field F]
    [DecidableEq α] (φ : MvPolynomial ℕ ℝ →+* F)
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (hqφ : ∀ i, φ (q i) ≠ 0)
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive) :
    ∃ num den : α → MvPolynomial ℕ ℝ,
      (∀ a, φ (num a) / φ (den a) = replaceResponses S
        (fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a))
        (fun _ => if positive then 1 else -1) a) ∧
      (∀ a, realCoordinateSlice K x (num a) ≠ 0) ∧
      (∀ a, realCoordinateSlice K x (den a) ≠ 0) ∧
      (∀ a, coordinatePolynomial (K : ℕ) x (num a) =
        if a ∈ S then Polynomial.C (if positive then 1 else -1)
        else coordinatePolynomial (K : ℕ) x (realResponseNumerator top p q a)) ∧
      (∀ a, coordinatePolynomial (K : ℕ) x (den a) =
        if a ∈ S then 1 else coordinatePolynomial (K : ℕ) x (q a ^ 2)) := by
  classical
  let num := fun a => if a ∈ S then (if positive then 1 else -1 : MvPolynomial ℕ ℝ)
    else realResponseNumerator top p q a
  let den := fun a => if a ∈ S then (1 : MvPolynomial ℕ ℝ) else q a ^ 2
  obtain ⟨hn, hd⟩ := realCoordinateSlice_regular N K hNK
    (fun a : {a : α // a ∉ S} => top a.val) (fun a => p a.val) (fun a => q a.val)
    (fun a j hj => hp a.val j hj) (fun a j hj => hq a.val j hj)
    hanchor positive x hx
  refine ⟨num, den, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ S
    · cases positive <;> simp only [num, den, replaceResponses, ha, ite_true,
        Bool.false_eq_true, ite_false, map_one, map_neg, div_one]
    · simpa only [num, den, replaceResponses, ha, ite_false] using
        realResponseNumerator_fraction_map φ top p q a (hqφ a)
  · intro a
    by_cases ha : a ∈ S
    · cases positive <;> simp only [num, ha, ite_true, Bool.false_eq_true, ite_false,
        map_one, map_neg, neg_ne_zero] <;> norm_num
    · simpa only [num, ha, ite_false, realResponseNumerator] using hn ⟨a, ha⟩
  · intro a
    by_cases ha : a ∈ S
    · simp only [den, ha, ite_true, map_one]
      exact one_ne_zero
    · simpa only [den, ha, ite_false] using hd ⟨a, ha⟩
  · intro a
    by_cases ha : a ∈ S
    · cases positive <;> simp [num, ha, coordinatePolynomial]
    · simp only [num, ha, ite_false]
  · intro a
    by_cases ha : a ∈ S <;> simp only [den, ha, ite_true, ite_false, map_one]

end SkewCornerDescent
