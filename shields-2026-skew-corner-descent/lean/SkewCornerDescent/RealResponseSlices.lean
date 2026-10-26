/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealResponseChambers
import SkewCornerDescent.ExposedPoleSum

/-!
# Regular exposed coordinate slices over real coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `thm:dual-general`).
Square-denominator representatives retain the complete triangular responses. The
simultaneous chamber produces a simple anchor root and strict common signs for every
other numerator, with no rational-label restriction. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

/-- Multiplying a triangular numerator by its denominator gives a positive square denominator. -/
noncomputable def realResponseNumerator {ι : Type*} (top : ι → ℕ+)
    (p q : ι → MvPolynomial ℕ ℝ) (i : ι) : MvPolynomial ℕ ℝ :=
  (X (top i : ℕ) * q i + p i) * q i

/-- The normalized representative is the unchanged real triangular response. -/
theorem realResponseNumerator_fraction {ι : Type*} (top : ι → ℕ+)
    (p q : ι → MvPolynomial ℕ ℝ) (x : ℕ → ℝ) (i : ι) (hq : eval x (q i) ≠ 0) :
    eval x (realResponseNumerator top p q i) / eval x (q i ^ 2) =
      rationalTriangularResponse (top i : ℕ) (p i) (q i) x := by
  simp only [realResponseNumerator, map_mul, map_add, eval_X, map_pow,
    rationalTriangularResponse]
  field_simp

/-- Triangular support and chamber membership supply a simple anchor root, positive
square denominators and strict common signs for all other normalized numerators. -/
theorem simultaneousRealChamber_exposed_slice {ι : Type*} [Finite ι]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K top p q positive) :
    ∃ a : {i : ι // top i = K},
      let r := rationalAnchorRoot (fun a : {i : ι // top i = K} => p a.val)
        (fun a => q a.val) a x
      let slice := coordinatePolynomial (K : ℕ) x
      let num := fun i => slice (realResponseNumerator top p q i)
      let den := fun i => slice (q i ^ 2)
      Polynomial.eval r (num a.val) = 0 ∧
        Polynomial.rootMultiplicity r (num a.val) = 1 ∧
        (∀ i, 0 < Polynomial.eval r (den i)) ∧
        (∀ i, i ≠ a.val → 0 < (if positive then 1 else -1) *
          Polynomial.eval r (num i)) := by
  classical
  obtain ⟨a, hzero, hreg, hsign⟩ := simultaneousRealChamber_exposed_extreme
    N K hNK top p q hp hq hanchor positive x hx
  let r := rationalAnchorRoot (fun a : {i : ι // top i = K} => p a.val)
    (fun a => q a.val) a x
  let y := Function.update x (K : ℕ) r
  let slice := coordinatePolynomial (K : ℕ) x
  let num := fun i => slice (realResponseNumerator top p q i)
  let den := fun i => slice (q i ^ 2)
  let sign : ℝ := if positive then 1 else -1
  have he (v : MvPolynomial ℕ ℝ) : Polynomial.eval r (slice v) = eval y v :=
    coordinatePolynomial_eval (K : ℕ) x r v
  have hden : ∀ i, 0 < Polynomial.eval r (den i) := by
    intro i
    rw [he, map_pow]
    exact sq_pos_of_ne_zero (hreg i)
  have hn : Polynomial.eval r (num a.val) = 0 := by
    have hz : eval y (realResponseNumerator top p q a.val) / eval y (q a.val ^ 2) = 0 := by
      rw [realResponseNumerator_fraction top p q y a.val (hreg a.val), a.property]
      exact hzero
    rw [he]
    have hda := hden a.val
    change 0 < Polynomial.eval r (slice (q a.val ^ 2)) at hda
    rw [he] at hda
    exact (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt hda)
  have hQK : (K : ℕ) ∉ (q a.val).vars := by
    intro h
    exact (not_lt_of_ge hNK) (hq a.val (K : ℕ) h)
  have hPK : (K : ℕ) ∉ (p a.val).vars := by
    intro h
    have hh := hp a.val (K : ℕ) h
    rw [a.property] at hh
    exact (lt_irrefl _) hh
  have hQ0 : eval x (q a.val) ≠ 0 := hx.1 a
  have hsimpleRaw : Polynomial.rootMultiplicity r
      (slice (X (K : ℕ) * q a.val + p a.val)) = 1 := by
    simpa only [r, rationalAnchorRoot, neg_div] using
      coordinatePolynomial_affine_rootMultiplicity (K : ℕ) x (p a.val) (q a.val)
        hPK hQK hQ0
  have hraw0 : slice (X (K : ℕ) * q a.val + p a.val) ≠ 0 := by
    intro hz
    rw [hz, Polynomial.rootMultiplicity_zero] at hsimpleRaw
    exact Nat.zero_ne_one hsimpleRaw
  have hsimple : Polynomial.rootMultiplicity r (num a.val) = 1 := by
    change Polynomial.rootMultiplicity r (slice
      ((X (top a.val : ℕ) * q a.val + p a.val) * q a.val)) = 1
    rw [a.property, map_mul, coordinatePolynomial_constant (K : ℕ) x (q a.val) hQK,
      Polynomial.rootMultiplicity_mul
        (mul_ne_zero hraw0 (Polynomial.C_ne_zero.mpr hQ0)), hsimpleRaw,
      Polynomial.rootMultiplicity_C, add_zero]
  have hnums : ∀ i, i ≠ a.val → 0 < sign * Polynomial.eval r (num i) := by
    intro i hi
    rw [he]
    apply normalizedResponseNumerator_pos (X (top i : ℕ) * q i + p i) (q i)
      (eval y) sign (hreg i)
    have hs := hsign i hi
    have heq : eval y (X (top i : ℕ) * q i + p i) / eval y (q i) =
        rationalTriangularResponse (top i : ℕ) (p i) (q i) y := by
      simp only [map_add, map_mul, eval_X, rationalTriangularResponse]
      have hqi : eval y (q i) ≠ 0 := hreg i
      field_simp [hqi]
    rw [heq]
    cases positive <;> simpa only [sign, y, r, anchorAssignment,
      Bool.false_eq_true, ite_false, ite_true, responseSign,
      neg_one_mul, one_mul, neg_pos] using hs
  exact ⟨a, hn, hsimple, hden, hnums⟩

end SkewCornerDescent
