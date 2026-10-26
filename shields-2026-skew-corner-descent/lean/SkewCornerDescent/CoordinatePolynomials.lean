/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Univariate slices of actual polynomial response coordinates

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:peeling`).
All coordinates except the exposed one retain their shared actual assignment. Evaluation
commutes with the slice, and a supported triangular numerator has exactly one root there.
Sorry-free.
-/

namespace SkewCornerDescent

/-- Freeze the other actual generators, leaving just the exposed coordinate polynomial. -/
noncomputable def coordinatePolynomial (K : ℕ) (x : ℕ → ℝ) :
    MvPolynomial ℕ ℝ →+* Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => if i = K then Polynomial.X else Polynomial.C (x i))

/-- Evaluating a coordinate slice is precisely updating that generator in the original ring. -/
theorem coordinatePolynomial_eval (K : ℕ) (x : ℕ → ℝ) (r : ℝ)
    (p : MvPolynomial ℕ ℝ) :
    Polynomial.eval r (coordinatePolynomial K x p) =
      MvPolynomial.eval (Function.update x K r) p := by
  change ((Polynomial.evalRingHom r).comp (coordinatePolynomial K x)) p = _
  apply RingHom.congr_fun
  ext a
  · simp [coordinatePolynomial]
  · by_cases ha : a = K <;> simp [coordinatePolynomial, ha]

/-- A polynomial not using the exposed coordinate becomes its unchanged constant value. -/
theorem coordinatePolynomial_constant (K : ℕ) (x : ℕ → ℝ) (p : MvPolynomial ℕ ℝ)
    (hp : K ∉ p.vars) :
    coordinatePolynomial K x p = Polynomial.C (MvPolynomial.eval x p) := by
  apply MvPolynomial.hom_congr_vars (f₂ := Polynomial.C.comp (MvPolynomial.eval x))
  · ext a
    simp [coordinatePolynomial]
  · intro i hi _
    have hne : i ≠ K := fun he => hp (he ▸ hi)
    simp [coordinatePolynomial, hne]
  · rfl

/-- The slice of an actual triangular numerator remains linear with its actual coefficients. -/
theorem coordinatePolynomial_affine (K : ℕ) (x : ℕ → ℝ)
    (p q : MvPolynomial ℕ ℝ) (hp : K ∉ p.vars) (hq : K ∉ q.vars) :
    coordinatePolynomial K x (MvPolynomial.X K * q + p) =
      Polynomial.X * Polynomial.C (MvPolynomial.eval x q) +
        Polynomial.C (MvPolynomial.eval x p) := by
  rw [map_add, map_mul, coordinatePolynomial_constant K x p hp,
    coordinatePolynomial_constant K x q hq]
  simp [coordinatePolynomial]

/-- The regular affine response numerator has a simple root in the exposed coordinate. -/
theorem coordinatePolynomial_affine_rootMultiplicity (K : ℕ) (x : ℕ → ℝ)
    (p q : MvPolynomial ℕ ℝ) (hp : K ∉ p.vars) (hq : K ∉ q.vars)
    (hq0 : MvPolynomial.eval x q ≠ 0) :
    Polynomial.rootMultiplicity (-MvPolynomial.eval x p / MvPolynomial.eval x q)
      (coordinatePolynomial K x (MvPolynomial.X K * q + p)) = 1 := by
  rw [coordinatePolynomial_affine K x p q hp hq]
  let a := MvPolynomial.eval x q
  let b := MvPolynomial.eval x p
  have he : Polynomial.X * Polynomial.C a + Polynomial.C b =
      Polynomial.C a * (Polynomial.X - Polynomial.C (-b / a)) := by
    have hab : a * (-b / a) = -b := by dsimp only [a]; field_simp [hq0]
    rw [mul_sub, ← Polynomial.C_mul, hab, Polynomial.C_neg]
    ring
  rw [he]
  change Polynomial.rootMultiplicity (-b / a)
    (Polynomial.C a * (Polynomial.X - Polynomial.C (-b / a))) = 1
  rw [Polynomial.rootMultiplicity_mul]
  · simp only [Polynomial.rootMultiplicity_C, Polynomial.rootMultiplicity_X_sub_C_self,
      zero_add]
  · exact mul_ne_zero (Polynomial.C_ne_zero.mpr hq0)
      (Polynomial.monic_X_sub_C _).ne_zero

end SkewCornerDescent
