/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.ConnectedIrreducibility
import Shields.LinearAlgebra.Matrix.DesnanotJacobi
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Weak caps: the bordered determinant

Substrate for `lem:cap-recognition` of `shields-2026-skew-coframe-rigidity.tex`.  The joint
polynomial ring `ℚ[z, h_1, h_2, …]` is `MvPolynomial (Option ℕ+) ℚ`, with `z = X none` and
`h_k = X (some k)`.  A weak cap is a pair of strictly decreasing positive lists `X`, `Y` with
`Y i ≤ X i`.  Its numerator is the determinant of the bordered matrix whose last row is
`(z^{Y_j}, 1)` and whose last column is `(h_{X_i})`; expansion along the last row exhibits its
`z`-coefficients as board minors.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence

/-- The joint polynomial ring in `z` and the complete generators. -/
abbrev J := MvPolynomial (Option ℕ+) ℚ

/-- The inclusion of the complete-generator ring into the joint ring. -/
noncomputable def ι : CompleteRing →+* J :=
  (MvPolynomial.rename some : CompleteRing →ₐ[ℚ] J).toRingHom

/-- The variable `z`. -/
noncomputable def zJ : J := MvPolynomial.X none

/-- A complete generator in the joint ring. -/
noncomputable def hJ (k : ℤ) : J := ι (complete k)

theorem ι_injective : Function.Injective ι :=
  MvPolynomial.rename_injective _ (Option.some_injective _)

/-- The coefficient-in-`z` isomorphism. -/
noncomputable def φ : J ≃ₐ[ℚ] Polynomial CompleteRing :=
  MvPolynomial.optionEquivLeft ℚ ℕ+

theorem φ_ι (s : CompleteRing) : φ (ι s) = Polynomial.C s := by
  have : (φ : J →ₐ[ℚ] Polynomial CompleteRing).comp (MvPolynomial.rename some) =
      (Polynomial.CAlgHom : CompleteRing →ₐ[ℚ] Polynomial CompleteRing) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [φ, MvPolynomial.optionEquivLeft_apply]
  exact congrArg (fun f => f s) this

theorem φ_zJ : φ zJ = Polynomial.X := by
  simp [φ, zJ, MvPolynomial.optionEquivLeft_apply]

/-- The `k`-th coefficient in `z`. -/
noncomputable def coefZ (k : ℕ) (p : J) : CompleteRing := (φ p).coeff k

theorem coefZ_add (k : ℕ) (p q : J) : coefZ k (p + q) = coefZ k p + coefZ k q := by
  simp [coefZ]

theorem coefZ_sum {ι' : Type*} (s : Finset ι') (f : ι' → J) (k : ℕ) :
    coefZ k (∑ i ∈ s, f i) = ∑ i ∈ s, coefZ k (f i) := by
  simp [coefZ]

theorem coefZ_zpow_mul (e k : ℕ) (s : CompleteRing) :
    coefZ k (zJ ^ e * ι s) = if k = e then s else 0 := by
  simp only [coefZ, map_mul, map_pow, φ_zJ, φ_ι]
  rw [mul_comm, Polynomial.coeff_C_mul_X_pow]

theorem coefZ_ι (k : ℕ) (s : CompleteRing) : coefZ k (ι s) = if k = 0 then s else 0 := by
  have := coefZ_zpow_mul 0 k s
  simpa using this

theorem coefZ_ι_of_ne {k : ℕ} (hk : k ≠ 0) (s : CompleteRing) : coefZ k (ι s) = 0 := by
  rw [coefZ_ι]
  exact ite_eq_right_iff.mpr fun h => absurd h hk

/-- A `z`-power combination with distinct exponents has the displayed coefficients. -/
theorem coefZ_zsum {q : ℕ} (e : Fin q → ℕ) (he : Function.Injective e) (d : Fin q → CompleteRing)
    (p : Fin q) : coefZ (e p) (∑ j, zJ ^ e j * ι (d j)) = d p := by
  rw [coefZ_sum]
  simp_rw [coefZ_zpow_mul]
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    exact ite_eq_right_iff.mpr fun h => absurd h.symm (fun h' => hj (he h'))
  · simp

/-- A weak cap: strictly decreasing positive lists with `Y i ≤ X i`. -/
structure WeakCap (r : ℕ) where
  X : Fin r → ℤ
  Y : Fin r → ℤ
  X_anti : StrictAnti X
  Y_anti : StrictAnti Y
  Y_pos : ∀ i, 0 < Y i
  Y_le : ∀ i, Y i ≤ X i

namespace WeakCap

variable {r : ℕ}

theorem ext' {c c' : WeakCap r} (hX : c.X = c'.X) (hY : c.Y = c'.Y) : c = c' := by
  cases c; cases c'; simp_all

/-- The column labels with the border label `0` appended. -/
def cols (c : WeakCap r) : Fin (r + 1) → ℤ := Fin.lastCases 0 c.Y

@[simp] theorem cols_castSucc (c : WeakCap r) (i : Fin r) : c.cols i.castSucc = c.Y i := by
  simp [cols]

@[simp] theorem cols_last (c : WeakCap r) : c.cols (Fin.last r) = 0 := by
  simp [cols]

theorem cols_nonneg (c : WeakCap r) (p : Fin (r + 1)) : 0 ≤ c.cols p := by
  induction p using Fin.lastCases with
  | last => simp
  | cast i => simpa using (c.Y_pos i).le

theorem cols_anti (c : WeakCap r) : StrictAnti c.cols := by
  intro p q hpq
  induction q using Fin.lastCases with
  | last =>
    induction p using Fin.lastCases with
    | last => exact absurd hpq (lt_irrefl _)
    | cast i => simpa using c.Y_pos i
  | cast j =>
    induction p using Fin.lastCases with
    | last => exact absurd hpq (not_lt.mpr (by simpa using Fin.le_last _))
    | cast i =>
      simp only [cols_castSucc]
      exact c.Y_anti (by simpa using hpq)

/-- The cap with its first entries deleted. -/
def tail (c : WeakCap (r + 1)) : WeakCap r where
  X i := c.X i.succ
  Y i := c.Y i.succ
  X_anti := c.X_anti.comp_strictMono (Fin.strictMono_succ)
  Y_anti := c.Y_anti.comp_strictMono (Fin.strictMono_succ)
  Y_pos _ := c.Y_pos _
  Y_le _ := c.Y_le _

theorem cols_succ (c : WeakCap (r + 1)) (p : Fin (r + 1)) : c.cols p.succ = c.tail.cols p := by
  induction p using Fin.lastCases with
  | last => simp [cols]
  | cast i =>
    rw [Fin.succ_castSucc, cols_castSucc, cols_castSucc]
    rfl

theorem X_pos (c : WeakCap (r + 1)) (i : Fin (r + 1)) : 0 < c.X i :=
  lt_of_lt_of_le (c.Y_pos i) (c.Y_le i)

end WeakCap

end SkewCoframeRigidity.CapRecognition
