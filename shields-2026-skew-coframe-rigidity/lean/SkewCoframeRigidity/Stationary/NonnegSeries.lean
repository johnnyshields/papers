/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Power series with nonnegative coefficients

Coefficient bounds used to prove `sc:component-remainder`: the nonnegative series over `ℚ` are
closed under sums, products and powers, a product dominates any single term of its convolution,
and a power of a series with coefficients at least one at two indices has coefficient at least
one at the larger index.  Sorry-free.
-/

namespace SkewCoframeRigidity

open PowerSeries

/-- A power series over `ℚ` with nonnegative coefficients. -/
def NonnegSeries (φ : PowerSeries ℚ) : Prop := ∀ m, 0 ≤ coeff m φ

theorem NonnegSeries.one : NonnegSeries (1 : PowerSeries ℚ) := fun m => by
  rw [coeff_one]; split_ifs <;> norm_num

theorem NonnegSeries.mul {φ ψ : PowerSeries ℚ} (hφ : NonnegSeries φ) (hψ : NonnegSeries ψ) :
    NonnegSeries (φ * ψ) := fun m => by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hφ _) (hψ _)

theorem NonnegSeries.pow {φ : PowerSeries ℚ} (hφ : NonnegSeries φ) (q : ℕ) :
    NonnegSeries (φ ^ q) := by
  induction q with
  | zero => rw [pow_zero]; exact NonnegSeries.one
  | succ q ih => rw [pow_succ]; exact ih.mul hφ

/-- A convolution dominates each of its terms. -/
theorem coeff_mul_ge {φ ψ : PowerSeries ℚ} (hφ : NonnegSeries φ) (hψ : NonnegSeries ψ)
    (a b : ℕ) : coeff a φ * coeff b ψ ≤ coeff (a + b) (φ * ψ) := by
  rw [coeff_mul]
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ => coeff x.1 φ * coeff x.2 ψ)
    (fun x _ => mul_nonneg (hφ _) (hψ _)) (by simp : (a, b) ∈ Finset.antidiagonal (a + b))

/-- A power of a nonnegative series with unit-size coefficients at `0` and `j` keeps a
coefficient at least one at `j`. -/
theorem one_le_coeff_pow {φ : PowerSeries ℚ} (hφ : NonnegSeries φ) {j : ℕ}
    (h0 : 1 ≤ coeff 0 φ) (hj : 1 ≤ coeff j φ) (q : ℕ) (hq : 1 ≤ q) :
    1 ≤ coeff j (φ ^ q) := by
  induction q, hq using Nat.le_induction with
  | base => rwa [pow_one]
  | succ q hq ih =>
    rw [pow_succ]
    have := coeff_mul_ge (hφ.pow q) hφ j 0
    rw [add_zero] at this
    nlinarith

end SkewCoframeRigidity
