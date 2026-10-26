/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib

/-!
# Cyclic ratios of proper-core units

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`). A common
self-product and periodic neighboring mixed products force one common phase
ratio. Iterating the phase shift through its actual cycle gives its finite-order
identity. Sorry-free.
-/

namespace SkewCornerDescent

private theorem unit_div_common_right {G : Type*} [CommGroup G] (a b c : G) :
    (a * c) / (b * c) = a / b := by
  simp [div_eq_mul_inv, mul_inv_rev, mul_assoc]

private theorem unit_div_common_left {G : Type*} [CommGroup G] (a b c : G) :
    (a * b) / (a * c) = b / c := by
  rw [mul_comm a b, mul_comm a c]
  exact unit_div_common_right b c a

/-- Common self-products and equal shifted neighboring products force one
common unit ratio throughout the original cycle. -/
theorem cyclic_core_ratio_constant {G : Type*} [CommGroup G] {M : ℕ} [NeZero M]
    (A B : ZMod M → G) (shift : ZMod M)
    (hself : ∀ i, A i * B i = A 0 * B 0)
    (hedge : ∀ i, A i * B (i + 1) = A (i + shift) * B (i + shift + 1)) :
    ∀ i, A (i + shift) / A i = A shift / A 0 := by
  let Z := fun i => A (i + shift) / A i
  have hnext (i) : Z i = Z (i + 1) := by
    have hprod : A (i + 1) * B (i + 1) =
        A (i + shift + 1) * B (i + shift + 1) := (hself _).trans (hself _).symm
    have hindex : i + 1 + shift = i + shift + 1 := by ring
    change A (i + shift) / A i = A (i + 1 + shift) / A (i + 1)
    rw [hindex]
    calc
      A (i + shift) / A i =
          (A (i + shift) * B (i + shift + 1)) / (A i * B (i + shift + 1)) :=
        (unit_div_common_right _ _ _).symm
      _ = (A i * B (i + 1)) / (A i * B (i + shift + 1)) := by rw [← hedge i]
      _ = B (i + 1) / B (i + shift + 1) := unit_div_common_left _ _ _
      _ = (A (i + 1) * B (i + 1)) /
          (A (i + 1) * B (i + shift + 1)) := (unit_div_common_left _ _ _).symm
      _ = (A (i + shift + 1) * B (i + shift + 1)) /
          (A (i + 1) * B (i + shift + 1)) := by rw [hprod]
      _ = A (i + shift + 1) / A (i + 1) := unit_div_common_right _ _ _
  have hnat (k : ℕ) : Z (k : ZMod M) = Z 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one]
      exact (hnext (k : ZMod M)).symm.trans ih
  intro i
  have h := hnat i.val
  rw [ZMod.natCast_zmod_val] at h
  simpa only [Z, zero_add] using h

/-- The common phase ratio has finite order when the actual cycle has length
`r*b`; no coprimality or primitive-cycle assumption is used. -/
theorem cyclic_core_ratio_power {G : Type*} [CommGroup G] (r b : ℕ) [NeZero (r * b)]
    (A B : ZMod (r * b) → G)
    (hself : ∀ i, A i * B i = A 0 * B 0)
    (hedge : ∀ i, A i * B (i + 1) = A (i + r) * B (i + r + 1)) :
    ∀ i, (A (i + r) / A i) ^ b = 1 := by
  let Z := A (r : ZMod (r * b)) / A 0
  have hratio (i) : A (i + r) / A i = Z :=
    cyclic_core_ratio_constant A B (r : ZMod (r * b)) hself hedge i
  have hstep (i) : A (i + r) = Z * A i := by
    have h := congrArg (fun x : G => x * A i) (hratio i)
    simpa only [div_mul_cancel] using h
  have hiter (k : ℕ) : A ((k * r : ℕ) : ZMod (r * b)) = Z ^ k * A 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Nat.cast_add, hstep, ih, pow_succ]
      simp only [mul_left_comm, mul_comm]
  have hzero : ((b * r : ℕ) : ZMod (r * b)) = 0 := by
    rw [Nat.mul_comm b r]
    exact ZMod.natCast_self _
  have h := hiter b
  rw [hzero] at h
  have hpow : Z ^ b = 1 := by
    have hc := congrArg (fun x : G => x / A 0) h
    simpa only [div_self', mul_div_cancel_right] using hc.symm
  intro i
  rw [hratio, hpow]

end SkewCornerDescent
