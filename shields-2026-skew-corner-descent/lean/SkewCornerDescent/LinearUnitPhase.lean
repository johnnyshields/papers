/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicUnitPhase

/-!
# Phase ratios on an open chain with a literal matched window

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Common self-products and shifted internal neighboring products identify one
phase ratio on the open chain. A matched window at a positive multiple of the
phase shift gives torsion without inserting an unproved closure edge. Sorry-free.
-/

namespace SkewCornerDescent

private theorem linear_div_common_right {G : Type*} [CommGroup G] (a b c : G) :
    (a * c) / (b * c) = a / b := by
  simp [div_eq_mul_inv, mul_inv_rev, mul_assoc]

private theorem linear_div_common_left {G : Type*} [CommGroup G] (a b c : G) :
    (a * b) / (a * c) = b / c := by
  rw [mul_comm a b, mul_comm a c]
  exact linear_div_common_right b c a

/-- The open-chain phase ratio has finite order from a matched window.
Only actual internal edges are used; no cyclic closure edge is required. -/
theorem linear_core_ratio_power {G : Type*} [CommGroup G] (r d L : ℕ)
    (hwindowSize : r * d < L) (A B : ℕ → G)
    (hself : ∀ i, i < L → A i * B i = A 0 * B 0)
    (hedge : ∀ i, i + r + 1 < L →
      A i * B (i + 1) = A (i + r) * B (i + r + 1))
    (hwindow : A (r * d) = A 0) :
    ∀ i, i + r < L → (A (i + r) / A i) ^ d = 1 := by
  let Z := A r / A 0
  have hnext (i : ℕ) (hi : i + r + 1 < L) :
      A (i + r) / A i = A (i + 1 + r) / A (i + 1) := by
    have hprod : A (i + 1) * B (i + 1) = A (i + r + 1) * B (i + r + 1) :=
      (hself _ (by omega)).trans (hself _ hi).symm
    rw [show i + 1 + r = i + r + 1 by omega]
    calc
      A (i + r) / A i =
          (A (i + r) * B (i + r + 1)) / (A i * B (i + r + 1)) :=
        (linear_div_common_right _ _ _).symm
      _ = (A i * B (i + 1)) / (A i * B (i + r + 1)) := by rw [← hedge i hi]
      _ = B (i + 1) / B (i + r + 1) := linear_div_common_left _ _ _
      _ = (A (i + 1) * B (i + 1)) / (A (i + 1) * B (i + r + 1)) :=
        (linear_div_common_left _ _ _).symm
      _ = (A (i + r + 1) * B (i + r + 1)) /
          (A (i + 1) * B (i + r + 1)) := by rw [hprod]
      _ = A (i + r + 1) / A (i + 1) := linear_div_common_right _ _ _
  have hratio (i : ℕ) : i + r < L → A (i + r) / A i = Z := by
    induction i with
    | zero => intro _; simp only [Nat.zero_add, Z]
    | succ i ih =>
      intro hi
      exact (hnext i (by omega)).symm.trans (ih (by omega))
  have hstep (i : ℕ) (hi : i + r < L) : A (i + r) = Z * A i := by
    have h := congrArg (fun x : G => x * A i) (hratio i hi)
    simpa only [div_mul_cancel] using h
  have hiter (k : ℕ) : k ≤ d → A (k * r) = Z ^ k * A 0 := by
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hbound : k * r + r < L := by
        have hm := Nat.mul_le_mul_right r hk
        rw [Nat.succ_mul, Nat.mul_comm d r] at hm
        omega
      rw [Nat.succ_mul, hstep _ hbound, ih (by omega), pow_succ]
      simp only [mul_left_comm, mul_comm]
  have hpower : Z ^ d = 1 := by
    have h := hiter d le_rfl
    rw [Nat.mul_comm d r, hwindow] at h
    have hc := congrArg (fun x : G => x / A 0) h
    simpa only [div_self', mul_div_cancel_right] using hc.symm
  intro i hi
  rw [hratio i hi, hpower]

end SkewCornerDescent
