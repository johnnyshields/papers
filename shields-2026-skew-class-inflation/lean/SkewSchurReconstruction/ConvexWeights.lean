/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/ConvexWeights.lean

import Mathlib

/-!
# Admissible convex weights

Formalizes `def:convex-weight` in “Weights and tropical notation” and
`lem:strict-monge` in “Strict-Monge geometry of cofactor actions” (`sec:geometry`), strict
superadditivity in “The ratio identity as a virtual row” (`subsec:virtual`),
and radix admissibility in “Weight collisions and coefficient cancellation”
(`subsec:weight-scope`, `eq:radix-weight`).  Finite differences are compared
by induction on their length.  Sorry-free.
-/

namespace SkewSchurReconstruction

/-- The positive, strictly increasing discrete increments of `def:convex-weight`. -/
structure ConvexWeight where
  /-- The real weight assigned to each nonnegative generator index. -/
  weight : ℕ → ℝ
  zero : weight 0 = 0
  increment_pos : ∀ k : ℕ, 0 < weight (k + 1) - weight k
  increment_strictMono : StrictMono (fun k : ℕ => weight (k + 1) - weight k)

namespace ConvexWeight

variable (w : ConvexWeight)

theorem strictMono_weight : StrictMono w.weight := by
  apply strictMono_nat_of_lt_succ
  intro k
  have := w.increment_pos k
  linarith

/-- A positive-length finite difference strictly increases with its base point. -/
theorem strictMono_difference {p : ℕ} (hp : 0 < p) :
    StrictMono (fun x : ℕ => w.weight (x + p) - w.weight x) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  clear hp
  induction q with
  | zero => simpa using w.increment_strictMono
  | succ q ih =>
    intro x y hxy
    have h₁ := ih hxy
    have h₂ := w.increment_strictMono (show x + (q + 1) < y + (q + 1) by omega)
    change w.weight (x + (q + 1)) - w.weight x <
      w.weight (y + (q + 1)) - w.weight y at h₁
    change w.weight (x + (q + 1) + 1) - w.weight (x + (q + 1)) <
      w.weight (y + (q + 1) + 1) - w.weight (y + (q + 1)) at h₂
    simp only [Nat.succ_eq_add_one]
    have ex : x + (q + 1 + 1) = x + (q + 1) + 1 := by omega
    have ey : y + (q + 1 + 1) = y + (q + 1) + 1 := by omega
    rw [ex, ey]
    linarith

/-- Natural-index version of `lem:strict-monge`. -/
theorem strict_monge {x p z : ℕ} (hp : 0 < p) (hz : 0 < z) :
    w.weight (x + p) + w.weight (x + z) <
      w.weight (x + p + z) + w.weight x := by
  have h := w.strictMono_difference hp (show x < x + z by omega)
  change w.weight (x + p) - w.weight x <
    w.weight (x + z + p) - w.weight (x + z) at h
  have e : x + z + p = x + p + z := by omega
  rw [e] at h
  linarith

/-- Integer row parameters, including negative virtual rows, in `lem:strict-monge`. -/
theorem strict_monge_int {A A' d d' : ℤ} (hA : A < A') (hd : d < d')
    (hfeasible : A' ≤ d) :
    w.weight (d - A).toNat + w.weight (d' - A').toNat <
      w.weight (d' - A).toNat + w.weight (d - A').toNat := by
  have hp : 0 < (A' - A).toNat := by omega
  have hz : 0 < (d' - d).toNat := by omega
  have h := w.strict_monge (x := (d - A').toNat) hp hz
  have e₁ : (d - A').toNat + (A' - A).toNat = (d - A).toNat := by omega
  have e₂ : (d - A').toNat + (d' - d).toNat = (d' - A').toNat := by omega
  have e₃ : (d - A').toNat + (A' - A).toNat + (d' - d).toNat =
      (d' - A).toNat := by omega
  rw [e₃, e₁, e₂] at h
  exact h

/-- Strict superadditivity at positive indices, used in `subsec:virtual`. -/
theorem strict_superadditive {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    w.weight x + w.weight y < w.weight (x + y) := by
  have h := w.strict_monge (x := 0) hx hy
  simpa only [Nat.zero_add, w.zero, add_zero] using h

end ConvexWeight

/-- The principal square weight of `def:convex-weight`. -/
def squareWeight : ConvexWeight where
  weight k := (k : ℝ) ^ 2
  zero := by norm_num
  increment_pos k := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  increment_strictMono := by
    intro x y hxy
    have h : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
    push_cast
    nlinarith

/-- The value function in `eq:radix-weight`, with a separate zero value. -/
def radixValue (B : ℕ) (k : ℕ) : ℝ := if k = 0 then 0 else (B : ℝ) ^ k

@[simp] theorem radixValue_zero (B : ℕ) : radixValue B 0 = 0 := by
  simp [radixValue]

@[simp] theorem radixValue_succ (B k : ℕ) :
    radixValue B (k + 1) = (B : ℝ) ^ (k + 1) := by
  simp [radixValue]

theorem radix_increment_succ (B k : ℕ) :
    radixValue B (k + 1 + 1) - radixValue B (k + 1) =
      (B : ℝ) ^ (k + 1) * ((B : ℝ) - 1) := by
  simp only [radixValue_succ, pow_succ]
  ring

/-- Radix weights are admissible for every integer base at least three. -/
def radixWeight (B : ℕ) (hB : 3 ≤ B) : ConvexWeight where
  weight := radixValue B
  zero := radixValue_zero B
  increment_pos k := by
    have hb : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    cases k with
    | zero =>
      change 0 < radixValue B 1 - radixValue B 0
      norm_num [radixValue]
      linarith
    | succ k =>
      rw [radix_increment_succ]
      exact mul_pos (pow_pos (by linarith) _) (by linarith)
  increment_strictMono := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hb : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    cases k with
    | zero =>
      simp only [radixValue_succ, radixValue_zero, sub_zero]
      norm_num [pow_succ]
      nlinarith
    | succ k =>
      simp only [radix_increment_succ]
      have hp : 0 < (B : ℝ) ^ (k + 1) := pow_pos (by linarith) _
      have hm : 0 < (B : ℝ) ^ (k + 1) * ((B : ℝ) - 1) :=
        mul_pos hp (by linarith)
      calc
        (B : ℝ) ^ (k + 1) * ((B : ℝ) - 1) <
            ((B : ℝ) ^ (k + 1) * ((B : ℝ) - 1)) * (B : ℝ) := by
          exact lt_mul_of_one_lt_right hm (by linarith)
        _ = (B : ℝ) ^ (k + 1 + 1) * ((B : ℝ) - 1) := by
          simp only [pow_succ]
          ring

/-- At base two the first two increments tie, so strict convexity fails. -/
theorem radix_two_increment_tie :
    radixValue 2 1 - radixValue 2 0 = radixValue 2 2 - radixValue 2 1 := by
  norm_num [radixValue]

theorem radix_two_not_strictMono :
    ¬ StrictMono (fun k : ℕ => radixValue 2 (k + 1) - radixValue 2 k) := by
  intro h
  have ht := h (show (0 : ℕ) < 1 by omega)
  norm_num [radixValue] at ht

end SkewSchurReconstruction
