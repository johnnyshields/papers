/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicDetectors
import SkewCornerDescent.CyclicComplementWindows

/-!
# Full-period signed detector from actual complementary windows

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original
coefficients» (`sec:dual`, `lem:dual-identities`, `eq:dual-first`). All denominator
nonvanishing is produced from the individual response nonvanishing. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

variable {R ι : Type*} [Field R] [Fintype ι]

/-- Nonzero response coordinates make the complete closure product nonzero. -/
theorem closureWord_product_ne_zero {n B : ℕ} [NeZero B]
    (f : ZMod n → R) (S : R) (hf : ∀ i, f i ≠ 0) (hS : S ≠ 0) :
    (∏ i : ZMod B, closureWord f S B i) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold closureWord
  split
  · exact hS
  · exact hf _

/-- Signed full-period subtraction, before imposing its numerical normalization. -/
theorem windowDefect_period_raw {n C b d : ℕ} [NeZero n] [NeZero (n + C)]
    (f : ZMod n → R) (S : ι → R) (e : ι → ℤ)
    (hf : ∀ i, f i ≠ 0) (hS : ∀ α, S α ≠ 0) (he : ∑ α, e α = (d : ℤ)) :
    windowDefect f S e b (n + C) n =
      ((b : R) * (n : R) - (d : R) * (C : R)) * (∏ i : ZMod n, f i)⁻¹ -
        (∑ i : ZMod n, windowProduct f 1 C i) *
          (∏ i ∈ Finset.range (n + C - 1), f (i : ZMod n))⁻¹ * closureLabelSum e S := by
  classical
  have heR : (∑ α, (e α : R)) = (d : R) := by
    simpa only [Int.cast_sum, Int.cast_natCast] using congrArg (fun z : ℤ => (z : R)) he
  unfold windowDefect inverseWindowSum
  rw [zmod_sum_inverse_full_cycle]
  change (b : R) * (n • (∏ i : ZMod n, f i)⁻¹) -
    (∑ α, (e α : R) * inverseWindowSum (closureWord f (S α) (n + C)) n) = _
  simp_rw [inverseWindowSum_closure_period f _
    (closureWord_product_ne_zero f _ hf (hS _)), closureWord_product,
    nsmul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  have hsum : (∑ α, (e α : R) * ((C : R) * (∏ i : ZMod n, f i)⁻¹ +
      (∑ i : ZMod n, windowProduct f 1 C i) * ((S α)⁻¹ *
        (∏ i ∈ Finset.range (n + C - 1), f (i : ZMod n))⁻¹))) =
      (d : R) * (C : R) * (∏ i : ZMod n, f i)⁻¹ +
        (∑ i : ZMod n, windowProduct f 1 C i) *
          (∏ i ∈ Finset.range (n + C - 1), f (i : ZMod n))⁻¹ * closureLabelSum e S := by
    calc
      _ = ∑ α, ((e α : R) * (C : R) * (∏ i : ZMod n, f i)⁻¹ +
          ((∑ i : ZMod n, windowProduct f 1 C i) *
            (∏ i ∈ Finset.range (n + C - 1), f (i : ZMod n))⁻¹) *
              ((e α : R) * (S α)⁻¹)) := Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
          ← Finset.mul_sum, heR]
        rfl
  rw [hsum]
  ring

/-- The full-period normalization yields precisely the first dual detector. -/
theorem windowDefect_period {n C b d : ℕ} [NeZero n] [NeZero (n + C)]
    (f : ZMod n → R) (S : ι → R) (e : ι → ℤ)
    (hf : ∀ i, f i ≠ 0) (hS : ∀ α, S α ≠ 0) (he : ∑ α, e α = (d : ℤ))
    (hbn : b * n = d * (n + C)) :
    windowDefect f S e b (n + C) n =
      (n : R) * (d : R) * (∏ i : ZMod n, f i)⁻¹ -
        (∑ i : ZMod n, windowProduct f 1 C i) *
          (∏ i ∈ Finset.range (n + C - 1), f (i : ZMod n))⁻¹ * closureLabelSum e S := by
  rw [windowDefect_period_raw f S e hf hS he]
  have hnum : (b : R) * (n : R) = (d : R) * ((n : R) + (C : R)) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using congrArg (fun z : ℕ => (z : R)) hbn
  linear_combination (∏ i : ZMod n, f i)⁻¹ * hnum

/-- The paper's quotient and remainder parameters produce the normalization, not a new binder. -/
theorem dual_period_normalization {n m k r d s b : ℕ} (hk : 0 < k)
    (hb : b = k * d + s) (hn : n = r * d) (hm : m = r * s) :
    b * n = d * (n + ((k - 1) * n + m)) := by
  have hk' : k - 1 + 1 = k := by omega
  have hC : n + ((k - 1) * n + m) = k * n + m := by
    calc
      _ = (k - 1 + 1) * n + m := by ring
      _ = k * n + m := by rw [hk']
  rw [hC, hb, hn, hm]
  ring

end SkewCornerDescent.CyclicWindows
