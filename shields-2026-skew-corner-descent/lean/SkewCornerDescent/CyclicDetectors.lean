/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicClosureInventories

/-!
# Signed short and complete-cycle detectors

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original
coefficients» (`sec:dual`, `lem:dual-identities`, `eq:dual-short`, `eq:dual-last`).
The signed identities are consequences of literal cyclic inventories, not hypotheses
about their crossing terms. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

variable {R ι : Type*} [Field R] [Fintype ι]

/-- The signed closure-label sum, with no positivity restriction on the exponents. -/
def closureLabelSum (e : ι → ℤ) (S : ι → R) : R := ∑ α, (e α : R) * (S α)⁻¹

/-- The original periodic inventory minus every signed closure-word inventory. -/
def windowDefect {n : ℕ} [NeZero n] (f : ZMod n → R) (S : ι → R)
    (e : ι → ℤ) (b B j : ℕ) [NeZero B] : R :=
  (b : R) * inverseWindowSum f j -
    ∑ α, (e α : R) * inverseWindowSum (closureWord f (S α) B) j

/-- Exact class balance reduces the short detector to its two actual inventories. -/
theorem windowDefect_short {n m k d s b : ℕ} [NeZero n] [NeZero m]
    [NeZero (k * n + m)] (f : ZMod n → R) (S : ι → R) (e : ι → ℤ)
    (hmn : m ≤ n) (hk : 0 < k) (hb : b = k * d + s) (he : ∑ α, e α = (d : ℤ)) :
    windowDefect f S e b (k * n + m) m =
      (s : R) * inverseWindowSum f m - (m : R) *
        (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹ * closureLabelSum e S := by
  classical
  have heR : (∑ α, (e α : R)) = (d : R) := by
    simpa only [Int.cast_sum, Int.cast_natCast] using congrArg (fun z : ℤ => (z : R)) he
  unfold windowDefect
  simp_rw [inverseWindowSum_closure_short f _ hmn hk, nsmul_eq_mul, mul_inv_rev]
  have hsum : (∑ α, (e α : R) * ((k : R) * inverseWindowSum f m +
      (m : R) * ((S α)⁻¹ * (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹))) =
      (d : R) * (k : R) * inverseWindowSum f m +
        (m : R) * (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹ *
          closureLabelSum e S := by
    calc
      _ = ∑ α, ((e α : R) * (k : R) * inverseWindowSum f m +
          ((m : R) * (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹) *
            ((e α : R) * (S α)⁻¹)) := Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
          ← Finset.mul_sum, heR]
        rfl
  rw [hsum, hb]
  push_cast
  ring

/-- The complete detector retains the full number of closure-cycle starts. -/
theorem windowDefect_full {n m k b : ℕ} [NeZero n] [NeZero m]
    [NeZero (k * n + m)] (f : ZMod n → R) (S : ι → R) (e : ι → ℤ) :
    windowDefect f S e b (k * n + m) (k * n + m) =
      (b : R) * (∏ i : ZMod n, f i)⁻¹ ^ k * inverseWindowSum f m -
        (k * n + m : ℕ) * (∏ i : ZMod n, f i)⁻¹ ^ k *
          (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹ * closureLabelSum e S := by
  classical
  unfold windowDefect
  rw [inverseWindowSum_mul_add]
  simp_rw [inverseWindowSum_closure_full, nsmul_eq_mul, mul_inv_rev, ← inv_pow]
  have hsum : (∑ α, (e α : R) * ((k * n + m : ℕ) *
      ((S α)⁻¹ * ((∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹ *
        (∏ i : ZMod n, f i)⁻¹ ^ k)))) =
      (k * n + m : ℕ) * (∏ i : ZMod n, f i)⁻¹ ^ k *
        (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹ * closureLabelSum e S := by
    calc
      _ = ∑ α, (((k * n + m : ℕ) * (∏ i : ZMod n, f i)⁻¹ ^ k *
          (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹) *
            ((e α : R) * (S α)⁻¹)) := Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [← Finset.mul_sum]; rfl
  rw [hsum]
  ring

/-- The long detector is the short detector with its exact nonzero scalar multiplier. -/
theorem windowDefect_full_eq_short {n m k r d s b : ℕ} [NeZero n] [NeZero m]
    [NeZero (k * n + m)] (f : ZMod n → R) (S : ι → R) (e : ι → ℤ)
    (hmn : m ≤ n) (hk : 0 < k) (hb : b = k * d + s)
    (hn : n = r * d) (hm : m = r * s) (hs : (s : R) ≠ 0)
    (he : ∑ α, e α = (d : ℤ)) :
    windowDefect f S e b (k * n + m) (k * n + m) =
      ((b : R) / (s : R)) * (∏ i : ZMod n, f i)⁻¹ ^ k *
        windowDefect f S e b (k * n + m) m := by
  rw [windowDefect_full, windowDefect_short f S e hmn hk hb he]
  have hnum : (s : R) * (k * n + m : ℕ) = (b : R) * (m : R) := by
    rw [hb, hn, hm]
    push_cast
    ring
  field_simp [hs]
  linear_combination -((∏ i : ZMod n, f i)⁻¹ ^ k *
    (∏ i ∈ Finset.range (m - 1), f (i : ZMod n))⁻¹ * closureLabelSum e S) * hnum

end SkewCornerDescent.CyclicWindows
