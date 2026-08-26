/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.ArgumentPrinciple.Analytic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# One dominant term fixes the zero count

A power series whose `k`-th term outweighs everything else on a circle has exactly `k` zeros
inside it.  This is Rouché against a monomial, and it is the standard way to read the zeros of an
entire function off Hadamard gaps in its Taylor coefficients: where the ratios `|a_{k-1}/a_k|`
grow fast enough, each ratio separates one zero from the next, and the count in the disc between
two consecutive ratios is exactly the index.

`zeroCount_monomial` computes the reference count — `a·z^k` has a `k`-fold zero at the origin and
no other — and `zeroCount_eq_of_dominant` transfers it.  The hypothesis is stated as a bound on
`f - a·z^k`, which is what a tail estimate on the series produces directly.

Used by `toeplitz-newton-boundary` to count the zeros of the Mittag-Leffler function
`Φ_m(λ) = Γ(m)E_{m,m}(-λ)` below a given radius, where the two-term exponential asymptotic that
localizes the large zeros says nothing.

## Main results

* `zeroCount_monomial` — `a·z^k` has exactly `k` zeros in any disc about the origin.
* `zeroCount_eq_of_dominant` — so does anything within `‖a·z^k‖` of it on the boundary.
* `zeroCount_eq_of_tsum_lt` — the same, with the deviation bounded by a tail sum.
* `sum_range_le_of_geometric_down` and `tsum_le_of_geometric_up` — each side of `k` sums to
  `θ/(1-θ)` of the `k`-th term.
* `tsum_ite_le_of_geometric` — the tail sum a Hadamard gap produces: consecutive coefficients
  separating by a factor `θ⁻¹` on both sides of `k` leave everything but the `k`-th term inside
  `2θ/(1-θ)` of it, so `θ < 1/3` is what the count needs.

## Tags

Rouché, zero count, Hadamard gap, dominant coefficient
-/

open Metric

namespace Shields

/-- **The reference count.**  `a·z^k` vanishes to order `k` at the origin and nowhere else, so
every disc about the origin holds exactly `k` of its zeros. -/
theorem zeroCount_monomial {a : ℂ} (ha : a ≠ 0) {R : ℝ} (hR : 0 < R) (k : ℕ) :
    zeroCount (fun z : ℂ => a * z ^ k) 0 R = k := by
  have hstep : zeroCount (fun z : ℂ => a * z ^ k) 0 R
      = Multiset.card (Multiset.replicate k (0 : ℂ)) := by
    refine zeroCount_eq_card (g := fun _ => a) ?_ ?_ ?_ ?_
    · intro u hu
      rw [Multiset.eq_of_mem_replicate hu]
      simpa using hR
    · exact fun z _ => analyticAt_const
    · exact fun _ _ => ha
    · intro z
      rw [zeroFactor_replicate, sub_zero, mul_comm]
  rw [hstep, Multiset.card_replicate]

/-- **A dominant term fixes the count.**  If `f` differs from `a·z^k` by strictly less than
`‖a·z^k‖` at every point of the circle `|z| = R`, then `f` has exactly `k` zeros in `|z| < R`,
counted with multiplicity. -/
theorem zeroCount_eq_of_dominant {f : ℂ → ℂ} {a : ℂ} {R : ℝ} {k : ℕ} (hR : 0 < R) (ha : a ≠ 0)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hlt : ∀ z ∈ sphere (0 : ℂ) R, ‖f z - a * z ^ k‖ < ‖a * z ^ k‖) :
    zeroCount f 0 R = k := by
  have hmon : AnalyticOnNhd ℂ (fun z : ℂ => a * z ^ k) (closedBall 0 R) :=
    fun z _ => analyticAt_const.mul ((analyticAt_id).pow k)
  have hrest : AnalyticOnNhd ℂ (fun z : ℂ => f z - a * z ^ k) (closedBall 0 R) :=
    fun z hz => (hf z hz).sub (hmon z hz)
  have hsum : ((fun z : ℂ => a * z ^ k) + fun z : ℂ => f z - a * z ^ k) = f := by
    funext z; simp
  have := zeroCount_add_eq hR hmon hrest hlt
  rw [hsum] at this
  rw [this, zeroCount_monomial ha hR]

/-- The form a tail estimate produces: the deviation from the `k`-th term is bounded by a sum
that is itself below `‖a‖R^k`. -/
theorem zeroCount_eq_of_tsum_lt {f : ℂ → ℂ} {a : ℂ} {R B : ℝ} {k : ℕ} (hR : 0 < R) (ha : a ≠ 0)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hdev : ∀ z ∈ sphere (0 : ℂ) R, ‖f z - a * z ^ k‖ ≤ B) (hB : B < ‖a‖ * R ^ k) :
    zeroCount f 0 R = k := by
  refine zeroCount_eq_of_dominant hR ha hf fun z hz => ?_
  have hzn : ‖z‖ = R := by simpa using mem_sphere_zero_iff_norm.mp hz
  have : ‖a * z ^ k‖ = ‖a‖ * R ^ k := by rw [norm_mul, norm_pow, hzn]
  rw [this]
  exact lt_of_le_of_lt (hdev z hz) hB

/-! ### The tail a Hadamard gap leaves -/

/-- Going up from `k`, the terms decay geometrically. -/
theorem le_pow_of_geometric_up {c : ℕ → ℝ} {R θ : ℝ} {k : ℕ} (hR : 0 < R) (hθ0 : 0 ≤ θ)
    (hA : ∀ n, k ≤ n → c (n + 1) * R ≤ θ * c n) (j : ℕ) :
    c (k + j) * R ^ (k + j) ≤ θ ^ j * (c k * R ^ k) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : c (k + j + 1) * R ≤ θ * c (k + j) := hA (k + j) (Nat.le_add_right k j)
      have hpow : (0 : ℝ) < R ^ (k + j) := pow_pos hR _
      have h1 : c (k + (j + 1)) * R ^ (k + (j + 1))
          = (c (k + j + 1) * R) * R ^ (k + j) := by
        rw [show k + (j + 1) = (k + j) + 1 from by omega, pow_succ]; ring
      calc c (k + (j + 1)) * R ^ (k + (j + 1))
          = (c (k + j + 1) * R) * R ^ (k + j) := h1
        _ ≤ (θ * c (k + j)) * R ^ (k + j) := by
            exact mul_le_mul_of_nonneg_right hstep hpow.le
        _ = θ * (c (k + j) * R ^ (k + j)) := by ring
        _ ≤ θ * (θ ^ j * (c k * R ^ k)) := by exact mul_le_mul_of_nonneg_left ih hθ0
        _ = θ ^ (j + 1) * (c k * R ^ k) := by ring

/-- Going down from `k`, the terms decay geometrically. -/
theorem le_pow_of_geometric_down {c : ℕ → ℝ} {R θ : ℝ} {k : ℕ} (hR : 0 < R) (hθ0 : 0 ≤ θ)
    (hB : ∀ n, n < k → c n ≤ θ * R * c (n + 1)) :
    ∀ j, j ≤ k → c (k - j) * R ^ (k - j) ≤ θ ^ j * (c k * R ^ k) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hjk
      have hj : j ≤ k := by omega
      have hi : k - (j + 1) + 1 = k - j := by omega
      have hlt : k - (j + 1) < k := by omega
      have hstep := hB (k - (j + 1)) hlt
      have hpow : (0 : ℝ) < R ^ (k - (j + 1)) := pow_pos hR _
      calc c (k - (j + 1)) * R ^ (k - (j + 1))
          ≤ (θ * R * c (k - (j + 1) + 1)) * R ^ (k - (j + 1)) :=
            mul_le_mul_of_nonneg_right hstep hpow.le
        _ = θ * (c (k - (j + 1) + 1) * R ^ (k - (j + 1) + 1)) := by rw [pow_succ]; ring
        _ = θ * (c (k - j) * R ^ (k - j)) := by rw [hi]
        _ ≤ θ * (θ ^ j * (c k * R ^ k)) := mul_le_mul_of_nonneg_left (ih hj) hθ0
        _ = θ ^ (j + 1) * (c k * R ^ k) := by ring

/-- **The head sums to `θ/(1-θ)` of the `k`-th term.**  Below `k` the terms decay geometrically
going down, so `∑_{i<k} c_i R^i` is dominated termwise by `θ^{k-i} c_k R^k` and the exponents
`k - i` run over `1, …, k`. -/
theorem sum_range_le_of_geometric_down {c : ℕ → ℝ} {R θ : ℝ} {k : ℕ}
    (hc : ∀ n, 0 < c n) (hR : 0 < R) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hB : ∀ n, n < k → c n ≤ θ * R * c (n + 1)) :
    ∑ i ∈ Finset.range k, c i * R ^ i ≤ θ * (1 - θ)⁻¹ * (c k * R ^ k) := by
  have hbase : 0 < c k * R ^ k := mul_pos (hc k) (pow_pos hR k)
  have hgs : Summable fun n : ℕ => θ ^ n := summable_geometric_of_lt_one hθ0.le hθ1
  have hgt : ∑' n : ℕ, θ ^ n = (1 - θ)⁻¹ := tsum_geometric_of_lt_one hθ0.le hθ1
  have hterm : ∀ i ∈ Finset.range k, c i * R ^ i ≤ θ ^ (k - i) * (c k * R ^ k) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have := le_pow_of_geometric_down hR hθ0.le hB (k - i) (Nat.sub_le k i)
    rwa [Nat.sub_sub_self hik.le] at this
  have hgeo : ∑ i ∈ Finset.range k, θ ^ (k - i) ≤ θ * (1 - θ)⁻¹ := by
    have hrefl : ∑ i ∈ Finset.range k, θ ^ (k - i) = ∑ i ∈ Finset.range k, θ ^ (i + 1) := by
      rw [← Finset.sum_range_reflect (fun i => θ ^ (i + 1)) k]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : k - 1 - i + 1 = k - i := by have := Finset.mem_range.mp hi; omega
      rw [this]
    have hpull : ∑ i ∈ Finset.range k, θ ^ (i + 1) = θ * ∑ i ∈ Finset.range k, θ ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrefl, hpull, ← hgt]
    exact mul_le_mul_of_nonneg_left (hgs.sum_le_tsum _ fun i _ => pow_nonneg hθ0.le i) hθ0.le
  calc ∑ i ∈ Finset.range k, c i * R ^ i
      ≤ ∑ i ∈ Finset.range k, θ ^ (k - i) * (c k * R ^ k) := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range k, θ ^ (k - i)) * (c k * R ^ k) := by rw [Finset.sum_mul]
    _ ≤ (θ * (1 - θ)⁻¹) * (c k * R ^ k) := mul_le_mul_of_nonneg_right hgeo hbase.le

/-- **The tail sums to `θ/(1-θ)` of the `k`-th term**, by the same geometric comparison run
upward from `k`. -/
theorem tsum_le_of_geometric_up {c : ℕ → ℝ} {R θ : ℝ} {k : ℕ}
    (hR : 0 < R) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hsum : Summable fun n => c n * R ^ n)
    (hA : ∀ n, k ≤ n → c (n + 1) * R ≤ θ * c n) :
    ∑' n : ℕ, c (n + (k + 1)) * R ^ (n + (k + 1)) ≤ θ * (1 - θ)⁻¹ * (c k * R ^ k) := by
  have hgs : Summable fun n : ℕ => θ ^ n := summable_geometric_of_lt_one hθ0.le hθ1
  have hgt : ∑' n : ℕ, θ ^ n = (1 - θ)⁻¹ := tsum_geometric_of_lt_one hθ0.le hθ1
  have hterm : ∀ n : ℕ, c (n + (k + 1)) * R ^ (n + (k + 1)) ≤ θ ^ (n + 1) * (c k * R ^ k) := by
    intro n
    have heq : n + (k + 1) = k + (n + 1) := by omega
    rw [heq]
    exact le_pow_of_geometric_up hR hθ0.le hA (n + 1)
  have hcomp : Summable fun n : ℕ => θ ^ (n + 1) * (c k * R ^ k) :=
    ((hgs.mul_right θ).mul_right (c k * R ^ k)).congr fun n => by ring
  have hshift : Summable fun n => c (n + (k + 1)) * R ^ (n + (k + 1)) :=
    (hsum.comp_injective (add_left_injective (k + 1))).congr fun n => rfl
  refine le_trans (hshift.tsum_le_tsum hterm hcomp) (le_of_eq ?_)
  rw [tsum_mul_right]
  congr 1
  rw [tsum_congr (fun n : ℕ => by ring : ∀ n : ℕ, θ ^ (n + 1) = θ * θ ^ n), tsum_mul_left, hgt]

/-- **The tail a Hadamard gap leaves.**  If consecutive terms of `∑ c_n R^n` separate by a factor
`θ⁻¹` above `k` and below it, everything but the `k`-th term sums to at most `2θ/(1-θ)` of it --
one `θ/(1-θ)` from each side. -/
theorem tsum_ite_le_of_geometric {c : ℕ → ℝ} {R θ : ℝ} {k : ℕ}
    (hc : ∀ n, 0 < c n) (hR : 0 < R) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hsum : Summable fun n => c n * R ^ n)
    (hA : ∀ n, k ≤ n → c (n + 1) * R ≤ θ * c n)
    (hB : ∀ n, n < k → c n ≤ θ * R * c (n + 1)) :
    ∑' n, (if n = k then 0 else c n * R ^ n) ≤ 2 * θ / (1 - θ) * (c k * R ^ k) := by
  set g : ℕ → ℝ := fun n => if n = k then 0 else c n * R ^ n with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n; rw [hg]; dsimp only; split
    · exact le_rfl
    · exact (mul_pos (hc n) (pow_pos hR n)).le
  have hgsum : Summable g := by
    refine hsum.of_nonneg_of_le hgnn fun n => ?_
    rw [hg]; dsimp only; split
    · exact (mul_pos (hc n) (pow_pos hR n)).le
    · exact le_rfl
  have hgk : g k = 0 := by rw [hg]; simp
  have hhead : ∑ i ∈ Finset.range (k + 1), g i = ∑ i ∈ Finset.range k, c i * R ^ i := by
    rw [Finset.sum_range_succ, hgk, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hg]; dsimp only; rw [if_neg (Finset.mem_range.mp hi).ne]
  have htail : ∀ n : ℕ, g (n + (k + 1)) = c (n + (k + 1)) * R ^ (n + (k + 1)) := by
    intro n; rw [hg]; dsimp only; rw [if_neg (by omega)]
  have hdecomp : ∑' n, g n = (∑ i ∈ Finset.range (k + 1), g i) + ∑' n, g (n + (k + 1)) :=
    (hgsum.sum_add_tsum_nat_add (k + 1)).symm
  have hsplit : 2 * θ / (1 - θ) * (c k * R ^ k)
      = θ * (1 - θ)⁻¹ * (c k * R ^ k) + θ * (1 - θ)⁻¹ * (c k * R ^ k) := by
    have h1θ : 0 < 1 - θ := by linarith
    field_simp; ring
  rw [hdecomp, hsplit, hhead, tsum_congr htail]
  exact add_le_add (sum_range_le_of_geometric_down hc hR hθ0 hθ1 hB)
    (tsum_le_of_geometric_up hR hθ0 hθ1 hsum hA)


end Shields
