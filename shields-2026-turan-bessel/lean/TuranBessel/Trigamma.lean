/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# The trigamma function as a series, with the bounds used in the paper

Mathlib has `digamma := logDeriv Gamma` but no polygamma/trigamma.  We define
`trigamma y = ∑' n, (y + n)⁻² = ψ₁(y)` directly and prove exactly the analytic
facts the coefficientwise argument of `shields-2026-turan-bessel.tex` consumes.
These are `lem:trigamma-bounds` of «Endpoint coefficientwise positivity»
(`sec:endpoint`): the sharp lower bound `eq:trig-lower` `ψ₁(y)>1/y+1/(2y²)` —
proved here, as in the paper, by the trapezoidal/convexity inequality
`∫_r^{r+1}f < (f(r)+f(r+1))/2` (`trigamma_gt_inv_sharp`) — the upper bound
`eq:trig-upper-half` `ψ₁(y)<1/(y-1/2)` (`trigamma_lt_upper`), and `eq:inverse-trig`.
The crude `ψ₁(y)>1/y` (`trigamma_gt_inv`) also feeds `Δ_1>0` (`eq:Delta1-sharp`,
`subsec:finite-defect`) via `aψ₁(a)>1`.

* `trigamma_summable`, `trigamma_pos`, `trigamma_succ` — the defining series is
  summable, positive, and satisfies the recurrence `ψ₁(y) = y⁻² + ψ₁(y+1)`.
* `telescope_hasSum` — the workhorse `∑' n, ((c+n)⁻¹ - (c+n+1)⁻¹) = c⁻¹`
  (`c > 0`), which drives every bound and the Gram cross term.
* `trigamma_gt_inv`  — the crude lower bound `ψ₁(y) > 1/y` (enough for `aψ₁(a)>1`).
* `trigamma_lt_upper` — the sharp upper bound `ψ₁(y) < 1/(y-1/2)` for `y > 1/2`
  (`eq:trig-upper-half`), the load-bearing estimate for the Gram slack.
* `tsum_mul_sq_le` — Cauchy–Schwarz for `ℓ²` series, the Gram positivity input.

Everything here is sorry-free.
-/

open Filter Topology
open scoped BigOperators

namespace TuranBessel

variable {y c : ℝ}

/-- Trigamma function `ψ₁(y) = ∑_{n≥0} (y+n)⁻²`. -/
noncomputable def trigamma (y : ℝ) : ℝ := ∑' n : ℕ, (y + (n : ℝ))⁻¹ ^ 2

/-- Partial fraction `A⁻¹ - (A+1)⁻¹ = (A(A+1))⁻¹`. -/
theorem inv_sub_inv_succ {A : ℝ} (hA : A ≠ 0) (hA1 : A + 1 ≠ 0) :
    A⁻¹ - (A + 1)⁻¹ = (A * (A + 1))⁻¹ := by field_simp; ring

/-- Strict comparison of summable series over `ℕ` (the additive `hasSum_lt`). -/
theorem strict_tsum_lt {small big : ℕ → ℝ} (i₀ : ℕ)
    (hle : ∀ n, small n ≤ big n) (hlt : small i₀ < big i₀)
    (hs : Summable small) (hb : Summable big) :
    ∑' n, small n < ∑' n, big n :=
  hasSum_lt hle hlt hs.hasSum hb.hasSum

/-- The defining series of `trigamma` is summable for `y > 0`. -/
theorem trigamma_summable (hy : 0 < y) :
    Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ ^ 2) := by
  have hmaj : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h2 := (summable_nat_add_iff 1).mpr h
    refine h2.congr (fun n => ?_)
    push_cast; rw [one_div, inv_pow]
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  rw [inv_pow, inv_pow]
  refine inv_anti₀ (by positivity) ?_
  push_cast; nlinarith [hy, Nat.cast_nonneg (α := ℝ) n]

/-- Telescoping workhorse: `∑' n, ((c+n)⁻¹ - (c+n+1)⁻¹) = c⁻¹` for `c > 0`. -/
theorem telescope_hasSum (hc : 0 < c) :
    HasSum (fun n : ℕ => (c + (n : ℝ))⁻¹ - (c + (n : ℝ) + 1)⁻¹) c⁻¹ := by
  have hcn : ∀ n : ℕ, (0 : ℝ) < c + (n : ℝ) := by
    intro n; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hpart : ∀ N : ℕ,
      ∑ i ∈ Finset.range N, ((c + (i : ℝ))⁻¹ - (c + (i : ℝ) + 1)⁻¹)
        = c⁻¹ - (c + (N : ℝ))⁻¹ := by
    intro N
    induction N with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hnn : ∀ n : ℕ, 0 ≤ (c + (n : ℝ))⁻¹ - (c + (n : ℝ) + 1)⁻¹ := by
    intro n
    have hp2 : c + (n : ℝ) + 1 ≠ 0 := (by linarith [hcn n] : (0 : ℝ) < c + (n : ℝ) + 1).ne'
    rw [inv_sub_inv_succ (hcn n).ne' hp2]
    have : 0 < (c + (n : ℝ)) * (c + (n : ℝ) + 1) := by nlinarith [hcn n]
    exact inv_nonneg.mpr this.le
  have hsummable : Summable (fun n : ℕ => (c + (n : ℝ))⁻¹ - (c + (n : ℝ) + 1)⁻¹) := by
    refine summable_of_sum_range_le (c := c⁻¹) hnn (fun N => ?_)
    rw [hpart]
    have : (0 : ℝ) ≤ (c + (N : ℝ))⁻¹ := inv_nonneg.mpr (hcn N).le
    linarith
  have hatTop : Tendsto (fun N : ℕ => c + (N : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_left hc.le) tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun N : ℕ => c⁻¹ - (c + (N : ℝ))⁻¹) atTop (𝓝 c⁻¹) := by
    have h0 : Tendsto (fun N : ℕ => (c + (N : ℝ))⁻¹) atTop (𝓝 0) := hatTop.inv_tendsto_atTop
    have hconst : Tendsto (fun _ : ℕ => c⁻¹) atTop (𝓝 c⁻¹) := tendsto_const_nhds
    simpa using hconst.sub h0
  have htend2 : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range N, ((c + (i : ℝ))⁻¹ - (c + (i : ℝ) + 1)⁻¹))
      atTop (𝓝 c⁻¹) := by simp only [hpart]; exact htend
  have hval : ∑' n : ℕ, ((c + (n : ℝ))⁻¹ - (c + (n : ℝ) + 1)⁻¹) = c⁻¹ :=
    tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat htend2
  exact hval ▸ hsummable.hasSum

/-- Summability by shifting: `∑(y+n)⁻²` converges as soon as `y + k > 0` for some
`k`, so it holds for negative non-integer `y` too (meromorphic continuation). -/
theorem trigamma_summable_shift {k : ℕ} (hy : 0 < y + (k : ℝ)) :
    Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ ^ 2) := by
  rw [← summable_nat_add_iff k]
  refine (trigamma_summable hy).congr (fun n => ?_)
  rw [show y + (k : ℝ) + (n : ℝ) = y + ((n + k : ℕ) : ℝ) from by push_cast; ring]

/-- Recurrence `ψ₁(y) = y⁻² + ψ₁(y+1)` from summability alone (any `y`). -/
theorem trigamma_succ_of_summable (hsum : Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ ^ 2)) :
    trigamma y = (y⁻¹) ^ 2 + trigamma (y + 1) := by
  rw [trigamma, hsum.tsum_eq_zero_add, trigamma]
  congr 1
  · norm_num
  · exact tsum_congr (fun n =>
      by rw [show y + ((n + 1 : ℕ) : ℝ) = (y + 1) + (n : ℝ) from by push_cast; ring])

/-- Recurrence `ψ₁(y) = y⁻² + ψ₁(y+1)`. -/
theorem trigamma_succ (hy : 0 < y) : trigamma y = (y⁻¹) ^ 2 + trigamma (y + 1) :=
  trigamma_succ_of_summable (trigamma_summable hy)

/-- `trigamma y > 0` for `y > 0`. -/
theorem trigamma_pos (hy : 0 < y) : 0 < trigamma y := by
  rw [trigamma_succ hy]
  have h2 : 0 ≤ trigamma (y + 1) := by
    rw [trigamma]; exact tsum_nonneg (fun n => by positivity)
  have h1 : (0 : ℝ) < (y⁻¹) ^ 2 := by positivity
  linarith

/-- The telescoping term is strictly below the trigamma term. -/
private theorem tel_lt_sq (hy : 0 < y) (n : ℕ) :
    (y + (n : ℝ))⁻¹ - (y + (n : ℝ) + 1)⁻¹ < (y + (n : ℝ))⁻¹ ^ 2 := by
  have hyn : (0 : ℝ) < y + (n : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hp2 : y + (n : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < y + (n : ℝ) + 1).ne'
  rw [inv_sub_inv_succ hyn.ne' hp2, inv_pow]
  exact inv_strictAnti₀ (pow_pos hyn 2) (by nlinarith [hyn])

/-- Crude lower bound `ψ₁(y) > 1/y`. -/
theorem trigamma_gt_inv (hy : 0 < y) : y⁻¹ < trigamma y := by
  have hbig : Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ ^ 2) := trigamma_summable hy
  have hsmall : Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ - (y + (n : ℝ) + 1)⁻¹) :=
    (telescope_hasSum hy).summable
  have key := strict_tsum_lt 0 (fun n => (tel_lt_sq hy n).le) (tel_lt_sq hy 0) hsmall hbig
  rw [(telescope_hasSum hy).tsum_eq] at key
  exact key

/-- Sharp lower bound `ψ₁(y) > 1/y + 1/(2y²)` (`eq:trig-lower`).  The telescoping
term is strictly below the trapezoidal average `((y+n)⁻²+(y+n+1)⁻²)/2`, whose sum
is `ψ₁(y) - y⁻²/2` by the recurrence. -/
theorem trigamma_gt_inv_sharp (hy : 0 < y) : y⁻¹ + (1 / 2) * (y ^ 2)⁻¹ < trigamma y := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hsy : Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ ^ 2) := trigamma_summable hy
  have hsy1 : Summable (fun n : ℕ => (y + (n : ℝ) + 1)⁻¹ ^ 2) := by
    refine (trigamma_summable hy1).congr (fun n => ?_)
    rw [show y + 1 + (n : ℝ) = y + (n : ℝ) + 1 from by ring]
  have hsav : Summable (fun n : ℕ => (1 / 2) * ((y + (n : ℝ))⁻¹ ^ 2 + (y + (n : ℝ) + 1)⁻¹ ^ 2)) :=
    (hsy.add hsy1).mul_left (1 / 2)
  have htel := telescope_hasSum hy
  -- termwise `telescope < average`
  have hlt : ∀ n : ℕ, (y + (n : ℝ))⁻¹ - (y + (n : ℝ) + 1)⁻¹
      < (1 / 2) * ((y + (n : ℝ))⁻¹ ^ 2 + (y + (n : ℝ) + 1)⁻¹ ^ 2) := by
    intro n
    have hu : 0 < y + (n : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hv : 0 < y + (n : ℝ) + 1 := by linarith
    have hne : (y + (n : ℝ))⁻¹ ≠ (y + (n : ℝ) + 1)⁻¹ := by
      intro h; have := inv_injective h; linarith
    rw [inv_sub_inv_succ hu.ne' hv.ne', mul_inv]
    have hsq : 0 < ((y + (n : ℝ))⁻¹ - (y + (n : ℝ) + 1)⁻¹) ^ 2 := by
      have := sub_ne_zero.mpr hne; positivity
    nlinarith [hsq]
  have key := strict_tsum_lt 0 (fun n => (hlt n).le) (hlt 0) htel.summable hsav
  rw [htel.tsum_eq] at key
  -- `∑ average = ψ₁(y) - y⁻²/2`
  have hB : (∑' n : ℕ, (y + (n : ℝ) + 1)⁻¹ ^ 2) = trigamma y - (y ^ 2)⁻¹ := by
    have e2 : (∑' n : ℕ, (y + (n : ℝ) + 1)⁻¹ ^ 2) = trigamma (y + 1) := by
      rw [trigamma]
      exact tsum_congr (fun n => by rw [show y + 1 + (n : ℝ) = y + (n : ℝ) + 1 from by ring])
    have hrec := trigamma_succ hy
    rw [e2]; rw [inv_pow] at hrec; linarith
  have hav_eq : (∑' n : ℕ, (1 / 2) * ((y + (n : ℝ))⁻¹ ^ 2 + (y + (n : ℝ) + 1)⁻¹ ^ 2))
      = trigamma y - (1 / 2) * (y ^ 2)⁻¹ := by
    rw [tsum_mul_left, (hsy.hasSum.add hsy1.hasSum).tsum_eq, hB,
      show (∑' n : ℕ, (y + (n : ℝ))⁻¹ ^ 2) = trigamma y from rfl]
    ring
  rw [hav_eq] at key
  linarith

/-- The trigamma term is strictly below the shifted telescoping term. -/
private theorem sq_lt_tel (hy : 1 / 2 < y) (n : ℕ) :
    (y + (n : ℝ))⁻¹ ^ 2
      < (y - 1 / 2 + (n : ℝ))⁻¹ - (y - 1 / 2 + (n : ℝ) + 1)⁻¹ := by
  have hcn : (0 : ℝ) < y - 1 / 2 + (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hyn : (0 : ℝ) < y + (n : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hp2 : y - 1 / 2 + (n : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < y - 1 / 2 + (n : ℝ) + 1).ne'
  rw [inv_sub_inv_succ hcn.ne' hp2, inv_pow]
  exact inv_strictAnti₀ (by nlinarith [hcn]) (by nlinarith [hcn, hyn])

/-- Sharp upper bound `ψ₁(y) < 1/(y - 1/2)` for `y > 1/2` (`eq:trig-upper-half`). -/
theorem trigamma_lt_upper (hy : 1 / 2 < y) : trigamma y < (y - 1 / 2)⁻¹ := by
  have hc : (0 : ℝ) < y - 1 / 2 := by linarith
  have hbig : Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ ^ 2) := trigamma_summable (by linarith)
  have htel := telescope_hasSum hc
  have key := strict_tsum_lt 0 (fun n => (sq_lt_tel hy n).le) (sq_lt_tel hy 0) hbig htel.summable
  rw [htel.tsum_eq] at key
  exact key

/-- Cauchy–Schwarz for `ℓ²` series: `(∑ fg)² ≤ (∑ f²)(∑ g²)`. -/
theorem tsum_mul_sq_le {f g : ℕ → ℝ}
    (hf : Summable (fun n => (f n) ^ 2)) (hg : Summable (fun n => (g n) ^ 2)) :
    (∑' n, f n * g n) ^ 2 ≤ (∑' n, (f n) ^ 2) * (∑' n, (g n) ^ 2) := by
  have hfg : Summable (fun n => f n * g n) := by
    refine Summable.of_norm_bounded (g := fun n => ((f n) ^ 2 + (g n) ^ 2) / 2)
      ((hf.add hg).div_const 2) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f n| - |g n|), sq_abs (f n), sq_abs (g n), abs_nonneg (f n),
      abs_nonneg (g n)]
  have key : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, f n * g n) ^ 2 ≤ (∑' n, (f n) ^ 2) * (∑' n, (g n) ^ 2) := by
    intro N
    calc (∑ n ∈ Finset.range N, f n * g n) ^ 2
        ≤ (∑ n ∈ Finset.range N, (f n) ^ 2) * (∑ n ∈ Finset.range N, (g n) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ f g
      _ ≤ (∑' n, (f n) ^ 2) * (∑' n, (g n) ^ 2) := by
          apply mul_le_mul
          · exact hf.sum_le_tsum _ (fun n _ => sq_nonneg _)
          · exact hg.sum_le_tsum _ (fun n _ => sq_nonneg _)
          · exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
          · exact tsum_nonneg (fun n => sq_nonneg _)
  have hlim : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n * g n) ^ 2)
      atTop (𝓝 ((∑' n, f n * g n) ^ 2)) :=
    (hfg.hasSum.tendsto_sum_nat).pow 2
  exact le_of_tendsto hlim (Eventually.of_forall key)

end TuranBessel
