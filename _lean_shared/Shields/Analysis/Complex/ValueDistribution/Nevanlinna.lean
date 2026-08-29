/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.ValueDistribution.ExponentOfConvergence
import Shields.Analysis.Complex.ValueDistribution.Order
import Shields.Analysis.Complex.ValueDistribution.Transfer
import Vendor.ProjectVD.SMT.Picard

/-!
# Nevanlinna's theorem on the order of a zero-free entire function

An entire function `F` without zeros satisfies `N(r, 0) = 0`, and having no poles it satisfies
`N(r, ∞) = 0`.  The Second Main Theorem applied to the three targets `0`, `a`, `∞` therefore
bounds the characteristic of `F` by the counting function of its `a`-points alone.  If those
points have finite exponent of convergence `ρ`, the counting function grows at most like `r ^ ρ`,
and the order of `F` is at most `ρ`.

## Main results

* `Shields.sum_truncatedLogCounting_eq_of_ne_zero` — the two targets that contribute nothing.
  Zero-freeness enters the argument here and nowhere else.
* `Shields.exists_characteristic_le_logCounting` — the Second Main Theorem in the only form the
  rest of the file uses: `T(r) ≤ N(r, a) + c(log⁺ T(r) + log r)` off a set of finite measure.
* `Shields.le_two_mul_add_of_le_add_mul_posLog` — the absorption step.  The Second Main Theorem
  bounds the characteristic by its own `log⁺`, so `T` sits on both sides until the right-hand
  occurrence is absorbed into half of the left.
* `Shields.exists_characteristic_le_const_mul_rpow` — the explicit bound `T(r) ≤ B r ^ p` off the
  exceptional set, where both error terms of the Second Main Theorem are spent.
* `Shields.characteristic_isBigO_rpow_of_summable` — for `F` entire and zero-free and `a ≠ 0`,
  convergence of `∑ ‖z‖ ^ (-p)` over the `a`-points forces `T(r, F) = O(r ^ p)`.
* `Shields.order_le_expConvergence` — the order of `F` is at most the exponent of convergence of
  its `a`-points.

## Tags

Nevanlinna theory, order of growth, exponent of convergence, second main theorem
-/

open Asymptotics Filter Function MeasureTheory Metric Real Set Topology ValueDistribution
open scoped ENNReal NNReal

namespace Shields

/--
For `0 ≤ x` and `0 < ε`, the positive part of the logarithm satisfies `log⁺ x ≤ ε x + log⁺ ε⁻¹`.
-/
theorem posLog_le_mul_add_posLog_inv {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    log⁺ x ≤ ε * x + log⁺ ε⁻¹ := by
  have h₁ : (0 : ℝ) ≤ ε * x + log⁺ ε⁻¹ := by
    have := posLog_nonneg (x := ε⁻¹)
    positivity
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simpa using h₁
  · have h₂ : log (ε * x) ≤ ε * x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_mul hε.ne' hx0.ne'] at h₂
    have h₃ : log ε⁻¹ ≤ log⁺ ε⁻¹ := le_max_right 0 _
    rw [Real.log_inv] at h₃
    rw [posLog_apply]
    exact max_le h₁ (by linarith)

/-- **Only the `a`-points contribute.**  An entire `F` with no zeros omits both `0` and `⊤`, so
the two truncated counting functions at those targets vanish and the Second Main Theorem's sum over
`{0, a, ⊤}` is the `a`-point term alone.

This is what makes the theorem say something: with three targets the SMT carries `card - 2 = 1`
copy of the characteristic, and two of the three contribute nothing. -/
theorem sum_truncatedLogCounting_eq_of_ne_zero {F : ℂ → ℂ} (hana : ∀ x, AnalyticAt ℂ F x)
    (hF0 : ∀ z, F z ≠ 0) {a : ℂ} (ha : a ≠ 0) (r : ℝ) :
    ∑ v ∈ ({((0 : ℂ) : WithTop ℂ), ((a : ℂ) : WithTop ℂ), ⊤} : Finset (WithTop ℂ)),
        truncatedLogCounting F v r
      = truncatedLogCounting F ((a : ℂ) : WithTop ℂ) r := by
  have hmero : Meromorphic F := fun x ↦ (hana x).meromorphicAt
  have hzero : truncatedLogCounting F ((0 : ℂ) : WithTop ℂ) = 0 :=
    (Omits.of_forall_ne hana hF0).truncatedLogCounting_eq_zero hmero
  have htopO : Omits F ⊤ := fun x ↦ (hana x).meromorphicOrderAt_nonneg
  have htop : truncatedLogCounting F ⊤ = 0 := htopO.truncatedLogCounting_eq_zero hmero
  rw [Finset.sum_insert (by simp [ha]), Finset.sum_insert (by simp), Finset.sum_singleton,
    hzero, htop]
  simp

/-- **Absorbing a logarithmic error term.**  A nonnegative `T` bounded by `M + c·log⁺ T` is
bounded by `2M` plus an explicit constant depending only on `c`.

This is the step that makes the Second Main Theorem usable: the theorem bounds the characteristic
by its own `log⁺`, so `T` appears on both sides and the bound says nothing until the right-hand
occurrence is absorbed.  Taking `ε = 1 / (2(c+1))` in `Shields.posLog_le_mul_add_posLog_inv` makes
`cε ≤ 1/2`, so the offending term is at most half of `T`. -/
theorem le_two_mul_add_of_le_add_mul_posLog {T M c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (h : T ≤ M + c * log⁺ T) : T ≤ 2 * M + 2 * (c * log⁺ (2 * (c + 1))) := by
  have hcpos : (0 : ℝ) < 2 * (c + 1) := by linarith
  set ε : ℝ := 1 / (2 * (c + 1)) with hε
  have hεpos : (0 : ℝ) < ε := by rw [hε]; positivity
  have hεinv : ε⁻¹ = 2 * (c + 1) := by rw [hε, one_div, inv_inv]
  have hcε : c * ε ≤ 1 / 2 := by
    rw [hε, mul_one_div, div_le_div_iff₀ hcpos two_pos]
    linarith
  have hstep := posLog_le_mul_add_posLog_inv hT hεpos
  rw [hεinv] at hstep
  nlinarith [mul_le_mul_of_nonneg_left hstep hc, hT]

/-- **The Second Main Theorem at `{0, a, ∞}`, for a zero-free entire function.**

Three targets make the SMT carry `card - 2 = 1` copy of the characteristic, and
`Shields.sum_truncatedLogCounting_eq_of_ne_zero` empties two of the three counting terms, so what
survives is

`T(r, F) ≤ N(r, a) + c (log⁺ T(r, F) + log r)`

for all large `r` outside a set of finite measure.  The constant is the theorem's own, raised to
`max c 0` so it can be used as a nonnegative multiplier.

This is the only form of the SMT the rest of the file needs; everything after it is real
analysis on that inequality. -/
theorem exists_characteristic_le_logCounting {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∀ z, F z ≠ 0) {a : ℂ} (ha : a ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ r in volume.cofinite ⊓ atTop,
      characteristic F ⊤ r ≤ logCounting F ((a : ℂ) : WithTop ℂ) r
        + c * log⁺ (characteristic F ⊤ r) + c * Real.log r := by
  have hana : ∀ x, AnalyticAt ℂ F x := fun x ↦ hF.analyticAt x
  have hmero : Meromorphic F := fun x ↦ (hana x).meromorphicAt
  set S : Finset (WithTop ℂ) := {((0 : ℂ) : WithTop ℂ), ((a : ℂ) : WithTop ℂ), ⊤} with hS
  have hcard : S.card = 3 := by
    rw [hS, Finset.card_insert_of_notMem (by simp [ha]),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  obtain ⟨c, hc⟩ := secondMainTheorem hmero S
  refine ⟨max c 0, le_max_right c 0, ?_⟩
  filter_upwards [hc, mem_inf_of_right (eventually_ge_atTop (1 : ℝ))] with r h₁ hr1
  have hpos : 0 ≤ log⁺ (characteristic F ⊤ r) + Real.log r :=
    add_nonneg posLog_nonneg (Real.log_nonneg hr1)
  have h₂ : ∑ v ∈ S, truncatedLogCounting F v r ≤ logCounting F ((a : ℂ) : WithTop ℂ) r := by
    rw [hS, sum_truncatedLogCounting_eq_of_ne_zero hana hF0 ha]
    exact truncatedLogCounting_le hr1
  have h₄ : ((S.card : ℝ) - 2) = 1 := by rw [hcard]; norm_num
  have h₅ : c * (log⁺ (characteristic F ⊤ r) + Real.log r)
      ≤ max c 0 * (log⁺ (characteristic F ⊤ r) + Real.log r) :=
    mul_le_mul_of_nonneg_right (le_max_left c 0) hpos
  rw [h₄, one_mul] at h₁
  nlinarith [h₁, h₂, h₅]

/--
**The explicit characteristic bound, off the exceptional set.**  For `F` entire and never zero and
`a ≠ 0`: if `∑ z, D z * ‖z‖ ^ (-p)` converges over the divisor `D` of `a`-points, the characteristic
is below a constant multiple of `r ^ p` for all large `r` outside a set of finite measure.

Everything the Second Main Theorem contributes is spent here.  Its two error terms are converted
into multiples of `r ^ p` — `log r` by `Real.log_le_rpow_div`, and `log⁺ T` by
`Shields.le_two_mul_add_of_le_add_mul_posLog`, which is where the characteristic on the right-hand
side is absorbed into half of the one on the left.  The constant is explicit because both
conversions are.
-/
theorem exists_characteristic_le_const_mul_rpow {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∀ z, F z ≠ 0) {a : ℂ} (ha : a ≠ 0) {p : ℝ} (hp : 0 < p)
    (hsum : Summable fun z : ℂ ↦
      (((MeromorphicOn.divisor (F · - a) univ)⁺ z : ℤ) : ℝ) * ‖z‖ ^ (-p)) :
    ∃ B : ℝ, ∀ᶠ r in volume.cofinite ⊓ atTop, characteristic F ⊤ r ≤ B * r ^ p := by
  set D := (MeromorphicOn.divisor (F · - a) univ)⁺ with hD
  have hD0 : 0 ≤ D := posPart_nonneg _
  -- The counting function of the `a`-points is `O(r ^ p)`, with an explicit constant.
  set C := ((∑' z : ℂ, ((D z : ℤ) : ℝ) * ‖z‖ ^ (-p)) + ((D 0 : ℤ) : ℝ)) / p with hC
  have hN : ∀ r : ℝ, 1 ≤ r → D.logCounting r ≤ C * r ^ p := fun r hr ↦
    logCounting_le_const_mul_rpow hD0 hp hsum hr
  obtain ⟨c', hc'0, hSMT⟩ := exists_characteristic_le_logCounting hF hF0 ha
  set K := c' * log⁺ (2 * (c' + 1)) with hK
  have hK0 : (0 : ℝ) ≤ K := by
    have := posLog_nonneg (x := 2 * (c' + 1))
    rw [hK]
    positivity
  refine ⟨2 * C + 2 * c' / p + 2 * K, ?_⟩
  filter_upwards [hSMT, mem_inf_of_right (eventually_ge_atTop (1 : ℝ))] with r hsmt hr1
  have hrp1 : (1 : ℝ) ≤ r ^ p := Real.one_le_rpow hr1 hp.le
  have hT0 : 0 ≤ characteristic F ⊤ r := characteristic_nonneg hr1
  have h₂ : logCounting F ((a : ℂ) : WithTop ℂ) r ≤ C * r ^ p := by
    rw [logCounting_coe]
    exact hN r hr1
  have hclog : c' * Real.log r ≤ c' / p * r ^ p := by
    calc c' * Real.log r ≤ c' * (r ^ p / p) :=
          mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (zero_le_one.trans hr1) hp) hc'0
      _ = c' / p * r ^ p := by ring
  -- the characteristic bounds its own `log⁺`, so absorb that occurrence into half of it
  have habsorb : characteristic F ⊤ r ≤ 2 * (C * r ^ p + c' / p * r ^ p) + 2 * K :=
    le_two_mul_add_of_le_add_mul_posLog (M := C * r ^ p + c' / p * r ^ p) hT0 hc'0
      (by linarith [hsmt, h₂, hclog])
  have hKr : 2 * K ≤ 2 * K * r ^ p := by nlinarith [hK0, hrp1]
  calc characteristic F ⊤ r
      ≤ 2 * (C * r ^ p + c' / p * r ^ p) + 2 * K := habsorb
    _ ≤ 2 * (C * r ^ p + c' / p * r ^ p) + 2 * K * r ^ p := by linarith [hKr]
    _ = (2 * C + 2 * c' / p + 2 * K) * r ^ p := by ring

/--
For `F` entire and never zero and `a ≠ 0`: if the series `∑ z, D z * ‖z‖ ^ (-p)` over the divisor
`D` of `a`-points of `F` converges for some `p > 0`, then the Nevanlinna characteristic of `F` is
`O(r ^ p)`.
-/
theorem characteristic_isBigO_rpow_of_summable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∀ z, F z ≠ 0) {a : ℂ} (ha : a ≠ 0) {p : ℝ} (hp : 0 < p)
    (hsum : Summable fun z : ℂ ↦
      (((MeromorphicOn.divisor (F · - a) univ)⁺ z : ℤ) : ℝ) * ‖z‖ ^ (-p)) :
    characteristic F ⊤ =O[atTop] fun r : ℝ ↦ r ^ p := by
  obtain ⟨B, hbound⟩ := exists_characteristic_le_const_mul_rpow hF hF0 ha hp hsum
  exact isBigO_rpow_of_monotoneOn (x₀ := 1) hp.le
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr using characteristic_nonneg hr)
    ((characteristic_monotoneOn (fun x ↦ (hF.analyticAt x).meromorphicAt)).mono
      fun x hx ↦ mem_Ioi.2 (lt_of_lt_of_le one_pos hx))
    hbound

/--
**Nevanlinna's theorem**: an entire function `F` without zeros has order at most the exponent of
convergence of its `a`-points, for any `a ≠ 0`.
-/
theorem order_le_expConvergence {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : ∀ z, F z ≠ 0)
    {a : ℂ} (ha : a ≠ 0) :
    order F ≤ expConvergence (MeromorphicOn.divisor (F · - a) univ)⁺ := by
  refine le_iInf₂ fun q hq ↦ ?_
  simp only [Set.mem_ofPred_eq] at hq
  rcases eq_zero_or_pos q with h0 | h0
  · subst h0
    have hq0 : Summable fun z : ℂ ↦
        (((MeromorphicOn.divisor (F · - a) univ)⁺ z : ℤ) : ℝ) * ‖z‖ ^ (-(0 : ℝ)) := by
      simpa using hq
    have hord : order F = 0 := order_eq_zero_of_forall_pos fun s hs ↦
      characteristic_isBigO_rpow_of_summable hF hF0 ha (by exact_mod_cast hs)
        (summable_rpow_of_summable_zero (posPart_nonneg _) hq0 (s : ℝ))
    simp [hord]
  · exact order_le_of_isBigO
      (characteristic_isBigO_rpow_of_summable hF hF0 ha (by exact_mod_cast h0) hq)


/-! ### Axiom footprint -/

/-- info: 'Shields.order_le_expConvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms order_le_expConvergence

end Shields
