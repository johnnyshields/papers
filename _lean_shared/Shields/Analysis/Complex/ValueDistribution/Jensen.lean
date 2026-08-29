/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Shields.Analysis.Complex.ValueDistribution.ExponentOfConvergence

/-!
# From a growth bound to summability of the zeros

`Shields.logCounting_le_const_mul_rpow` bounds the counting function of a divisor by the exponent
at which its series converges.  This file runs the implication in the other direction: a growth
bound on the counting function gives *summability* of `∑ D z * ‖z‖ ^ (-p)` at every exponent `p`
above the growth exponent, and Jensen's inequality supplies such a growth bound from a bound on
the modulus of the function whose zeros the divisor counts.

The chain is

  `log ‖F‖ = O(r ^ σ)`  ⟹  `counting = O(r ^ σ)`  ⟹  `∑ ‖z‖ ^ (-p) < ∞` for every `p > σ`.

The second step is a summation by parts over dyadic shells: the shell `2 ^ k ≤ ‖z‖ < 2 ^ (k + 1)`
contributes at most `(2 ^ k) ^ (-p)` times the mass in the ball of radius `2 ^ (k + 1)`, so the
shell sums are dominated by the geometric series of ratio `2 ^ (σ - p) < 1`.

For a function with nonnegative Taylor coefficients the modulus bound is free:
`‖F z‖ ≤ F ‖z‖`, so the growth hypothesis is a statement about the values on the positive real
axis alone and needs no information about where the zeros lie.

## Main results

* `Shields.counting` — the unweighted counting function, the mass of a divisor in a closed ball.
* `Shields.sum_le_counting` — a finite sum of the masses of points in the ball is at most
  `counting`.
* `Shields.sum_far_le` — the points beyond `r₀`, summed over dyadic shells.
* `Shields.summable_rpow_of_counting_le` — the converse of `logCounting_le_const_mul_rpow`:
  `counting D r = O(r ^ σ)` with `σ < p` gives summability of `∑ D z * ‖z‖ ^ (-p)`.
* `Shields.counting_le_log_div_log_two` — Jensen's inequality in counting form: the mass in the
  ball of radius `r` is at most `log (M / ‖f 0‖) / log 2` for `M` a bound on the circle of radius
  `2 * r`.
* `Shields.norm_le_re_of_nonneg_coeffs` — a power series with nonnegative real coefficients attains
  its maximum modulus on the positive real axis.
* `Shields.counting_le_const_mul_rpow` — Jensen against a growth bound on the positive axis: the
  mass in the ball of radius `r` is `O(r ^ σ)`.
* `Shields.summable_rpow_divisor_of_growth` — the composite: a polynomial-in-`r ^ σ` bound on
  `log ‖F r‖` along the positive axis makes the zero divisor of `F` summable at every `p > σ`.

## Tags

Jensen's inequality, counting function, exponent of convergence, value distribution
-/

open Filter Function Metric Real Set
open scoped NNReal Topology

namespace Shields

variable {E : Type*} [NormedAddCommGroup E]

/-! ### The unweighted counting function -/

/--
The unweighted counting function of a divisor: the total mass of `D` in the closed ball of radius
`|r|` about the origin, counted with multiplicity.  This is the function written `n(r)` in
Nevanlinna theory, without the logarithmic weight carried by
`Function.locallyFinsuppWithin.logCounting`.
-/
noncomputable def counting (D : locallyFinsupp E ℤ) (r : ℝ) : ℝ :=
  ∑ᶠ z : E, ((D.toClosedBall r) z : ℝ)

/--
The restriction of a nonnegative divisor to a closed ball is nonnegative.
-/
theorem toClosedBall_nonneg {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) (r : ℝ) (z : E) :
    (0 : ℤ) ≤ (D.toClosedBall r) z := by
  by_cases hmem : z ∈ closedBall (0 : E) |r|
  · rw [locallyFinsuppWithin.toClosedBall_eval_within D hmem]
    exact hD z
  · have h0 : (D.toClosedBall r) z = 0 := by
      by_contra hne
      exact hmem (locallyFinsuppWithin.toClosedBall_support_subset_closedBall D hne)
    simp [h0]

/--
The summand of `counting` has finite support, so the unordered sum defining it is a finite sum.
-/
theorem finite_support_toClosedBall [ProperSpace E] (D : locallyFinsupp E ℤ) (r : ℝ) :
    (Function.support fun z : E ↦ ((D.toClosedBall r) z : ℝ)).Finite := by
  refine Set.Finite.subset ((D.toClosedBall r).finiteSupport (isCompact_closedBall 0 |r|)) ?_
  intro z hz
  simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hz ⊢
  exact hz

/--
Any finite sum of the masses of points in the closed ball of radius `|r|` is at most the total
mass there.
-/
theorem sum_le_counting [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) {r : ℝ}
    {s : Finset E} (hs : ∀ z ∈ s, ‖z‖ ≤ |r|) :
    ∑ z ∈ s, (D z : ℝ) ≤ counting D r := by
  classical
  have hfin := finite_support_toClosedBall D r
  have hsub : (Function.support fun z : E ↦ ((D.toClosedBall r) z : ℝ))
      ⊆ ↑(hfin.toFinset ∪ s) := by
    intro z hz
    simp only [Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]
    exact Or.inl hz
  have hcount : counting D r = ∑ z ∈ hfin.toFinset ∪ s, ((D.toClosedBall r) z : ℝ) := by
    rw [counting, finsum_eq_sum_of_support_subset _ hsub]
  have hres : ∀ z ∈ s, (D z : ℝ) = ((D.toClosedBall r) z : ℝ) := by
    intro z hz
    rw [locallyFinsuppWithin.toClosedBall_eval_within D
      (by simpa [mem_closedBall_zero_iff] using hs z hz)]
  rw [hcount, Finset.sum_congr rfl hres]
  refine Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right ?_
  intro z _ _
  exact_mod_cast toClosedBall_nonneg hD r z


/-! ### The Borel converse: a growth bound on the counting function gives summability -/

/--
A point of norm exceeding `1` lies in the dyadic shell indexed by `Nat.log 2 ⌊‖z‖⌋₊`.
-/
theorem dyadic_shell {z : E} (hz : 1 ≤ ‖z‖) :
    (2 : ℝ) ^ (Nat.log 2 ⌊‖z‖⌋₊) ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) := by
  have hfloor : 1 ≤ ⌊‖z‖⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hne : ⌊‖z‖⌋₊ ≠ 0 := by omega
  constructor
  · have h1 : (2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊) ≤ ⌊‖z‖⌋₊ := Nat.pow_log_le_self 2 hne
    have h2 : ((2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊) : ℝ) ≤ (⌊‖z‖⌋₊ : ℝ) := by exact_mod_cast h1
    calc (2 : ℝ) ^ (Nat.log 2 ⌊‖z‖⌋₊) = ((2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊) : ℝ) := by norm_cast
      _ ≤ (⌊‖z‖⌋₊ : ℝ) := h2
      _ ≤ ‖z‖ := Nat.floor_le (norm_nonneg z)
  · have h1 : ⌊‖z‖⌋₊ < (2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) := Nat.lt_pow_succ_log_self one_lt_two _
    have h2 : (⌊‖z‖⌋₊ : ℝ) + 1 ≤ ((2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) : ℝ) := by
      have : ⌊‖z‖⌋₊ + 1 ≤ (2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) := by omega
      exact_mod_cast this
    calc ‖z‖ < (⌊‖z‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ‖z‖
      _ ≤ ((2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) : ℝ) := h2
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) := by norm_cast

/-- **The shell-to-shell ratio is `2 ^ (σ - p)`.**  A point of the `k`-th dyadic shell contributes
at most `(2 ^ k) ^ (-p)` and the shell carries mass at most `C * (2 ^ (k+1)) ^ σ`, so its total is
`C * 2 ^ σ` times `(2 ^ (σ - p)) ^ k`.

This identity is where the hypothesis `σ < p` earns its place: it is exactly the condition making
that ratio less than one, and so the only reason the sum over shells converges. -/
theorem rpow_shell_bound (σ p C : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ k) ^ (-p) * (C * ((2 : ℝ) ^ (k + 1)) ^ σ)
      = C * (2 : ℝ) ^ σ * ((2 : ℝ) ^ (σ - p)) ^ k := by
  have h2pos : (0 : ℝ) < 2 := two_pos
  have e1 : ((2 : ℝ) ^ k) ^ (-p) = (2 : ℝ) ^ ((k : ℝ) * (-p)) := by
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul h2pos.le]
  have e2 : ((2 : ℝ) ^ (k + 1)) ^ σ = (2 : ℝ) ^ (((k : ℝ) + 1) * σ) := by
    rw [← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul h2pos.le]
    push_cast
    ring_nf
  have e3 : ((2 : ℝ) ^ (σ - p)) ^ k = (2 : ℝ) ^ ((σ - p) * (k : ℝ)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (σ - p)) k, ← Real.rpow_mul h2pos.le]
  rw [e1, e2, e3, show ((k : ℝ) + 1) * σ = σ + (k : ℝ) * σ by ring, Real.rpow_add h2pos,
    show (σ - p) * (k : ℝ) = (k : ℝ) * (-p) + (k : ℝ) * σ by ring, Real.rpow_add h2pos]
  ring

/-- **The near part is bounded once and for all.**  Points inside the ball of radius `r₀` are
finitely many, so whatever finite set of them a partial sum happens to meet, it is dominated by the
one fixed sum over the whole support there. -/
theorem sum_near_le_sum_support_ball [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    {p r₀ : ℝ} (hr₀ : 0 ≤ r₀) {A : Finset E} (hA : ∀ z ∈ A, ‖z‖ ≤ r₀) :
    ∑ z ∈ A, (D z : ℝ) * ‖z‖ ^ (-p)
      ≤ ∑ z ∈ (finite_support_toClosedBall D r₀).toFinset, (D z : ℝ) * ‖z‖ ^ (-p) := by
  classical
  have hfnn : ∀ z : E, 0 ≤ (D z : ℝ) * ‖z‖ ^ (-p) := fun z ↦ summand_nonneg hD p z
  have h1 : ∑ z ∈ A.filter (fun z ↦ D z ≠ 0), (D z : ℝ) * ‖z‖ ^ (-p)
      = ∑ z ∈ A, (D z : ℝ) * ‖z‖ ^ (-p) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro z hzA hzA0
    have hDz : D z = 0 := by
      by_contra hne
      exact hzA0 (Finset.mem_filter.2 ⟨hzA, hne⟩)
    simp [hDz]
  have h2 : A.filter (fun z ↦ D z ≠ 0) ⊆ (finite_support_toClosedBall D r₀).toFinset := by
    intro z hz
    obtain ⟨hzA, hzne⟩ := Finset.mem_filter.1 hz
    have hmem : z ∈ closedBall (0 : E) |r₀| := by
      rw [mem_closedBall_zero_iff, abs_of_nonneg hr₀]
      exact hA z hzA
    rw [Set.Finite.mem_toFinset]
    simp only [Function.mem_support, ne_eq, Int.cast_eq_zero]
    rw [locallyFinsuppWithin.toClosedBall_eval_within D hmem]
    exact hzne
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg h2 fun z _ _ ↦ hfnn z

/-- **One dyadic shell's contribution.**  A shell whose points all lie beyond `r₀` carries mass at
most `C * (2 ^ (k+1)) ^ σ`, and each of its points is weighted by at most `(2 ^ k) ^ (-p)`;
`rpow_shell_bound` turns the product into the `k`-th term of a geometric series of ratio
`2 ^ (σ - p)`. -/
theorem shell_sum_le [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    {σ p C r₀ : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hcount : ∀ r : ℝ, r₀ ≤ r → counting D r ≤ C * r ^ σ)
    {S : Finset E} {k : ℕ} (hlb : ∀ z ∈ S, (2 : ℝ) ^ k ≤ ‖z‖)
    (hub : ∀ z ∈ S, ‖z‖ < (2 : ℝ) ^ (k + 1)) (hout : ∀ z ∈ S, r₀ < ‖z‖) :
    ∑ z ∈ S, (D z : ℝ) * ‖z‖ ^ (-p) ≤ C * 2 ^ σ * ((2 : ℝ) ^ (σ - p)) ^ k := by
  rcases S.eq_empty_or_nonempty with he | ⟨w, hw⟩
  · rw [he, Finset.sum_empty]
    positivity
  have hr₀le : r₀ ≤ (2 : ℝ) ^ (k + 1) := le_of_lt (lt_trans (hout w hw) (hub w hw))
  have hmass : ∑ z ∈ S, (D z : ℝ) ≤ C * ((2 : ℝ) ^ (k + 1)) ^ σ := by
    refine le_trans (sum_le_counting hD ?_) (hcount _ hr₀le)
    intro z hz
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1))]
    exact (hub z hz).le
  have hterm : ∀ z ∈ S, (D z : ℝ) * ‖z‖ ^ (-p) ≤ ((2 : ℝ) ^ k) ^ (-p) * (D z : ℝ) := by
    intro z hz
    have hDz : (0 : ℝ) ≤ (D z : ℝ) := locallyFinsuppWithin_apply_intCast_nonneg hD z
    have hnorm : ‖z‖ ^ (-p) ≤ ((2 : ℝ) ^ k) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hlb z hz) (by linarith)
    calc (D z : ℝ) * ‖z‖ ^ (-p) ≤ (D z : ℝ) * ((2 : ℝ) ^ k) ^ (-p) :=
          mul_le_mul_of_nonneg_left hnorm hDz
      _ = ((2 : ℝ) ^ k) ^ (-p) * (D z : ℝ) := by ring
  calc ∑ z ∈ S, (D z : ℝ) * ‖z‖ ^ (-p)
      ≤ ∑ z ∈ S, ((2 : ℝ) ^ k) ^ (-p) * (D z : ℝ) := Finset.sum_le_sum hterm
    _ = ((2 : ℝ) ^ k) ^ (-p) * ∑ z ∈ S, (D z : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ k) ^ (-p) * (C * ((2 : ℝ) ^ (k + 1)) ^ σ) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = C * 2 ^ σ * ((2 : ℝ) ^ (σ - p)) ^ k := rpow_shell_bound σ p C k


/-- **The far part: the dyadic shells sum to a geometric series.**  A finite set of points all
lying beyond `r₀` is cut into the shells `2 ^ k ≤ ‖z‖ < 2 ^ (k + 1)`, each of which
`Shields.shell_sum_le` bounds by the `k`-th term of a geometric series of ratio `2 ^ (σ - p) < 1`.

The companion of `Shields.sum_near_le_sum_support_ball`, which bounds the points inside `r₀`. -/
theorem sum_far_le [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) {σ p C r₀ : ℝ}
    (hσp : σ < p) (hp : 0 < p) (hC : 0 ≤ C) (hr₀ : 1 ≤ r₀)
    (hcount : ∀ r : ℝ, r₀ ≤ r → counting D r ≤ C * r ^ σ) {A : Finset E}
    (hA : ∀ z ∈ A, r₀ < ‖z‖) :
    ∑ z ∈ A, (D z : ℝ) * ‖z‖ ^ (-p) ≤ C * 2 ^ σ * (1 - (2 : ℝ) ^ (σ - p))⁻¹ := by
  classical
  set q : ℝ := (2 : ℝ) ^ (σ - p) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos two_pos _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set idx : E → ℕ := fun z ↦ Nat.log 2 ⌊‖z‖⌋₊ with hidx
  set K : ℕ := A.sup idx with hK
  have hshell : ∀ z ∈ A, (2 : ℝ) ^ (idx z) ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (idx z + 1) := fun z hz ↦
    dyadic_shell (by linarith [hA z hz])
  have hfar : ∀ k : ℕ, ∑ z ∈ A.filter (fun z ↦ idx z = k), (D z : ℝ) * ‖z‖ ^ (-p)
      ≤ C * 2 ^ σ * q ^ k := by
    intro k
    refine shell_sum_le hD hp.le hC hcount ?_ ?_ ?_ <;> intro z hz <;>
      obtain ⟨hzA, hzk⟩ := Finset.mem_filter.1 hz
    · exact hzk ▸ (hshell z hzA).1
    · exact hzk ▸ (hshell z hzA).2
    · exact hA z hzA
  have hmaps : ∀ z ∈ A, idx z ∈ Finset.range (K + 1) := fun z hz ↦
    Finset.mem_range_succ_iff.2 (Finset.le_sup hz)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Finset.range (K + 1), ∑ z ∈ A.filter (fun z ↦ idx z = k), (D z : ℝ) * ‖z‖ ^ (-p)
      ≤ ∑ k ∈ Finset.range (K + 1), C * 2 ^ σ * q ^ k := Finset.sum_le_sum fun k _ ↦ hfar k
    _ = C * 2 ^ σ * ∑ k ∈ Finset.range (K + 1), q ^ k := by rw [Finset.mul_sum]
    _ ≤ C * 2 ^ σ * (1 - q)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := geom_sum_Ico_le_of_lt_one (x := q) (m := 0) (n := K + 1) hq0.le hq1
        rw [pow_zero, one_div] at h
        rwa [Finset.range_eq_Ico]

/--
**The converse of `Shields.logCounting_le_const_mul_rpow`.**  If the mass of a nonnegative divisor
in the ball of radius `r` grows at most like `r ^ σ`, then `∑ D z * ‖z‖ ^ (-p)` converges at every
exponent `p > σ`.

The proof is a summation by parts over dyadic shells: the shell `2 ^ k ≤ ‖z‖ < 2 ^ (k + 1)` carries
mass at most `C * (2 ^ (k + 1)) ^ σ` and each of its points contributes at most `(2 ^ k) ^ (-p)`,
so the shell sums are dominated by a geometric series of ratio `2 ^ (σ - p) < 1`.
-/
theorem summable_rpow_of_counting_le [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    {σ p C r₀ : ℝ} (hσp : σ < p) (hp : 0 < p) (hC : 0 ≤ C) (hr₀ : 1 ≤ r₀)
    (hcount : ∀ r : ℝ, r₀ ≤ r → counting D r ≤ C * r ^ σ) :
    Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-p) := by
  classical
  set f : E → ℝ := fun z ↦ (D z : ℝ) * ‖z‖ ^ (-p) with hfdef
  set F₀ : Finset E := (finite_support_toClosedBall D r₀).toFinset with hF₀
  refine summable_of_sum_le (fun z ↦ summand_nonneg hD p z)
    (c := (∑ z ∈ F₀, f z) + C * 2 ^ σ * (1 - (2 : ℝ) ^ (σ - p))⁻¹) fun u ↦ ?_
  have hnear : ∑ z ∈ u.filter (fun z ↦ ‖z‖ ≤ r₀), f z ≤ ∑ z ∈ F₀, f z :=
    sum_near_le_sum_support_ball hD (by linarith) fun z hz ↦ (Finset.mem_filter.1 hz).2
  have hfarsum := sum_far_le hD hσp hp hC hr₀ hcount
    (A := u.filter fun z ↦ ¬ ‖z‖ ≤ r₀) fun z hz ↦ not_le.1 (Finset.mem_filter.1 hz).2
  calc ∑ z ∈ u, f z
      = ∑ z ∈ u.filter (fun z ↦ ‖z‖ ≤ r₀), f z + ∑ z ∈ u.filter (fun z ↦ ¬ ‖z‖ ≤ r₀), f z :=
        (Finset.sum_filter_add_sum_filter_not u _ f).symm
    _ ≤ (∑ z ∈ F₀, f z) + C * 2 ^ σ * (1 - (2 : ℝ) ^ (σ - p))⁻¹ := add_le_add hnear hfarsum

/-! ### Jensen's inequality in counting form -/

/--
**Jensen's inequality, in counting form.**  If `f` is entire, `f 0 ≠ 0`, and `‖f‖ ≤ M` on the
circle of radius `2 * r`, then the number of zeros of `f` in the closed ball of radius `r`, counted
with multiplicity, is at most `log (M / ‖f 0‖) / log 2`.

This is Mathlib's `AnalyticOnNhd.sum_divisor_le` at `R = 2 * r`, restated for the divisor of `f` on
the whole plane rather than its restriction to the ball.
-/
theorem counting_le_log_div_log_two {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {r M : ℝ} (hr : 0 < r) (hM : 1 ≤ M) (hbd : ∀ z : ℂ, ‖z‖ = 2 * r → ‖f z‖ ≤ M) :
    counting (MeromorphicOn.divisor f Set.univ) r ≤ Real.log (M / ‖f 0‖) / Real.log 2 := by
  have habsr : |r| = r := abs_of_pos hr
  have habsR : |2 * r| = 2 * r := abs_of_pos (by linarith)
  have hmero : Meromorphic f := fun z ↦ (hf.analyticAt z).meromorphicAt
  have key := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := 2 * r) (M := M) (f := f)
      (by rw [habsr]; exact hr) (by rw [habsr, habsR]; linarith) hM
      (fun z _ ↦ hf.analyticAt z) hf0
      (fun z hz ↦ hbd z (by
        have hzn : ‖z - 0‖ = |2 * r| := by simpa [mem_sphere_iff_norm] using hz
        simpa [habsR] using hzn))
  have hRr : (2 * r) / r = 2 := by field_simp
  rw [hRr] at key
  refine le_trans (le_of_eq ?_) key
  have hfin := (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|)).finiteSupport
    (isCompact_closedBall 0 |r|)
  rw [counting, ← Function.locallyFinsuppWithin.toClosedBall_divisor hmero]
  exact (map_finsum (Int.castRingHom ℝ) hfin).symm

/-! ### Nonnegative coefficients put the maximum modulus on the positive axis -/

/--
A power series with nonnegative real coefficients attains its maximum modulus on a circle at the
positive real point of that circle: `‖F z‖ ≤ F ‖z‖`, the right-hand side being real.

This is what makes a growth hypothesis on the positive axis suffice: no information about the
location of the zeros of `F` is needed.
-/
theorem norm_le_re_of_nonneg_coeffs {a : ℕ → ℝ} {F : ℂ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hF : ∀ z : ℂ, HasSum (fun n ↦ (a n : ℂ) * z ^ n) (F z)) (z : ℂ) :
    ‖F z‖ ≤ (F (‖z‖ : ℂ)).re := by
  have h1 : HasSum (fun n ↦ (a n : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ n) (F (‖z‖ : ℂ)) := hF _
  have h2 : HasSum (fun n ↦ a n * ‖z‖ ^ n) (F (‖z‖ : ℂ)).re := by
    have h3 := h1.mapL Complex.reCLM
    simpa [← Complex.ofReal_pow, ← Complex.ofReal_mul] using h3
  refine HasSum.norm_le_of_bounded (hF z) h2 fun n ↦ ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]

/--
The maximum-modulus form of `Shields.norm_le_re_of_nonneg_coeffs`.
-/
theorem norm_le_norm_ofReal_norm {a : ℕ → ℝ} {F : ℂ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hF : ∀ z : ℂ, HasSum (fun n ↦ (a n : ℂ) * z ^ n) (F z)) (z : ℂ) :
    ‖F z‖ ≤ ‖F (‖z‖ : ℂ)‖ :=
  le_trans (norm_le_re_of_nonneg_coeffs ha hF z) (Complex.re_le_norm _)

/-! ### The composite: growth on the positive axis bounds the exponent of convergence -/

/-- **A growth bound on the positive axis bounds the counting function.**  For `F` entire with
nonnegative Taylor coefficients and `F 0 ≠ 0`, a bound `|log ‖F s‖| ≤ c s ^ σ` beyond `r₀ ≥ 1`
gives `counting (divisor F) r ≤ ((c 2 ^ σ + |log ‖F 0‖|) / log 2) r ^ σ` beyond `r₀`.

Nonnegative coefficients put the maximum modulus on the circle of radius `2r` at the positive real
point of that circle, so `Shields.counting_le_log_div_log_two` reads the count off a hypothesis
about the positive axis alone.  Nothing is assumed about where the zeros lie. -/
theorem counting_le_const_mul_rpow {a : ℕ → ℝ} {F : ℂ → ℂ} {σ c r₀ : ℝ}
    (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (ha : ∀ n, 0 ≤ a n)
    (hsum : ∀ z : ℂ, HasSum (fun n ↦ (a n : ℂ) * z ^ n) (F z)) (hσ : 0 ≤ σ) (hc0 : 0 ≤ c)
    (hr₀ : 1 ≤ r₀) (hbound : ∀ s : ℝ, r₀ ≤ s → |Real.log ‖F (s : ℂ)‖| ≤ c * s ^ σ)
    {r : ℝ} (hr : r₀ ≤ r) :
    counting (MeromorphicOn.divisor F Set.univ) r
      ≤ (c * 2 ^ σ + |Real.log ‖F 0‖|) / Real.log 2 * r ^ σ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hr1 : 1 ≤ r := le_trans hr₀ hr
  have hr0 : 0 < r := by linarith
  have hrσ : 1 ≤ r ^ σ := Real.one_le_rpow hr1 hσ
  -- the modulus bound on the circle of radius `2 * r` comes from the nonnegative coefficients
  set M : ℝ := max 1 ‖F ((2 * r : ℝ) : ℂ)‖ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hbd : ∀ z : ℂ, ‖z‖ = 2 * r → ‖F z‖ ≤ M := fun z hz => by
    refine le_trans (norm_le_norm_ofReal_norm ha hsum z) ?_
    rw [hz]
    exact le_max_right _ _
  have hnn : (0 : ℝ) ≤ c * 2 ^ σ * r ^ σ :=
    mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) σ)) (Real.rpow_nonneg hr0.le σ)
  have hlogM : Real.log M ≤ c * 2 ^ σ * r ^ σ := by
    have hb := hbound (2 * r) (by linarith)
    rw [Real.mul_rpow (by norm_num) hr0.le] at hb
    rcases max_cases 1 ‖F ((2 * r : ℝ) : ℂ)‖ with ⟨he, _⟩ | ⟨he, _⟩
    · rw [hMdef, he, Real.log_one]
      exact hnn
    · rw [hMdef, he]
      linarith [le_abs_self (Real.log ‖F ((2 * r : ℝ) : ℂ)‖)]
  have hnum : Real.log M - Real.log ‖F 0‖
      ≤ c * 2 ^ σ * r ^ σ + |Real.log ‖F 0‖| * r ^ σ := by
    have h1 : -Real.log ‖F 0‖ ≤ |Real.log ‖F 0‖| := neg_le_abs _
    have h2 : |Real.log ‖F 0‖| ≤ |Real.log ‖F 0‖| * r ^ σ := by
      nlinarith [abs_nonneg (Real.log ‖F 0‖)]
    linarith
  -- and Jensen turns it into a bound on the counting function
  calc counting (MeromorphicOn.divisor F Set.univ) r
      ≤ Real.log (M / ‖F 0‖) / Real.log 2 := counting_le_log_div_log_two hF hF0 hr0 hM1 hbd
    _ = (Real.log M - Real.log ‖F 0‖) / Real.log 2 := by
        rw [Real.log_div hM0.ne' (norm_ne_zero_iff.2 hF0)]
    _ ≤ (c * 2 ^ σ * r ^ σ + |Real.log ‖F 0‖| * r ^ σ) / Real.log 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.2 hlog2.le)
    _ = (c * 2 ^ σ + |Real.log ‖F 0‖|) / Real.log 2 * r ^ σ := by ring

/--
**A growth bound along the positive axis makes the zeros of an entire function with nonnegative
Taylor coefficients summable.**

If `F` is entire with nonnegative Taylor coefficients and `F 0 ≠ 0`, and if
`log ‖F r‖ = O(r ^ σ)` as `r → ∞` along the positive real axis, then
`∑ z, divisor F z * ‖z‖ ^ (-p)` converges for every `p > σ`.  Nothing is assumed about where the
zeros of `F` lie.
-/
theorem summable_rpow_divisor_of_growth {a : ℕ → ℝ} {F : ℂ → ℂ} {σ p : ℝ}
    (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (ha : ∀ n, 0 ≤ a n)
    (hsum : ∀ z : ℂ, HasSum (fun n ↦ (a n : ℂ) * z ^ n) (F z))
    (hσ : 0 ≤ σ) (hσp : σ < p)
    (hgrowth : (fun r : ℝ ↦ Real.log ‖F (r : ℂ)‖) =O[atTop] fun r : ℝ ↦ r ^ σ) :
    Summable fun z : ℂ ↦ ((MeromorphicOn.divisor F Set.univ) z : ℝ) * ‖z‖ ^ (-p) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨c, hc0, hcw⟩ := hgrowth.exists_nonneg
  obtain ⟨r₁, hr₁⟩ := Filter.eventually_atTop.1 hcw.bound
  have hbound : ∀ s : ℝ, max r₁ 1 ≤ s → |Real.log ‖F (s : ℂ)‖| ≤ c * s ^ σ := by
    intro s hs
    have hs1 : (1 : ℝ) ≤ s := le_trans (le_max_right r₁ 1) hs
    have h := hr₁ s (le_trans (le_max_left r₁ 1) hs)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) σ)] at h
  refine summable_rpow_of_counting_le
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg fun x _ ↦ hF.analyticAt x) (σ := σ) (p := p)
    (C := (c * 2 ^ σ + |Real.log ‖F 0‖|) / Real.log 2) (r₀ := max r₁ 1) hσp
    (lt_of_le_of_lt hσ hσp) (div_nonneg (by positivity) hlog2.le) (le_max_right _ _)
    fun r hr ↦ counting_le_const_mul_rpow hF hF0 ha hsum hσ hc0 (le_max_right _ _) hbound hr


/-! ### Axiom footprint -/

/-- info: 'Shields.summable_rpow_divisor_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms summable_rpow_divisor_of_growth

end Shields
