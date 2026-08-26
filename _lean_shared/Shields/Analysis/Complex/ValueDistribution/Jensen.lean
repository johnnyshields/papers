/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
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
* `Shields.summable_rpow_of_counting_le` — the converse of `logCounting_le_const_mul_rpow`:
  `counting D r = O(r ^ σ)` with `σ < p` gives summability of `∑ D z * ‖z‖ ^ (-p)`.
* `Shields.counting_le_log_div_log_two` — Jensen's inequality in counting form: the mass in the
  ball of radius `r` is at most `log (M / ‖f 0‖) / log 2` for `M` a bound on the circle of radius
  `2 * r`.
* `Shields.norm_le_re_of_nonneg_coeffs` — a power series with nonnegative real coefficients attains
  its maximum modulus on the positive real axis.
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
    simpa using (locallyFinsuppWithin.le_def.1 hD) z
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
    calc (2 : ℝ) ^ (Nat.log 2 ⌊‖z‖⌋₊) = ((2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊) : ℝ) := by push_cast; ring
      _ ≤ (⌊‖z‖⌋₊ : ℝ) := h2
      _ ≤ ‖z‖ := Nat.floor_le (norm_nonneg z)
  · have h1 : ⌊‖z‖⌋₊ < (2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) := Nat.lt_pow_succ_log_self one_lt_two _
    have h2 : (⌊‖z‖⌋₊ : ℝ) + 1 ≤ ((2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) : ℝ) := by
      have : ⌊‖z‖⌋₊ + 1 ≤ (2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) := by omega
      exact_mod_cast this
    calc ‖z‖ < (⌊‖z‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ‖z‖
      _ ≤ ((2 : ℕ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) : ℝ) := h2
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊‖z‖⌋₊ + 1) := by push_cast; ring

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
  have h2pos : (0 : ℝ) < 2 := two_pos
  set f : E → ℝ := fun z ↦ (D z : ℝ) * ‖z‖ ^ (-p) with hfdef
  have hfnn : ∀ z, 0 ≤ f z := fun z ↦ summand_nonneg hD p z
  set q : ℝ := (2 : ℝ) ^ (σ - p) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos h2pos _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set F₀ : Finset E := (finite_support_toClosedBall D r₀).toFinset with hF₀
  refine summable_of_sum_le hfnn (c := (∑ z ∈ F₀, f z) + C * 2 ^ σ * (1 - q)⁻¹) ?_
  intro u
  set A : Finset E := u.filter fun z ↦ ‖z‖ ≤ r₀ with hA
  set A' : Finset E := u.filter fun z ↦ ¬ ‖z‖ ≤ r₀ with hA'
  -- the near part is bounded by the fixed finite sum over the support in the ball of radius `r₀`
  have hnear : ∑ z ∈ A, f z ≤ ∑ z ∈ F₀, f z := by
    have h1 : ∑ z ∈ A.filter (fun z ↦ D z ≠ 0), f z = ∑ z ∈ A, f z := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro z hzA hzA0
      have hDz : D z = 0 := by
        by_contra hne
        exact hzA0 (Finset.mem_filter.2 ⟨hzA, hne⟩)
      simp [hfdef, hDz]
    have h2 : A.filter (fun z ↦ D z ≠ 0) ⊆ F₀ := by
      intro z hz
      obtain ⟨hzA, hzne⟩ := Finset.mem_filter.1 hz
      have hznear : ‖z‖ ≤ r₀ := (Finset.mem_filter.1 hzA).2
      have hmem : z ∈ closedBall (0 : E) |r₀| := by
        rw [mem_closedBall_zero_iff, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₀)]
        exact hznear
      rw [hF₀, Set.Finite.mem_toFinset]
      simp only [Function.mem_support, ne_eq, Int.cast_eq_zero]
      rw [locallyFinsuppWithin.toClosedBall_eval_within D hmem]
      exact hzne
    rw [← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg h2 fun z _ _ ↦ hfnn z
  -- the far part splits into dyadic shells
  set idx : E → ℕ := fun z ↦ Nat.log 2 ⌊‖z‖⌋₊ with hidx
  set K : ℕ := A'.sup idx with hK
  have hshell : ∀ z ∈ A', (2 : ℝ) ^ (idx z) ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (idx z + 1) := by
    intro z hz
    have : ¬ ‖z‖ ≤ r₀ := (Finset.mem_filter.1 hz).2
    exact dyadic_shell (by linarith [not_le.1 this])
  have hfar : ∀ k : ℕ, ∑ z ∈ A'.filter (fun z ↦ idx z = k), f z ≤ C * 2 ^ σ * q ^ k := by
    intro k
    have hid : ((2 : ℝ) ^ k) ^ (-p) * (C * ((2 : ℝ) ^ (k + 1)) ^ σ) = C * (2 : ℝ) ^ σ * q ^ k := by
      rw [hq]; exact rpow_shell_bound σ p C k
    rcases (A'.filter (fun z ↦ idx z = k)).eq_empty_or_nonempty with he | ⟨w, hw⟩
    · rw [he, Finset.sum_empty]
      positivity
    · obtain ⟨hwA', hwk⟩ := Finset.mem_filter.1 hw
      have hwfar : r₀ < ‖w‖ := not_le.1 (Finset.mem_filter.1 hwA').2
      have hwub : ‖w‖ < (2 : ℝ) ^ (k + 1) := by
        have := (hshell w hwA').2
        rwa [hwk] at this
      have hr₀le : r₀ ≤ (2 : ℝ) ^ (k + 1) := le_of_lt (lt_trans hwfar hwub)
      have hmass : ∑ z ∈ A'.filter (fun z ↦ idx z = k), (D z : ℝ)
          ≤ C * ((2 : ℝ) ^ (k + 1)) ^ σ := by
        refine le_trans (sum_le_counting hD ?_) (hcount _ hr₀le)
        intro z hz
        obtain ⟨hzA', hzk⟩ := Finset.mem_filter.1 hz
        have hub : ‖z‖ < (2 : ℝ) ^ (k + 1) := by
          have := (hshell z hzA').2
          rwa [hzk] at this
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1))]
        exact hub.le
      have hterm : ∀ z ∈ A'.filter (fun z ↦ idx z = k),
          f z ≤ ((2 : ℝ) ^ k) ^ (-p) * (D z : ℝ) := by
        intro z hz
        obtain ⟨hzA', hzk⟩ := Finset.mem_filter.1 hz
        have hlb : (2 : ℝ) ^ k ≤ ‖z‖ := by
          have := (hshell z hzA').1
          rwa [hzk] at this
        have hDz : (0 : ℝ) ≤ (D z : ℝ) := by
          have : (0 : ℤ) ≤ D z := by simpa using (locallyFinsuppWithin.le_def.1 hD) z
          exact_mod_cast this
        have hnorm : ‖z‖ ^ (-p) ≤ ((2 : ℝ) ^ k) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlb (by linarith)
        calc f z = (D z : ℝ) * ‖z‖ ^ (-p) := rfl
          _ ≤ (D z : ℝ) * ((2 : ℝ) ^ k) ^ (-p) := mul_le_mul_of_nonneg_left hnorm hDz
          _ = ((2 : ℝ) ^ k) ^ (-p) * (D z : ℝ) := by ring
      calc ∑ z ∈ A'.filter (fun z ↦ idx z = k), f z
          ≤ ∑ z ∈ A'.filter (fun z ↦ idx z = k), ((2 : ℝ) ^ k) ^ (-p) * (D z : ℝ) :=
            Finset.sum_le_sum hterm
        _ = ((2 : ℝ) ^ k) ^ (-p) * ∑ z ∈ A'.filter (fun z ↦ idx z = k), (D z : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ ((2 : ℝ) ^ k) ^ (-p) * (C * ((2 : ℝ) ^ (k + 1)) ^ σ) := by
            refine mul_le_mul_of_nonneg_left hmass (by positivity)
        _ = C * (2 : ℝ) ^ σ * q ^ k := hid
  have hmaps : ∀ z ∈ A', idx z ∈ Finset.range (K + 1) := by
    intro z hz
    exact Finset.mem_range_succ_iff.2 (Finset.le_sup hz)
  have hfarsum : ∑ z ∈ A', f z ≤ C * 2 ^ σ * (1 - q)⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
    calc ∑ k ∈ Finset.range (K + 1), ∑ z ∈ A'.filter (fun z ↦ idx z = k), f z
        ≤ ∑ k ∈ Finset.range (K + 1), C * 2 ^ σ * q ^ k := Finset.sum_le_sum fun k _ ↦ hfar k
      _ = C * 2 ^ σ * ∑ k ∈ Finset.range (K + 1), q ^ k := by rw [Finset.mul_sum]
      _ ≤ C * 2 ^ σ * (1 - q)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ k ∈ Finset.range (K + 1), q ^ k ≤ ∑' k : ℕ, q ^ k :=
                Summable.sum_le_tsum _ (fun k _ ↦ by positivity)
                  (summable_geometric_of_lt_one hq0.le hq1)
            _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0.le hq1
  calc ∑ z ∈ u, f z = ∑ z ∈ A, f z + ∑ z ∈ A', f z :=
        (Finset.sum_filter_add_sum_filter_not u _ f).symm
    _ ≤ (∑ z ∈ F₀, f z) + C * 2 ^ σ * (1 - q)⁻¹ := add_le_add hnear hfarsum

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
  have hp : 0 < p := lt_of_le_of_lt hσ hσp
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨c, hc0, hcw⟩ := hgrowth.exists_nonneg
  obtain ⟨r₁, hr₁⟩ := Filter.eventually_atTop.1 hcw.bound
  set L : ℝ := |Real.log ‖F 0‖| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  have hDnn : 0 ≤ MeromorphicOn.divisor F Set.univ :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg fun x _ ↦ hF.analyticAt x
  refine summable_rpow_of_counting_le hDnn (σ := σ) (p := p)
    (C := (c * 2 ^ σ + L) / Real.log 2) (r₀ := max r₁ 1) hσp hp
    (div_nonneg (by positivity) hlog2.le) (le_max_right _ _) ?_
  intro r hrr₀
  have hr1 : 1 ≤ r := le_trans (le_max_right r₁ 1) hrr₀
  have hr0 : 0 < r := by linarith
  have hr₁le : r₁ ≤ 2 * r := by
    have : r₁ ≤ r := le_trans (le_max_left r₁ 1) hrr₀
    linarith
  have hrσ : 1 ≤ r ^ σ := by simpa using Real.rpow_le_rpow zero_le_one hr1 hσ
  set M : ℝ := max 1 ‖F ((2 * r : ℝ) : ℂ)‖ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  -- the modulus bound on the circle of radius `2 * r` comes from the nonnegative coefficients
  have hbd : ∀ z : ℂ, ‖z‖ = 2 * r → ‖F z‖ ≤ M := by
    intro z hz
    have h1 : ‖F z‖ ≤ (F (‖z‖ : ℂ)).re := norm_le_re_of_nonneg_coeffs ha hsum z
    have h2 : (F (‖z‖ : ℂ)).re ≤ ‖F (‖z‖ : ℂ)‖ := Complex.re_le_norm _
    rw [hz] at h1 h2
    exact le_trans h1 (le_trans h2 (le_max_right _ _))
  -- and Jensen turns it into a bound on the counting function
  have hcnt := counting_le_log_div_log_two hF hF0 hr0 hM1 hbd
  have hlogM : Real.log M ≤ c * 2 ^ σ * r ^ σ := by
    have hnn : (0 : ℝ) ≤ c * 2 ^ σ * r ^ σ :=
      mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) σ)) (Real.rpow_nonneg hr0.le σ)
    rcases max_cases 1 ‖F ((2 * r : ℝ) : ℂ)‖ with ⟨he, _⟩ | ⟨he, _⟩
    · rw [hMdef, he, Real.log_one]
      exact hnn
    · rw [hMdef, he]
      have hb := hr₁ (2 * r) hr₁le
      have h2 : |Real.log ‖F ((2 * r : ℝ) : ℂ)‖| ≤ c * |(2 * r) ^ σ| := by
        simpa [Real.norm_eq_abs] using hb
      rw [abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * r) σ)] at h2
      have h4 : (2 * r) ^ σ = 2 ^ σ * r ^ σ := Real.mul_rpow (by norm_num) hr0.le
      rw [h4] at h2
      have h5 : Real.log ‖F ((2 * r : ℝ) : ℂ)‖ ≤ c * (2 ^ σ * r ^ σ) :=
        le_trans (le_abs_self _) h2
      linarith
  have hnum : Real.log M - Real.log ‖F 0‖ ≤ c * 2 ^ σ * r ^ σ + L * r ^ σ := by
    have h1 : -Real.log ‖F 0‖ ≤ L := neg_le_abs _
    have h2 : L ≤ L * r ^ σ := by nlinarith
    linarith
  calc counting (MeromorphicOn.divisor F Set.univ) r
      ≤ Real.log (M / ‖F 0‖) / Real.log 2 := hcnt
    _ = (Real.log M - Real.log ‖F 0‖) / Real.log 2 := by
        rw [Real.log_div hM0.ne' (norm_ne_zero_iff.2 hF0)]
    _ ≤ (c * 2 ^ σ * r ^ σ + L * r ^ σ) / Real.log 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.2 hlog2.le)
    _ = (c * 2 ^ σ + L) / Real.log 2 * r ^ σ := by ring

end Shields
