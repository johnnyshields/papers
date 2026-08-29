/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Field
import Shields.Probability.PoissonBinomialMode
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Le Cam's inequality

A sum of independent Bernoulli variables is within total-variation distance `\sum_ip_i^2` of the
Poisson law of the same mean.  This is the quantitative law of small numbers: it bounds the error
of the Poisson approximation with no limit and no asymptotic, so a family of Poisson binomials
whose squared parameters sum to something tending to `0` converges to the Poisson law in total
variation.

## Route

Mass functions on `\mathbb N` are handled directly as `\mathbb N \to \mathbb R`, with `dconv` the
discrete convolution.  Three ingredients:

* convolution is contractive for total variation, `tvDist_dconv_le`, because
  `|\sum_{k\le n}d_kr_{n-k}| \le \sum_{k\le n}|d_k|r_{n-k}` and the Cauchy product of the majorant
  sums to `\mathrm{tv}(p,q)`;
* the Poisson family is a convolution semigroup, `dconv_poisPMF`, by the binomial theorem;
* one Bernoulli against one Poisson costs exactly `2t(1-e^{-t})`, `tvDist_bernPMF_poisPMF`, which
  is at most `2t^2`.

Telescoping the first along a list of factors and collapsing the second gives the theorem.

## Normalization

`tvDist` here is the **unnormalized** `\sum_k|p_k-q_k|`, twice the usual total-variation distance;
the constant in `tvDist_bernConv_poisPMF_le` therefore reads `2\sum_ip_i^2` rather than
`\sum_ip_i^2`.

## Main results

* `Shields.tvDist_bernPMF_poisPMF_le` — the one-variable estimate `2t^2`, which is the whole
  content; `Shields.tvDist_pbNat_poisPMF_le` is **Le Cam's inequality**, `2\sum_ip_i^2`, obtained
  from it by the convolution bound `Shields.tvDist_dconv_le`.
* `Shields.exists_pbNat_tvDist_poisPMF_le` — the Poisson limit theorem in total variation: at `N`
  trials the cost is `2\lambda^2/N`, so a Poisson factor is replaced by binomials of the same mean
  at arbitrarily small cost.
* `Shields.mode_of_dconv_pbNat` — Darroch's theorem for a convolution of two Poisson binomials,
  which is what the replacement is fed to.
* `Shields.mode_of_dconv_pbNat_poisPMF`, `Shields.mode_of_approx_bernPoisson` — the mode placement
  that replacement buys, for a finite Bernoulli family and for an approximable one.
-/

namespace Shields

open Finset Nat

variable {p q r s : ℕ → ℝ}

/-! ### Mass functions and total variation -/

/-- A mass function on `\mathbb N`: nonnegative, summing to one. -/
structure IsPMF (p : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ p n
  hasSum : HasSum p 1

theorem IsPMF.summable (hp : IsPMF p) : Summable p := hp.hasSum.summable

theorem IsPMF.tsum_eq (hp : IsPMF p) : ∑' n, p n = 1 := hp.hasSum.tsum_eq

/-- A summable nonnegative real family is absolutely summable, its norm being itself. -/
theorem summable_norm_of_nonneg (hp0 : ∀ n, 0 ≤ p n) (hp : Summable p) :
    Summable fun n => ‖p n‖ := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hp0 _)] using hp

theorem IsPMF.summable_norm (hp : IsPMF p) : Summable fun n => ‖p n‖ :=
  summable_norm_of_nonneg hp.nonneg hp.summable

/-- The unnormalized total-variation distance, `\sum_k|p_k-q_k|`. -/
noncomputable def tvDist (p q : ℕ → ℝ) : ℝ := ∑' k, |p k - q k|

theorem tvDist_nonneg : 0 ≤ tvDist p q := tsum_nonneg fun _ => abs_nonneg _

theorem tvDist_self (p : ℕ → ℝ) : tvDist p p = 0 := by simp [tvDist]

theorem tvDist_comm (p q : ℕ → ℝ) : tvDist p q = tvDist q p := by
  simp only [tvDist, abs_sub_comm]

/-- Two mass functions are absolutely comparable. -/
theorem IsPMF.summable_sub (hp : IsPMF p) (hq : IsPMF q) :
    Summable fun k => |p k - q k| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
    (hp.summable.add hq.summable)
  calc |p k - q k| ≤ |p k| + |q k| := abs_sub _ _
    _ = p k + q k := by rw [abs_of_nonneg (hp.nonneg k), abs_of_nonneg (hq.nonneg k)]

theorem tvDist_triangle (h₁ : Summable fun k => |p k - q k|)
    (h₂ : Summable fun k => |q k - r k|) : tvDist p r ≤ tvDist p q + tvDist q r := by
  have hle : ∀ k, |p k - r k| ≤ |p k - q k| + |q k - r k| := fun k => by
    calc |p k - r k| = |(p k - q k) + (q k - r k)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hs : Summable fun k => |p k - r k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle (h₁.add h₂)
  calc tvDist p r ≤ ∑' k, (|p k - q k| + |q k - r k|) :=
        hs.tsum_le_tsum hle (h₁.add h₂)
    _ = tvDist p q + tvDist q r := h₁.tsum_add h₂

/-! ### Discrete convolution -/

/-- The convolution of two mass functions on `\mathbb N`. -/
noncomputable def dconv (p q : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), p k * q (n - k)

theorem dconv_nonneg (hp : ∀ n, 0 ≤ p n) (hq : ∀ n, 0 ≤ q n) (n : ℕ) : 0 ≤ dconv p q n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hp _) (hq _)

/-- A convolution is positive at `n` as soon as the first factor is positive at `0` and the second
at `n`: that single term already sits below the sum. -/
theorem dconv_pos (hp : ∀ n, 0 ≤ p n) (hq : ∀ n, 0 ≤ q n) (hp0 : 0 < p 0) {n : ℕ}
    (hqn : 0 < q n) : 0 < dconv p q n := by
  rw [dconv]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun k => p k * q (n - k))
    (fun k _ => mul_nonneg (hp k) (hq _)) (Finset.mem_range.2 (Nat.succ_pos n)))
  rw [Nat.sub_zero]
  exact mul_pos hp0 hqn

theorem dconv_comm (p q : ℕ → ℝ) : dconv p q = dconv q p := by
  funext n
  simp only [dconv]
  rw [← Finset.sum_range_reflect (fun k => p k * q (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Finset.mem_range_succ_iff.1 hk
  rw [show n + 1 - 1 - k = n - k from by omega, show n - (n - k) = k from by omega]
  ring

/-- Convolution is the coefficientwise product of the generating power series. -/
theorem mk_dconv (p q : ℕ → ℝ) :
    PowerSeries.mk (dconv p q) = PowerSeries.mk p * PowerSeries.mk q := by
  refine PowerSeries.ext fun n => ?_
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, dconv]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p i * q j)]

theorem dconv_assoc (p q r : ℕ → ℝ) : dconv (dconv p q) r = dconv p (dconv q r) := by
  have h : PowerSeries.mk (dconv (dconv p q) r) = PowerSeries.mk (dconv p (dconv q r)) := by
    rw [mk_dconv, mk_dconv, mk_dconv, mk_dconv, mul_assoc]
  funext n
  have hn := congrArg (PowerSeries.coeff n) h
  rwa [PowerSeries.coeff_mk, PowerSeries.coeff_mk] at hn

/-- The Cauchy product: convolution of summable nonnegative families is summable, with the
product sum. -/
theorem hasSum_dconv {a b : ℝ} (hp0 : ∀ n, 0 ≤ p n) (hq0 : ∀ n, 0 ≤ q n)
    (hp : HasSum p a) (hq : HasSum q b) : HasSum (dconv p q) (a * b) := by
  have h := hasSum_sum_range_mul_of_summable_norm (summable_norm_of_nonneg hp0 hp.summable)
    (summable_norm_of_nonneg hq0 hq.summable)
  rw [hp.tsum_eq, hq.tsum_eq] at h
  exact h

theorem IsPMF.dconv (hp : IsPMF p) (hq : IsPMF q) : IsPMF (Shields.dconv p q) where
  nonneg := dconv_nonneg hp.nonneg hq.nonneg
  hasSum := by simpa using hasSum_dconv hp.nonneg hq.nonneg hp.hasSum hq.hasSum

/-- Convolution against a fixed mass function is a contraction for total variation. -/
theorem tvDist_dconv_le (hp : IsPMF p) (hq : IsPMF q) (hr : IsPMF r) :
    tvDist (dconv p r) (dconv q r) ≤ tvDist p q := by
  have hdsum : Summable fun k => |p k - q k| := hp.summable_sub hq
  have hmaj : HasSum (dconv (fun k => |p k - q k|) r) (tvDist p q) := by
    have h := hasSum_dconv (p := fun k => |p k - q k|) (q := r) (fun _ => abs_nonneg _)
      hr.nonneg hdsum.hasSum hr.hasSum
    rw [mul_one] at h
    exact h
  have hle : ∀ n, |dconv p r n - dconv q r n| ≤ dconv (fun k => |p k - q k|) r n := by
    intro n
    have hsub : dconv p r n - dconv q r n = ∑ k ∈ Finset.range (n + 1),
        (p k - q k) * r (n - k) := by
      simp only [dconv, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsub]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun k _ => by
      rw [abs_mul, abs_of_nonneg (hr.nonneg (n - k))]
  have hsl : Summable fun n => |dconv p r n - dconv q r n| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hmaj.summable
  calc tvDist (dconv p r) (dconv q r) ≤ ∑' n, dconv (fun k => |p k - q k|) r n :=
        hsl.tsum_le_tsum hle hmaj.summable
    _ = tvDist p q := hmaj.tsum_eq

/-- The same contraction on the other side, the convolution factor now fixed on the left. -/
theorem tvDist_dconv_le' (hp : IsPMF p) (hq : IsPMF q) (hr : IsPMF r) :
    tvDist (dconv r p) (dconv r q) ≤ tvDist p q := by
  rw [dconv_comm r p, dconv_comm r q]
  exact tvDist_dconv_le hp hq hr

/-- Convolution is a contraction in both arguments at once. -/
theorem tvDist_dconv_le₂ (hp : IsPMF p) (hq : IsPMF q) (hr : IsPMF r) (hs : IsPMF s) :
    tvDist (dconv p r) (dconv q s) ≤ tvDist p q + tvDist r s := by
  refine (tvDist_triangle (q := dconv q r) ((hp.dconv hr).summable_sub (hq.dconv hr))
    ((hq.dconv hr).summable_sub (hq.dconv hs))).trans ?_
  have h₁ : tvDist (dconv p r) (dconv q r) ≤ tvDist p q := tvDist_dconv_le hp hq hr
  have h₂ : tvDist (dconv q r) (dconv q s) ≤ tvDist r s := tvDist_dconv_le' hr hs hq
  linarith

/-! ### The three mass functions -/

/-- The point mass at `0`, the unit for convolution. -/
noncomputable def diracPMF : ℕ → ℝ := fun n => if n = 0 then 1 else 0

theorem isPMF_diracPMF : IsPMF diracPMF where
  nonneg n := by unfold diracPMF; split <;> norm_num
  hasSum := hasSum_ite_eq (0 : ℕ) (1 : ℝ)

/-- The Bernoulli mass function with success probability `t`. -/
noncomputable def bernPMF (t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 - t else if n = 1 then t else 0

@[simp] theorem bernPMF_zero (t : ℝ) : bernPMF t 0 = 1 - t := by simp [bernPMF]

@[simp] theorem bernPMF_one (t : ℝ) : bernPMF t 1 = t := by simp [bernPMF]

theorem bernPMF_of_two_le {t : ℝ} {n : ℕ} (hn : 2 ≤ n) : bernPMF t n = 0 := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [bernPMF, h0, h1]

/-- Off `\{0,1\}` the Bernoulli mass vanishes.  This is `Shields.bernPMF_of_two_le` in the form
every sum over the support consumes it. -/
theorem bernPMF_of_notMem_zero_one {t : ℝ} {n : ℕ} (hn : n ∉ ({0, 1} : Finset ℕ)) :
    bernPMF t n = 0 :=
  bernPMF_of_two_le (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn; omega)

theorem isPMF_bernPMF {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : IsPMF (bernPMF t) where
  nonneg n := by
    match n with
    | 0 => simpa using h1
    | 1 => simpa using h0
    | (m + 2) => simp [bernPMF_of_two_le (show 2 ≤ m + 2 by omega)]
  hasSum := by
    simpa using hasSum_sum_of_ne_finset_zero fun n hn => bernPMF_of_notMem_zero_one (t := t) hn

/-- The Poisson mass function with mean `t`. -/
noncomputable def poisPMF (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t) * t ^ n / n !

theorem poisPMF_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poisPMF t n := by
  unfold poisPMF; positivity

theorem hasSum_poisPMF (t : ℝ) : HasSum (poisPMF t) 1 := by
  have hbase : HasSum (fun n : ℕ => t ^ n / n !) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have h := hbase.mul_left (Real.exp (-t))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have heq : poisPMF t = fun n : ℕ => Real.exp (-t) * (t ^ n / n !) := by
    funext n; rw [poisPMF, mul_div_assoc]
  rw [heq]; exact h

theorem isPMF_poisPMF {t : ℝ} (ht : 0 ≤ t) : IsPMF (poisPMF t) where
  nonneg := poisPMF_nonneg ht
  hasSum := hasSum_poisPMF t

theorem poisPMF_zero_apply (t : ℝ) : poisPMF t 0 = Real.exp (-t) := by simp [poisPMF]

theorem poisPMF_one_apply (t : ℝ) : poisPMF t 1 = t * Real.exp (-t) := by
  simp [poisPMF]; ring

theorem poisPMF_zero : poisPMF 0 = diracPMF := by
  funext n
  match n with
  | 0 => simp [poisPMF, diracPMF]
  | (m + 1) => simp [poisPMF, diracPMF]

/-- The Poisson family is a convolution semigroup. -/
theorem dconv_poisPMF (a b : ℝ) : dconv (poisPMF a) (poisPMF b) = poisPMF (a + b) := by
  funext n
  have key : ∑ k ∈ Finset.range (n + 1), a ^ k / k ! * (b ^ (n - k) / (n - k)!)
      = (a + b) ^ n / n ! := by
    rw [add_pow, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.cast_choose ℝ (Finset.mem_range_succ_iff.1 hk)]
    have h1 : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have h2 : ((n - k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (n - k).factorial_ne_zero
    have h3 : ((n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    field_simp
  calc dconv (poisPMF a) (poisPMF b) n
      = Real.exp (-(a + b)) * ∑ k ∈ Finset.range (n + 1),
          a ^ k / k ! * (b ^ (n - k) / (n - k)!) := by
        rw [dconv, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [poisPMF, poisPMF, neg_add, Real.exp_add]
        ring
    _ = poisPMF (a + b) n := by rw [key, poisPMF]; ring

/-! ### One Bernoulli against one Poisson -/

/-- The exact cost of replacing one Bernoulli factor by a Poisson one. -/
theorem tvDist_bernPMF_poisPMF {t : ℝ} (h0 : 0 ≤ t) :
    tvDist (bernPMF t) (poisPMF t) = 2 * t * (1 - Real.exp (-t)) := by
  have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hlin : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  set f : ℕ → ℝ := fun k => |bernPMF t k - poisPMF t k| with hf
  set c : ℕ → ℝ := fun k => f k - poisPMF t k with hc
  have hc0 : c 0 = t - 1 := by
    rw [hc, hf]
    simp only [bernPMF_zero, poisPMF_zero_apply]
    rw [abs_of_nonpos (by linarith)]; ring
  have hc1 : c 1 = t - 2 * (t * Real.exp (-t)) := by
    rw [hc, hf]
    simp only [bernPMF_one, poisPMF_one_apply]
    rw [abs_of_nonneg (by nlinarith)]; ring
  have hcz : ∀ n ∉ ({0, 1} : Finset ℕ), c n = 0 := by
    intro n hn
    have hfn : f n = poisPMF t n := by
      rw [hf]; simp only [bernPMF_of_notMem_zero_one hn, zero_sub, abs_neg]
      exact abs_of_nonneg (poisPMF_nonneg h0 n)
    simp [hc, hfn]
  have hcs : HasSum c (c 0 + c 1) := by simpa using hasSum_sum_of_ne_finset_zero hcz
  have hfs : HasSum f (1 + (c 0 + c 1)) := by
    have heq : ∀ n, f n = poisPMF t n + c n := fun n => by rw [hc]; ring
    simpa only [← heq] using (hasSum_poisPMF t).add hcs
  rw [show tvDist (bernPMF t) (poisPMF t) = 1 + (c 0 + c 1) from hfs.tsum_eq, hc0, hc1]; ring

theorem tvDist_bernPMF_poisPMF_le {t : ℝ} (h0 : 0 ≤ t) :
    tvDist (bernPMF t) (poisPMF t) ≤ 2 * t ^ 2 := by
  rw [tvDist_bernPMF_poisPMF h0]
  nlinarith [Real.add_one_le_exp (-t)]

variable {ι κ : Type*}

theorem abs_sub_le_tvDist (h : Summable fun k => |p k - q k|) (n : ℕ) :
    |p n - q n| ≤ tvDist p q :=
  h.le_tsum n fun _ _ => abs_nonneg _

/-- **A mode survives a total-variation limit.**  This is the step back from the replaced law to
the original one: `j` is a mode of `P` as soon as it is a mode of laws approaching `P` in total
variation. -/
theorem mode_of_tvDist_le {P : ℕ → ℝ} {j : ℕ}
    (h : ∀ ε > 0, ∃ Q : ℕ → ℝ, (Summable fun k => |P k - Q k|) ∧ tvDist P Q ≤ ε ∧
      ∀ k, Q k ≤ Q j) : ∀ k, P k ≤ P j := by
  intro k
  by_contra hc
  rw [not_le] at hc
  obtain ⟨Q, hsum, htv, hmode⟩ := h ((P k - P j) / 3) (by linarith)
  have hk := abs_le.1 (abs_sub_le_tvDist hsum k)
  have hj := abs_le.1 (abs_sub_le_tvDist hsum j)
  have hQ := hmode k
  linarith [hk.2, hj.1]

/-! ### Le Cam's inequality -/

open Polynomial

/-- The Poisson binomial's mass function on `\mathbb N`, so that it can be convolved.  This is
`Shields.pbPmf` with its `\mathbb Z` index restricted; the negative part is zero. -/
noncomputable def pbNat (s : Finset ι) (p : ι → ℝ) (n : ℕ) : ℝ := pbPmf s p (n : ℤ)

theorem pbNat_eq_coeff (s : Finset ι) (p : ι → ℝ) (n : ℕ) :
    pbNat s p n = (pbPoly s p).coeff n := by
  rw [pbNat, pbPmf_eq_coeff _ _ (Int.natCast_nonneg n)]
  simp

theorem pbNat_empty (p : ι → ℝ) : pbNat (∅ : Finset ι) p = diracPMF := by
  funext n
  rw [pbNat, pbPmf_empty, diracPMF]
  by_cases h : n = 0 <;> simp [h]

theorem dconv_bernPMF_zero (t : ℝ) (q : ℕ → ℝ) : dconv (bernPMF t) q 0 = (1 - t) * q 0 := by
  simp [dconv]

theorem dconv_bernPMF_succ (t : ℝ) (q : ℕ → ℝ) (n : ℕ) :
    dconv (bernPMF t) q (n + 1) = (1 - t) * q (n + 1) + t * q n := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 2) := by
    simp [Finset.insert_subset_iff]
  have hz : ∀ x ∈ Finset.range (n + 2), x ∉ ({0, 1} : Finset ℕ) →
      bernPMF t x * q (n + 1 - x) = 0 := fun x _ hx => by
    rw [bernPMF_of_notMem_zero_one hx, zero_mul]
  rw [dconv, ← Finset.sum_subset hsub hz]
  simp

theorem pbNat_insert [DecidableEq ι] {s : Finset ι} {i : ι} (hi : i ∉ s) (p : ι → ℝ) :
    pbNat (insert i s) p = dconv (bernPMF (p i)) (pbNat s p) := by
  funext n
  have hrec := pbPmf_rec (Finset.mem_insert_self i s) p (n : ℤ)
  rw [Finset.erase_insert hi] at hrec
  match n with
  | 0 =>
    rw [dconv_bernPMF_zero, pbNat, hrec, pbPmf_of_neg _ _ (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0)]
    simp [pbNat]
  | (m + 1) =>
    have he : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
    rw [dconv_bernPMF_succ, pbNat, hrec, he]
    rfl

theorem pbNat_nonneg {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (s : Finset ι)
    (n : ℕ) : 0 ≤ pbNat s p n := by
  classical
  exact pbPmf_nonneg hp0 hp1 s (n : ℤ)

theorem isPMF_pbNat {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (s : Finset ι) :
    IsPMF (pbNat s p) where
  nonneg := pbNat_nonneg hp0 hp1 s
  hasSum := by
    have hz : ∀ n ∉ Finset.range ((pbPoly s p).natDegree + 1), pbNat s p n = 0 := by
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [pbNat_eq_coeff]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h : HasSum (pbNat s p) (∑ n ∈ Finset.range ((pbPoly s p).natDegree + 1), pbNat s p n) :=
      hasSum_sum_of_ne_finset_zero hz
    have hval : ∑ n ∈ Finset.range ((pbPoly s p).natDegree + 1), pbNat s p n = 1 := by
      have hcast : ∀ n ∈ Finset.range ((pbPoly s p).natDegree + 1),
          pbNat s p n = (pbPoly s p).coeff n := fun n _ => pbNat_eq_coeff s p n
      rw [Finset.sum_congr rfl hcast]
      have he := Polynomial.eval_eq_sum_range (p := pbPoly s p) (1 : ℝ)
      simp only [one_pow, mul_one] at he
      rw [← he, pbPoly, Polynomial.eval_prod]
      simp
    rwa [hval] at h

/-- **Le Cam's inequality.**  A sum of independent Bernoulli variables is within total-variation
distance `\sum_ip_i^2` of the Poisson law of the same mean.  (In the unnormalized `tvDist` of this
file the constant reads `2\sum_ip_i^2`.)  No limit and no asymptotic: the bound is uniform, so a
family of Poisson binomials whose squared parameters sum to something tending to `0` converges to
the Poisson law in total variation. -/
theorem tvDist_pbNat_poisPMF_le {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (s : Finset ι) : tvDist (pbNat s p) (poisPMF (∑ i ∈ s, p i)) ≤ 2 * ∑ i ∈ s, p i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pbNat_empty, poisPMF_zero, tvDist_self]
  | @insert i s hi ih =>
    have hsum0 : 0 ≤ ∑ j ∈ s, p j := Finset.sum_nonneg fun j _ => hp0 j
    have hpois : poisPMF (∑ j ∈ insert i s, p j)
        = dconv (poisPMF (p i)) (poisPMF (∑ j ∈ s, p j)) := by
      rw [dconv_poisPMF, Finset.sum_insert hi]
    have hstep := tvDist_dconv_le₂ (isPMF_bernPMF (hp0 i) (hp1 i)) (isPMF_poisPMF (hp0 i))
      (isPMF_pbNat hp0 hp1 s) (isPMF_poisPMF hsum0)
    rw [pbNat_insert hi, hpois]
    refine hstep.trans ?_
    have h1 := tvDist_bernPMF_poisPMF_le (hp0 i)
    rw [Finset.sum_insert hi]
    linarith

/-! ### The Poisson binomial mode, unconditionally -/

/-- **The Poisson limit theorem in total variation.**  A Poisson law of mean `lam` is approximated
to within any prescribed `\varepsilon` by a Poisson binomial of the *same* mean: run `N` trials of
probability `lam/N`, whose Le Cam cost `2lam^2/N` is driven to zero by the choice of `N`.  The trial
count can be taken past any prescribed `M`, which is what lets the approximant carry a prescribed
mode; and the parameters are strictly interior, which is what makes its mass at `M` positive. -/
theorem exists_pbNat_tvDist_poisPMF_le {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ (N : ℕ) (q : Fin N → ℝ), M ≤ N ∧ (∀ i, 0 < q i) ∧ (∀ i, q i < 1) ∧
      ∑ i : Fin N, q i = lam ∧
      tvDist (poisPMF lam) (pbNat (Finset.univ : Finset (Fin N)) q) ≤ ε := by
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max (max (M : ℝ) 1) (max lam (2 * lam ^ 2 / ε)))
  have hNM : (M : ℝ) < N := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hNgt
  have hN1 : (1 : ℝ) < N := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hNgt
  have hNlam : lam < N := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hNgt
  have hNeps : 2 * lam ^ 2 / ε < N :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hNgt
  have hNpos : (0 : ℝ) < N := by linarith
  set t : ℝ := lam / N with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hNpos]; exact hNlam
  have hsum : ∑ _i : Fin N, t = lam := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht]; field_simp
  have hsq : (2 : ℝ) * ∑ _i : Fin N, t ^ 2 = 2 * lam ^ 2 / N := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht]; field_simp
  refine ⟨N, fun _ => t, by exact_mod_cast hNM.le, fun _ => ht0, fun _ => ht1, hsum, ?_⟩
  have hlecam := tvDist_pbNat_poisPMF_le (p := fun _ : Fin N => t)
    (fun _ => ht0.le) (fun _ => ht1.le) (Finset.univ : Finset (Fin N))
  rw [hsum, hsq] at hlecam
  have hfin : 2 * lam ^ 2 / N ≤ ε := by
    rw [div_le_iff₀ hNpos]; rw [div_lt_iff₀ hε] at hNeps; linarith
  rw [tvDist_comm]
  linarith


/-- Convolution of two independent Poisson binomials is the Poisson binomial of the disjoint
union of their parameter families. -/
theorem dconv_pbNat (s : Finset ι) (t : Finset κ) (p : ι → ℝ) (q : κ → ℝ) :
    dconv (pbNat s p) (pbNat t q) = pbNat (s.disjSum t) (Sum.elim p q) := by
  funext n
  have hL : dconv (pbNat s p) (pbNat t q) n
      = ∑ ij ∈ Finset.antidiagonal n, (pbPoly s p).coeff ij.1 * (pbPoly t q).coeff ij.2 := by
    rw [dconv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (pbPoly s p).coeff i * (pbPoly t q).coeff j)]
    exact Finset.sum_congr rfl fun k _ => by rw [pbNat_eq_coeff, pbNat_eq_coeff]
  rw [hL, pbNat_eq_coeff, pbPoly_disjSum, Polynomial.coeff_mul]

/-- Two disjoint blocks of Bernoulli parameters convolve. -/
theorem dconv_pbNat_union [DecidableEq ι] {s t : Finset ι} (hst : Disjoint s t) (p : ι → ℝ) :
    dconv (pbNat s p) (pbNat t p) = pbNat (s ∪ t) p := by
  funext n
  have hpoly : pbPoly (s ∪ t) p = pbPoly s p * pbPoly t p := by
    rw [pbPoly, pbPoly, pbPoly, Finset.prod_union hst]
  have hL : dconv (pbNat s p) (pbNat t p) n
      = ∑ ij ∈ Finset.antidiagonal n, (pbPoly s p).coeff ij.1 * (pbPoly t p).coeff ij.2 := by
    rw [dconv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (pbPoly s p).coeff i * (pbPoly t p).coeff j)]
    exact Finset.sum_congr rfl fun k _ => by rw [pbNat_eq_coeff, pbNat_eq_coeff]
  rw [hL, pbNat_eq_coeff, hpoly, Polynomial.coeff_mul]

/-- **Darroch's theorem for a convolution of two Poisson binomials.**  The convolution is itself a
Poisson binomial, on the disjoint union of the two parameter families, and its mean is the sum of
the two means, so the mode sits at that sum whenever it is an integer. -/
theorem mode_of_dconv_pbNat {p : ι → ℝ} {q : κ → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (s : Finset ι) (t : Finset κ) {M : ℕ}
    (hmean : ∑ i ∈ s, p i + ∑ i ∈ t, q i = M)
    (hpos : 0 < dconv (pbNat s p) (pbNat t q) M) :
    ∀ k, dconv (pbNat s p) (pbNat t q) k ≤ dconv (pbNat s p) (pbNat t q) M := by
  classical
  intro k
  have hmean' : ∑ x ∈ s.disjSum t, Sum.elim p q x = ((M : ℤ) : ℝ) := by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    push_cast
    exact hmean
  rw [dconv_pbNat] at hpos ⊢
  rw [pbNat, pbNat]
  exact pbPmf_le_of_mean_eq (Sum.rec hp0 hq0) (Sum.rec hp1 hq1) hmean'
    (by rw [← pbNat]; exact hpos) k

/-- **The truncation cost.**  Dropping a block `t` of Bernoulli factors and carrying its mean in
the Poisson parameter preserves the total mean exactly and changes the law by at most
`2\sum_{i\in t}p_i^2` — Le Cam's inequality again, now applied to the dropped block.  This is
what lets the paper's infinite Bernoulli family be truncated. -/
theorem tvDist_truncate_le [DecidableEq ι] {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {s t : Finset ι} (hst : Disjoint s t) {lam : ℝ} (hlam : 0 ≤ lam) :
    tvDist (dconv (pbNat (s ∪ t) p) (poisPMF lam))
        (dconv (pbNat s p) (poisPMF (lam + ∑ i ∈ t, p i))) ≤ 2 * ∑ i ∈ t, p i ^ 2 := by
  have htsum : 0 ≤ ∑ i ∈ t, p i := Finset.sum_nonneg fun i _ => hp0 i
  have hsplit : dconv (pbNat (s ∪ t) p) (poisPMF lam)
      = dconv (pbNat s p) (dconv (pbNat t p) (poisPMF lam)) := by
    rw [← dconv_pbNat_union hst, dconv_assoc]
  have hpois : poisPMF (lam + ∑ i ∈ t, p i)
      = dconv (poisPMF (∑ i ∈ t, p i)) (poisPMF lam) := by
    rw [dconv_poisPMF, add_comm]
  rw [hsplit, hpois]
  refine (tvDist_dconv_le' ((isPMF_pbNat hp0 hp1 t).dconv (isPMF_poisPMF hlam))
    ((isPMF_poisPMF htsum).dconv (isPMF_poisPMF hlam)) (isPMF_pbNat hp0 hp1 s)).trans ?_
  have h2 : tvDist (dconv (pbNat t p) (poisPMF lam)) (dconv (poisPMF (∑ i ∈ t, p i))
      (poisPMF lam)) ≤ tvDist (pbNat t p) (poisPMF (∑ i ∈ t, p i)) :=
    tvDist_dconv_le (isPMF_pbNat hp0 hp1 t) (isPMF_poisPMF htsum) (isPMF_poisPMF hlam)
  have h3 := tvDist_pbNat_poisPMF_le hp0 hp1 t
  linarith

theorem pbNat_zero_pos {p : ι → ℝ} {s : Finset ι} (h1 : ∀ i ∈ s, p i < 1) :
    0 < pbNat s p 0 := by
  rw [pbNat_eq_coeff, Polynomial.coeff_zero_eq_eval_zero, pbPoly, Polynomial.eval_prod]
  refine Finset.prod_pos fun i hi => ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero, add_zero]
  linarith [h1 i hi]

theorem pbNat_pos {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 < p i) → (∀ i ∈ s, p i < 1) →
      ∀ n ≤ s.card, 0 < pbNat s p n := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ n hn
    simp only [Finset.card_empty, Nat.le_zero] at hn
    subst hn
    simp [pbNat_empty, diracPMF]
  | @insert i s hi ih =>
    intro hpos hlt n hn
    rw [Finset.card_insert_of_notMem hi] at hn
    have hposS : ∀ j ∈ s, 0 < p j := fun j hj => hpos j (Finset.mem_insert_of_mem hj)
    have hltS : ∀ j ∈ s, p j < 1 := fun j hj => hlt j (Finset.mem_insert_of_mem hj)
    have hi1 : p i < 1 := hlt i (Finset.mem_insert_self i s)
    have hi0 : 0 < p i := hpos i (Finset.mem_insert_self i s)
    rw [pbNat_insert hi]
    match n with
    | 0 =>
      rw [dconv_bernPMF_zero]
      have := ih hposS hltS 0 (Nat.zero_le _)
      nlinarith
    | (m + 1) =>
      rw [dconv_bernPMF_succ]
      have hm : 0 < pbNat s p m := ih hposS hltS m (by omega)
      have hm1 : 0 ≤ pbNat s p (m + 1) := pbNat_nonneg hp0 hp1 s (m + 1)
      nlinarith

/-- **The Poisson-binomial mode of a law with a Poisson factor.**  A finite Bernoulli convolution
against a Poisson factor puts its mode at the mean whenever that mean is an integer.  This is
`eq:saddle-mass`'s mode placement: the Poisson factor is replaced by binomials of the same mean,
Darroch's theorem applies to the replacement, and Le Cam's inequality drives the replacement cost
to zero. -/
theorem mode_of_dconv_pbNat_poisPMF {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {s : Finset ι} (hlt : ∀ i ∈ s, p i < 1) {lam : ℝ} (hlam : 0 < lam) {M : ℕ}
    (hmean : ∑ i ∈ s, p i + lam = M) :
    ∀ k, dconv (pbNat s p) (poisPMF lam) k ≤ dconv (pbNat s p) (poisPMF lam) M := by
  classical
  have hsP : IsPMF (pbNat s p) := isPMF_pbNat hp0 hp1 s
  refine mode_of_tvDist_le ?_
  intro ε hε
  obtain ⟨N, q, hMN, hqpos, hqlt, hqsum, htv⟩ := exists_pbNat_tvDist_poisPMF_le hlam hε M
  have hq0 : ∀ i, 0 ≤ q i := fun i => (hqpos i).le
  have hq1 : ∀ i, q i ≤ 1 := fun i => (hqlt i).le
  set B : ℕ → ℝ := pbNat (Finset.univ : Finset (Fin N)) q with hB
  have hBP : IsPMF B := isPMF_pbNat hq0 hq1 _
  refine ⟨dconv (pbNat s p) B, ?_, ?_, ?_⟩
  · exact (hsP.dconv (isPMF_poisPMF hlam.le)).summable_sub (hsP.dconv hBP)
  · -- the replacement costs at most `ε`, by the choice of approximant
    have hcost : tvDist (dconv (pbNat s p) (poisPMF lam)) (dconv (pbNat s p) B)
        ≤ tvDist (poisPMF lam) B :=
      tvDist_dconv_le' (isPMF_poisPMF hlam.le) hBP hsP
    linarith
  · -- Darroch on the replacement
    have hpos : 0 < dconv (pbNat s p) B M :=
      dconv_pos (pbNat_nonneg hp0 hp1 s) (fun n => hBP.nonneg n) (pbNat_zero_pos hlt)
        (by rw [hB]
            exact pbNat_pos hq0 hq1 _ (fun i _ => hqpos i) (fun i _ => hqlt i) M
              (by rw [Finset.card_univ, Fintype.card_fin]; exact hMN))
    rw [hB] at hpos ⊢
    exact mode_of_dconv_pbNat hp0 hp1 hq0 hq1 s Finset.univ (by rw [hqsum]; exact hmean) hpos

/-- **The mode placement survives an infinite Bernoulli family.**  A law approximable in total
variation by Bernoulli–Poisson convolutions of the same integer mean has its mode at that mean.
With `tvDist_truncate_le` supplying the approximants, this is `\eqref{eq:saddle-mass}`'s mode
placement for the saddle law of an entire Pólya-frequency symbol, whose Bernoulli family
`\prod(1+q_\nu z)` is infinite. -/
theorem mode_of_approx_bernPoisson {P : ℕ → ℝ} {M : ℕ} (hP : IsPMF P)
    (h : ∀ ε > 0, ∃ (ι' : Type) (s : Finset ι') (p : ι' → ℝ) (lam : ℝ),
      (∀ i, 0 ≤ p i) ∧ (∀ i, p i ≤ 1) ∧ (∀ i ∈ s, p i < 1) ∧ 0 < lam ∧
      ∑ i ∈ s, p i + lam = M ∧
      tvDist P (dconv (pbNat s p) (poisPMF lam)) ≤ ε) :
    ∀ k, P k ≤ P M := by
  refine mode_of_tvDist_le ?_
  intro ε hε
  obtain ⟨ι', s, p, lam, hp0, hp1, hlt, hlam, hmean, htv⟩ := h ε hε
  exact ⟨dconv (pbNat s p) (poisPMF lam),
    hP.summable_sub ((isPMF_pbNat hp0 hp1 s).dconv (isPMF_poisPMF hlam.le)), htv,
    mode_of_dconv_pbNat_poisPMF hp0 hp1 hlt hlam hmean⟩


/-! ### Axiom footprint -/

/-- info: 'Shields.mode_of_approx_bernPoisson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mode_of_approx_bernPoisson

end Shields
