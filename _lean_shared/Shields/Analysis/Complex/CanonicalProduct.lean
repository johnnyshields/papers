/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Shields.Order.Finset.StrictSeparation

/-!
# Canonical products of genus zero

For `a : ℕ → ℂ` with every `a n ≠ 0` and `∑ ‖a n‖⁻¹ < ∞`, the canonical product

`canonicalProduct a z = ∏' n, (1 - z / a n)`

converges locally uniformly on `ℂ`, is entire, has minimal exponential type, and vanishes
exactly on the range of `a`.  This is the genus-zero case of the Hadamard factorization, and
the summability hypothesis is what makes the elementary factors `1 - z/aₙ` suffice with no
exponential convergence factors.

Mathlib carries the convergence criteria this is built from but no canonical product itself, at
the pinned revision and in flight.

## Main results

* `canonicalProduct` — the product itself.
* `differentiable_canonicalProduct` — it is entire.
* `canonicalProduct_eq_zero_iff` — `canonicalProduct a z = 0 ↔ ∃ n, a n = z`.
* `finite_setOf_mem_ball` — the zero set meets each ball finitely, so it is discrete.
* `norm_canonicalProduct_le` — order at most one, finite type.
* `tsum_log_norm_factor_add_le`, `sum_log_norm_factor_le` — the tail and the head of the sum of
  logarithms, the two halves the bound below is assembled from.
* `exists_bound_of_minimalType` — **minimal** exponential type: for every `ε > 0` there is an
  `M` with `‖F z‖ ≤ M exp(ε‖z‖)`.

## Implementation notes

The growth comparisons run through `∑ log‖·‖` rather than through a product inequality: `ℝ`
under multiplication is not an `IsOrderedMonoid`, so `Multipliable.tprod_le_tprod` does not
apply to it, while `∑ log` is an ordinary `tsum_le_tsum`.

The three Mathlib ingredients are `Summable.hasProdLocallyUniformlyOn_nat_one_add` for the
convergence, `TendstoLocallyUniformlyOn.differentiableOn` for holomorphy of the limit, and
`tprod_one_add_ne_zero_of_summable` for nonvanishing off the range.

What consumes this is a symbol presented as an infinite product: entirety and the exact zero set
are what a modulus-minimal selection needs, and the critical and circular rigidity of a
Laguerre--Pólya symbol are read off the same product.

## Tags

canonical product, Hadamard factorization, entire function, genus zero, minimal type
-/

open Filter Metric Set Topology

namespace Shields

variable {a : ℕ → ℂ}

/-- The canonical product `∏ (1 - z/aₙ)`. -/
noncomputable def canonicalProduct (a : ℕ → ℂ) (z : ℂ) : ℂ := ∏' n, (1 - z / a n)

/-! ### Convergence

The product is written in the `1 + f n z` shape Mathlib's criterion consumes, with
`f n z = -(z / a n)`.  On a ball of radius `R` the norms are dominated by `R * ‖a n‖⁻¹`, whose
summability is the standing hypothesis. -/

/-- `1 - z/aₙ` in the `1 + fₙ` form, for rewriting into and out of the Mathlib criterion. -/
theorem one_sub_div_eq (a : ℕ → ℂ) (z : ℂ) (n : ℕ) : 1 - z / a n = 1 + -(z / a n) :=
  sub_eq_add_neg 1 (z / a n)

/-- The dominating sequence on a ball of radius `R`. -/
theorem norm_neg_div_le {R : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (n : ℕ) :
    ‖-(z / a n)‖ ≤ R * ‖a n‖⁻¹ := by
  rw [mem_ball, dist_zero_right] at hz
  rw [norm_neg, norm_div, div_eq_mul_inv]
  gcongr

/-- The factors are summable in the shape the multipliability criteria consume. -/
theorem summable_norm_neg_div (hsum : Summable fun n => ‖a n‖⁻¹) (z : ℂ) :
    Summable fun n => ‖-(z / a n)‖ := by
  have hre : (fun n => ‖-(z / a n)‖) = fun n => ‖z‖ * ‖a n‖⁻¹ := by
    funext n
    rw [norm_neg, norm_div, div_eq_mul_inv]
  rw [hre]
  exact hsum.mul_left ‖z‖

/-- On every ball the product converges locally uniformly. -/
theorem hasProdLocallyUniformlyOn_canonical (hsum : Summable fun n => ‖a n‖⁻¹) (R : ℝ) :
    HasProdLocallyUniformlyOn (fun n z => 1 + -(z / a n))
      (fun z => ∏' n, (1 + -(z / a n))) (ball (0 : ℂ) R) := by
  refine Summable.hasProdLocallyUniformlyOn_nat_one_add isOpen_ball (hsum.mul_left R)
    (.of_forall fun n z hz => norm_neg_div_le hz n) fun n => ?_
  fun_prop

/-- The partial products are entire, being polynomials in `z`. -/
theorem differentiable_partial (a : ℕ → ℂ) (s : Finset ℕ) :
    Differentiable ℂ fun z : ℂ => ∏ n ∈ s, (1 + -(z / a n)) := by
  fun_prop

/-! ### Entirety -/

/-- The canonical product is differentiable on every ball about the origin. -/
theorem differentiableOn_canonicalProduct_ball (hsum : Summable fun n => ‖a n‖⁻¹) (R : ℝ) :
    DifferentiableOn ℂ (canonicalProduct a) (ball (0 : ℂ) R) := by
  have h := hasProdLocallyUniformlyOn_canonical (a := a) hsum R
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  have h' : TendstoLocallyUniformlyOn (fun s : Finset ℕ => fun z : ℂ => ∏ n ∈ s, (1 + -(z / a n)))
      (canonicalProduct a) atTop (ball (0 : ℂ) R) := by
    refine h.congr_right fun z _ => ?_
    simp only [canonicalProduct]
    exact tprod_congr fun n => (one_sub_div_eq a z n).symm
  exact h'.differentiableOn (.of_forall fun s => (differentiable_partial a s).differentiableOn)
    isOpen_ball

/-- **The canonical product is entire.** -/
theorem differentiable_canonicalProduct (hsum : Summable fun n => ‖a n‖⁻¹) :
    Differentiable ℂ (canonicalProduct a) := by
  intro z
  have hz : z ∈ ball (0 : ℂ) (‖z‖ + 1) := mem_ball_zero_iff.mpr (lt_add_one ‖z‖)
  exact ((differentiableOn_canonicalProduct_ball hsum (‖z‖ + 1)) z hz).differentiableAt
    (isOpen_ball.mem_nhds hz)

/-! ### The zero set

Off the range of `a` the product is nonzero, by `tprod_one_add_ne_zero_of_summable`; on the range
one factor vanishes and the net of partial products is eventually `0`. -/

/-- A factor vanishes exactly at its own root. -/
theorem one_add_neg_div_eq_zero_iff (ha : ∀ n, a n ≠ 0) (z : ℂ) (n : ℕ) :
    1 + -(z / a n) = 0 ↔ a n = z := by
  rw [← one_sub_div_eq, sub_eq_zero, eq_comm, div_eq_one_iff_eq (ha n)]
  exact eq_comm

/-- **Nonvanishing from the factors directly**, with no hypothesis on `a`.  A family with a zero
entry — which is what removing a root produces — carries the factor `1` there, so it satisfies
this hypothesis while falling outside the reach of `canonicalProduct_ne_zero` below. -/
theorem canonicalProduct_ne_zero' (hsum : Summable fun n => ‖a n‖⁻¹) {z : ℂ}
    (hfac : ∀ n, (1 : ℂ) - z / a n ≠ 0) : canonicalProduct a z ≠ 0 := by
  have hfac' : ∀ n, 1 + -(z / a n) ≠ 0 := fun n => by
    rw [← one_sub_div_eq]
    exact hfac n
  have h := tprod_one_add_ne_zero_of_summable (f := fun n => -(z / a n)) hfac'
    (summable_norm_neg_div hsum z)
  simpa only [canonicalProduct, ← one_sub_div_eq] using h

/-- Off the range of `a` the canonical product does not vanish. -/
theorem canonicalProduct_ne_zero (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹) {z : ℂ}
    (hz : ∀ n, a n ≠ z) : canonicalProduct a z ≠ 0 :=
  canonicalProduct_ne_zero' hsum fun n => by
    rw [one_sub_div_eq]
    exact (one_add_neg_div_eq_zero_iff ha z n).not.mpr (hz n)

/-- On the range of `a` the canonical product vanishes.  The nonvanishing of `a n` is genuinely
needed: at `a n = 0` the factor reads `1 - z/0 = 1`, and the conclusion is false. -/
theorem canonicalProduct_eq_zero (a : ℕ → ℂ) {z : ℂ} {n : ℕ} (han : a n ≠ 0) (hn : a n = z) :
    canonicalProduct a z = 0 :=
  tprod_of_exists_eq_zero ⟨n, by rw [← hn, div_self han, sub_self]⟩

/-- **The zero set of the canonical product is exactly the range of `a`.** -/
theorem canonicalProduct_eq_zero_iff (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹)
    (z : ℂ) : canonicalProduct a z = 0 ↔ ∃ n, a n = z := by
  constructor
  · intro h
    by_contra hcon
    exact canonicalProduct_ne_zero ha hsum (fun n hn => hcon ⟨n, hn⟩) h
  · rintro ⟨n, hn⟩
    exact canonicalProduct_eq_zero a (ha n) hn

/-! ### Growth

The crude bound first: `‖F(z)‖ ≤ exp(‖z‖ ∑ ‖aₙ‖⁻¹)`, giving order at most `1` and finite type.
At a point of the zero set the logarithms are undefined and the bound is trivial, so that case
is split off first. -/

/-- The product converges at each point. -/
theorem multipliable_canonical (hsum : Summable fun n => ‖a n‖⁻¹) (z : ℂ) :
    Multipliable fun n => 1 - z / a n := by
  have h := Complex.multipliable_one_add_of_summable
    (Summable.of_norm (summable_norm_neg_div hsum z))
  exact h.congr fun n => (one_sub_div_eq a z n).symm

/-- **The factor's logarithm against the triangle-inequality bound.**  `‖1 - z/aₙ‖ ≤ 1 + ‖z‖‖aₙ‖⁻¹`
carried through `Real.log`.  The bound on the right is at least `1`, which is what makes the
inequality survive the zero factor, where the left side is `Real.log 0 = 0`; Mathlib's
monotonicity of `Real.log` needs the left side positive and so does not apply there. -/
theorem log_norm_factor_le_log_one_add (z : ℂ) (n : ℕ) :
    Real.log ‖1 - z / a n‖ ≤ Real.log (1 + ‖z‖ * ‖a n‖⁻¹) := by
  have hb : ‖1 - z / a n‖ ≤ 1 + ‖z‖ * ‖a n‖⁻¹ := by
    calc ‖1 - z / a n‖ ≤ ‖(1 : ℂ)‖ + ‖z / a n‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ * ‖a n‖⁻¹ := by rw [norm_one, norm_div, div_eq_mul_inv]
  rcases eq_or_lt_of_le (norm_nonneg (1 - z / a n)) with h0 | h0
  · rw [← h0, Real.log_zero]
    exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  · exact Real.log_le_log h0 hb

/-- `log‖1 - z/aₙ‖ ≤ ‖z‖‖aₙ‖⁻¹`, the pointwise form of the comparison. -/
theorem log_norm_factor_le (z : ℂ) (n : ℕ) :
    Real.log ‖1 - z / a n‖ ≤ ‖z‖ * ‖a n‖⁻¹ := by
  have hpos : (0 : ℝ) < 1 + ‖z‖ * ‖a n‖⁻¹ := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  linarith [log_norm_factor_le_log_one_add (a := a) z n]

/-- The factors' logarithms are summable off the zero set. -/
theorem summable_log_norm_factor (hsum : Summable fun n => ‖a n‖⁻¹) (z : ℂ) :
    Summable fun n => Real.log ‖1 - z / a n‖ := by
  have h := Summable.summable_log_norm_one_add (f := fun n => -(z / a n))
    (summable_norm_neg_div hsum z)
  exact h.congr fun n => by rw [← one_sub_div_eq]

/-- A factor never vanishes off the root, **trivial slots included**: at `a n = 0` it reads
`1 - z/0 = 1`, so `a n ≠ z` alone is enough and no nonvanishing of `a` is needed. -/
theorem one_sub_div_ne_zero_of_ne {z : ℂ} (hz : ∀ n, a n ≠ z) (n : ℕ) :
    (1 : ℂ) - z / a n ≠ 0 := by
  by_cases h : a n = 0
  · simp [h]
  · intro hcon
    have hone : z / a n = 1 := by linear_combination -hcon
    exact hz n ((div_eq_one_iff_eq h).mp hone).symm

/-- **The modulus as an exponentiated sum, with trivial slots allowed.**  A slot `a n = 0`
contributes the factor `1`, so only `a n ≠ z` is required.  This is the form a family whose
parameters may degenerate to `0` consumes. -/
theorem norm_canonicalProduct_eq_exp_tsum_of_ne (hsum : Summable fun n => ‖a n‖⁻¹) {z : ℂ}
    (hz : ∀ n, a n ≠ z) :
    ‖canonicalProduct a z‖ = Real.exp (∑' n, Real.log ‖1 - z / a n‖) := by
  rw [canonicalProduct, (multipliable_canonical hsum z).norm_tprod,
    ← Real.rexp_tsum_eq_tprod (fun n => norm_pos_iff.mpr (one_sub_div_ne_zero_of_ne hz n))
      (summable_log_norm_factor hsum z)]

/-- **The modulus as an exponentiated sum.**  Off the zero set,
`‖F(z)‖ = exp(∑ log‖1 - z/aₙ‖)`.  This is the form every growth comparison here runs through,
`ℝ` under multiplication not being an `IsOrderedMonoid`. -/
theorem norm_canonicalProduct_eq_exp_tsum (_ha : ∀ n, a n ≠ 0)
    (hsum : Summable fun n => ‖a n‖⁻¹) {z : ℂ} (hz : ∀ n, a n ≠ z) :
    ‖canonicalProduct a z‖ = Real.exp (∑' n, Real.log ‖1 - z / a n‖) :=
  norm_canonicalProduct_eq_exp_tsum_of_ne hsum hz

/-- **Order at most one, finite type.**  `‖F(z)‖ ≤ exp(‖z‖ ∑ ‖aₙ‖⁻¹)`. -/
theorem norm_canonicalProduct_le (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹) (z : ℂ) :
    ‖canonicalProduct a z‖ ≤ Real.exp (‖z‖ * ∑' n, ‖a n‖⁻¹) := by
  by_cases hz : ∃ n, a n = z
  · obtain ⟨n, hn⟩ := hz
    rw [canonicalProduct_eq_zero a (ha n) hn, norm_zero]
    positivity
  · have hz' : ∀ n, a n ≠ z := fun n hn => hz ⟨n, hn⟩
    have hfac : ∀ n, (1 : ℂ) - z / a n ≠ 0 := one_sub_div_ne_zero_of_ne hz'
    have hlogsum : Summable fun n => Real.log ‖1 - z / a n‖ := summable_log_norm_factor hsum z
    rw [canonicalProduct, (multipliable_canonical hsum z).norm_tprod,
      ← Real.rexp_tsum_eq_tprod (fun n => norm_pos_iff.mpr (hfac n)) hlogsum]
    rw [Real.exp_le_exp, ← tsum_mul_left]
    exact hlogsum.tsum_le_tsum (fun n => log_norm_factor_le z n) (hsum.mul_left ‖z‖)

/-! ### Peeling one factor, and simplicity of the zeros

Setting `a m := 0` turns the `m`-th factor into `1`, because `z / 0 = 0` in Lean; so the family
with one root removed is again a canonical product, over `Function.update a m 0`.  That is what
makes the zeros simple: `F = (1 - z/aₘ) · G` with `G` a canonical product not vanishing at
`aₘ`, so `F'(aₘ) = -aₘ⁻¹ G(aₘ) ≠ 0`. -/

/-- Removing one root leaves a canonical product: the `m`-th factor of the updated family is
`1 - z/0 = 1`. -/
theorem summable_inv_norm_update (hsum : Summable fun n => ‖a n‖⁻¹) (m : ℕ) :
    Summable fun n => ‖Function.update a m 0 n‖⁻¹ := by
  refine (hsum.update m 0).congr fun n => ?_
  rcases eq_or_ne n m with rfl | hn
  · simp
  · simp [Function.update_of_ne hn]

/-- **Peeling one factor.**  `F(z) = (1 - z/aₘ) · G(z)` with `G` the canonical product over the
family with `aₘ` removed. -/
theorem canonicalProduct_peel (hsum : Summable fun n => ‖a n‖⁻¹) (m : ℕ) (z : ℂ) :
    canonicalProduct a z = (1 - z / a m) * canonicalProduct (Function.update a m 0) z := by
  have hupd : Multipliable (Function.update (fun n => 1 - z / a n) m 1) := by
    refine (multipliable_canonical (summable_inv_norm_update hsum m) z).congr fun n => ?_
    rcases eq_or_ne n m with rfl | hn
    · simp
    · simp [Function.update_of_ne hn]
  have hpeel := Multipliable.tprod_eq_mul_tprod_ite' (f := fun n => 1 - z / a n) m hupd
  rw [canonicalProduct, hpeel, canonicalProduct]
  congr 1
  refine tprod_congr fun n => ?_
  rcases eq_or_ne n m with rfl | hn
  · simp
  · simp [hn]

/-- The peeled product does not vanish at the removed root. -/
theorem canonicalProduct_update_ne_zero (ha : ∀ n, a n ≠ 0) (hinj : Function.Injective a)
    (hsum : Summable fun n => ‖a n‖⁻¹) (m : ℕ) :
    canonicalProduct (Function.update a m 0) (a m) ≠ 0 := by
  refine canonicalProduct_ne_zero' (summable_inv_norm_update hsum m) fun n => ?_
  rcases eq_or_ne n m with rfl | hn
  · simp
  · rw [Function.update_of_ne hn]
    intro hcon
    rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq (ha n)] at hcon
    exact hn (hinj hcon.symm)

/-! ### Multiplicity -/

/-- Zeroing out a set of indices keeps the reciprocal norms summable: each term is either
unchanged or `‖0‖⁻¹ = 0`. -/
theorem summable_inv_norm_zeroed (hsum : Summable fun n => ‖a n‖⁻¹) (S : Finset ℕ) :
    Summable fun n => ‖if n ∈ S then 0 else a n‖⁻¹ := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  by_cases hn : n ∈ S
  · rw [if_pos hn, norm_zero, inv_zero]
    positivity
  · rw [if_neg hn]

/-- **Peeling a whole packet.**  If every index of a finite set `S` carries the same value `z₀`,
the canonical product factors as `(1 - z/z₀)^{#S}` times the product over the family with those
indices zeroed out.  Only one direction of the characterization of `S` is used, so `S` need not be
*all* the indices carrying `z₀`. -/
theorem canonicalProduct_eq_pow_mul (hsum : Summable fun n => ‖a n‖⁻¹) {z₀ : ℂ}
    (S : Finset ℕ) (hS : ∀ n ∈ S, a n = z₀) (z : ℂ) :
    canonicalProduct a z
      = (1 - z / z₀) ^ S.card * canonicalProduct (fun n => if n ∈ S then 0 else a n) z := by
  induction S using Finset.induction generalizing a with
  | empty => simp [canonicalProduct]
  | @insert m T hm ih =>
    have hmz : a m = z₀ := hS m (Finset.mem_insert_self m T)
    have hTa : ∀ n ∈ T, Function.update a m 0 n = z₀ := fun n hn => by
      have hnm : n ≠ m := by rintro rfl; exact hm hn
      rw [Function.update_of_ne hnm]
      exact hS n (Finset.mem_insert_of_mem hn)
    have hfam : (fun n => if n ∈ T then 0 else Function.update a m 0 n)
        = fun n => if n ∈ insert m T then 0 else a n := by
      funext n
      by_cases hnT : n ∈ T
      · rw [if_pos hnT, if_pos (Finset.mem_insert_of_mem hnT)]
      · rcases eq_or_ne n m with rfl | hnm
        · rw [if_neg hnT, Function.update_self, if_pos (Finset.mem_insert_self _ _)]
        · rw [if_neg hnT, Function.update_of_ne hnm, if_neg ?_]
          intro h
          rcases Finset.mem_insert.mp h with h | h
          · exact hnm h
          · exact hnT h
    rw [canonicalProduct_peel hsum m z, hmz,
      ih (summable_inv_norm_update hsum m) hTa, hfam, Finset.card_insert_of_notMem hm]
    ring

/-- The peeled packet product does not vanish at `z₀`, provided `S` collects **every** index
carrying `z₀`. -/
theorem canonicalProduct_zeroed_ne_zero (ha : ∀ n, a n ≠ 0)
    (hsum : Summable fun n => ‖a n‖⁻¹) {z₀ : ℂ} (S : Finset ℕ) (hS : ∀ n, a n = z₀ → n ∈ S) :
    canonicalProduct (fun n => if n ∈ S then 0 else a n) z₀ ≠ 0 := by
  refine canonicalProduct_ne_zero' (summable_inv_norm_zeroed hsum S) fun n => ?_
  by_cases hn : n ∈ S
  · rw [if_pos hn]
    simp
  · rw [if_neg hn]
    intro hcon
    rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq (ha n)] at hcon
    exact hn (hS n hcon.symm)

/-- **The order of vanishing is the multiplicity.**  At a nonzero value `z₀`, the canonical product
vanishes to order exactly the number of indices carrying it — `0` when none does, so this also says
where the product is nonzero.  `deriv_canonicalProduct_ne_zero` is the injective case, where a
value that is carried is carried once. -/
theorem analyticOrderAt_canonicalProduct (ha : ∀ n, a n ≠ 0)
    (hsum : Summable fun n => ‖a n‖⁻¹) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (S : Finset ℕ)
    (hS : ∀ n, n ∈ S ↔ a n = z₀) :
    analyticOrderAt (canonicalProduct a) z₀ = (S.card : ℕ∞) := by
  set G := canonicalProduct (fun n => if n ∈ S then 0 else a n) with hG
  have hGd : Differentiable ℂ G := differentiable_canonicalProduct (summable_inv_norm_zeroed hsum S)
  have hGne : G z₀ ≠ 0 :=
    canonicalProduct_zeroed_ne_zero ha hsum S fun n h => (hS n).mpr h
  refine (((differentiable_canonicalProduct hsum).analyticAt
    z₀).analyticOrderAt_eq_natCast).mpr ⟨fun z => (-z₀)⁻¹ ^ S.card * G z, ?_, ?_, ?_⟩
  · exact analyticAt_const.mul (hGd.analyticAt z₀)
  · exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (neg_ne_zero.mpr hz₀))) hGne
  · filter_upwards with z
    rw [canonicalProduct_eq_pow_mul hsum S (fun n hn => (hS n).mp hn) z, smul_eq_mul]
    have hfac : 1 - z / z₀ = (-z₀)⁻¹ * (z - z₀) := by
      field
    rw [hfac, mul_pow]
    ring

/-- **The zeros of the canonical product are simple.**  This is the "simple positive zeros"
clause of a Laguerre--Pólya product, and it needs the roots to be *distinct*: without
injectivity a repeated `aₙ` gives a double zero. -/
theorem deriv_canonicalProduct_ne_zero (ha : ∀ n, a n ≠ 0) (hinj : Function.Injective a)
    (hsum : Summable fun n => ‖a n‖⁻¹) (m : ℕ) :
    deriv (canonicalProduct a) (a m) ≠ 0 := by
  set G := canonicalProduct (Function.update a m 0) with hG
  have hGd : Differentiable ℂ G :=
    differentiable_canonicalProduct (summable_inv_norm_update hsum m)
  have h1 : HasDerivAt (fun z : ℂ => 1 - z / a m) (-(a m)⁻¹) (a m) := by
    simpa using ((hasDerivAt_id (a m)).div_const (a m)).const_sub 1
  have hfd := h1.mul ((hGd (a m)).hasDerivAt)
  rw [div_self (ha m), sub_self, zero_mul, add_zero] at hfd
  have heq : canonicalProduct a = (fun z : ℂ => 1 - z / a m) * G :=
    funext fun z => canonicalProduct_peel hsum m z
  rw [heq, hfd.deriv]
  exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (ha m)))
    (canonicalProduct_update_ne_zero ha hinj hsum m)

/-! ### Minimal type

Minimal exponential type is `∀ ε > 0, ∃ M > 0, ∀ z, ‖F z‖ ≤ M exp(ε‖z‖)`, which is strictly
stronger than the finite type above.

The split is of the *sum* of logarithms, not of the product: `∑' log` breaks at `N` by
`Summable.sum_add_tsum_nat_add`, the tail is below `ε/2` by summability, and the head — finitely
many terms — is bounded by `N log(1 + B‖z‖)`, which is logarithmic in `‖z‖` and so absorbed into
`(ε/2)‖z‖` plus a constant.  Absorbing it is one application of `log x ≤ x - 1` at the scaled
argument `λ(1 + B‖z‖)`, with `λ` small enough that `NλB ≤ ε/2`. -/

/-- `log(1 + u) ≤ λ(1 + u) - 1 - log λ` for `λ > 0`: the scaled `log x ≤ x - 1`, which is what
turns a logarithm of `‖z‖` into an arbitrarily small multiple of `‖z‖` plus a constant. -/
theorem log_one_add_le_scaled {u lam : ℝ} (hu : 0 ≤ u) (hlam : 0 < lam) :
    Real.log (1 + u) ≤ lam * (1 + u) - 1 - Real.log lam := by
  have hpos : (0 : ℝ) < lam * (1 + u) := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_mul (ne_of_gt hlam) (by positivity)] at h
  linarith

/-- **The tail of the sum of logarithms.**  Past an index where the tail of `∑‖aₙ‖⁻¹` is below
`c`, the tail of `∑ log‖1 - z/aₙ‖` is below `c‖z‖` — the factorwise bound `log‖1 - z/aₙ‖ ≤
‖z‖‖aₙ‖⁻¹` summed. -/
theorem tsum_log_norm_factor_add_le (hsum : Summable fun n => ‖a n‖⁻¹) (z : ℂ) (N : ℕ) {c : ℝ}
    (hN : ∑' n, ‖a (n + N)‖⁻¹ ≤ c) :
    ∑' n, Real.log ‖1 - z / a (n + N)‖ ≤ c * ‖z‖ := by
  have hsum' : Summable fun n => ‖z‖ * ‖a (n + N)‖⁻¹ :=
    ((summable_nat_add_iff N).mpr hsum).mul_left ‖z‖
  calc ∑' n, Real.log ‖1 - z / a (n + N)‖
      ≤ ∑' n, ‖z‖ * ‖a (n + N)‖⁻¹ :=
        ((summable_nat_add_iff N).mpr (summable_log_norm_factor hsum z)).tsum_le_tsum
          (fun n => log_norm_factor_le z (n + N)) hsum'
    _ = ‖z‖ * ∑' n, ‖a (n + N)‖⁻¹ := tsum_mul_left
    _ ≤ ‖z‖ * c := mul_le_mul_of_nonneg_left hN (norm_nonneg z)
    _ = c * ‖z‖ := mul_comm _ _

/-- **The head of the sum of logarithms.**  Over finitely many indices whose `‖aₙ‖⁻¹` are bounded
by `B`, each factor contributes at most the scaled `log x ≤ x - 1` at argument `λ(1 + B‖z‖)`, so
the head is at most `N` times that.  The bound is logarithmic in `‖z‖` before the scaling and
linear with an arbitrarily small slope after it, which is what `λ` is for. -/
theorem sum_log_norm_factor_le (z : ℂ) {N : ℕ} {B lam : ℝ}
    (hB : ∀ n ∈ Finset.range N, ‖a n‖⁻¹ ≤ B) (hB0 : 0 ≤ B) (hlam : 0 < lam) :
    ∑ n ∈ Finset.range N, Real.log ‖1 - z / a n‖
      ≤ (N : ℝ) * (lam * (1 + B * ‖z‖) - 1 - Real.log lam) := by
  have hterm : ∀ n ∈ Finset.range N,
      Real.log ‖1 - z / a n‖ ≤ lam * (1 + B * ‖z‖) - 1 - Real.log lam := by
    intro n hn
    have h1 : Real.log ‖1 - z / a n‖ ≤ Real.log (1 + B * ‖z‖) :=
      (log_norm_factor_le_log_one_add z n).trans
        (Real.log_le_log (by positivity) (by nlinarith [norm_nonneg z, hB n hn]))
    exact h1.trans (log_one_add_le_scaled (by positivity) hlam)
  calc ∑ n ∈ Finset.range N, Real.log ‖1 - z / a n‖
      ≤ ∑ _n ∈ Finset.range N, (lam * (1 + B * ‖z‖) - 1 - Real.log lam) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) * (lam * (1 + B * ‖z‖) - 1 - Real.log lam) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The canonical product has minimal exponential type.** -/
theorem exists_bound_of_minimalType (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ z, ‖canonicalProduct a z‖ ≤ M * Real.exp (ε * ‖z‖) := by
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- an index past which the tail of `∑ ‖aₙ‖⁻¹` is below `ε/2`
  obtain ⟨N, hN⟩ :=
    ((tendsto_sum_nat_add fun n => ‖a n‖⁻¹).eventually (gt_mem_nhds hε2)).exists
  set B : ℝ := ∑ n ∈ Finset.range N, ‖a n‖⁻¹ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun n _ => by positivity
  set lam : ℝ := ε / (2 * ((N : ℝ) + 1) * (B + 1)) with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  set C : ℝ := (N : ℝ) * (lam * 1 - 1 - Real.log lam) with hC
  refine ⟨Real.exp C, Real.exp_pos _, fun z => ?_⟩
  by_cases hz : ∃ n, a n = z
  · obtain ⟨n, hn⟩ := hz
    rw [canonicalProduct_eq_zero a (ha n) hn, norm_zero]
    positivity
  · have hz' : ∀ n, a n ≠ z := fun n hn => hz ⟨n, hn⟩
    have hfac : ∀ n, (1 : ℂ) - z / a n ≠ 0 := one_sub_div_ne_zero_of_ne hz'
    have hlogsum : Summable fun n => Real.log ‖1 - z / a n‖ := summable_log_norm_factor hsum z
    -- the tail
    have htail : ∑' n, Real.log ‖1 - z / a (n + N)‖ ≤ ε / 2 * ‖z‖ :=
      tsum_log_norm_factor_add_le hsum z N (by simpa using hN.le)
    -- the head, with the `N λ B ≤ ε/2` absorption that fixes `λ`
    have hhead : ∑ n ∈ Finset.range N, Real.log ‖1 - z / a n‖ ≤ ε / 2 * ‖z‖ + C := by
      refine (sum_log_norm_factor_le z (fun n hn => Finset.single_le_sum
        (f := fun m => ‖a m‖⁻¹) (fun m _ => by positivity) hn) hB0 hlam).trans ?_
      rw [hC]
      have hkey : (N : ℝ) * (lam * (B * ‖z‖)) ≤ ε / 2 * ‖z‖ := by
        have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
        have hlamid : lam * (((N : ℝ) + 1) * (B + 1)) = ε / 2 := by
          rw [hlamdef]
          field_simp
        have hfrac : (N : ℝ) * (lam * B) ≤ ε / 2 := by
          rw [← hlamid]
          nlinarith [Nat.cast_nonneg (α := ℝ) N, hB0, hlam.le]
        nlinarith
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    -- combine
    have hsplit : (∑ n ∈ Finset.range N, Real.log ‖1 - z / a n‖)
        + ∑' n, Real.log ‖1 - z / a (n + N)‖ = ∑' n, Real.log ‖1 - z / a n‖ :=
      hlogsum.sum_add_tsum_nat_add N
    have hlog : ∑' n, Real.log ‖1 - z / a n‖ ≤ ε * ‖z‖ + C := by
      rw [← hsplit]
      linarith
    rw [canonicalProduct, (multipliable_canonical hsum z).norm_tprod,
      ← Real.rexp_tsum_eq_tprod (fun n => norm_pos_iff.mpr (hfac n)) hlogsum,
      ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

/-! ### Discreteness

The zero set has finitely many points in each ball, so it is discrete; this is what makes
"the `k` smallest moduli" of the zero set exist.  Summability of `‖a n‖⁻¹` forces `‖a n‖ → ∞`,
so
only finitely many `a n` lie in any ball. -/

/-- Summable reciprocals force the moduli to diverge.  Injectivity of `a` is not needed. -/
theorem tendsto_norm_atTop_of_summable_inv_norm (ha : ∀ n, a n ≠ 0)
    (hsum : Summable fun n => ‖a n‖⁻¹) :
    Tendsto (fun n => ‖a n‖) atTop atTop := by
  have hpos : ∀ n, (0 : ℝ) < ‖a n‖⁻¹ := fun n => inv_pos.mpr (norm_pos_iff.mpr (ha n))
  have h0 : Tendsto (fun n => ‖a n‖⁻¹) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsum.tendsto_atTop_zero
      (.of_forall hpos)
  have h1 := h0.inv_tendsto_nhdsGT_zero
  simpa [Pi.inv_def, inv_inv] using h1

/-- **The zero set meets each ball in a finite set**, which is what makes "the `k` smallest
moduli" exist. -/
theorem finite_setOf_mem_ball (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹) (R : ℝ) :
    {n | a n ∈ ball (0 : ℂ) R}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_norm_atTop_of_summable_inv_norm ha hsum).eventually_ge_atTop R)
  refine Set.Finite.subset (Set.finite_Iio N) fun n hn => ?_
  simp only [Set.mem_ofPred_eq, mem_ball, dist_zero_right] at hn
  simp only [Set.mem_Iio]
  by_contra hcon
  exact absurd (hN n (not_lt.mp hcon)) (not_le.mpr hn)

/-! ### Selecting the smallest moduli

The zeros accumulate only at infinity, so the family has an *initial segment by modulus* of any
size: a finite set of indices every one of whose moduli is strictly below every modulus outside it.
This is what lets "the `k` zeros of smallest modulus" be spoken of on an infinite family, where no
finite sort is available.
-/

/-- **An initial segment by modulus of any prescribed size.**  For any `k` there is a finite set of
at least `k` indices whose moduli are all strictly smaller than every modulus outside it.

The set is a sublevel set `{n | ‖aₙ‖ < r}`, which is finite because the moduli tend to infinity and
contains `{0, …, k-1}` once `r` clears their maximum.  Being a sublevel set is exactly what makes
the separation strict, and it is why no ordering of the index type is needed. -/
theorem exists_finset_lt_of_notMem (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹)
    (k : ℕ) :
    ∃ S : Finset ℕ, k ≤ S.card ∧ ∀ i ∈ S, ∀ j ∉ S, ‖a i‖ < ‖a j‖ := by
  -- a radius clearing the first `k` moduli
  set r : ℝ := 1 + ∑ i ∈ Finset.range k, ‖a i‖ with hr
  have hmem : ∀ i ∈ Finset.range k, ‖a i‖ < r := by
    intro i hi
    have hle : ‖a i‖ ≤ ∑ j ∈ Finset.range k, ‖a j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (a j)) hi
    rw [hr]; linarith
  set T : Set ℕ := {n | a n ∈ ball (0 : ℂ) r} with hT
  have hTfin : T.Finite := finite_setOf_mem_ball ha hsum r
  have hTmem : ∀ n, n ∈ hTfin.toFinset ↔ ‖a n‖ < r := by
    intro n
    rw [Set.Finite.mem_toFinset, hT]
    simp [mem_ball, dist_zero_right]
  refine ⟨hTfin.toFinset, ?_, ?_⟩
  · refine le_trans (le_of_eq (Finset.card_range k).symm) (Finset.card_le_card fun i hi => ?_)
    exact (hTmem i).mpr (hmem i hi)
  · intro i hi j hj
    have hlt : ‖a i‖ < r := (hTmem i).mp hi
    have hge : r ≤ ‖a j‖ := not_lt.mp fun h => hj ((hTmem j).mpr h)
    exact lt_of_lt_of_le hlt hge

/-- **The modulus-minimal packet, as a definite object.**  Combining the two previous results: the
selected initial segment is the unique set of its cardinality separating strictly by modulus, so
"the zeros of smallest modulus" names one set and not a choice. -/
theorem eq_of_forall_norm_lt_of_card_eq {S T : Finset ℕ} (hcard : S.card = T.card)
    (hS : ∀ i ∈ S, ∀ j ∉ S, ‖a i‖ < ‖a j‖) (hT : ∀ i ∈ T, ∀ j ∉ T, ‖a i‖ < ‖a j‖) :
    S = T :=
  eq_of_forall_lt_of_card_eq (f := fun n => ‖a n‖) hcard hS hT

/-- The same selection stated on the *zeros of the product* rather than on the family: the entire
function `canonicalProduct a` has at least `k` zeros, counted with multiplicity, whose moduli are
strictly below every other zero's.  Multiplicity is `analyticOrderAt_canonicalProduct`. -/
theorem exists_finset_zero_lt_of_notMem (ha : ∀ n, a n ≠ 0)
    (hsum : Summable fun n => ‖a n‖⁻¹) (k : ℕ) :
    ∃ S : Finset ℕ, k ≤ S.card ∧ (∀ i ∈ S, canonicalProduct a (a i) = 0) ∧
      ∀ i ∈ S, ∀ j ∉ S, ‖a i‖ < ‖a j‖ := by
  obtain ⟨S, hcard, hsep⟩ := exists_finset_lt_of_notMem ha hsum k
  exact ⟨S, hcard, fun i _ => canonicalProduct_eq_zero a (ha i) rfl, hsep⟩

/-! ### The logarithmic derivative

Off the zero set the product has the classical logarithmic derivative

`F'(z)/F(z) = -∑ (aₙ - z)⁻¹`.

The interchange of derivative and infinite product is Mathlib's `logDeriv_tprod_eq_tsum`, which
consumes exactly the local uniform convergence established above. -/

/-- A single factor's logarithmic derivative. -/
theorem logDeriv_factor {n : ℕ} {z : ℂ} (han : a n ≠ 0) (hz : a n ≠ z) :
    logDeriv (fun w => 1 - w / a n) z = -(a n - z)⁻¹ := by
  have hd : HasDerivAt (fun w : ℂ => 1 - w / a n) (-(a n)⁻¹) z := by
    simpa using ((hasDerivAt_id z).div_const (a n)).const_sub 1
  have hsub : a n - z ≠ 0 := sub_ne_zero.mpr hz
  rw [logDeriv_apply, hd.deriv, show (1 : ℂ) - z / a n = (a n - z) / a n by field_simp]
  field_simp

/-- The logarithmic derivative's terms are summable: `‖aₙ‖ → ∞`, so eventually
`‖aₙ - z‖ ≥ ‖aₙ‖/2` and the terms are dominated by `2‖aₙ‖⁻¹`. -/
theorem summable_inv_sub (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹) (z : ℂ) :
    Summable fun n => (a n - z)⁻¹ := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n => 2 * ‖a n‖⁻¹) (hsum.mul_left 2) ?_
  filter_upwards [(tendsto_norm_atTop_of_summable_inv_norm ha hsum).eventually_ge_atTop (2 * ‖z‖)]
    with n hn
  have hpos : (0 : ℝ) < ‖a n‖ := norm_pos_iff.mpr (ha n)
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hhalf : ‖a n‖ / 2 ≤ ‖a n - z‖ := by
    have := norm_sub_norm_le (a n) z
    linarith
  have hhalfpos : (0 : ℝ) < ‖a n‖ / 2 := by linarith
  rw [norm_inv]
  calc ‖a n - z‖⁻¹ ≤ (‖a n‖ / 2)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hhalfpos hhalf
    _ = 2 * ‖a n‖⁻¹ := by
        rw [inv_div]
        field_simp

/-- The factors converge locally uniformly in the `1 - w/aₙ` shape, which is the form
`logDeriv_tprod_eq_tsum` consumes. -/
theorem multipliableLocallyUniformlyOn_canonical (hsum : Summable fun n => ‖a n‖⁻¹) (R : ℝ) :
    MultipliableLocallyUniformlyOn (fun n (w : ℂ) => 1 - w / a n) (ball (0 : ℂ) R) := by
  refine ⟨fun w => ∏' n, (1 - w / a n), ?_⟩
  have h := hasProdLocallyUniformlyOn_canonical (a := a) hsum R
  have heq : (fun n (w : ℂ) => 1 + -(w / a n)) = fun n (w : ℂ) => 1 - w / a n := by
    funext n w; ring
  have heq2 : (fun w : ℂ => ∏' n, (1 + -(w / a n))) = fun w : ℂ => ∏' n, (1 - w / a n) := by
    funext w
    exact tprod_congr fun n => by ring
  rwa [heq, heq2] at h

/-- **The logarithmic derivative of the canonical product.**  Off the zero set,

`F'(z)/F(z) = -∑ (aₙ - z)⁻¹`. -/
theorem logDeriv_canonicalProduct (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹)
    {z : ℂ} (hz : ∀ n, a n ≠ z) :
    logDeriv (canonicalProduct a) z = -∑' n, (a n - z)⁻¹ := by
  have hzmem : z ∈ ball (0 : ℂ) (‖z‖ + 1) := mem_ball_zero_iff.mpr (lt_add_one ‖z‖)
  have hfac : ∀ n, (1 : ℂ) - z / a n ≠ 0 := one_sub_div_ne_zero_of_ne hz
  have hsummable : Summable fun n => logDeriv (fun w => 1 - w / a n) z := by
    refine (summable_inv_sub ha hsum z).neg.congr fun n => ?_
    rw [logDeriv_factor (ha n) (hz n)]
  have hkey := logDeriv_tprod_eq_tsum (s := ball (0 : ℂ) (‖z‖ + 1)) isOpen_ball hzmem
    (f := fun n (w : ℂ) => 1 - w / a n) hfac (fun n => by fun_prop) hsummable
    (multipliableLocallyUniformlyOn_canonical hsum _) (canonicalProduct_ne_zero ha hsum hz)
  rw [show (canonicalProduct a) = (fun w : ℂ => ∏' n, (1 - w / a n)) from rfl, hkey,
    ← tsum_neg]
  exact tsum_congr fun n => logDeriv_factor (ha n) (hz n)

/-! ### Non-vacuity

The hypotheses are satisfiable, and by a family with infinitely many distinct points — the
squares `a n = (n+1)²`, whose reciprocals are summable while `∑ ‖a n‖⁻¹` for `a n = n+1` is not.
Without a witness the results above would be consistent with an empty hypothesis class. -/

/-- The powers of two are a family with infinitely many distinct points for which the standing
hypotheses hold. -/
theorem summable_inv_norm_two_pow : Summable fun n : ℕ => ‖(2 : ℂ) ^ n‖⁻¹ := by
  have hre : (fun n : ℕ => ‖(2 : ℂ) ^ n‖⁻¹) = fun n : ℕ => ((2 : ℝ)⁻¹) ^ n := by
    funext n
    rw [norm_pow, ← inv_pow]
    norm_num
  rw [hre]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- The whole package is inhabited: an entire canonical product whose zero set is exactly the
powers of two. -/
theorem exists_entire_canonicalProduct :
    ∃ a : ℕ → ℂ, Differentiable ℂ (canonicalProduct a) ∧
      ∀ z, canonicalProduct a z = 0 ↔ ∃ n, (2 : ℂ) ^ n = z :=
  ⟨fun n => (2 : ℂ) ^ n,
    differentiable_canonicalProduct summable_inv_norm_two_pow,
    canonicalProduct_eq_zero_iff (fun n => pow_ne_zero n two_ne_zero)
    summable_inv_norm_two_pow⟩

/-! ### Axiom footprint -/

/-- info: 'Shields.differentiable_canonicalProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differentiable_canonicalProduct

/-- info: 'Shields.canonicalProduct_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonicalProduct_eq_zero_iff

/-- info: 'Shields.finite_setOf_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_setOf_mem_ball

/-- info: 'Shields.exists_entire_canonicalProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_entire_canonicalProduct

/-- info: 'Shields.norm_canonicalProduct_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_canonicalProduct_le

/-- info: 'Shields.exists_bound_of_minimalType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_of_minimalType

end Shields
