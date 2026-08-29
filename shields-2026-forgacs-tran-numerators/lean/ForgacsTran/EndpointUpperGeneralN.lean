/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PencilIndex
import ForgacsTran.EndpointUpperOneBinders

/-!
# The `r = 1` upper endpoint at general `n`

`EndpointUpperOne` separates the collision from the rest of the spectrum at
`n = 3`, where the pencil has exactly ONE non-collision root and Vieta therefore
bounds it: the product over the other roots IS the minimum.  From `n = 4` the
product says nothing about the smallest, and that is why the retained set is
stated at `Fin 3`.

This module builds the two facts a general-`n` separation runs on.

## The normalization

With `u_k = L/(a_k+L)` and `s = (w+L)/L`, a root `w` of the endpoint pencil is a
root of `∏(1 - u_k s) = 1 - s`, on the simplex `∑ u_k = 1` — which is the deficit
equation `sum_div_add_eq_of_eval_ftCriticalReal_neg` already supplies.  `c`, `L`
and the `a_k` all leave.  `s = 0` is a double root *because* the `u_k` sum to one,
so the non-collision roots are the roots of `G(s) = (∏(1-u_k s) - 1 + s)/s²`, and
the circle `‖w‖ = 2L` is the disk `|s - 1| ≤ 2`.

## Why the bound is taken at `s = 1`

Every bound taken about the ORIGIN fails as `n` grows — the triangle bound at
radius 3 at `n = 7`, Fujiwara at `n = 8` — because the disk to avoid is centered
at `1`, not at `0`.  Taken at `1` the bound holds at every `n`, and it collapses
to a single inequality on the simplex.  `scripts/check_upper_endpoint_general_n.py`
measures all of it.

## What this proof does NOT need

**No triangular sum swap.**  The natural shape for this argument is to expand
`∑_l a_l C_l(-σ)` into `∑_i (∑_{l ≥ i+2} a_l (l-1-i)) (-σ)^i` and bound the inner
coefficients — which is a reindexing over a triangular region and is where a
development like this usually gets expensive.  It is not needed: the modulus bound
`norm_geomQuot_sub_le` applies **per `l`**, and the weights `a_l ≥ 0` carry through
the outer triangle inequality.  That is what keeps this file to fifteen theorems
instead of a reindexing development, so do not "simplify" it by introducing the
swap.

## Main statements

* `pow_sub_one_sub_smul` — `x^l - 1 - l(x-1) = (x-1)² ∑_{i<l-1} (l-1-i) x^i`, the
  identity that makes the coefficients of `G` at `s = 1` non-negative.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`.

## Tags

upper endpoint, general n, separation, elementary symmetric functions
-/

namespace ForgacsTran

open Finset

/-- **The second-order geometric identity.**  `x^l - 1 - l(x-1)` is divisible by
`(x-1)²`, and the quotient has coefficients `l-1, l-2, …, 1` — all non-negative.

That non-negativity is the whole of the sign fact the general-`n` separation
rests on: `∏(v_k + u_k t) - t` is a non-negative combination of these, so the
Taylor coefficients of `G` at `s = 1` alternate and the triangle bound there
collapses to a two-point evaluation. -/
theorem pow_sub_one_sub_smul {R : Type*} [CommRing R] (x : R) (l : ℕ) :
    x ^ l - 1 - (l : R) * (x - 1)
      = (x - 1) ^ 2 * ∑ i ∈ range (l - 1), ((l - 1 - i : ℕ) : R) * x ^ i := by
  induction l with
  | zero => simp
  | succ l ih =>
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · have hrange : l + 1 - 1 = (l - 1) + 1 := by omega
      rw [hrange, Finset.sum_range_succ']
      have hshift : ∀ i ∈ range (l - 1),
          ((l - 1 + 1 - (i + 1) : ℕ) : R) * x ^ (i + 1)
            = x * (((l - 1 - i : ℕ) : R) * x ^ i) := by
        intro i _
        have : l - 1 + 1 - (i + 1) = l - 1 - i := by omega
        rw [this]; ring
      rw [Finset.sum_congr rfl hshift, ← Finset.mul_sum]
      have hzero : ((l - 1 + 1 - 0 : ℕ) : R) = (l : R) := by
        have : l - 1 + 1 - 0 = l := by omega
        rw [this]
      rw [hzero, pow_zero, mul_one, mul_add]
      push_cast
      linear_combination x * ih

/-! ### The elementary symmetric step

The inequality the separation collapses to is
`∏(1+u_k) < 2 + 2∏(1-u_k)` on the simplex, which in elementary symmetric
functions is `∑_{even j≥2} e_j ≥ 3∑_{odd j≥3} e_j`.  It follows TERMWISE from
`e_j ≥ (j+1)e_{j+1}`, and that in turn from the identity

  `e_1 e_j = (j+1) e_{j+1} + (a sum of terms each carrying a square)`,

because a squarefree monomial of degree `j+1` arises from each of its `j+1`
sub-monomials of degree `j`.  Newton's inequalities would also give it; they are
not in Mathlib and are not needed. -/

/-- The Pascal recurrence for `Multiset.esymm`. -/
theorem esymm_cons {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  classical
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons]
  rw [← Multiset.sum_map_mul_left]

/-- `e_n` of a multiset of non-negative elements is non-negative. -/
theorem esymm_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) : 0 ≤ s.esymm n := by
  refine Multiset.sum_nonneg fun y hy => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hy
  refine Multiset.prod_nonneg fun x hx => hs x ?_
  exact Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hx

/-- **`e_1 e_j ≥ (j+1) e_(j+1)` for non-negative entries.**  With `e_1 = 1` this is
`e_j ≥ (j+1)e_(j+1)`, and at `j ≥ 2` it is the factor `3` the separation needs.

Proved by induction on the multiset through `esymm_cons`: adding `a` contributes
`a e_j` to `e_(j+1)` and `a` to `e_1`, and the two induction hypotheses cover the
cross terms with `a² e_(j-1) ≥ 0` left over. -/
theorem succ_mul_esymm_le {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (j : ℕ) :
    ((j : ℝ) + 1) * s.esymm (j + 1) ≤ s.esymm 1 * s.esymm j := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    cases j <;>
      simp [Multiset.esymm, Multiset.powersetCard_zero_right,
        Multiset.powersetCard_zero_left]
  | cons a t ih =>
    have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have h0 : t.esymm 0 = 1 := by simp [Multiset.esymm]
    cases j with
    | zero =>
      have : (a ::ₘ t).esymm 0 = 1 := by simp [Multiset.esymm]
      simp [this]
    | succ k =>
      have e1 : (a ::ₘ t).esymm 1 = t.esymm 1 + a := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, esymm_cons, h0, mul_one]
      have e2 : (a ::ₘ t).esymm (k + 2) = t.esymm (k + 2) + a * t.esymm (k + 1) :=
        esymm_cons a t (k + 1)
      have e3 : (a ::ₘ t).esymm (k + 1) = t.esymm (k + 1) + a * t.esymm k :=
        esymm_cons a t k
      have ih1 := ih ht (k + 1)
      have ih2 := ih ht k
      have hk : 0 ≤ t.esymm k := esymm_nonneg ht k
      have hk1 : 0 ≤ t.esymm (k + 1) := esymm_nonneg ht (k + 1)
      rw [e1, e2, e3]
      push_cast at ih1 ih2 ⊢
      nlinarith [mul_nonneg ha ha, mul_nonneg (mul_nonneg ha ha) hk,
        mul_nonneg ha hk1, mul_nonneg ha hk, ih1, ih2]


/-! ### From the termwise step to the one inequality

`∏(1+u_k) - 2∏(1-u_k) = ∑_j e_j (1 - 2(-1)^j)`, whose `j = 0` and `j = 1` terms
contribute `-1 + 3 = 2` on the simplex.  What is left runs `-e_2 + 3e_3 - e_4 + …`,
and pairing each even index with the odd one above it makes every pair
non-positive by `succ_mul_esymm_le`.  The pairing is where the parity matters: the
same decay summed without it is a factor `3/2` too weak. -/

/-- **The paired alternating sum is non-positive.**  `-f 2 + 3 f 3 - f 4 + …`, with
each `(-f (2i) + 3 f (2i+1))` non-positive by the decay hypothesis.

Stated over `Ico 2 (2M+2)` so the induction adds exactly one pair at a time; the
even upper limit is what makes every term paired rather than leaving a dangling
`-f` that would have to be discarded. -/
theorem sum_alternating_le_zero {f : ℕ → ℝ}
    (hdec : ∀ j, 2 ≤ j → 3 * f (j + 1) ≤ f j) (M : ℕ) :
    ∑ j ∈ Finset.Ico 2 (2 * M + 2), (1 - 2 * (-1 : ℝ) ^ j) * f j ≤ 0 := by
  induction M with
  | zero => simp
  | succ m ih =>
    have hstep : 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 := by ring
    rw [hstep, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
    have heven : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; norm_num
    have hodd : (-1 : ℝ) ^ (2 * m + 2 + 1) = -1 := by
      rw [pow_succ, heven]; ring
    rw [heven, hodd]
    have hd := hdec (2 * m + 2) (by omega)
    nlinarith [ih, hd]


/-- `∏(1 + x) = ∑_j e_j`, Vieta evaluated at `1`. -/
theorem prod_one_add_eq_sum_esymm (s : Multiset ℝ) :
    (s.map (fun x => 1 + x)).prod
      = ∑ j ∈ Finset.range (Multiset.card s + 1), s.esymm j := by
  have h := congrArg (Polynomial.eval (1 : ℝ)) (Multiset.prod_X_add_C_eq_sum_esymm s)
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_pow, one_pow, mul_one] at h
  exact h

/-- `∏(1 - x) = ∑_j (-1)^j e_j`, Vieta evaluated at `-1`.  The sign bookkeeping is
the only content: `(-1)^(card - j) = (-1)^(card-j) ((-1)^j)² (-1)^j` for `j ≤ card`,
and the overall `(-1)^card` cancels against the one the product picks up. -/
theorem prod_one_sub_eq_sum_esymm (s : Multiset ℝ) :
    (s.map (fun x => 1 - x)).prod
      = ∑ j ∈ Finset.range (Multiset.card s + 1), (-1 : ℝ) ^ j * s.esymm j := by
  have h := congrArg (Polynomial.eval (-1 : ℝ)) (Multiset.prod_X_add_C_eq_sum_esymm s)
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_pow] at h
  have hmapeq : Multiset.map (fun x : ℝ => -1 + x) s
      = Multiset.map (fun y : ℝ => -y) (Multiset.map (fun x : ℝ => 1 - x) s) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring
  have hleft : (Multiset.map (fun x : ℝ => -1 + x) s).prod
      = (-1 : ℝ) ^ Multiset.card s * (Multiset.map (fun x : ℝ => 1 - x) s).prod := by
    rw [hmapeq, Multiset.prod_map_neg, Multiset.card_map]
  have hright : ∑ j ∈ Finset.range (Multiset.card s + 1),
        s.esymm j * (-1 : ℝ) ^ (Multiset.card s - j)
      = (-1 : ℝ) ^ Multiset.card s
        * ∑ j ∈ Finset.range (Multiset.card s + 1), (-1 : ℝ) ^ j * s.esymm j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjle : j ≤ Multiset.card s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have hsplit : (-1 : ℝ) ^ Multiset.card s
        = (-1 : ℝ) ^ (Multiset.card s - j) * (-1 : ℝ) ^ j := by
      rw [← pow_add]; congr 1; omega
    calc s.esymm j * (-1 : ℝ) ^ (Multiset.card s - j)
        = (-1 : ℝ) ^ (Multiset.card s - j) * (((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j))
            * s.esymm j := by rw [hsq]; ring
      _ = _ := by rw [hsplit]; ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (by positivity : ((-1 : ℝ) ^ Multiset.card s) ≠ 0) h

/-- **The one inequality the general-`n` separation collapses to.**
`∏(1+u_k) ≤ 2 + 2∏(1-u_k)` whenever the `u_k` are non-negative and sum to one.

Equality holds at a vertex of the simplex, and the equal-point limit as `n → ∞` is
`e < 2/e + 2` with margin `0.0175`.

**That narrowness is an `n ≤ 3` phenomenon and not a limit on the constant `2`.**
`scripts/check_disk_bound_sharpness.py` measures `2 + 2∏(1-u) - ∏(1+u)` against the
boundary minimum of `|F(s)/s²|` at `n = 2..14`: it is a valid lower bound
everywhere and positive throughout, but at `n = 2, 3` it is not a bound at all — it
is *exactly* the value at `s = 3`, the circle point farthest from the collision
along the positive axis, which is `w = 2L` itself, and that value is the minimum.
From `n = 4` it separates by at least `0.0267` and the gap grows.  So the route has
real slack above `n = 3`; do not read the thin margin at a skewed `n = 3` point as
the constant being at its limit. -/
theorem prod_one_add_le_two_add_two_mul_prod_one_sub {s : Multiset ℝ}
    (hs : ∀ x ∈ s, 0 ≤ x) (h1 : s.esymm 1 = 1) :
    (s.map (fun x => 1 + x)).prod ≤ 2 + 2 * (s.map (fun x => 1 - x)).prod := by
  classical
  set N := Multiset.card s with hN
  set g : ℕ → ℝ := fun j => (1 - 2 * (-1 : ℝ) ^ j) * s.esymm j with hg
  have h0 : s.esymm 0 = 1 := by
    simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  -- the decay, from the termwise step and `e_1 = 1`
  have hdec : ∀ j, 2 ≤ j → 3 * s.esymm (j + 1) ≤ s.esymm j := by
    intro j hj
    have h := succ_mul_esymm_le hs j
    rw [h1, one_mul] at h
    have h3 : (3 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    nlinarith [esymm_nonneg hs (j + 1), h, h3]
  -- `e_j` vanishes past the cardinality, so the range may be widened freely
  have hzero : ∀ j, N < j → s.esymm j = 0 := by
    intro j hj
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty j (by omega)]
    simp
  have hcomb : (s.map (fun x => 1 + x)).prod - 2 * (s.map (fun x => 1 - x)).prod
      = ∑ j ∈ Finset.range (N + 1), g j := by
    rw [prod_one_add_eq_sum_esymm, prod_one_sub_eq_sum_esymm, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hg]; ring
  have hext : ∑ j ∈ Finset.range (N + 1), g j = ∑ j ∈ Finset.range (2 * N + 2), g j := by
    refine Finset.sum_subset (fun x hx => ?_) (fun x _ hx => ?_)
    · simp only [Finset.mem_range] at hx ⊢; omega
    · simp only [Finset.mem_range] at hx
      rw [hg]
      simp only []
      rw [hzero x (by omega), mul_zero]
  have hsplit : ∑ j ∈ Finset.range (2 * N + 2), g j
      = (g 0 + g 1) + ∑ j ∈ Finset.Ico 2 (2 * N + 2), g j := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive g (Nat.zero_le 2) (by omega : 2 ≤ 2 * N + 2)]
    congr 1
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    simp
  have hhead : g 0 + g 1 = 2 := by
    rw [hg]
    simp only []
    rw [h0, h1]
    norm_num
  have htail : ∑ j ∈ Finset.Ico 2 (2 * N + 2), g j ≤ 0 :=
    sum_alternating_le_zero hdec N
  have : (s.map (fun x => 1 + x)).prod - 2 * (s.map (fun x => 1 - x)).prod ≤ 2 := by
    rw [hcomb, hext, hsplit, hhead]
    linarith
  linarith


/-! ### The disk bound

With the coefficients non-negative, a polynomial's modulus on a disk is bounded
below by twice its constant term less its value at the radius.  That is the whole
of the analytic step: applied to the quotient `(A(t) - t)/(t-1)²` at radius `2` it
gives `2∏(1-u_k) - (∏(1+u_k) - 2)`, which
`prod_one_add_le_two_add_two_mul_prod_one_sub` makes positive. -/

/-- **A series with non-negative coefficients is bounded below on a disk.**
`‖∑ c_i z^i‖ ≥ 2c_0 - ∑ c_i r^i` for `‖z‖ ≤ r`.

The `2c_0` is not a slack constant: `c_0` is recovered once from the triangle
inequality against the tail and once from the tail's own bound at the radius, and
the statement is exactly `‖P(z)‖ ≥ P(0) - (P(r) - P(0))`. -/
theorem two_mul_sub_sum_le_norm_sum {N : ℕ} {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i)
    {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    2 * c 0 - ∑ i ∈ Finset.range (N + 1), c i * r ^ i
      ≤ ‖∑ i ∈ Finset.range (N + 1), (c i : ℂ) * z ^ i‖ := by
  have hr : 0 ≤ r := le_trans (norm_nonneg z) hz
  -- the tail, bounded termwise at the radius
  have htail : ‖∑ i ∈ Finset.range N, (c (i + 1) : ℂ) * z ^ (i + 1)‖
      ≤ ∑ i ∈ Finset.range N, c (i + 1) * r ^ (i + 1) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc (i + 1))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (hc (i + 1))
  -- peel the constant term off both sides
  rw [Finset.sum_range_succ' (fun i => (c i : ℂ) * z ^ i) N]
  rw [Finset.sum_range_succ' (fun i => c i * r ^ i) N]
  simp only [pow_zero, mul_one]
  have hlow := norm_sub_norm_le ((c 0 : ℂ))
    (-(∑ i ∈ Finset.range N, (c (i + 1) : ℂ) * z ^ (i + 1)))
  rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hc 0), add_comm] at hlow
  linarith


/-- The quotient `pow_sub_one_sub_smul` produces: `C_l(x) = ∑_{i<l-1} (l-1-i) x^i`,
with all coefficients non-negative. -/
noncomputable def geomQuot {R : Type*} [CommRing R] (l : ℕ) (x : R) : R :=
  ∑ i ∈ Finset.range (l - 1), ((l - 1 - i : ℕ) : R) * x ^ i

theorem pow_sub_one_sub_smul' {R : Type*} [CommRing R] (x : R) (l : ℕ) :
    x ^ l - 1 - (l : R) * (x - 1) = (x - 1) ^ 2 * geomQuot l x :=
  pow_sub_one_sub_smul x l

/-- `C_l(0) = l - 1`, truncated subtraction included: at `l ≤ 1` the sum is empty
and `(l-1 : ℕ)` is `0`. -/
theorem geomQuot_zero {R : Type*} [CommRing R] (l : ℕ) :
    geomQuot l (0 : R) = ((l - 1 : ℕ) : R) := by
  rcases Nat.lt_or_ge l 2 with hl | hl
  · interval_cases l <;> simp [geomQuot]
  · have h : l - 1 = (l - 2) + 1 := by omega
    rw [geomQuot, h, Finset.sum_range_succ']
    simp

/-- `C_l(2) = 2^l - l - 1`, read off the identity at `x = 2`. -/
theorem geomQuot_two (l : ℕ) : geomQuot l (2 : ℝ) = 2 ^ l - (l : ℝ) - 1 := by
  have h := pow_sub_one_sub_smul' (2 : ℝ) l
  norm_num at h
  linarith

/-- **The tail bound.**  A series with non-negative coefficients moves at most
`P(r) - P(0)` over the disk of radius `r`. -/
theorem norm_sum_sub_const_le {N : ℕ} {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i) {z : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) :
    ‖(∑ i ∈ Finset.range (N + 1), (c i : ℂ) * z ^ i) - (c 0 : ℂ)‖
      ≤ (∑ i ∈ Finset.range (N + 1), c i * r ^ i) - c 0 := by
  rw [Finset.sum_range_succ' (fun i => (c i : ℂ) * z ^ i) N,
    Finset.sum_range_succ' (fun i => c i * r ^ i) N]
  simp only [pow_zero, mul_one, add_sub_cancel_right]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc (i + 1))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (hc (i + 1))

/-- `C_l` moves at most `C_l(2) - C_l(0)` over the disk of radius `2`. -/
theorem norm_geomQuot_sub_le (l : ℕ) {σ : ℂ} (hσ : ‖σ‖ ≤ 2) :
    ‖geomQuot l (-σ) - ((l - 1 : ℕ) : ℂ)‖ ≤ geomQuot l (2 : ℝ) - ((l - 1 : ℕ) : ℝ) := by
  rcases Nat.lt_or_ge l 2 with hl | hl
  · interval_cases l <;> simp [geomQuot]
  · have h : l - 1 = (l - 2) + 1 := by omega
    have hz : ‖(-σ)‖ ≤ 2 := by rwa [norm_neg]
    have hc : ∀ i : ℕ, (0 : ℝ) ≤ ((l - 1 - i : ℕ) : ℝ) := fun i => Nat.cast_nonneg _
    have key := norm_sum_sub_const_le (N := l - 2) (c := fun i => ((l - 1 - i : ℕ) : ℝ)) hc hz
    simp only [Nat.sub_zero] at key
    rw [← h] at key
    simpa [geomQuot] using key


/-- **The disk bound, abstractly.**  For non-negative weights with `∑ a_l = 1` and
`∑ l a_l = 1`, and `‖σ‖ ≤ 2`,

  `‖A(-σ) + σ‖ ≥ ‖1+σ‖² (2a_0 + 2 - A(2))`.

`A(-σ) + σ` is `F(1+σ)` for `F(s) = ∏(1-u_k s) - (1-s)` when the `a_l` are the
coefficients of `∏(v_k + u_k t)`, so this says the only zero of `F` in
`|s - 1| ≤ 2` is the collision at `s = 0` — provided the right-hand factor is
positive, which is `prod_one_add_le_two_add_two_mul_prod_one_sub`.

The two normalizations are what make `A(t) - t` divisible by `(t-1)²`; the
non-negativity of the `a_l` and of `C_l`'s coefficients is what makes the quotient
bounded below on the disk. -/
theorem norm_weighted_ge {N : ℕ} {a : ℕ → ℝ} (ha : ∀ l, 0 ≤ a l)
    (h1 : ∑ l ∈ Finset.range (N + 1), a l = 1)
    (hd : ∑ l ∈ Finset.range (N + 1), (l : ℝ) * a l = 1)
    {σ : ℂ} (hσ : ‖σ‖ ≤ 2) :
    ‖1 + σ‖ ^ 2 * (2 * a 0 + 2 - ∑ l ∈ Finset.range (N + 1), a l * 2 ^ l)
      ≤ ‖(∑ l ∈ Finset.range (N + 1), (a l : ℂ) * (-σ) ^ l) + σ‖ := by
  classical
  set R := Finset.range (N + 1) with hR
  have e1 : ∑ l ∈ R, (a l : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]
  have e2 : ∑ l ∈ R, (l : ℂ) * (a l : ℂ) = 1 := by
    rw [← Complex.ofReal_one, ← hd, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun l _ => by push_cast; ring
  -- the factorization, from the two normalizations
  have hfac : (∑ l ∈ R, (a l : ℂ) * (-σ) ^ l) + σ
      = (1 + σ) ^ 2 * ∑ l ∈ R, (a l : ℂ) * geomQuot l (-σ) := by
    have hsq : ((-σ) - 1) ^ 2 = (1 + σ) ^ 2 := by ring
    have hstep : ∑ l ∈ R, (a l : ℂ) * ((-σ) ^ l - 1 - (l : ℂ) * ((-σ) - 1))
        = (∑ l ∈ R, (a l : ℂ) * (-σ) ^ l) + σ := by
      have hsplit : ∑ l ∈ R, (a l : ℂ) * ((-σ) ^ l - 1 - (l : ℂ) * ((-σ) - 1))
          = (∑ l ∈ R, (a l : ℂ) * (-σ) ^ l) - (∑ l ∈ R, (a l : ℂ))
            - ((-σ) - 1) * ∑ l ∈ R, (l : ℂ) * (a l : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hsplit, e1, e2]; ring
    rw [← hstep, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, mul_comm ((1 + σ) ^ 2) ((a l : ℂ)), mul_assoc, ← hsq,
      ← pow_sub_one_sub_smul' (-σ) l]
  -- the quotient, bounded below on the disk
  have hX0 : ∑ l ∈ R, a l * ((l - 1 : ℕ) : ℝ) = a 0 := by
    have hpt : ∀ l ∈ R, a l * ((l - 1 : ℕ) : ℝ)
        = a l * ((l : ℝ) - 1) + (if l = 0 then a 0 else 0) := by
      intro l _
      rcases Nat.eq_zero_or_pos l with rfl | hl
      · norm_num
      · rw [if_neg (by omega)]
        have : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := cast_pred_eq_sub_one hl
        rw [this]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    have hA : ∑ l ∈ R, a l * ((l : ℝ) - 1) = 0 := by
      have : ∑ l ∈ R, a l * ((l : ℝ) - 1)
          = (∑ l ∈ R, (l : ℝ) * a l) - ∑ l ∈ R, a l := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this, h1, hd]; ring
    have hB : ∑ l ∈ R, (if l = 0 then a 0 else 0) = a 0 := by
      rw [Finset.sum_ite_eq' R 0 (fun _ => a 0), if_pos (by simp [hR])]
    rw [hA, hB, zero_add]
  have hX2 : ∑ l ∈ R, a l * geomQuot l (2 : ℝ)
      = (∑ l ∈ R, a l * 2 ^ l) - 2 := by
    have hpt : ∀ l ∈ R, a l * geomQuot l (2 : ℝ)
        = a l * 2 ^ l - (l : ℝ) * a l - a l := by
      intro l _; rw [geomQuot_two]; ring
    rw [Finset.sum_congr rfl hpt]
    simp only [Finset.sum_sub_distrib]
    rw [hd, h1]; ring
  have hbound : 2 * a 0 + 2 - (∑ l ∈ R, a l * 2 ^ l)
      ≤ ‖∑ l ∈ R, (a l : ℂ) * geomQuot l (-σ)‖ := by
    have hdiff : ‖(∑ l ∈ R, (a l : ℂ) * geomQuot l (-σ))
        - ((∑ l ∈ R, a l * ((l - 1 : ℕ) : ℝ) : ℝ) : ℂ)‖
        ≤ ∑ l ∈ R, a l * (geomQuot l (2 : ℝ) - ((l - 1 : ℕ) : ℝ)) := by
      rw [Complex.ofReal_sum]
      rw [← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun l _ => ?_)
      have : (a l : ℂ) * geomQuot l (-σ) - ((a l * ((l - 1 : ℕ) : ℝ) : ℝ) : ℂ)
          = (a l : ℂ) * (geomQuot l (-σ) - ((l - 1 : ℕ) : ℂ)) := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha l)]
      exact mul_le_mul_of_nonneg_left (norm_geomQuot_sub_le l hσ) (ha l)
    have hsum : ∑ l ∈ R, a l * (geomQuot l (2 : ℝ) - ((l - 1 : ℕ) : ℝ))
        = (∑ l ∈ R, a l * 2 ^ l) - 2 - a 0 := by
      have : ∑ l ∈ R, a l * (geomQuot l (2 : ℝ) - ((l - 1 : ℕ) : ℝ))
          = (∑ l ∈ R, a l * geomQuot l (2 : ℝ)) - ∑ l ∈ R, a l * ((l - 1 : ℕ) : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this, hX2, hX0]
    rw [hX0, hsum] at hdiff
    have hlow := norm_sub_norm_le ((a 0 : ℝ) : ℂ) (∑ l ∈ R, (a l : ℂ) * geomQuot l (-σ))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha 0), norm_sub_rev] at hlow
    linarith
  rw [hfac, norm_mul, norm_pow]
  have hnn : (0 : ℝ) ≤ ‖1 + σ‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hbound hnn


/-! ### Strictness

The disk bound needs the factor `2 + 2∏(1-u) - ∏(1+u)` STRICTLY positive, since a
zero factor makes the bound vacuous rather than false.  Equality holds exactly at
a vertex of the simplex, so strictness is where `u_k = L/(a_k+L) < 1` stops being
reassurance and becomes load-bearing.

One strict pair suffices, and the first is the natural one: `3e_3 < e_2`. -/

/-- `sum_alternating_le_zero` with the first pair strict. -/
theorem sum_alternating_lt_zero {f : ℕ → ℝ}
    (hdec : ∀ j, 2 ≤ j → 3 * f (j + 1) ≤ f j) (hstrict : 3 * f 3 < f 2) (m : ℕ) :
    ∑ j ∈ Finset.Ico 2 (2 * (m + 1) + 2), (1 - 2 * (-1 : ℝ) ^ j) * f j < 0 := by
  induction m with
  | zero =>
    rw [show 2 * (0 + 1) + 2 = 4 from rfl]
    rw [show (4 : ℕ) = 2 + 1 + 1 from rfl, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    norm_num
    linarith
  | succ k ih =>
    have hstep : 2 * (k + 1 + 1) + 2 = (2 * (k + 1) + 2) + 1 + 1 := by ring
    rw [hstep, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
    have heven : (-1 : ℝ) ^ (2 * (k + 1) + 2) = 1 := by
      rw [show 2 * (k + 1) + 2 = 2 * (k + 2) by ring, pow_mul]; norm_num
    have hodd : (-1 : ℝ) ^ (2 * (k + 1) + 2 + 1) = -1 := by rw [pow_succ, heven]; ring
    rw [heven, hodd]
    have hd := hdec (2 * (k + 1) + 2) (by omega)
    nlinarith [ih, hd]

/-- **The strict form of the one inequality.**  One strict pair upgrades
`prod_one_add_le_two_add_two_mul_prod_one_sub`, and `3e_3 < e_2` is that pair. -/
theorem prod_one_add_lt_two_add_two_mul_prod_one_sub {s : Multiset ℝ}
    (hs : ∀ x ∈ s, 0 ≤ x) (h1 : s.esymm 1 = 1) (hstrict : 3 * s.esymm 3 < s.esymm 2) :
    (s.map (fun x => 1 + x)).prod < 2 + 2 * (s.map (fun x => 1 - x)).prod := by
  classical
  set N := Multiset.card s with hN
  set g : ℕ → ℝ := fun j => (1 - 2 * (-1 : ℝ) ^ j) * s.esymm j with hg
  have h0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  have hdec : ∀ j, 2 ≤ j → 3 * s.esymm (j + 1) ≤ s.esymm j := by
    intro j hj
    have h := succ_mul_esymm_le hs j
    rw [h1, one_mul] at h
    have h3 : (3 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    nlinarith [esymm_nonneg hs (j + 1), h, h3]
  have hzero : ∀ j, N < j → s.esymm j = 0 := by
    intro j hj
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty j (by omega)]
    simp
  have hcomb : (s.map (fun x => 1 + x)).prod - 2 * (s.map (fun x => 1 - x)).prod
      = ∑ j ∈ Finset.range (N + 1), g j := by
    rw [prod_one_add_eq_sum_esymm, prod_one_sub_eq_sum_esymm, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hg]; ring
  have hext : ∑ j ∈ Finset.range (N + 1), g j
      = ∑ j ∈ Finset.range (2 * (N + 1) + 2), g j := by
    refine Finset.sum_subset (fun x hx => ?_) (fun x _ hx => ?_)
    · simp only [Finset.mem_range] at hx ⊢; omega
    · simp only [Finset.mem_range] at hx
      rw [hg]; simp only []
      rw [hzero x (by omega), mul_zero]
  have hsplit : ∑ j ∈ Finset.range (2 * (N + 1) + 2), g j
      = (g 0 + g 1) + ∑ j ∈ Finset.Ico 2 (2 * (N + 1) + 2), g j := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive g (Nat.zero_le 2) (by omega : 2 ≤ 2 * (N + 1) + 2)]
    congr 1
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    simp
  have hhead : g 0 + g 1 = 2 := by
    rw [hg]; simp only []; rw [h0, h1]; norm_num
  have htail : ∑ j ∈ Finset.Ico 2 (2 * (N + 1) + 2), g j < 0 :=
    sum_alternating_lt_zero hdec hstrict N
  have : (s.map (fun x => 1 + x)).prod - 2 * (s.map (fun x => 1 - x)).prod < 2 := by
    rw [hcomb, hext, hsplit, hhead]
    linarith
  linarith


/-- `e_1` is the sum. -/
theorem esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp

/-- **Newton's second identity**, `p_2 = e_1² - 2e_2`, by one cons induction. -/
theorem psum_two (s : Multiset ℝ) :
    (s.map (fun x => x ^ 2)).sum = (s.esymm 1) ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a t ih =>
    have h0 : t.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    have e1 : (a ::ₘ t).esymm 1 = t.esymm 1 + a := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, esymm_cons, h0, mul_one]
    have e2 : (a ::ₘ t).esymm 2 = t.esymm 2 + a * t.esymm 1 := esymm_cons a t 1
    rw [Multiset.map_cons, Multiset.sum_cons, ih, e1, e2]
    ring

/-- **The strictness identity.**  `e_1e_2 - 3e_3 = e_1 p_2 - p_3`, which is Newton's
third identity rearranged — every term of `e_1e_2` either repeats an index or does
not, and the ones that do not give `3e_3`.

Under `∑u_k = 1` the right-hand side is `∑_k u_k²(1 - u_k)`, positive as soon as one
coordinate is interior; that is what makes
`prod_one_add_lt_two_add_two_mul_prod_one_sub`'s hypothesis dischargeable. -/
theorem esymm_one_mul_esymm_two_sub (s : Multiset ℝ) :
    s.esymm 1 * s.esymm 2 - 3 * s.esymm 3
      = s.esymm 1 * (s.map (fun x => x ^ 2)).sum - (s.map (fun x => x ^ 3)).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a t ih =>
    have h0 : t.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    have e1 : (a ::ₘ t).esymm 1 = t.esymm 1 + a := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, esymm_cons, h0, mul_one]
    have e2 : (a ::ₘ t).esymm 2 = t.esymm 2 + a * t.esymm 1 := esymm_cons a t 1
    have e3 : (a ::ₘ t).esymm 3 = t.esymm 3 + a * t.esymm 2 := esymm_cons a t 2
    have hp2 := psum_two t
    rw [e1, e2, e3, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
      Multiset.sum_cons]
    linear_combination ih - a * hp2

/-- **`3e_3 < e_2` on the simplex, whenever one coordinate is interior.**  The
identity above with `e_1 = 1` reads `e_2 - 3e_3 = ∑_k u_k²(1 - u_k)`; every term is
non-negative because `∑u_k = 1` forces `u_k ≤ 1`, and the interior coordinate makes
one of them positive. -/
theorem three_mul_esymm_three_lt_esymm_two {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x)
    (h1 : s.esymm 1 = 1) {y : ℝ} (hy : y ∈ s) (hy0 : 0 < y) (hy1 : y < 1) :
    3 * s.esymm 3 < s.esymm 2 := by
  have hsum : s.sum = 1 := by rw [← esymm_one, h1]
  have hle : ∀ x ∈ s, x ≤ 1 := by
    intro x hx
    rw [← hsum]
    exact Multiset.single_le_sum hs x hx
  -- `e_2 - 3e_3 = ∑ x²(1 - x)`, termwise non-negative and positive at `y`
  have hid := esymm_one_mul_esymm_two_sub s
  simp only [h1, one_mul] at hid
  have hsplit : (s.map (fun x => x ^ 2)).sum - (s.map (fun x => x ^ 3)).sum
      = (s.map (fun x => x ^ 2 * (1 - x))).sum := by
    rw [← Multiset.sum_map_sub]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => by ring)
  have hpos : 0 < (s.map (fun x => x ^ 2 * (1 - x))).sum := by
    refine lt_of_lt_of_le ?_ (Multiset.single_le_sum ?_ (y ^ 2 * (1 - y)) ?_)
    · have : 0 < y ^ 2 := by positivity
      nlinarith
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
      have := hs x hx
      have := hle x hx
      nlinarith [sq_nonneg x]
    · exact Multiset.mem_map_of_mem _ hy
  rw [hsplit] at hid
  linarith


/-- **The strict inequality under the hypotheses the endpoint actually supplies.**
Non-negative coordinates summing to one, with one of them interior — which is
`u_k = L/(a_k+L)` for `n ≥ 2` and every `a_k > 0`.

This is what the disk bound consumes: `norm_weighted_ge`'s right-hand factor is
`2 + 2∏(1-u_k) - ∏(1+u_k)`, and it has to be strictly positive rather than merely
non-negative, since a zero factor makes that bound vacuous rather than false. -/
theorem prod_one_add_lt_of_interior {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x)
    (h1 : s.esymm 1 = 1) {y : ℝ} (hy : y ∈ s) (hy0 : 0 < y) (hy1 : y < 1) :
    (s.map (fun x => 1 + x)).prod < 2 + 2 * (s.map (fun x => 1 - x)).prod :=
  prod_one_add_lt_two_add_two_mul_prod_one_sub hs h1
    (three_mul_esymm_three_lt_esymm_two hs h1 hy hy0 hy1)


/-! ### The coefficient layer

`A(t) = ∏_k ((1-u_k) + u_k t)` as a polynomial, with the three facts
`norm_weighted_ge` asks of its coefficients.

**Two of the three are evaluations, not expansions.**  `∑_l a_l` is `A(1)`, which
is `∏_k ((1-u_k) + u_k) = ∏_k 1 = 1`; and `∑_l l a_l` is `A'(1)`, which the product
rule collapses to `∑_k u_k` because every cofactor is again `1`.  Neither needs the
coefficient list, and only the non-negativity does — the same shape as the sum swap
above, where the claim is *stated* about coefficients and the quantity is an
evaluation. -/

/-- `A(t) = ∏_k ((1-u_k) + u_k t)`. -/
noncomputable def simplexPoly (s : Multiset ℝ) : Polynomial ℝ :=
  (s.map (fun u => Polynomial.C (1 - u) + Polynomial.C u * Polynomial.X)).prod

theorem simplexPoly_eval (s : Multiset ℝ) (t : ℝ) :
    (simplexPoly s).eval t = (s.map (fun u => (1 - u) + u * t)).prod := by
  rw [simplexPoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => by simp)

@[simp] theorem simplexPoly_zero : simplexPoly (0 : Multiset ℝ) = 1 := by
  simp [simplexPoly]

theorem simplexPoly_cons (a : ℝ) (s : Multiset ℝ) :
    simplexPoly (a ::ₘ s)
      = (Polynomial.C (1 - a) + Polynomial.C a * Polynomial.X) * simplexPoly s := by
  rw [simplexPoly, Multiset.map_cons, Multiset.prod_cons, simplexPoly]

/-- `A(1) = 1`: every factor is `(1-u_k) + u_k`. -/
theorem simplexPoly_eval_one (s : Multiset ℝ) : (simplexPoly s).eval 1 = 1 := by
  rw [simplexPoly_eval]
  rw [show (s.map (fun u => (1 - u) + u * 1)) = s.map (fun _ => (1 : ℝ)) from
    Multiset.map_congr rfl fun u _ => by ring]
  simp

/-- `A(0) = ∏(1-u_k)` and `A(2) = ∏(1+u_k)`, the two the disk bound reads. -/
theorem simplexPoly_eval_zero (s : Multiset ℝ) :
    (simplexPoly s).eval 0 = (s.map (fun u => 1 - u)).prod := by
  rw [simplexPoly_eval]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => by ring)

theorem simplexPoly_eval_two (s : Multiset ℝ) :
    (simplexPoly s).eval 2 = (s.map (fun u => 1 + u)).prod := by
  rw [simplexPoly_eval]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => by ring)

/-- `A'(1) = ∑ u_k`: the product rule, with every cofactor equal to `1`.

**Not `Polynomial.derivative_prod`**, which is stated for `Finset.prod` while this
layer is multisets: taking it would mean a bridge in each direction for a step a
cons induction closes outright.  The induction consumes `simplexPoly_eval_one` for
the cofactors and is three lines. -/
theorem derivative_simplexPoly_eval_one (s : Multiset ℝ) :
    (Polynomial.derivative (simplexPoly s)).eval 1 = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [simplexPoly_cons, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_C_mul,
      Polynomial.derivative_X, zero_add, mul_one, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [ih, simplexPoly_eval_one, Multiset.sum_cons]
    ring

/-- The coefficients are non-negative, which is the one fact that does need the
expansion — three lines over `coeff_mul`. -/
theorem simplexPoly_coeff_nonneg {s : Multiset ℝ} (h0 : ∀ u ∈ s, 0 ≤ u)
    (h1 : ∀ u ∈ s, u ≤ 1) (n : ℕ) : 0 ≤ (simplexPoly s).coeff n := by
  induction s using Multiset.induction_on generalizing n with
  | empty => rcases n with _ | n <;> simp [Polynomial.coeff_one]
  | cons a t ih =>
    have ha0 : 0 ≤ a := h0 a (Multiset.mem_cons_self a t)
    have ha1 : a ≤ 1 := h1 a (Multiset.mem_cons_self a t)
    have ht0 : ∀ u ∈ t, 0 ≤ u := fun u hu => h0 u (Multiset.mem_cons_of_mem hu)
    have ht1 : ∀ u ∈ t, u ≤ 1 := fun u hu => h1 u (Multiset.mem_cons_of_mem hu)
    have hfac : ∀ i : ℕ,
        0 ≤ (Polynomial.C (1 - a) + Polynomial.C a * Polynomial.X).coeff i := by
      intro i
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X]
      rcases i with _ | i
      · norm_num; linarith
      · rcases i with _ | i
        · norm_num; exact ha0
        · norm_num
    rw [simplexPoly_cons, Polynomial.coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hfac _) (ih ht0 ht1 _)


/-- `∑_{l ≤ M} a_l = A(1)` for any `M` past the degree. -/
theorem sum_coeff_eq_eval_one {P : Polynomial ℝ} {M : ℕ} (hM : P.natDegree ≤ M) :
    ∑ l ∈ Finset.range (M + 1), P.coeff l = P.eval 1 := by
  rw [Polynomial.eval_eq_sum_range' (n := M + 1) (by omega)]
  simp

/-- `∑_{l ≤ M} l a_l = A'(1)` for any `M` past the degree.  The `l = 0` term
vanishes on the left and the `l = M+1` term on the right, which is what makes the
two ranges agree. -/
theorem sum_smul_coeff_eq_derivative_eval_one {P : Polynomial ℝ} {M : ℕ}
    (hM : P.natDegree ≤ M) :
    ∑ l ∈ Finset.range (M + 1), (l : ℝ) * P.coeff l
      = (Polynomial.derivative P).eval 1 := by
  have hdeg : (Polynomial.derivative P).natDegree < M + 1 := by
    have hle := Polynomial.natDegree_derivative_le P
    omega
  rw [Polynomial.eval_eq_sum_range' (n := M + 1) hdeg]
  simp only [one_pow, mul_one, Polynomial.coeff_derivative]
  rw [Finset.sum_range_succ' (fun l => (l : ℝ) * P.coeff l) M,
    Finset.sum_range_succ (fun i => P.coeff (i + 1) * ((i : ℝ) + 1)) M]
  have hzero : P.coeff (M + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hzero]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  exact Finset.sum_congr rfl fun i _ => by push_cast; ring


/-! ### The conclusion, abstractly

Everything above meets here.  A root of `∏(1 - u_k s) = 1 - s` in the disk
`|s - 1| ≤ 2` must be the collision `s = 0`: the disk bound makes the modulus at
least `‖1+σ‖²` times a factor, and `prod_one_add_lt_of_interior` makes that factor
strictly positive, so the only way the root can sit there is `‖1+σ‖ = 0`. -/

/-- **The only root of `∏(1-u_k s) = 1-s` in `|s-1| ≤ 2` is `s = 0`.**  Stated in
`σ = s - 1`, so the conclusion is `σ = -1`.

The interiority witness `y` is the one hypothesis that is about the *simplex*
rather than about the disk: it excludes a vertex, where the inequality degenerates
to an equality and the disk bound says nothing.  It is not needed for either
normalization — those hold at a vertex too — so it appears exactly once. -/
theorem eq_neg_one_of_prod_eq_of_norm_le {u : Multiset ℝ} (h0 : ∀ x ∈ u, 0 ≤ x)
    (hsum : u.esymm 1 = 1) {y : ℝ} (hy : y ∈ u) (hy0 : 0 < y) (hy1 : y < 1)
    {σ : ℂ} (hσ : ‖σ‖ ≤ 2)
    (hroot : (u.map (fun x : ℝ => (1 : ℂ) - (x : ℂ) * (1 + σ))).prod = -σ) :
    σ = -1 := by
  classical
  -- every coordinate is at most one, since they are non-negative and sum to one
  have hle : ∀ x ∈ u, x ≤ 1 := by
    intro x hx
    have hs : u.sum = 1 := by rw [← esymm_one, hsum]
    rw [← hs]
    exact Multiset.single_le_sum h0 x hx
  set P : Polynomial ℝ := simplexPoly u with hP
  set N : ℕ := P.natDegree with hN
  have hcoeff : ∀ l, 0 ≤ P.coeff l := simplexPoly_coeff_nonneg h0 hle
  -- the two normalizations, as evaluations
  have hone : ∑ l ∈ Finset.range (N + 1), P.coeff l = 1 := by
    rw [sum_coeff_eq_eval_one (le_refl N), hP, simplexPoly_eval_one]
  have hder : ∑ l ∈ Finset.range (N + 1), (l : ℝ) * P.coeff l = 1 := by
    rw [sum_smul_coeff_eq_derivative_eval_one (le_refl N), hP,
      derivative_simplexPoly_eval_one, ← esymm_one, hsum]
  -- the root, as the vanishing of `A(-σ) + σ`
  have hmapeval : ∑ l ∈ Finset.range (N + 1), ((P.coeff l : ℝ) : ℂ) * (-σ) ^ l
      = (u.map (fun x : ℝ => (1 : ℂ) - (x : ℂ) * (1 + σ))).prod := by
    have hmap : ((P.map (algebraMap ℝ ℂ)).eval (-σ))
        = ∑ l ∈ Finset.range (N + 1), ((P.coeff l : ℝ) : ℂ) * (-σ) ^ l := by
      rw [Polynomial.eval_eq_sum_range' (n := N + 1)
        (lt_of_le_of_lt (Polynomial.natDegree_map_le) (by omega))]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Polynomial.coeff_map, Complex.coe_algebraMap]
    have hstep : ((P.map (algebraMap ℝ ℂ)).eval (-σ))
        = (u.map (fun x : ℝ => (1 : ℂ) - (x : ℂ) * (1 + σ))).prod := by
      rw [hP, simplexPoly, Polynomial.map_multiset_prod, Multiset.map_map,
        Polynomial.eval_multiset_prod, Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
      simp only [Function.comp_apply, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Complex.coe_algebraMap]
      push_cast
      ring
    rw [← hmap, hstep]
  have hvanish : (∑ l ∈ Finset.range (N + 1), ((P.coeff l : ℝ) : ℂ) * (-σ) ^ l) + σ = 0 := by
    rw [hmapeval, hroot]; ring
  -- the disk bound, and the strictly positive factor
  have hbound := norm_weighted_ge (a := fun l => P.coeff l) hcoeff hone hder hσ
  rw [hvanish, norm_zero] at hbound
  have hzero : P.coeff 0 = (u.map (fun x => 1 - x)).prod := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hP, simplexPoly_eval_zero]
  have htwo : ∑ l ∈ Finset.range (N + 1), P.coeff l * 2 ^ l
      = (u.map (fun x => 1 + x)).prod := by
    rw [← simplexPoly_eval_two u, ← hP, Polynomial.eval_eq_sum_range' (n := N + 1) (by omega)]
  have hstrict := prod_one_add_lt_of_interior h0 hsum hy hy0 hy1
  rw [hzero, htwo] at hbound
  have hpos : 0 < 2 * (u.map (fun x => 1 - x)).prod + 2 - (u.map (fun x => 1 + x)).prod := by
    linarith
  have hnorm : ‖1 + σ‖ ^ 2 ≤ 0 := by
    by_contra hcon
    exact absurd hbound (not_le.2 (mul_pos (not_le.1 hcon) hpos))
  have hz : ‖1 + σ‖ = 0 := by nlinarith [norm_nonneg (1 + σ), hnorm]
  have hzz := norm_eq_zero.1 hz
  linear_combination hzz


/-! ### The conclusion at the pencil

The substitution is `u_k = L/(a_k + L)` and `s = (w+L)/L`, so `σ = s - 1 = w/L`.
Then `1 - u_k s = (a_k - w)/(a_k + L)`, and the root condition
`∏(1 - u_k s) = 1 - s` is `L·∏(a_k - w) = -w·∏(a_k + L)`, which is the pencil
equation `Q(w) + bw = 0` at `b = Q(-L)/L` with `c` and the products divided out.

**Every division here is guarded rather than notated.**  `a_k + L > 0` and `L > 0`
are carried, because `x/0 = 0` succeeds silently in Lean and returns a nicer number
than the mathematics has.  The interiority the disk bound needs survives the
substitution in a form neither quotient shows: `u_k < 1` is `0 < a_k` and
`0 < u_k` is `0 < L`.

**And the simplex condition IS the collision equation, not a normalization.**
`ftSigmaReal a r s = ∑_k s/(a_k - s) + r` is the real critical function, and
`Σ(-L) = r - ∑_k L/(a_k+L)`.  So `∑_k u_k = 1` holds **precisely when `-L` is a real
zero of `Σ` at `r = 1`** — it is what *defines* the endpoint `L`, delivered by
`sum_div_add_eq_of_eval_ftCriticalReal_neg` from `E(-L) = 0`.  At `2 ≤ r` the
constraint would read `∑_k u_k = r` and the simplex would be the wrong object
entirely.  A reader who meets `u_k = L/(a_k+L)` cold will take the simplex
condition for a convention; it is a theorem about where `L` sits.

**Nothing here divides by `s²`.**  `s = 0` — the collision — lies INSIDE the disk
`|s-1| ≤ 2`, so forming `F(s)/s²` by division would hit `0/0` exactly there and
Lean's `x/0 = 0` would make it succeed, reporting a zero modulus and hence a root
inside the disk: the opposite of the truth.  The quotient is CONSTRUCTED instead,
by `pow_sub_one_sub_smul`, whose right-hand side is a sum and never a division —
so `norm_weighted_ge` reads `‖1+σ‖² · factor ≤ ‖…‖`, a product, and at `σ = -1` it
degenerates to `0 ≤ ‖0‖`: uninformative at the collision rather than false. -/

/-- **BANK-39's upper side, at every `n`.**  Every zero of the endpoint pencil
other than the collision at `-L` lies strictly outside the circle of radius `2L`.

`EndpointUpperOne` proves this at `n = 3` through Vieta, which works there because
the pencil has exactly ONE non-collision root so the product over the others IS the
minimum.  This route does not go through the product at all. -/
theorem two_mul_lt_norm_of_root_endpoint_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    {w : ℂ} (hw : (ftDen (ftRootPoly c a) 1
      ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).eval w = 0)
    (hne : w ≠ ((-L : ℝ) : ℂ)) :
    2 * L < ‖w‖ := by
  classical
  by_contra hcon
  have hcon' : ‖w‖ ≤ 2 * L := not_lt.1 hcon
  -- the simplex coordinates, and the guards on their denominators
  have hpos : ∀ k, 0 < a k + L := fun k => by linarith [ha k]
  set u : Multiset ℝ := (Finset.univ : Finset (Fin n)).val.map (fun k => L / (a k + L))
    with hu
  have h0 : ∀ x ∈ u, 0 ≤ x := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
    exact le_of_lt (div_pos hL (hpos k))
  -- PRODUCED, not assumed: the deficit equation is what defines `L`
  have hsum : u.esymm 1 = 1 := by
    rw [esymm_one, hu, ← Finset.sum_eq_multiset_sum]
    simpa using sum_div_add_eq_of_eval_ftCriticalReal_neg (r := 1) ha hc hL hE
  -- interiority: `u_k < 1` is `0 < a_k`, `0 < u_k` is `0 < L`
  obtain ⟨k₀⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
  have hy : L / (a k₀ + L) ∈ u := by
    rw [hu]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ k₀)
  have hy0 : 0 < L / (a k₀ + L) := div_pos hL (hpos k₀)
  have hy1 : L / (a k₀ + L) < 1 := by
    rw [div_lt_one (hpos k₀)]; linarith [ha k₀]
  -- the chart `σ = w/L`
  set σ : ℂ := w / ((L : ℝ) : ℂ) with hσdef
  have hLne : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hσ : ‖σ‖ ≤ 2 := by
    rw [hσdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
      div_le_iff₀ hL]
    linarith [hcon']
  -- the normalization: the root condition, transported
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hane : ∀ k : Fin n, ((a k : ℂ) + ((L : ℝ) : ℂ)) ≠ 0 := by
    intro k
    have : (((a k + L : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (hpos k).ne'
    push_cast at this
    exact this
  have hQL : (ftRootPolyReal c a).eval (-L) = c * ∏ k, (a k + L) := by
    rw [eval_ftRootPolyReal]
    exact congrArg (fun z => c * z) (Finset.prod_congr rfl fun k _ => by ring)
  have hbL : ((L : ℝ) : ℂ) * ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)
      = ((c : ℝ) : ℂ) * ∏ k, ((a k : ℂ) + ((L : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul]
    have hr : (L : ℝ) * (-((ftRootPolyReal c a).eval (-L)) / (-L)) = c * ∏ k, (a k + L) := by
      rw [hQL]; field_simp
    rw [hr]
    push_cast
    ring
  rw [ftDen_eval, eval_ftRootPoly, pow_one] at hw
  have hfac : ((c : ℝ) : ℂ) * (((L : ℝ) : ℂ) * (∏ k, ((a k : ℂ) - w))
      + w * ∏ k, ((a k : ℂ) + ((L : ℝ) : ℂ))) = 0 := by
    have hmul : ((L : ℝ) : ℂ) * (((c : ℝ) : ℂ) * (∏ k, ((a k : ℂ) - w))
        + ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ) * w) = 0 := by
      rw [hw, mul_zero]
    rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm ((L : ℝ) : ℂ) (((c : ℝ) : ℂ))] at hmul
    rw [mul_assoc] at hmul
    calc ((c : ℝ) : ℂ) * (((L : ℝ) : ℂ) * (∏ k, ((a k : ℂ) - w))
          + w * ∏ k, ((a k : ℂ) + ((L : ℝ) : ℂ)))
        = ((c : ℝ) : ℂ) * (((L : ℝ) : ℂ) * (∏ k, ((a k : ℂ) - w)))
          + (((L : ℝ) : ℂ) * ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)) * w := by
          rw [hbL]; ring
      _ = 0 := by linear_combination hmul
  have hpencil : ((L : ℝ) : ℂ) * (∏ k, ((a k : ℂ) - w))
      = -w * ∏ k, ((a k : ℂ) + ((L : ℝ) : ℂ)) := by
    have h2 := (mul_eq_zero.1 hfac).resolve_left hcne
    linear_combination h2
  have hroot : (u.map (fun x : ℝ => (1 : ℂ) - (x : ℂ) * (1 + σ))).prod = -σ := by
    rw [hu, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    simp only [Function.comp_apply]
    have hterm : ∀ k : Fin n, ((1 : ℂ) - ((L / (a k + L) : ℝ) : ℂ) * (1 + σ))
        = ((a k : ℂ) - w) / ((a k : ℂ) + ((L : ℝ) : ℂ)) := by
      intro k
      have hne1 : ((L : ℝ) : ℂ) + (a k : ℂ) ≠ 0 := by rw [add_comm]; exact hane k
      have hne2 : (a k : ℂ) + ((L : ℝ) : ℂ) ≠ 0 := hane k
      rw [hσdef]
      push_cast
      field
    rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_div_distrib, hσdef]
    have hprodne : (∏ k, ((a k : ℂ) + ((L : ℝ) : ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => hane k
    field_simp
    linear_combination hpencil
  have hfin := eq_neg_one_of_prod_eq_of_norm_le h0 hsum hy hy0 hy1 hσ hroot
  rw [hσdef, div_eq_iff hLne] at hfin
  exact hne (by rw [hfin]; push_cast; ring)

end ForgacsTran
