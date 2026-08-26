/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Blocks
import CubicPochhammer.Weighting
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The weighted cubic residue kernel: `J_{m,w}(t) ≥ 0`, `> 0`

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:kernel` «The cubic
residue kernel», `thm:kernel` (weighted cubic residue monotonicity) at
the level of its analytic content, the derivative numerator

  `J_{m,w}(t) = ∑_{k=1}^{m-1} w_k C(3m-2,3k-1) t^{3k-1} (k - (m-k) t)`   (`eq:Jw-def`),

which is `≥ 0` on `(0,1)` whenever the symmetric weights increase toward the
center, and the passage `eq:J-weighted` from it to `thm:kernel`'s own
conclusion: `G_{m,w}` (`eq:G-weighted`) is nondecreasing on `[0,1/2]`, strictly
increasing once the central weight is positive.

The proof pairs the terms `k ↔ m-k` into blocks `B_{m,k}` (`eq:B-def`); the
block sequence has at most one sign change (`lem:block-sign`) and sums to `J_m > 0`
(`Bernstein.jm_pos`).  The one-sign-change weighting principle
`sum_weighted_nonneg` (`Weighting.lean`) then carries positivity through the
nondecreasing weights.  The pairing and the sign change are proven, in
`Blocks.lean`, the weighting principle in `Weighting.lean`, and the
constant-weight positivity in `Bernstein.lean`.

Sorry-free, no project axioms.  The
endpoint continuity at `p = 0, 1/2` is carried by the `Set.Icc` statements
themselves: `G_{m,w}` is a polynomial, so `monotoneOn_of_hasDerivWithinAt_nonneg`
needs the derivative only on the open interval.

## Main definitions

* `jmw` --- the derivative numerator `J_{m,w}` of `eq:Jw-def`.
* `gmw` --- the weighted cubic residue kernel `G_{m,w}` of `eq:G-weighted`.
* `gmwNum` --- its numerator after the projective substitution `p = t/(1+t)`.

## Main statements

* `jmw_nonneg`, `jmw_pos` --- `J_{m,w} ≥ 0` on `(0,1)` for symmetric weights
  increasing toward the center, strictly once the central weight is positive.
* `gmw_proj`, `gmwNum_deriv_key` --- the passage `eq:J-weighted` from the
  numerator to the kernel's own derivative.
* `monotoneOn_of_proj_deriv_nonneg`, `strictMonoOn_of_proj_deriv_pos` --- the
  projective transport: the sign of the derivative of `t ↦ F(t/(1+t))` on
  `(0,1)` decides the monotonicity of `F` on `[0,1/2]`, for any `F`.
* `gmw_monotoneOn`, `gmw_strictMonoOn` --- `thm:kernel`: `G_{m,w}` is
  nondecreasing on `[0,1/2]`, strictly increasing once the central weight is
  positive.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:kernel` «The cubic residue
  kernel»: `thm:kernel`, `eq:Jw-def`, `eq:J-weighted`, `eq:G-weighted`.
-/

open scoped BigOperators

namespace CubicPochhammer

variable (m : ℕ)

/-- The weighted cubic residue kernel's derivative numerator `J_{m,w}`
(`eq:Jw-def`). -/
noncomputable def jmw (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1), w r * aterm m r t

/-- **Weighted cubic residue monotonicity** (`thm:kernel`, analytic content):
for symmetric weights nondecreasing toward the center, `J_{m,w}(t) ≥ 0` on
`(0,1)`; `gmw_monotoneOn` below turns this into the paper's `G_{m,w}`
nondecreasing on `[0,1/2]`.

The pairing identity `sum_weighted_aterm_eq_blocks` rewrites `J_{m,w}` over the
blocks, `block_sign_change` gives them a single sign change, and the weighting
principle `sum_weighted_nonneg` transfers the constant-weight positivity
`∑ B_{m,k} = J_m > 0` through the nondecreasing weights. -/
theorem jmw_nonneg (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hwnn : ∀ i, 1 ≤ i → i ≤ m / 2 → 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ jmw m w t := by
  unfold jmw
  rw [sum_weighted_aterm_eq_blocks w hm hsym t]
  have hsum_pos : 0 ≤ ∑ k ∈ Finset.range (m / 2), bblock m (k + 1) t := by
    rw [sum_blocks_eq_jm hm]
    exact (jm_pos m hm t ht0 ht1).le
  rcases block_sign_change hm ht0 ht1 with ⟨q, hq, hle, hge⟩ | hall
  · exact sum_weighted_nonneg (fun k => w (k + 1)) (fun k => bblock m (k + 1) t) (m / 2)
      (fun i j hij hjn => hwmono (i + 1) (j + 1) (by omega) (by omega) (by omega))
      (fun k hk => hwnn (k + 1) (by omega) (by omega))
      q (by omega) hle (fun k hqk hkn => hge k hqk hkn) hsum_pos
  · refine Finset.sum_nonneg fun k hk => ?_
    have hk' : k < m / 2 := Finset.mem_range.mp hk
    exact mul_nonneg (hwnn (k + 1) (by omega) (by omega)) (hall k hk')

/-- **`thm:kernel`, strict clause, analytic content**: `J_{m,w}(t) > 0` on
`(0,1)` once the central weight is positive; `gmw_strictMonoOn` below turns this
into the paper's `G_{m,w}` strictly increasing on `[0,1/2]`.  Since the weights
are nondecreasing toward the center, `w_{⌊m/2⌋}` is the largest of them, so
`0 < w_{⌊m/2⌋}` is the paper's "not all zero".

The strict weighting principle `sum_weighted_pos` supplies the conclusion from
`J_m > 0` and the positive final block `bblock_top_pos`; it needs no hypothesis
on the pivot weight, which is what lets the log-concave case through. -/
theorem jmw_pos (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hwnn : ∀ i, 1 ≤ i → i ≤ m / 2 → 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hwc : 0 < w (m / 2))
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < jmw m w t := by
  unfold jmw
  rw [sum_weighted_aterm_eq_blocks w hm hsym t]
  have hsum_pos : 0 < ∑ k ∈ Finset.range (m / 2), bblock m (k + 1) t := by
    rw [sum_blocks_eq_jm hm]
    exact jm_pos m hm t ht0 ht1
  have hidx : m / 2 - 1 + 1 = m / 2 := by omega
  have htop : 0 < bblock m (m / 2 - 1 + 1) t := by
    rw [hidx]; exact bblock_top_pos hm ht0 ht1
  have hwlast : 0 < w (m / 2 - 1 + 1) := by rw [hidx]; exact hwc
  rcases block_sign_change hm ht0 ht1 with ⟨q, hq, hle, hge⟩ | hall
  · exact sum_weighted_pos (fun k => w (k + 1)) (fun k => bblock m (k + 1) t) (m / 2)
      (fun i j hij hjn => hwmono (i + 1) (j + 1) (by omega) (by omega) (by omega))
      (fun k hk => hwnn (k + 1) (by omega) (by omega))
      q (by omega) hle (fun k hqk hkn => hge k hqk hkn) hsum_pos hwlast htop
  · refine Finset.sum_pos' (fun k hk => ?_) ⟨m / 2 - 1, Finset.mem_range.mpr (by omega), ?_⟩
    · have hk' : k < m / 2 := Finset.mem_range.mp hk
      exact mul_nonneg (hwnn (k + 1) (by omega) (by omega)) (hall k hk')
    · exact mul_pos hwlast htop

/-! ### The kernel `G_{m,w}` and the passage `eq:J-weighted` -/

/-- The weighted cubic residue kernel `G_{m,w}` (`eq:G-weighted`):
`G_{m,w}(p) = ∑_{k=1}^{m-1} w_k C(3m-2,3k-1) p^{3k}(1-p)^{3(m-k)}`. -/
noncomputable def gmw (w : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1),
    w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * p ^ (3 * r) * (1 - p) ^ (3 * (m - r))

/-- **Symmetry of the kernel** `G_{m,w}(1-p) = G_{m,w}(p)` for symmetric weights, by the
reindexing `k ↔ m-k` together with `C(3m-2,3(m-k)-1) = C(3m-2,3k-1)`
(`sec:reduction`, after `eq:G-weighted`).  This is what makes `G_{m,w}` a
function of the centrality coordinate `q = p(1-p)`, and so what `lem:beta-order`
requires of its integrand. -/
theorem gmw_symm (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) (p : ℝ) :
    gmw m w (1 - p) = gmw m w p := by
  unfold gmw
  refine Finset.sum_nbij' (fun r => m - r) (fun r => m - r) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only
    have hback : m - (m - a) = a := by omega
    have hchoose : Nat.choose (3 * m - 2) (3 * (m - a) - 1)
        = Nat.choose (3 * m - 2) (3 * a - 1) := by
      have hle : 3 * a - 1 ≤ 3 * m - 2 := by omega
      have hsub : 3 * m - 2 - (3 * a - 1) = 3 * (m - a) - 1 := by omega
      rw [← hsub, Nat.choose_symm hle]
    rw [hback, hchoose, ← hsym a h1 h2, sub_sub_cancel]
    ring

/-- The numerator of `G_{m,w}` after the projective substitution `p = t/(1+t)`. -/
noncomputable def gmwNum (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1), w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * t ^ (3 * r)

/-- `G_{m,w}` under the projective substitution `p = t/(1+t)`.  Since
`1 - t/(1+t) = 1/(1+t)` and `3k + 3(m-k) = 3m`, every summand loses its second
factor and the whole sum acquires the single denominator `(1+t)^{3m}`. -/
theorem gmw_proj (w : ℕ → ℝ) {t : ℝ} (ht : 1 + t ≠ 0) :
    gmw m w (t / (1 + t)) = gmwNum m w t / (1 + t) ^ (3 * m) := by
  unfold gmw gmwNum
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
  have hexp : 3 * m = 3 * r + 3 * (m - r) := by omega
  have hproj : (1 : ℝ) - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
  rw [hproj, hexp, pow_add, div_pow, div_pow, one_pow]
  field_simp

/-- Derivative of the numerator. -/
theorem hasDerivAt_gmwNum (w : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (gmwNum m w)
      (∑ r ∈ Finset.Icc 1 (m - 1), w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ)
        * (((3 * r : ℕ) : ℝ) * t ^ (3 * r - 1))) t := by
  unfold gmwNum
  refine HasDerivAt.fun_sum fun r _ => ?_
  simpa [mul_assoc] using (hasDerivAt_pow (3 * r) t).const_mul
    (w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ))

/-- The identity behind `eq:J-weighted`, before any division:
`(1+t)·G'_{num} - 3m·G_{num} = 3 J_{m,w}(t)`.  Termwise, `t^{3k}` factors as
`t^{3k-1}·t` and `3k(1+t) - 3mt = 3(k - (m-k)t)`. -/
theorem gmwNum_deriv_key (w : ℕ → ℝ) (t : ℝ) :
    (∑ r ∈ Finset.Icc 1 (m - 1), w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ)
        * (((3 * r : ℕ) : ℝ) * t ^ (3 * r - 1))) * (1 + t)
      - ((3 * m : ℕ) : ℝ) * gmwNum m w t
      = 3 * jmw m w t := by
  unfold gmwNum jmw
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
  have hp : t ^ (3 * r) = t ^ (3 * r - 1) * t := by
    rw [← pow_succ]; congr 1; omega
  unfold aterm
  push_cast
  rw [hp]
  ring

/-- **`eq:J-weighted`**: `d/dt G_{m,w}(t/(1+t)) = 3 J_{m,w}(t)/(1+t)^{3m+1}`.
The quotient rule on `gmw_proj` plus the numerator identity `gmwNum_deriv_key`. -/
theorem hasDerivAt_gmw_proj (hm : 1 ≤ m) (w : ℕ → ℝ) {t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (fun t : ℝ => gmw m w (t / (1 + t)))
      (3 * jmw m w t / (1 + t) ^ (3 * m + 1)) t := by
  obtain ⟨K, hK⟩ : ∃ K, 3 * m = K + 1 := ⟨3 * m - 1, by omega⟩
  have hcont : ContinuousAt (fun s : ℝ => 1 + s) t := by fun_prop
  have hnb : ∀ᶠ s in nhds t, 1 + s ≠ 0 := hcont.eventually_ne ht
  have hden : HasDerivAt (fun s : ℝ => (1 + s) ^ (3 * m))
      (((3 * m : ℕ) : ℝ) * (1 + t) ^ (3 * m - 1)) t := by
    simpa using HasDerivAt.fun_pow ((hasDerivAt_id t).const_add 1) (3 * m)
  have hdiv := (hasDerivAt_gmwNum m w t).div hden (pow_ne_zero _ ht)
  refine HasDerivAt.congr_of_eventuallyEq ?_ (hnb.mono fun s hs => gmw_proj m w hs)
  convert hdiv using 1
  have hkey := gmwNum_deriv_key m w t
  rw [hK] at hkey ⊢
  simp only [Nat.add_sub_cancel]
  rw [div_eq_div_iff (pow_ne_zero _ ht) (pow_ne_zero _ (pow_ne_zero _ ht))]
  linear_combination (-((1 + t) ^ K * (1 + t) ^ (K + 2))) * hkey

/-! ### The projective transport

The substitution `p = t/(1+t)` carries `[0,1]` monotonically onto `[0,1/2]`, so a
sign condition on the derivative of the projectivized kernel is a monotonicity
statement about the kernel itself on the paper's own interval.  Stated for an
arbitrary `F`, because the same passage runs three times: at `r = 3` in both
clauses of `thm:kernel`, and again at `r = 2` in `Multiplicity/OrderTwo.lean`.
-/

/-- The projective substitution inverted: for `0 ≤ p ≤ 1/2` the point
`t = p/(1-p)` lies in `[0,1]` and satisfies `t/(1+t) = p`. -/
theorem proj_inv_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    0 ≤ p / (1 - p) ∧ p / (1 - p) ≤ 1 ∧ (p / (1 - p)) / (1 + p / (1 - p)) = p := by
  have hd : (0 : ℝ) < 1 - p := by linarith
  refine ⟨div_nonneg hp0 hd.le, (div_le_one hd).mpr (by linarith), ?_⟩
  have hne : (1 : ℝ) - p ≠ 0 := hd.ne'
  field

/-- `p ↦ p/(1-p)` is monotone on `[0,1/2]`. -/
theorem proj_inv_mono {p q : ℝ} (hp1 : p ≤ 1 / 2) (hq1 : q ≤ 1 / 2) (hpq : p ≤ q) :
    p / (1 - p) ≤ q / (1 - q) := by
  have hdp : (0 : ℝ) < 1 - p := by linarith
  have hdq : (0 : ℝ) < 1 - q := by linarith
  rw [div_le_div_iff₀ hdp hdq]
  nlinarith

/-- `p ↦ p/(1-p)` is strictly monotone on `[0,1/2]`.  Only the upper endpoint is
constrained: `p < q ≤ 1/2` already puts `p` below the pole at `1`. -/
theorem proj_inv_strictMono {p q : ℝ} (hq1 : q ≤ 1 / 2) (hpq : p < q) :
    p / (1 - p) < q / (1 - q) := by
  have hdp : (0 : ℝ) < 1 - p := by linarith
  have hdq : (0 : ℝ) < 1 - q := by linarith
  rw [div_lt_div_iff₀ hdp hdq]
  nlinarith

/-- **Projective transport, nonstrict.**  If the projectivization
`t ↦ F(t/(1+t))` is differentiable on `[0,∞)` with a nonnegative derivative on
`(0,1)`, then `F` is nondecreasing on `[0,1/2]`.

The derivative is needed only on the open interval: continuity at the endpoints
comes from differentiability there, and the inverse substitution `p ↦ p/(1-p)`
of `proj_inv_mem` carries `[0,1/2]` into `[0,1]` monotonically. -/
theorem monotoneOn_of_proj_deriv_nonneg {F g : ℝ → ℝ}
    (hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt (fun t : ℝ => F (t / (1 + t))) (g x) x)
    (hg : ∀ x : ℝ, 0 < x → x < 1 → 0 ≤ g x) :
    MonotoneOn F (Set.Icc 0 (1 / 2)) := by
  have hproj : MonotoneOn (fun t : ℝ => F (t / (1 + t))) (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := g) (convex_Icc 0 1)
      (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt) (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hd x hx.1.le).hasDerivWithinAt
    · rw [interior_Icc] at hx
      exact hg x hx.1 hx.2
  intro p hp q hq hpq
  obtain ⟨htp0, htp1, htpe⟩ := proj_inv_mem hp.1 hp.2
  obtain ⟨htq0, htq1, htqe⟩ := proj_inv_mem hq.1 hq.2
  have := hproj (Set.mem_Icc.mpr ⟨htp0, htp1⟩) (Set.mem_Icc.mpr ⟨htq0, htq1⟩)
    (proj_inv_mono hp.2 hq.2 hpq)
  simpa only [htpe, htqe] using this

/-- **Projective transport, strict.**  The strict form of
`monotoneOn_of_proj_deriv_nonneg`: a positive derivative of the projectivization
on `(0,1)` makes `F` strictly increasing on `[0,1/2]`. -/
theorem strictMonoOn_of_proj_deriv_pos {F g : ℝ → ℝ}
    (hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt (fun t : ℝ => F (t / (1 + t))) (g x) x)
    (hg : ∀ x : ℝ, 0 < x → x < 1 → 0 < g x) :
    StrictMonoOn F (Set.Icc 0 (1 / 2)) := by
  have hproj : StrictMonoOn (fun t : ℝ => F (t / (1 + t))) (Set.Icc 0 1) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := g) (convex_Icc 0 1)
      (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt) (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hd x hx.1.le).hasDerivWithinAt
    · rw [interior_Icc] at hx
      exact hg x hx.1 hx.2
  intro p hp q hq hpq
  obtain ⟨htp0, htp1, htpe⟩ := proj_inv_mem hp.1 hp.2
  obtain ⟨htq0, htq1, htqe⟩ := proj_inv_mem hq.1 hq.2
  have := hproj (Set.mem_Icc.mpr ⟨htp0, htp1⟩) (Set.mem_Icc.mpr ⟨htq0, htq1⟩)
    (proj_inv_strictMono hq.2 hpq)
  simpa only [htpe, htqe] using this

/-- **`thm:kernel`, nonstrict clause, as the paper states it**: for symmetric
weights nondecreasing toward the center, `G_{m,w}` is nondecreasing on `[0,1/2]`.

`eq:J-weighted` (`hasDerivAt_gmw_proj`) turns the proven `jmw_nonneg` into a
nonnegative derivative of `t ↦ G_{m,w}(t/(1+t))` on `(0,1)`, and the projective
substitution carries the conclusion back to `[0,1/2]`. -/
theorem gmw_monotoneOn (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hwnn : ∀ i, 1 ≤ i → i ≤ m / 2 → 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) :
    MonotoneOn (gmw m w) (Set.Icc 0 (1 / 2)) :=
  monotoneOn_of_proj_deriv_nonneg
    (fun x hx => hasDerivAt_gmw_proj m (by omega) w (by linarith))
    (fun x hx0 hx1 => div_nonneg (by linarith [jmw_nonneg m hm w hwmono hwnn hsym x hx0 hx1])
      (pow_nonneg (by linarith) _))

/-- **`thm:kernel`, strict clause, as the paper states it**: once the central
weight is positive, `G_{m,w}` is strictly increasing on `[0,1/2]`.  Since the
weights are nondecreasing toward the center, `0 < w_{⌊m/2⌋}` is the paper's
"not all zero". -/
theorem gmw_strictMonoOn (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hwnn : ∀ i, 1 ≤ i → i ≤ m / 2 → 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hwc : 0 < w (m / 2)) :
    StrictMonoOn (gmw m w) (Set.Icc 0 (1 / 2)) :=
  strictMonoOn_of_proj_deriv_pos
    (fun x hx => hasDerivAt_gmw_proj m (by omega) w (by linarith))
    (fun x hx0 hx1 => div_pos (by linarith [jmw_pos m hm w hwmono hwnn hsym hwc x hx0 hx1])
      (pow_pos (by linarith) _))

end CubicPochhammer
