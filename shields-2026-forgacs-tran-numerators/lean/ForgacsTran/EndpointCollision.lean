/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.FTMinModulus.RealCritical
import ForgacsTran.LowerSeparationPencil

/-!
# A branch endpoint is a collision, at either end and at every `r`

Both ends of the viewing arc are governed by the same identity.  The paper takes
`t_a > 0` to be the smallest positive critical point of `g = -Q/t^r` and `t_b < 0`
the negative one, and the branch radius runs into one at each end.  A critical
point of `g` off the origin is a zero of `E = XQ' - rQ`, and there the pencil at
the branch's own spectral value acquires a **double** root.

That is one lemma, not two: `EndpointUpperOne`'s `r = 1` upper endpoint at `-L`
and the lower endpoint at `t_a` are the same statement at different critical
points.  Nothing about the sign of the point, the value of `r`, or the
multiplicity of the smallest zero enters.

**The rule the two endpoints obey.**  Every ingredient that transfers between
them is *position-free* — its statement says nothing about where the point sits
among the zeros.  `Σ' = \sum_k a_k/(a_k - s)^2 > 0` is position-free, and it
transfers.  Every ingredient that fails carries a hidden assumption about
position: `Q'' > 0` needs the negative axis, Vieta's degree count needs `n > r`,
the AM-GM slack needs all terms positive, and a literal separating radius needs a
uniform constant that exists at one end and not the other.  When deciding what to
reuse across the two endpoints, that is the test — not whether the geometry looks
alike, which it does.

**What does not generalize with it.**  Raising the lower bound to an equality —
multiplicity *exactly* two — is a separate question, and at the upper endpoint
`EndpointUpperOne` settles it by a sign argument that works only on the negative
axis, where every factor `a_k - t` of `Q` is positive.  The lower endpoint's
collision sits at `t_a`, which is **above** the smallest zero (`t_a = 1.371`
against `x_1 = 1` at `a = (1,2,4)`, `r = 1`), so `Q` changes sign there and that
argument does not apply.  The two ends share this lemma and diverge immediately
after it.

## Main statements

The collision is one theorem; the rest of the file is three further layers, each
under its own section heading and each about a different object.  They are named
here so a reader is not misled into taking the collision for the whole subject.
The `ρ = 1` normalized separation was a fourth and is now
`LowerSeparationPencil`, which this module imports because the last layer below
uses its boundary identity.

* `two_le_rootMultiplicity_ftDen_at_critical` — the collision, at any nonzero
  critical point and any `r ≥ 1`.  This is the module's title, and the only
  statement in it that both endpoints share.

Then, in order:

* **`Σ` and the bracket.**  `hasDerivAt_ftSigmaReal`, `sum_div_sq_pos` — the
  critical function's derivative and its positivity, which is position-free and so
  transfers between the two endpoints; then `exists_ftSigmaReal_eq_zero_between`
  and its supporting sign lemmas, which place `t_a` in the first gap.
* **The clearance.**  `two_le_prod_add_div_of_sum_inv_eq` and
  `clearance_ge_relative_gap` at `n = 3`, `clearance_ge_relative_gap_of_r_general`
  by a two-index reduction at every `n`, and `clearance_ge_sub_two_mul_relative_gap`
  with the sharp constant `n - 2`.  The last needs every zero and the reduction
  cannot reach it; § The sharp constant says why, with the measured table.
  `one_add_sum_le_prod_one_add` and `sq_card_le_sum_mul_sum_inv` (AM–HM) are its
  two general ingredients.
* **The second derivative at a collision.**  `eval_derivative_ftCritical` through
  `rootMultiplicity_ftDen_eq_two_at_critical` — the collision is exactly double
  wherever `Σ' ≠ 0`, with no numerator entering.
* **The indented contour's geometry.**  `one_le_norm_one_add_arc` places the
  indentation outside the unit circle; `modInterp` is the modulus-interpolating
  homotopy and `norm_modInterp` through `modInterp_of_norm_one` are its moduli;
  `one_le_re_one_sub_mul` and `re_one_sub_mul_neg` separate the one factor that
  winds from the rest.  **This is an abandoned route**: the tree counts on an
  un-indented circle instead, so nothing here has a consumer and nothing here
  states a paper step — the manuscript has no argument principle in it at all, so
  this is not a divergence from the paper's route but a formalization route that
  lost to `LowerSeparationQuotient`'s.  It is kept because each fact is exact,
  each says which part of the indented route it holds, and each is pinned by an
  axiom guard.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `thm:weighted-dominance`, `subsec:proof`.

## Tags

branch endpoint, critical point, double root, collision
-/

namespace ForgacsTran

open Polynomial

/-- **A nonzero critical point of `g` is a double root of the pencil there.**
With `b = -Q(t)/t^r` — the branch's own spectral value at `t` — the point `t` is a
root of `D(·,b)` because `b` was chosen to make it one, and a root of the
derivative because `E(t) = tQ'(t) - rQ(t) = 0` says exactly
`Q'(t) = rQ(t)/t = -b r t^{r-1}`.

`t ≠ 0` is what lets `E(t) = 0` be divided back into the derivative, and `1 ≤ r`
is what keeps the origin off the pencil, which is how the pencil is seen to be
nonzero. -/
theorem two_le_rootMultiplicity_ftDen_at_critical {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 1 ≤ r) {t : ℝ} (ht : t ≠ 0)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval t = 0) :
    2 ≤ (ftDen (ftRootPoly c a) r
        ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ)).rootMultiplicity
      ((t : ℝ) : ℂ) := by
  classical
  set P : Polynomial ℝ := ftRootPolyReal c a with hP
  set b : ℝ := -(P.eval t) / t ^ r with hb
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have htr : (t : ℝ) ^ r ≠ 0 := pow_ne_zero _ ht
  have hmap : ftRootPoly c a = P.map (algebraMap ℝ ℂ) := by
    rw [hP, ftRootPoly, ftRootPolyReal, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_prod]
    simp
  have hval : (ftRootPoly c a).eval ((t : ℝ) : ℂ) = ((P.eval t : ℝ) : ℂ) := by
    rw [hmap, Polynomial.eval_map]
    simpa using Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) (t : ℝ)
  have hdval : (derivative (ftRootPoly c a)).eval ((t : ℝ) : ℂ)
      = (((derivative P).eval t : ℝ) : ℂ) := by
    rw [hmap, Polynomial.derivative_map, Polynomial.eval_map]
    simpa using Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) (t : ℝ)
  -- `E(t) = 0` in the form the derivative needs
  have hEr : t * (derivative P).eval t - r * P.eval t = 0 := by simpa using hE
  have hdb : (derivative P).eval t + b * r * t ^ (r - 1) = 0 := by
    have hsplit : (t : ℝ) ^ r = t ^ (r - 1) * t := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hb, hsplit]
    field_simp
    nlinarith [hEr]
  have hDne : ftDen (ftRootPoly c a) r ((b : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hev : (ftDen (ftRootPoly c a) r ((b : ℝ) : ℂ)).eval 0
        = (ftRootPoly c a).eval 0 := by
      rw [ftDen_eval, zero_pow (by omega : r ≠ 0), mul_zero, add_zero]
    rw [h0] at hev
    simp only [Polynomial.eval_zero] at hev
    refine absurd hev.symm ?_
    rw [eval_ftRootPoly]
    exact mul_ne_zero (by exact_mod_cast hc)
      (Finset.prod_ne_zero_iff.2 fun k _ => by
        simpa using (by exact_mod_cast (ha k).ne' : ((a k : ℝ) : ℂ) ≠ 0))
  refine (Polynomial.one_lt_rootMultiplicity_iff_isRoot hDne).2 ⟨?_, ?_⟩
  · rw [Polynomial.IsRoot, ftDen_eval, hval, hb]
    push_cast
    field
  · rw [Polynomial.IsRoot, eval_derivative_ftDen_eq, hdval]
    exact_mod_cast hdb

/-! ### `Σ` is strictly increasing, as a derivative

`FTMinModulus.RealCritical.ftSigmaReal_lt_of_lt` records that `Σ` increases on the
negative axis.  What the collision needs is the *derivative*, and it is positive
wherever `Σ` is defined at all — no hypothesis on the sign of `s`:

`Σ(s) = \sum_k s/(a_k - s) + r`, so `Σ'(s) = \sum_k a_k/(a_k - s)^2`,

a sum of positive terms because every `a_k > 0`.  The squares in the denominators
are what make the sign independent of where `s` sits relative to the zeros, which
is exactly why this serves the lower endpoint — where the collision point `t_a`
lies *above* the smallest zero — as well as the upper one.

This is the second half of a pair the tree already had: monotonicity was there,
the derivative was not. -/

/-- **`Σ'(s) = \sum_k a_k/(a_k - s)^2`.**  Termwise: `d/ds [s/(a-s)] = a/(a-s)^2`,
the numerator `(a-s) + s` collapsing to `a`. -/
theorem hasDerivAt_ftSigmaReal {n : ℕ} {a : Fin n → ℝ} {r : ℕ} {s : ℝ}
    (h : ∀ k, a k - s ≠ 0) :
    HasDerivAt (ftSigmaReal a r) (∑ k, a k / (a k - s) ^ 2) s := by
  classical
  have hterm : ∀ k : Fin n,
      HasDerivAt (fun u : ℝ => u / (a k - u)) (a k / (a k - s) ^ 2) s := by
    intro k
    have hu : HasDerivAt (fun u : ℝ => u) 1 s := hasDerivAt_id s
    have hv : HasDerivAt (fun u : ℝ => a k - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (a k)
    have hd := hu.fun_div hv (h k)
    have hnum : (1 : ℝ) * (a k - s) - s * (-1) = a k := by ring
    rw [hnum] at hd
    exact hd
  have hsum : HasDerivAt (fun u : ℝ => ∑ k, u / (a k - u))
      (∑ k, a k / (a k - s) ^ 2) s := HasDerivAt.fun_sum fun k _ => hterm k
  have hfun : ftSigmaReal a r = fun u : ℝ => (∑ k, u / (a k - u)) + (r : ℝ) := by
    funext u
    rw [ftSigmaReal]
  rw [hfun]
  exact hsum.add_const (r : ℝ)

/-- **The derivative is strictly positive**, wherever `Σ` is defined: every term is
`a_k/(a_k - s)^2` with `a_k > 0` and the denominator a nonzero square.  Nothing is
assumed about the sign of `s` or about where it sits among the zeros. -/
theorem sum_div_sq_pos {n : ℕ} {a : Fin n → ℝ} {s : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (h : ∀ k, a k - s ≠ 0) :
    0 < ∑ k, a k / (a k - s) ^ 2 := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  refine Finset.sum_pos (fun k _ => ?_) hne
  have hsq : 0 < (a k - s) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (h k)))
  exact div_pos (ha k) hsq

/-! ### The clearance at the lower endpoint, in the normalized variables

The lower endpoint has no uniform clearance constant — `∏a_k/t_a^3` has infimum
`1`, unattained.  What it does have is a bound in terms of the **relative** gap
between the two smallest zeros, and normalizing by `t_a` removes the pencil from
the statement entirely.

Put `w_k = a_k/t_a`.  Then `Σ(t_a) = 0` reads `∑_k 1/(w_k - 1) = -r`, the
clearance ratio `∏a_k/t_a^3` is `∏ w_k`, and the relative gap `(x_2 - x_1)/x_2` is
`1 - w_1/w_2`.  So `∏a_k/t_a^3 - 1 ≥ (x_2 - x_1)/x_2` becomes the inequality
below, with `w_1 < 1 < w_2` saying exactly that `t_a` lies between the two
smallest zeros.

The bound is **sharp at first order**: on `a = (1, 1+g, 1+g)` one has
`w_1 ≈ 1 - g/2` and `w_2 = w_3 ≈ 1 + g`, and the left side is `2 + O(g^2)`.  So
the `2` is attained in the limit and nothing lossy can be inserted. -/

/-- **The lower endpoint's clearance, as a bare inequality in three reals.**
`w₁w₂w₃ + w₁/w₂ ≥ 2` under `∑ 1/(wₖ - 1) = -1`, with `w₁ < 1 < w₂ ≤ w₃`.

This is `∏a_k/t_a^3 - 1 ≥ (x_2 - x_1)/x_2` with the pencil normalized away — no
polynomial, no root of `E`, and no branch.  Stating it over three reals rather
than over pencils is what makes it reachable: the pencil form is a statement about
the smallest positive zero of `E`, and this one is algebra. -/
theorem two_le_prod_add_div_of_sum_inv_eq {w₁ w₂ w₃ : ℝ}
    (h1 : 0 < w₁) (h1' : w₁ < 1) (h2 : 1 < w₂) (h23 : w₂ ≤ w₃)
    (hc : 1 / (w₁ - 1) + 1 / (w₂ - 1) + 1 / (w₃ - 1) = -1) :
    2 ≤ w₁ * w₂ * w₃ + w₁ / w₂ := by
  have hn1 : w₁ - 1 < 0 := by linarith
  have hp2 : (0 : ℝ) < w₂ - 1 := by linarith
  have hp3 : (0 : ℝ) < w₃ - 1 := by linarith
  have hw2 : (0 : ℝ) < w₂ := by linarith
  have hne1 : w₁ - 1 ≠ 0 := ne_of_lt hn1
  have hne2 : w₂ - 1 ≠ 0 := ne_of_gt hp2
  have hne3 : w₃ - 1 ≠ 0 := ne_of_gt hp3
  have hpoly : (w₂ - 1) * (w₃ - 1) + (w₁ - 1) * (w₃ - 1) + (w₁ - 1) * (w₂ - 1)
      = -((w₁ - 1) * (w₂ - 1) * (w₃ - 1)) := by
    field_simp at hc
    nlinarith [hc]
  rw [show w₁ * w₂ * w₃ + w₁ / w₂ = (w₁ * w₂ ^ 2 * w₃ + w₁) / w₂ by field_simp,
    le_div_iff₀ hw2]
  nlinarith [hpoly, sq_nonneg (w₂ - w₃), sq_nonneg (w₂ * w₃ - 1), sq_nonneg (w₁ - 1),
    mul_pos hp2 hp3, mul_pos hw2 hp3, h1, h1', h2, h23, sq_nonneg (w₂ - 1),
    mul_nonneg (le_of_lt hp2) (sub_nonneg.2 h23)]

/-- **The clearance at the lower endpoint, in the pencil's own terms.**  Given the
bracket `a₀ < t < a₁ ≤ a₂` — which is what `Σ` increasing already delivers, since
`Σ(0) = r > 0` puts no root below `a₀` and the poles at `a₀` and `a₁` trap exactly
one between them — the clearance ratio `∏aₖ/t³` exceeds `1` by at least the
**relative** gap `(a₁ - a₀)/a₁`.

The three translations are `1/(wₖ - 1) = t/(aₖ - t)`, `∏wₖ = ∏aₖ/t³`, and
`w₀/w₁ = a₀/a₁`, at `wₖ = aₖ/t`.  Everything quantitative is
`two_le_prod_add_div_of_sum_inv_eq`; this only removes the normalization.

The bracket is doing real work and cannot be replaced by "a root of `Q` is a pole
of `Σ`": that is true in `ℝ` and **false in Lean**, where `aⱼ/0 = 0` makes `Σ`
finite at a zero of `Q` — at `a = (1, 3, 1/3)`, `r = 1`, `Σ(1) = 0` at `1 = a₀`.
The strict inequalities below are what keep `t` off every zero. -/
theorem clearance_ge_relative_gap {a : Fin 3 → ℝ} {t : ℝ}
    (ht : 0 < t) (h0 : 0 < a 0) (h01 : a 0 < t) (h1t : t < a 1) (h12 : a 1 ≤ a 2)
    (hSig : ftSigmaReal a 1 t = 0) :
    (a 1 - a 0) / a 1 ≤ a 0 * a 1 * a 2 / t ^ 3 - 1 := by
  have hne : ∀ k : Fin 3, a k - t ≠ 0 := by
    intro k
    fin_cases k
    · exact sub_ne_zero.2 (ne_of_lt h01)
    · exact sub_ne_zero.2 (ne_of_gt h1t)
    · exact sub_ne_zero.2 (ne_of_gt (lt_of_lt_of_le h1t h12))
  have ha1 : 0 < a 1 := lt_trans ht h1t
  -- the three normalized variables
  set w : Fin 3 → ℝ := fun k => a k / t with hw
  have hwsub : ∀ k : Fin 3, w k - 1 = (a k - t) / t := by
    intro k; rw [hw]; field_simp
  have hinv : ∀ k : Fin 3, 1 / (w k - 1) = t / (a k - t) := by
    intro k
    rw [hwsub k, one_div_div]
  -- the constraint, translated
  have hc : 1 / (w 0 - 1) + 1 / (w 1 - 1) + 1 / (w 2 - 1) = -1 := by
    rw [hinv 0, hinv 1, hinv 2]
    have h := hSig
    rw [ftSigmaReal, Fin.sum_univ_three] at h
    linarith
  -- the ordering, translated
  have hw0 : 0 < w 0 := div_pos h0 ht
  have hw0' : w 0 < 1 := by rw [hw, div_lt_one ht]; exact h01
  have hw1 : 1 < w 1 := by rw [hw, lt_div_iff₀ ht]; linarith
  have hw12 : w 1 ≤ w 2 := by
    rw [hw]
    exact div_le_div_of_nonneg_right h12 ht.le
  have hkey := two_le_prod_add_div_of_sum_inv_eq hw0 hw0' hw1 hw12 hc
  -- and back
  have hprod : w 0 * w 1 * w 2 = a 0 * a 1 * a 2 / t ^ 3 := by
    rw [hw]; field_simp
  have hratio : w 0 / w 1 = a 0 / a 1 := by
    rw [hw]; field_simp
  rw [hprod, hratio] at hkey
  have hgap : (a 1 - a 0) / a 1 = 1 - a 0 / a 1 := by field_simp
  rw [hgap]
  linarith

/-- **The clearance at every `r ≥ 1`.**  `two_le_prod_add_div_of_sum_inv_eq` is
this at `r = 1`, which is the tightest case: the constraint enters only through
`S₂ + P ≥ 0`, where `S₂` is the sum of the pairwise products of `wₖ - 1` and `P`
their product.  At `r = 1` the constraint gives that as an *equation*; at `r ≥ 1`
it gives the inequality, since `P < 0` and `S₂ = -rP` grows with `r`.  So the
slack grows with `r`.

Whether the `r = 1` proof survived the extra parameter was **tested, not
inferred** — the hint set does not carry `-r`, and what makes it go through is
replacing the equation by the one-sided fact it was always used through.

`Σ(t_a) = 0` is `∑ₖ 1/(wₖ - 1) = -r` at `wₖ = aₖ/t_a`, so this is the form the
lower endpoint needs at `r ≥ 2`.  Reading it as a *clearance* needs Vieta, which
wants `deg D = n`, i.e. `n > r`: at `n = 3` that holds for `r = 1, 2` and fails at
`r = 3`, where the leading coefficient picks up the spectral parameter. -/
theorem two_le_prod_add_div_of_sum_inv_eq_neg {w₁ w₂ w₃ r : ℝ} (hr : 1 ≤ r)
    (h1 : 0 < w₁) (h1' : w₁ < 1) (h2 : 1 < w₂) (h23 : w₂ ≤ w₃)
    (hc : 1 / (w₁ - 1) + 1 / (w₂ - 1) + 1 / (w₃ - 1) = -r) :
    2 ≤ w₁ * w₂ * w₃ + w₁ / w₂ := by
  have hn1 : w₁ - 1 < 0 := by linarith
  have hp2 : (0 : ℝ) < w₂ - 1 := by linarith
  have hp3 : (0 : ℝ) < w₃ - 1 := by linarith
  have hw2 : (0 : ℝ) < w₂ := by linarith
  have hne1 : w₁ - 1 ≠ 0 := ne_of_lt hn1
  have hne2 : w₂ - 1 ≠ 0 := ne_of_gt hp2
  have hne3 : w₃ - 1 ≠ 0 := ne_of_gt hp3
  have hpoly : (w₂ - 1) * (w₃ - 1) + (w₁ - 1) * (w₃ - 1) + (w₁ - 1) * (w₂ - 1)
      = -r * ((w₁ - 1) * (w₂ - 1) * (w₃ - 1)) := by
    field_simp at hc
    linear_combination hc
  have hPneg : (w₁ - 1) * ((w₂ - 1) * (w₃ - 1)) < 0 :=
    mul_neg_of_neg_of_pos hn1 (mul_pos hp2 hp3)
  have hge : (w₂ - 1) * (w₃ - 1) + (w₁ - 1) * (w₃ - 1) + (w₁ - 1) * (w₂ - 1)
      + (w₁ - 1) * (w₂ - 1) * (w₃ - 1) ≥ 0 := by
    have h1r : (r - 1) * (-((w₁ - 1) * (w₂ - 1) * (w₃ - 1))) ≥ 0 := by
      apply mul_nonneg (by linarith)
      nlinarith [hPneg]
    nlinarith [hpoly, h1r]
  rw [show w₁ * w₂ * w₃ + w₁ / w₂ = (w₁ * w₂ ^ 2 * w₃ + w₁) / w₂ by field_simp,
    le_div_iff₀ hw2]
  nlinarith [hge, sq_nonneg (w₂ - w₃), sq_nonneg (w₂ * w₃ - 1), sq_nonneg (w₁ - 1),
    mul_pos hp2 hp3, mul_pos hw2 hp3, h1, h1', h2, h23, sq_nonneg (w₂ - 1),
    mul_nonneg (le_of_lt hp2) (sub_nonneg.2 h23), hr,
    mul_nonneg (mul_nonneg (le_of_lt hp2) (le_of_lt hp3)) (sub_nonneg.2 hr)]

/-- **`Σ > 0` at or below the smallest zero**, so no root of `Σ` lies in
`(0, x₁]` and every positive root exceeds the smallest zero.

This is the lower half of the bracket, and it needs neither monotonicity nor the
poles: for `0 < s ≤ x₁` every term `s/(a_k - s)` is **nonnegative** — positive
when `a_k > s`, and exactly `0` when `a_k = s`, since Lean's `x/0 = 0` sends that
term to zero rather than to a pole — and `r ≥ 1` is added on top.

The `x/0 = 0` convention, which has been a trap all along here, is for once
harmless: it can only *remove* a term from the sum, and every term it could remove
was nonnegative anyway.  At `s = x₁` exactly one term vanishes that way and the
rest are strictly positive, so the conclusion is strict with room. -/
theorem ftSigmaReal_pos_of_le_lower {n : ℕ} {a : Fin n → ℝ} {r : ℕ} (hr : 1 ≤ r)
    {m s : ℝ} (hmin : ∀ k, m ≤ a k) (hs : 0 < s) (hsm : s ≤ m) :
    0 < ftSigmaReal a r s := by
  classical
  have hterm : ∀ k : Fin n, 0 ≤ s / (a k - s) := by
    intro k
    rcases eq_or_lt_of_le (le_trans hsm (hmin k)) with h | h
    · rw [← h]
      simp
    · exact le_of_lt (div_pos hs (by linarith))
  have hsum : 0 ≤ ∑ k, s / (a k - s) := Finset.sum_nonneg fun k _ => hterm k
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rw [ftSigmaReal]
  linarith

/-- **Every positive root of `Σ` exceeds the smallest zero.**  Immediate from
`ftSigmaReal_pos_of_le_lower`, and it is the hypothesis `a₀ < t` that
`clearance_ge_relative_gap` takes. -/
theorem lt_of_ftSigmaReal_eq_zero {n : ℕ} {a : Fin n → ℝ} {r : ℕ} (hr : 1 ≤ r)
    {m t : ℝ} (hmin : ∀ k, m ≤ a k) (ht : 0 < t) (hSig : ftSigmaReal a r t = 0) :
    m < t := by
  by_contra hle
  rw [not_lt] at hle
  exact absurd hSig (ne_of_gt (ftSigmaReal_pos_of_le_lower hr hmin ht hle))

/-- **`Σ > 0` at the midpoint of the two smallest zeros.**  The two straddling
terms cancel *identically*: at `s = (a₀+a₁)/2` the `a₀` term is `-2s/(a₁-a₀)` and
the `a₁` term is `+2s/(a₁-a₀)`.  What is left is `r` plus the outer terms, every
one positive because `aₖ ≥ a₁ > s`.

No bound and no limit — the same species as `Q''` being a sum of positive terms.
It also survives `a₁` being repeated, since a second `a₁` contributes another
`+2s/(a₁-a₀)` against the single negative one.

This is the upper endpoint of an IVT interval whose **both** ends are evaluated,
so the bracket never mentions a pole — which matters here beyond convenience,
because `x/0 = 0` has already made one pole argument false in this tree. -/
theorem ftSigmaReal_pos_at_midpoint {a : Fin 3 → ℝ} {r : ℕ} (hr : 1 ≤ r)
    (h0 : 0 < a 0) (h01 : a 0 < a 1) (h12 : a 1 ≤ a 2) :
    0 < ftSigmaReal a r ((a 0 + a 1) / 2) := by
  classical
  have hs0 : 0 < (a 0 + a 1) / 2 := by linarith
  have hg : 0 < (a 1 - a 0) / 2 := by linarith
  have hd0 : a 0 - (a 0 + a 1) / 2 = -((a 1 - a 0) / 2) := by ring
  have hd1 : a 1 - (a 0 + a 1) / 2 = (a 1 - a 0) / 2 := by ring
  have hcancel : (a 0 + a 1) / 2 / (a 0 - (a 0 + a 1) / 2)
      + (a 0 + a 1) / 2 / (a 1 - (a 0 + a 1) / 2) = 0 := by
    rw [hd0, hd1, div_neg]
    ring
  have hd2 : 0 < a 2 - (a 0 + a 1) / 2 := by linarith
  have ht2 : 0 < (a 0 + a 1) / 2 / (a 2 - (a 0 + a 1) / 2) := div_pos hs0 hd2
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rw [ftSigmaReal, Fin.sum_univ_three]
  linarith [hcancel, ht2]

/-- **`Σ < 0` just above the smallest zero.**  At `s = a₀ + g/K` with
`g = a₁ - a₀` and `K = 5 + 2rg/a₀`, the `a₀` term is `-sK/g` and the other two are
each at most `sK/(g(K-1))`, so `K` chosen this way forces the sum negative.

Explicit, so this is the *lower* endpoint of an IVT interval whose both ends are
evaluated.  Together with `ftSigmaReal_pos_at_midpoint` the bracket needs no limit
at either end and never mentions a pole. -/
theorem neg_near_lower {a : Fin 3 → ℝ} {r : ℕ} (hr : 1 ≤ r)
    (h0 : 0 < a 0) (h01 : a 0 < a 1) (h12 : a 1 ≤ a 2) :
    ftSigmaReal a r (a 0 + (a 1 - a 0) / (5 + 2 * r * (a 1 - a 0) / a 0)) < 0 := by
  classical
  have hg : 0 < a 1 - a 0 := by linarith
  have hrpos : (0:ℝ) < r := by exact_mod_cast hr
  set g : ℝ := a 1 - a 0 with hgdef
  set K : ℝ := 5 + 2 * r * g / a 0 with hKdef
  have hKextra : 0 < 2 * r * g / a 0 := by positivity
  have hK5 : 5 ≤ K := by rw [hKdef]; linarith
  have hKp : 0 < K := by linarith
  have hK1 : 0 < K - 1 := by linarith
  have hK3 : 0 < K - 3 := by linarith
  have hKa : a 0 * (K - 3) = 2 * a 0 + 2 * r * g := by
    rw [hKdef]; field
  set s : ℝ := a 0 + g / K with hsdef
  have hgKpos : 0 < g / K := div_pos hg hKp
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsa0 : a 0 < s := by rw [hsdef]; linarith
  have hgK : g / K < g := by rw [div_lt_iff₀ hKp]; nlinarith
  have hsa1 : s < a 1 := by rw [hsdef]; rw [hgdef] at hgK ⊢; linarith
  have hd1 : 0 < a 1 - s := by linarith
  have hd2 : 0 < a 2 - s := by linarith
  have hgK1 : (0:ℝ) < g * (K - 1) := by positivity
  -- the polynomial core
  have step1 : r * g * (K - 1) < r * g * K := by nlinarith [hrpos, hg, hKp]
  have step2 : r * g * K ≤ a 0 * (K - 3) * K := by
    rw [hKa]; nlinarith [h0, hrpos, hg, hKp]
  have step3 : a 0 * (K - 3) * K < s * K * (K - 3) := by
    nlinarith [mul_pos (mul_pos (sub_pos.2 hsa0) hKp) hK3]
  have hpoly : r * g * (K - 1) < s * K * (K - 3) := by linarith
  -- the two straddling terms
  have ht0 : s / (a 0 - s) = -(s * K / g) := by
    have : a 0 - s = -(g / K) := by rw [hsdef]; ring
    rw [this]; field_simp
  have hd1eq : a 1 - s = g * (K - 1) / K := by
    rw [hsdef, hgdef] at *; field
  have ht1 : s / (a 1 - s) = s * K / (g * (K - 1)) := by rw [hd1eq]; field_simp
  have hle : s / (a 2 - s) ≤ s / (a 1 - s) :=
    div_le_div_of_nonneg_left hs0.le hd1 (by linarith)
  have hkey : -(s * K / g) + 2 * (s * K / (g * (K - 1))) + r < 0 := by
    rw [show -(s * K / g) + 2 * (s * K / (g * (K - 1))) + r
        = (-(s * K * (K - 1)) + 2 * (s * K) + r * (g * (K - 1))) / (g * (K - 1)) by
      field_simp]
    exact div_neg_of_neg_of_pos (by nlinarith [hpoly]) hgK1
  rw [ftSigmaReal, Fin.sum_univ_three, ht0]
  rw [ht1] at hle
  linarith [hle, hkey]

/-- **The bracket: `Σ` has a root strictly between the two smallest zeros.**
Intermediate value on `[a₀ + g/K, (a₀+a₁)/2]`, whose two ends are the explicit
sign evaluations above.  No limit, no pole, and no Rolle.

With `lt_of_ftSigmaReal_eq_zero` — which puts every positive root above `a₀` — this
is the hypothesis pair `a₀ < t`, `t < a₁` that `clearance_ge_relative_gap` takes. -/
theorem exists_ftSigmaReal_eq_zero_between {a : Fin 3 → ℝ} {r : ℕ} (hr : 1 ≤ r)
    (h0 : 0 < a 0) (h01 : a 0 < a 1) (h12 : a 1 ≤ a 2) :
    ∃ t, a 0 < t ∧ t < a 1 ∧ ftSigmaReal a r t = 0 := by
  classical
  have hg : 0 < a 1 - a 0 := by linarith
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  set K : ℝ := 5 + 2 * r * (a 1 - a 0) / a 0 with hKdef
  have hKextra : 0 < 2 * r * (a 1 - a 0) / a 0 := by positivity
  have hKp : 0 < K := by rw [hKdef]; linarith
  set lo : ℝ := a 0 + (a 1 - a 0) / K with hlo
  set hi : ℝ := (a 0 + a 1) / 2 with hhi
  have hgK : 0 < (a 1 - a 0) / K := div_pos hg hKp
  have hlo0 : a 0 < lo := by rw [hlo]; linarith
  have hgKlt : (a 1 - a 0) / K < (a 1 - a 0) / 2 := by
    apply div_lt_div_of_pos_left hg (by norm_num)
    rw [hKdef]; linarith
  have hlohi : lo < hi := by rw [hlo, hhi]; linarith
  have hhi1 : hi < a 1 := by rw [hhi]; linarith
  -- continuity on the closed interval, where no denominator vanishes
  have hne : ∀ s ∈ Set.Icc lo hi, ∀ k : Fin 3, a k - s ≠ 0 := by
    intro s hs k
    have hsl : a 0 < s := lt_of_lt_of_le hlo0 hs.1
    have hsr : s < a 1 := lt_of_le_of_lt hs.2 hhi1
    fin_cases k
    · change a 0 - s ≠ 0
      exact sub_ne_zero.2 (ne_of_lt hsl)
    · change a 1 - s ≠ 0
      exact sub_ne_zero.2 (ne_of_gt hsr)
    · change a 2 - s ≠ 0
      exact sub_ne_zero.2 (ne_of_gt (lt_of_lt_of_le hsr h12))
  have hcont : ContinuousOn (ftSigmaReal a r) (Set.Icc lo hi) := by
    have hterm : ∀ k : Fin 3,
        ContinuousOn (fun s : ℝ => s / (a k - s)) (Set.Icc lo hi) := by
      intro k
      exact continuousOn_id.div (continuousOn_const.sub continuousOn_id)
        (fun s hs => hne s hs k)
    have hsum : ContinuousOn (fun s : ℝ => ∑ k, s / (a k - s)) (Set.Icc lo hi) :=
      continuousOn_finsetSum _ fun k _ => hterm k
    have hfun : ftSigmaReal a r = fun u : ℝ => (∑ k, u / (a k - u)) + (r : ℝ) := by
      funext u
      rw [ftSigmaReal]
    rw [hfun]
    exact hsum.add continuousOn_const
  have hlt := neg_near_lower hr h0 h01 h12
  have hgt := ftSigmaReal_pos_at_midpoint hr h0 h01 h12
  have hmem : (0 : ℝ) ∈ Set.Icc (ftSigmaReal a r lo) (ftSigmaReal a r hi) :=
    ⟨le_of_lt hlt, le_of_lt hgt⟩
  obtain ⟨t, ht, hteq⟩ :=
    intermediate_value_Icc (le_of_lt hlohi) hcont hmem
  exact ⟨t, lt_of_lt_of_le hlo0 ht.1, lt_of_le_of_lt ht.2 hhi1, hteq⟩

/-! ### The second derivative at a collision, without the numerator

`Geometry.ftCritical_ftDen` already records that `E = XQ' - rQ` is unchanged by
the pencil — the `z t^r` terms cancel exactly, so `E` is the *same polynomial* for
`D(·,z)` at every `z`.  Differentiating that identity gives
`E' = X·D'' + (1-r)·D'`, and at a **double** root the second term drops:

`D''(t) = E'(t)/t`,  for every `r ≥ 1` and every `t ≠ 0`.

This is what makes the multiplicity question independent of `z` and of the sign of
`t`: `Q''` never appears, so the negative-axis argument that settles the upper
endpoint is not needed at the lower one, where it would not apply. -/
theorem eval_derivative_ftCritical {D : Polynomial ℂ} {r : ℕ} (t : ℂ) :
    (derivative (ftCritical D r)).eval t
      = t * (derivative (derivative D)).eval t + (1 - (r : ℂ)) * (derivative D).eval t := by
  rw [ftCritical, derivative_sub, derivative_mul, derivative_X, derivative_C_mul]
  simp
  ring

theorem eval_derivative_two_ftDen_of_double_root {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {z t : ℂ} (ht : t ≠ 0) (hd : (derivative (ftDen Q r z)).eval t = 0) :
    (derivative (derivative (ftDen Q r z))).eval t
      = (derivative (ftCritical Q r)).eval t / t := by
  have h := eval_derivative_ftCritical (D := ftDen Q r z) (r := r) t
  rw [ftCritical_ftDen Q hr z, hd, mul_zero, add_zero] at h
  rw [eq_div_iff ht]
  linear_combination -h


/-- **`E'` at a zero of `Σ`.**  Differentiating `E = -Σ·Q` where it holds — on a
neighbourhood of `t`, since only the finitely many `a_k` are excluded — gives
`E' = -Σ'·Q - Σ·Q'`, and the second term drops at a zero of `Σ`.

Combined with `eval_derivative_two_ftDen_of_double_root` this is the whole
multiplicity question: `D''(t) = E'(t)/t = -Σ'(t)Q(t)/t`, with `Σ' > 0` from
`sum_div_sq_pos` and `Q(t) ≠ 0` from the bracket. -/
theorem eval_derivative_ftCriticalReal_of_ftSigmaReal_eq_zero {n : ℕ} {a : Fin n → ℝ}
    {c : ℝ} {r : ℕ} {t : ℝ} (hne : ∀ k, a k - t ≠ 0) (hSig : ftSigmaReal a r t = 0) :
    (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval t
      = -(∑ k, a k / (a k - t) ^ 2) * (ftRootPolyReal c a).eval t := by
  classical
  have hnbhd : ∀ᶠ s in nhds t, ∀ k, a k - s ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    exact (continuousAt_const.sub continuousAt_id).eventually_ne (hne k)
  have hL : HasDerivAt (fun s => (ftCriticalReal (ftRootPolyReal c a) r).eval s)
      ((derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval t) t :=
    (ftCriticalReal (ftRootPolyReal c a) r).hasDerivAt t
  have hS : HasDerivAt (ftSigmaReal a r) (∑ k, a k / (a k - t) ^ 2) t :=
    hasDerivAt_ftSigmaReal hne
  have hPd : HasDerivAt (fun s => (ftRootPolyReal c a).eval s)
      ((derivative (ftRootPolyReal c a)).eval t) t := (ftRootPolyReal c a).hasDerivAt t
  have hR : HasDerivAt (fun s => -(ftSigmaReal a r s) * (ftRootPolyReal c a).eval s)
      (-(∑ k, a k / (a k - t) ^ 2) * (ftRootPolyReal c a).eval t
        + -(ftSigmaReal a r t) * (derivative (ftRootPolyReal c a)).eval t) t := hS.neg.mul hPd
  have hRHS : HasDerivAt (fun s => -(ftSigmaReal a r s) * (ftRootPolyReal c a).eval s)
      ((derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval t) t := by
    refine hL.congr_of_eventuallyEq ?_
    filter_upwards [hnbhd] with s hs
    exact (eval_ftCriticalReal_eq_neg_sigma_mul hs).symm
  have huniq := hRHS.unique hR
  rw [hSig] at huniq
  simpa using huniq

/-- `E` over `ℂ` is `E` over `ℝ` mapped, so its derivative at a real point is the
real one coerced. -/
theorem eval_derivative_ftCritical_ofReal {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {r : ℕ} (t : ℝ) :
    (derivative (ftCritical (ftRootPoly c a) r)).eval ((t : ℝ) : ℂ)
      = (((derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval t : ℝ) : ℂ) := by
  have hmap : ftRootPoly c a = (ftRootPolyReal c a).map (algebraMap ℝ ℂ) := by
    rw [ftRootPoly, ftRootPolyReal, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_prod]
    simp
  have hcrit : ftCritical (ftRootPoly c a) r
      = (ftCriticalReal (ftRootPolyReal c a) r).map (algebraMap ℝ ℂ) := by
    rw [hmap, ftCritical, ftCriticalReal]
    simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.derivative_map]
  rw [hcrit, Polynomial.derivative_map, Polynomial.eval_map]
  simpa using Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) t

/-- **The collision is exactly double, at either endpoint and every `r ≥ 1`.**
`D''(t) = E'(t)/t = -Σ'(t)Q(t)/t`, and every factor is nonzero: `Σ' > 0` because
it is a sum of `a_k/(a_k-t)^2`, `Q(t) ≠ 0` by hypothesis — the bracket supplies it
at the lower endpoint — and `t ≠ 0`.

Nothing here sees the sign of `t`, so this settles the multiplicity at the lower
endpoint, where `t_a` sits above the smallest zero and `Q''` is unusable, by the
same argument that settles it at the upper one. -/
theorem rootMultiplicity_ftDen_eq_two_at_critical {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {r : ℕ} (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 1 ≤ r) {t : ℝ}
    (ht : t ≠ 0) (hne : ∀ k, a k - t ≠ 0)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval t = 0)
    (hQ : (ftRootPolyReal c a).eval t ≠ 0) :
    (ftDen (ftRootPoly c a) r
        ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ)).rootMultiplicity
      ((t : ℝ) : ℂ) = 2 := by
  classical
  have hlow := two_le_rootMultiplicity_ftDen_at_critical ha hc hr ht hE
  refine le_antisymm ?_ hlow
  by_contra hgt
  rw [Nat.not_le] at hgt
  -- `Σ(t) = 0`, since `E = -Σ·Q` and `Q(t) ≠ 0`
  have hSig : ftSigmaReal a r t = 0 := by
    have h := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := r) hne
    rw [hE] at h
    rcases mul_eq_zero.1 h.symm with h' | h'
    · exact neg_eq_zero.1 h'
    · exact absurd h' hQ
  have hEd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval t
      = -(∑ k, a k / (a k - t) ^ 2) * (ftRootPolyReal c a).eval t :=
    eval_derivative_ftCriticalReal_of_ftSigmaReal_eq_zero hne hSig
  have hEdne : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval t ≠ 0 := by
    rw [hEd]
    exact mul_ne_zero (neg_ne_zero.2 (ne_of_gt (sum_div_sq_pos hn ha hne))) hQ
  -- the double root, and the second derivative through it
  have hd1 : (derivative (ftDen (ftRootPoly c a) r
      ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ))).eval ((t : ℝ) : ℂ) = 0 := by
    have := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 1) hlow
    simpa using this
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hd2 := eval_derivative_two_ftDen_of_double_root (Q := ftRootPoly c a) hr htC hd1
  have hroot2 := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 2) hgt
  rw [Polynomial.IsRoot] at hroot2
  have : ((t : ℝ) : ℂ) ^ 0 = 1 := pow_zero _
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at hroot2
  rw [hroot2, eq_comm, div_eq_zero_iff] at hd2
  rcases hd2 with h' | h'
  · rw [eval_derivative_ftCritical_ofReal] at h'
    exact hEdne (by exact_mod_cast h')
  · exact htC h'

/-- **The clearance at every `r ≥ 1`**, off `two_le_prod_add_div_of_sum_inv_eq_neg`;
`clearance_ge_relative_gap` is this at `r = 1`.

With this, the whole `ρ = 1` chain is general in `r`: the collision, `D'' = E'/t`,
`E' = -Σ'Q`, the multiplicity, the bracket and the clearance all carry only
`1 ≤ r`.  What is **not** general is the reading of `∏a_k/t^3` as the modulus of
the non-collision root — that is Vieta, which wants `deg D = n`, i.e. `n > r`.  At
`n = 3` that holds for `r = 1, 2` and fails at `r = 3`. -/
theorem clearance_ge_relative_gap_of_r {a : Fin 3 → ℝ} {t : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (ht : 0 < t) (h0 : 0 < a 0) (h01 : a 0 < t) (h1t : t < a 1) (h12 : a 1 ≤ a 2)
    (hSig : ftSigmaReal a r t = 0) :
    (a 1 - a 0) / a 1 ≤ a 0 * a 1 * a 2 / t ^ 3 - 1 := by
  have hne : ∀ k : Fin 3, a k - t ≠ 0 := by
    intro k
    fin_cases k
    · exact sub_ne_zero.2 (ne_of_lt h01)
    · exact sub_ne_zero.2 (ne_of_gt h1t)
    · exact sub_ne_zero.2 (ne_of_gt (lt_of_lt_of_le h1t h12))
  have ha1 : 0 < a 1 := lt_trans ht h1t
  -- the three normalized variables
  set w : Fin 3 → ℝ := fun k => a k / t with hw
  have hwsub : ∀ k : Fin 3, w k - 1 = (a k - t) / t := by
    intro k; rw [hw]; field_simp
  have hinv : ∀ k : Fin 3, 1 / (w k - 1) = t / (a k - t) := by
    intro k
    rw [hwsub k, one_div_div]
  -- the constraint, translated
  have hc : 1 / (w 0 - 1) + 1 / (w 1 - 1) + 1 / (w 2 - 1) = -(r : ℝ) := by
    rw [hinv 0, hinv 1, hinv 2]
    have h := hSig
    rw [ftSigmaReal, Fin.sum_univ_three] at h
    linarith
  -- the ordering, translated
  have hw0 : 0 < w 0 := div_pos h0 ht
  have hw0' : w 0 < 1 := by rw [hw, div_lt_one ht]; exact h01
  have hw1 : 1 < w 1 := by rw [hw, lt_div_iff₀ ht]; linarith
  have hw12 : w 1 ≤ w 2 := by
    rw [hw]
    exact div_le_div_of_nonneg_right h12 ht.le
  have hkey := two_le_prod_add_div_of_sum_inv_eq_neg (by exact_mod_cast hr) hw0 hw0' hw1 hw12 hc
  -- and back
  have hprod : w 0 * w 1 * w 2 = a 0 * a 1 * a 2 / t ^ 3 := by
    rw [hw]; field_simp
  have hratio : w 0 / w 1 = a 0 / a 1 := by
    rw [hw]; field_simp
  rw [hprod, hratio] at hkey
  have hgap : (a 1 - a 0) / a 1 = 1 - a 0 / a 1 := by field_simp
  rw [hgap]
  linarith

/-! ### The clearance at general `n`

`clearance_ge_relative_gap_of_r` is the same bound at `Fin 3`.  Widening it needs
nothing new about the pencil: the constraint is consumed through **two** of its
terms and the product through **two** of its factors, so what carries the whole
inequality is a polynomial fact in two variables.

Put `w_k = a_k/t`, so `Sigma(t) = 0` reads `sum_k 1/(w_k - 1) = -r` and the
clearance is `prod_k w_k`.  Every `w_k` with `k` other than the smallest zero
exceeds `1`, so dropping all but one of them only weakens the product, and every
term of the constraint is positive, so dropping all but one of them only weakens
the sum.  What is left is `p = w_1 - 1` against `q = w_j - 1`.

**Three distinct indices is a real boundary, not an artifact.**  At `n = 2` the
bound is false: there `Sigma(t) = 0` at `r = 1` puts `t` at exactly the geometric
mean `sqrt(a_0 a_1)`, the clearance `a_0a_1/t^2 - 1` is exactly `0`, and the
relative gap is whatever the pencil's is.

**What this does NOT need.**  No Cauchy-Schwarz, and no bound of the form
`1 + sum_k v_k <= prod_k (1 + v_k)` -- both were reached for first and both are
strictly more than the two-term reduction consumes.  Nothing here is a bound on
`n`, and the slack grows with `n` rather than shrinking, since the discarded
factors each exceed `1`. -/

/-- **The two-variable core.**  `2D <= (p+q)(1 + D + 1/(1+p))` at `D = p+q+pq`,
for `0 < p <= q`.

The difference is `E/(1+p)` with
`E = p^3 + p^2q + q(q-p) + 2pq^2 + p^3q + p^2q^2`, and exactly one term of `E`
carries a minus sign.  So `p <= q` is the whole of what the sign argument needs,
and it is genuinely needed: `E` is negative at `p = 1/10`, `q = 1/25`.

Sharp in the limit: at `p = q` the difference is `(2p^2 + p^3)/(1+p)`, which is
`O(p^2)` and vanishes only as `p -> 0`. -/
theorem two_le_sum_mul_of_le {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    2 * (p + q + p * q) ≤ (p + q) * (1 + (p + q + p * q) + 1 / (1 + p)) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have h1p : (0 : ℝ) < 1 + p := by linarith
  rw [← sub_nonneg]
  have key : (p + q) * (1 + (p + q + p * q) + 1 / (1 + p)) - 2 * (p + q + p * q)
      = (p ^ 3 + p ^ 2 * q + q * (q - p) + 2 * p * q ^ 2 + p ^ 3 * q + p ^ 2 * q ^ 2)
        / (1 + p) := by
    field
  rw [key]
  refine div_nonneg ?_ h1p.le
  have h2 : 0 ≤ q * (q - p) := mul_nonneg hq.le (by linarith)
  nlinarith [pow_pos hp 3, mul_pos (pow_pos hp 2) hq, mul_pos hp (mul_pos hq hq),
    mul_pos (pow_pos hp 3) hq, mul_pos (pow_pos hp 2) (mul_pos hq hq)]

/-- **The clearance in the normalized variables, over two retained terms.**
`2 <= w_0 P + w_0/w_1` whenever `P` dominates the single product `w_1 w_j` and
`S` dominates the two constraint terms `1/(w_1 - 1) + 1/(w_j - 1)`.

Stating it with `P` and `S` as bare reals rather than as a product and a sum is
what makes it reusable at any `n`: the caller discharges the two domination
hypotheses from whatever index set it has, and nothing here knows how many zeros
the pencil carries.

`1 <= r` enters once, to replace `r + S - 1` by `S`.  It is what this route
consumes rather than where the bound stops -- the inequality survives well below
`r = 1` -- so widening `r` is available and is simply not needed, since `r` is a
positive natural in the pencil. -/
theorem two_le_prod_add_div_of_two_terms {w₀ w₁ wj P S r : ℝ} (hr : 1 ≤ r)
    (h1 : 1 < w₁) (hj : w₁ ≤ wj)
    (hP : w₁ * wj ≤ P) (hS : 1 / (w₁ - 1) + 1 / (wj - 1) ≤ S)
    (hc : 1 / (w₀ - 1) + S = -r) :
    2 ≤ w₀ * P + w₀ / w₁ := by
  have hp : (0 : ℝ) < w₁ - 1 := by linarith
  have hq : (0 : ℝ) < wj - 1 := by linarith
  have hw1 : (0 : ℝ) < w₁ := by linarith
  have hpq : w₁ - 1 ≤ wj - 1 := by linarith
  have hD : (0 : ℝ) < (w₁ - 1) + (wj - 1) + (w₁ - 1) * (wj - 1) := by positivity
  have hpqpos : (0 : ℝ) < (w₁ - 1) * (wj - 1) := mul_pos hp hq
  -- the two-term lower bound on `S`, over a common denominator
  have hSlb : ((w₁ - 1) + (wj - 1)) / ((w₁ - 1) * (wj - 1)) ≤ S := by
    have hid : 1 / (w₁ - 1) + 1 / (wj - 1)
        = ((w₁ - 1) + (wj - 1)) / ((w₁ - 1) * (wj - 1)) := by field
    linarith [hid ▸ hS]
  have hfrac : (0 : ℝ) < ((w₁ - 1) + (wj - 1)) / ((w₁ - 1) * (wj - 1)) := by positivity
  have hSpos : (0 : ℝ) < S := lt_of_lt_of_le hfrac hSlb
  have hRS : (0 : ℝ) < r + S := by linarith
  have hRS1 : (1 : ℝ) < r + S := by linarith
  -- the constraint, cleared of its one negative term.  `w₀ - 1 = 0` is not a
  -- degenerate case to exclude by hypothesis: Lean's `1/0 = 0` sends `hc` to
  -- `S = -r`, which the positivity of `S` already refutes.
  have hne : w₀ - 1 ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
    linarith
  have hkey : (r + S) * (1 - w₀) = 1 := by
    field_simp at hc
    linarith [hc]
  -- both bounds on `w₀` are consequences, not assumptions
  have h0' : w₀ < 1 := by nlinarith [hkey, hRS]
  have h0 : 0 < w₀ := by nlinarith [hkey, hRS1]
  have hone : 1 - w₀ = 1 / (r + S) := by
    field_simp
    linarith [hkey]
  -- hence a lower bound on `w₀` in the two variables alone
  have hw0lb : ((w₁ - 1) + (wj - 1)) / ((w₁ - 1) + (wj - 1) + (w₁ - 1) * (wj - 1)) ≤ w₀ := by
    have hup : 1 - w₀ ≤ ((w₁ - 1) * (wj - 1))
        / ((w₁ - 1) + (wj - 1) + (w₁ - 1) * (wj - 1)) := by
      rw [hone, div_le_div_iff₀ hRS hD]
      have := mul_le_mul_of_nonneg_left hSlb hpqpos.le
      have hexp : (w₁ - 1) * (wj - 1) * (((w₁ - 1) + (wj - 1)) / ((w₁ - 1) * (wj - 1)))
          = (w₁ - 1) + (wj - 1) := by field_simp
      nlinarith [hexp, hr]
    have heq : ((w₁ - 1) + (wj - 1)) / ((w₁ - 1) + (wj - 1) + (w₁ - 1) * (wj - 1))
        = 1 - ((w₁ - 1) * (wj - 1)) / ((w₁ - 1) + (wj - 1) + (w₁ - 1) * (wj - 1)) := by
      rw [eq_sub_iff_add_eq, div_add_div _ _ hD.ne' hD.ne', div_eq_one_iff_eq
        (mul_ne_zero hD.ne' hD.ne')]
      ring
    rw [heq]
    linarith [hup]
  -- the two retained factors, and the core
  have hwj : (0 : ℝ) < wj := by linarith
  have hM : (0 : ℝ) < w₁ * wj + 1 / w₁ :=
    add_pos (mul_pos hw1 hwj) (by positivity)
  have hMeq : w₁ * wj + 1 / w₁
      = 1 + ((w₁ - 1) + (wj - 1) + (w₁ - 1) * (wj - 1)) + 1 / (1 + (w₁ - 1)) := by
    field
  have hcore := two_le_sum_mul_of_le hp hpq
  rw [← hMeq] at hcore
  have hstep : ((w₁ - 1) + (wj - 1)) / ((w₁ - 1) + (wj - 1) + (w₁ - 1) * (wj - 1))
      * (w₁ * wj + 1 / w₁) ≤ w₀ * (w₁ * wj + 1 / w₁) :=
    mul_le_mul_of_nonneg_right hw0lb hM.le
  have hlow : (2 : ℝ) ≤ w₀ * (w₁ * wj + 1 / w₁) := by
    refine le_trans ?_ hstep
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    linarith [hcore]
  have hPstep : w₀ * (w₁ * wj) ≤ w₀ * P := mul_le_mul_of_nonneg_left hP h0.le
  have hsplit : w₀ * (w₁ * wj + 1 / w₁) = w₀ * (w₁ * wj) + w₀ / w₁ := by
    field_simp
  linarith [hsplit ▸ hlow, hPstep]

/-- **The clearance at every `n`, in the pencil's own terms.**  Given the bracket
`a i₀ < t < a i₁` and `a i₁` the smallest of the zeros other than `a i₀`, the
clearance ratio `prod_k a_k/t^n` exceeds `1` by at least the relative gap
`(a i₁ - a i₀)/a i₁`.

`clearance_ge_relative_gap_of_r` is this at `Fin 3` with `i₀, i₁, j = 0, 1, 2`.

**Kept as superseded-but-correct.**  `clearance_ge_sub_two_mul_relative_gap`
implies this for `3 <= n`, so nothing consumes it; it stays because its proof
runs on strictly less -- three of the `n` zeros rather than all of them -- and
that is a different fact, not a weaker version of the same one.  The bare
`two_le_prod_add_div_of_two_terms` is the reusable half, for a caller that can
bound the product and the sum from two terms each and no more.

**The three indices are named rather than counted**, and that is what the proof
uses: `i₀` is where the branch radius sits below the zero, `i₁` is the zero
immediately above it, and `j` is any third.  A pencil with `3 <= n` supplies one,
and one with `n = 2` cannot -- where the bound is genuinely false, since at
`r = 1` the critical point is exactly `sqrt(a_0 a_1)` and the clearance vanishes
identically.

**`0 < a i₀` is not assumed here either**, and for the same reason as in
`clearance_ge_sub_two_mul_relative_gap`: the constraint forces `w i₀ < 1` and
`0 < w i₀` both, through `(r + S)(1 - w i₀) = 1` with `1 < r + S`.  Lean's
`1/0 = 0` does not open a degenerate case, since `w i₀ = 1` sends the constraint
to `S = -r`, which the positivity of `S` refutes.  `clearance_ge_relative_gap_of_r`
at `Fin 3` still carries the hypothesis and does not need it; it is left as it
stands rather than restated here.

`h1k` cannot be relaxed to "`a i₁` is one of the other zeros".  The core is false
without `w i₁ <= w j`, so `a i₁` really must be the smallest of them; the bound it
gives is then also the strongest, since a larger `a i₁` is a larger relative gap. -/
theorem clearance_ge_relative_gap_of_r_general {n : ℕ} {a : Fin n → ℝ} {t : ℝ} {r : ℕ}
    {i₀ i₁ j : Fin n} (h01 : i₀ ≠ i₁) (h0j : i₀ ≠ j) (h1j : i₁ ≠ j)
    (hr : 1 ≤ r) (ht : 0 < t) (h0t : a i₀ < t) (ht1 : t < a i₁)
    (h1k : ∀ k, k ≠ i₀ → a i₁ ≤ a k)
    (hSig : ftSigmaReal a r t = 0) :
    (a i₁ - a i₀) / a i₁ ≤ (∏ k, a k) / t ^ n - 1 := by
  classical
  set w : Fin n → ℝ := fun k => a k / t with hw
  have htne : t ≠ 0 := ne_of_gt ht
  have hgt : ∀ k, k ≠ i₀ → t < a k := fun k hk => lt_of_lt_of_le ht1 (h1k k hk)
  have hne : ∀ k, a k - t ≠ 0 := by
    intro k
    rcases eq_or_ne k i₀ with rfl | hk
    · exact sub_ne_zero.2 (ne_of_lt h0t)
    · exact sub_ne_zero.2 (ne_of_gt (hgt k hk))
  have hwsub : ∀ k, w k - 1 = (a k - t) / t := by intro k; rw [hw]; field_simp
  have hinv : ∀ k, 1 / (w k - 1) = t / (a k - t) := by
    intro k; rw [hwsub k, one_div_div]
  have hw1gt : ∀ k, k ≠ i₀ → 1 < w k := by
    intro k hk; rw [hw]; exact (one_lt_div ht).2 (hgt k hk)
  -- the constraint, translated and split off the distinguished index
  have hK : i₀ ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i₀
  have hcsum : ∑ k, 1 / (w k - 1) = -(r : ℝ) := by
    have h := hSig
    rw [ftSigmaReal] at h
    have hterm : ∑ k, 1 / (w k - 1) = ∑ k, t / (a k - t) :=
      Finset.sum_congr rfl fun k _ => hinv k
    rw [hterm]; linarith
  have hsplit : 1 / (w i₀ - 1) + ∑ k ∈ Finset.univ.erase i₀, 1 / (w k - 1) = -(r : ℝ) := by
    rw [Finset.add_sum_erase _ (fun k => 1 / (w k - 1)) hK]; exact hcsum
  -- the two retained terms of the sum
  have hpair : ({i₁, j} : Finset (Fin n)) ⊆ Finset.univ.erase i₀ := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ k⟩
    rcases hk with rfl | rfl
    · exact fun h => h01 h.symm
    · exact fun h => h0j h.symm
  have hSle : 1 / (w i₁ - 1) + 1 / (w j - 1)
      ≤ ∑ k ∈ Finset.univ.erase i₀, 1 / (w k - 1) := by
    have hnn : ∀ k ∈ Finset.univ.erase i₀, k ∉ ({i₁, j} : Finset (Fin n)) →
        0 ≤ 1 / (w k - 1) := by
      intro k hk _
      have := hw1gt k (Finset.mem_erase.1 hk).1
      positivity
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hpair hnn
    rwa [Finset.sum_pair h1j] at hsum
  -- the two retained factors of the product
  have hPle : w i₁ * w j ≤ ∏ k ∈ Finset.univ.erase i₀, w k := by
    have hrest : (1 : ℝ) ≤ ∏ k ∈ (Finset.univ.erase i₀) \ ({i₁, j} : Finset (Fin n)), w k := by
      refine Finset.one_le_prod fun k hk => ?_
      exact le_of_lt (hw1gt k (Finset.mem_erase.1 (Finset.mem_sdiff.1 hk).1).1)
    have hsd := Finset.prod_sdiff (f := w) hpair
    rw [Finset.prod_pair h1j] at hsd
    have hpos : (0 : ℝ) ≤ w i₁ * w j :=
      le_of_lt (mul_pos (lt_trans one_pos (hw1gt i₁ (fun h => h01 h.symm)))
        (lt_trans one_pos (hw1gt j (fun h => h0j h.symm))))
    calc w i₁ * w j = 1 * (w i₁ * w j) := (one_mul _).symm
      _ ≤ (∏ k ∈ (Finset.univ.erase i₀) \ ({i₁, j} : Finset (Fin n)), w k) * (w i₁ * w j) :=
          mul_le_mul_of_nonneg_right hrest hpos
      _ = ∏ k ∈ Finset.univ.erase i₀, w k := hsd
  -- the bare inequality
  have hw1lt : 1 < w i₁ := hw1gt i₁ (fun h => h01 h.symm)
  have hwj : w i₁ ≤ w j := by
    rw [hw]
    exact div_le_div_of_nonneg_right (h1k j (fun h => h0j h.symm)) ht.le
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hbare := two_le_prod_add_div_of_two_terms hrR hw1lt hwj hPle hSle hsplit
  -- and back to the pencil
  have hprod : w i₀ * ∏ k ∈ Finset.univ.erase i₀, w k = (∏ k, a k) / t ^ n := by
    rw [Finset.mul_prod_erase _ _ hK, hw]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hratio : w i₀ / w i₁ = a i₀ / a i₁ := by rw [hw]; field_simp
  rw [hprod, hratio] at hbare
  have ha1 : 0 < a i₁ := lt_trans ht ht1
  have hgap : (a i₁ - a i₀) / a i₁ = 1 - a i₀ / a i₁ := by field_simp
  rw [hgap]
  linarith

/-! ### The sharp constant, and why it needs every zero

`clearance_ge_relative_gap_of_r_general` is not sharp beyond `n = 3`.  Its
equality case is a **direction** rather than a point -- the whole tail collapsing
together onto the smallest zero -- and along it the clearance exceeds `1` by
`n - 2` times the relative gap rather than by one.  Sending `a_1 -> a_0` alone
never finds this: with the tail spread the clearance tends to a large constant
while the gap tends to `0`, so that direction is slack by orders of magnitude and
reports nothing about the constant.

So the sharp form carries a factor the three-term case cannot show, and `n - 2`
is exactly the largest constant available: inflating it by two percent is refuted
at every `n` from `3` to `8`.

**This one needs all `n` zeros, and the two routes are incompatible rather than
one being weaker.**  Along the collapsing direction every discarded factor
contributes, so the clearance the two-zero reduction can certify SATURATES while
`(n-2)g` grows linearly.  On `a = (1, 1+e, ..., 1+e)` at `e = 1/2`, `r = 1`:

```
  n         3       4       5       6       7
  (n-2)g    0.333   0.667   1.000   1.333   1.667
  retained  0.474   0.623   0.723   0.795   0.849
```

They cross between `n = 3` and `n = 4`, and never come back.  So the reduction
reaching `n - 2` at `n = 3` is the coincidence of `n - 2 = 1` there, and no
amount of work on that route reaches the sharp constant -- it discards exactly
the factors this direction lives in.  Both are kept: this is the stronger
theorem, and the reduction is what a consumer holding only three of the zeros can
still use, through the bare `two_le_prod_add_div_of_two_terms`.

The table is guarded rather than typed: `check_clearance_two_index_reduction.py`
(C10) recomputes it and parses these rows back out of this docstring.

Three ingredients, and each is used once.  `1 + sum v <= prod (1 + v)`, which is
lossless to leading order in the collapsing direction and so may not be replaced
by anything cruder; the AM-HM inequality `m^2 <= (sum v)(sum 1/v)`, which the
two-zero reduction could avoid and this cannot; and `v_1 (sum 1/v) <= m`, from
`v_1` being the smallest. -/

/-- `1 + sum v <= prod (1 + v)` for nonnegative `v`. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) {v : ι → ℝ}
    (hv : ∀ i ∈ s, 0 ≤ v i) : 1 + ∑ i ∈ s, v i ≤ ∏ i ∈ s, (1 + v i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hva : 0 ≤ v a := hv a (Finset.mem_cons_self a s)
      have hvs : ∀ i ∈ s, 0 ≤ v i := fun i hi => hv i (Finset.mem_cons_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, v i := Finset.sum_nonneg hvs
      rw [Finset.prod_cons, Finset.sum_cons]
      have := ih hvs
      nlinarith [mul_nonneg hva hsum]


/-- **AM-HM.**  `(#s)^2 <= (sum_s v)(sum_s 1/v)` for positive `v`.

Through `Finset.sq_sum_div_le_sum_sq_div` at `f = 1`, which is Cauchy-Schwarz in
Engel form and carries no square roots -- the `f = sqrt v`, `g = 1/sqrt v`
route reaches the same place through two more coercions. -/
theorem sq_card_le_sum_mul_sum_inv {ι : Type*} (s : Finset ι) {v : ι → ℝ}
    (hv : ∀ i ∈ s, 0 < v i) :
    ((s.card : ℝ)) ^ 2 ≤ (∑ i ∈ s, v i) * ∑ i ∈ s, 1 / v i := by
  have hT : 0 < ∑ i ∈ s, v i ∨ s = ∅ := by
    rcases s.eq_empty_or_nonempty with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sum_pos hv h)
  rcases hT with hT | rfl
  · have h := Finset.sq_sum_div_le_sum_sq_div s (fun _ => (1 : ℝ)) hv
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_pow] at h
    rw [div_le_iff₀ hT] at h
    calc ((s.card : ℝ)) ^ 2 = ((s.card : ℝ) * 1) ^ 2 := by ring
      _ ≤ (∑ i ∈ s, 1 / v i) * ∑ i ∈ s, v i := by simpa using h
      _ = (∑ i ∈ s, v i) * ∑ i ∈ s, 1 / v i := by ring
  · simp


/-- **The sharp clearance in the normalized variables.**  `P` dominating `1 + T`,
`m^2 <= TS` and `v_1 S <= m` give `(m-1)(u + v_1)/(1 + v_1) <= (1-u)P - 1`.

Stated over bare reals for the same reason as `two_le_prod_add_div_of_two_terms`:
the caller discharges the three dominations from whatever index set it has, and
nothing here knows how many zeros the pencil carries.

The proof is one positive combination, and it is an **identity, not estimate**:
after clearing `(1 + v_1)(1 + S)`, the difference is

  `A(1+T)(1+v_1) + (m-1)A + (TS - m^2)(1+v_1) + (m-1)(m - v_1 S) + m(m-1)v_1`

at `A = 1 - u(1+S)`, and every term is nonnegative.  Nothing is discarded on the
way, which is why all five vanish together exactly as the tail collapses and the
constant is attained there rather than approached from far away -- and it is the
answer to whether `1 + sum v <= prod (1 + v)` could be replaced by something
cruder.  It could not: that step is lossless to leading order in the same
direction, so any slack introduced there is slack in the constant.

`1 <= r` enters once, through `A >= 0`. -/
theorem sub_one_mul_relative_gap_le {P S T u v₁ r : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hv₁ : 0 < v₁) (hS : 0 < S) (hr : 1 ≤ r) (hu : 0 < u)
    (hueq : u * (r + S) = 1) (hP : 1 + T ≤ P)
    (hTS : ((m : ℝ)) ^ 2 ≤ T * S) (hvS : v₁ * S ≤ (m : ℝ)) :
    (((m : ℝ)) - 1) * ((u + v₁) / (1 + v₁)) ≤ (1 - u) * P - 1 := by
  have hM2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hS1 : (0 : ℝ) < 1 + S := by linarith
  have hv1' : (0 : ℝ) < 1 + v₁ := by linarith
  -- `r >= 1` is used exactly once, here
  have hA : 0 ≤ 1 - u * (1 + S) := by nlinarith [hueq, hr, hu]
  have hu1 : u < 1 := by nlinarith [hA, hS, hu]
  have hT : 0 < T := by nlinarith [hTS, hS, hM2]
  -- the reduced goal, after `1 + T <= P`
  have hred : (((m : ℝ)) - 1) * ((u + v₁) / (1 + v₁)) ≤ (1 - u) * (1 + T) - 1 := by
    have hL : ((m : ℝ) - 1) * ((u + v₁) / (1 + v₁))
        = (((m : ℝ) - 1) * (u + v₁)) / (1 + v₁) := by ring
    rw [hL, div_le_iff₀ hv1']
    have hkey : ((1 - u) * (1 + T) - 1) * (1 + v₁) - ((m : ℝ) - 1) * (u + v₁) ≥ 0 := by
      have hcert : (((1 - u) * (1 + T) - 1) * (1 + v₁)
            - ((m : ℝ) - 1) * (u + v₁)) * (1 + S)
          = (1 - u * (1 + S)) * (1 + T) * (1 + v₁) + ((m : ℝ) - 1) * (1 - u * (1 + S))
            + (T * S - (m : ℝ) ^ 2) * (1 + v₁) + ((m : ℝ) - 1) * ((m : ℝ) - v₁ * S)
            + (m : ℝ) * ((m : ℝ) - 1) * v₁ := by ring
      have h1 : 0 ≤ (1 - u * (1 + S)) * (1 + T) * (1 + v₁) :=
        mul_nonneg (mul_nonneg hA (by linarith)) hv1'.le
      have h2 : 0 ≤ ((m : ℝ) - 1) * (1 - u * (1 + S)) := mul_nonneg (by linarith) hA
      have h3 : 0 ≤ (T * S - (m : ℝ) ^ 2) * (1 + v₁) :=
        mul_nonneg (by linarith) hv1'.le
      have h4 : 0 ≤ ((m : ℝ) - 1) * ((m : ℝ) - v₁ * S) :=
        mul_nonneg (by linarith) (by linarith)
      have h5 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) * v₁ :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hv₁.le
      have hXS : 0 ≤ (((1 - u) * (1 + T) - 1) * (1 + v₁)
          - ((m : ℝ) - 1) * (u + v₁)) * (1 + S) := by rw [hcert]; linarith
      nlinarith [hXS, hS1]
    linarith [hkey]
  have hstep : (1 - u) * (1 + T) ≤ (1 - u) * P :=
    mul_le_mul_of_nonneg_left hP (by linarith)
  linarith [hred, hstep]


/-- **The sharp clearance at every `n`, in the pencil's own terms.**  The
clearance ratio exceeds `1` by at least `n - 2` times the relative gap.

**Kept as the paper's own statement of the clearance.**
`clearance_ge_relative_gap_of_r_general` is the `n - 2 = 1` case and is implied
by this for `3 <= n`; it is kept for the reason above, not for want of pruning.

**Only two indices are named**, against the reduction's three: the third was
needed to carry a product bound, and here the product is used whole.

**`0 < a i_0` is not assumed, because it is not needed.**  `Sigma(t) = 0` forces
`u = (t - a i_0)/t < 1` on its own, through `u(1 + S) <= u(r + S) = 1` with
`S > 0`, and that is exactly positivity of the smallest zero.  So the bracket and
the critical-point condition already carry it. -/
theorem clearance_ge_sub_two_mul_relative_gap {n : ℕ} {a : Fin n → ℝ} {t : ℝ} {r : ℕ}
    {i₀ i₁ : Fin n} (hn : 3 ≤ n) (h01 : i₀ ≠ i₁)
    (hr : 1 ≤ r) (ht : 0 < t) (h0t : a i₀ < t) (ht1 : t < a i₁)
    (h1k : ∀ k, k ≠ i₀ → a i₁ ≤ a k)
    (hSig : ftSigmaReal a r t = 0) :
    ((n : ℝ) - 2) * ((a i₁ - a i₀) / a i₁) ≤ (∏ k, a k) / t ^ n - 1 := by
  classical
  have htne : t ≠ 0 := ne_of_gt ht
  have hgt : ∀ k, k ≠ i₀ → t < a k := fun k hk => lt_of_lt_of_le ht1 (h1k k hk)
  set K : Finset (Fin n) := Finset.univ.erase i₀ with hK
  set v : Fin n → ℝ := fun k => (a k - t) / t with hv
  have hvpos : ∀ k ∈ K, 0 < v k := by
    intro k hk
    exact div_pos (sub_pos.2 (hgt k (Finset.mem_erase.1 hk).1)) ht
  have hcard : K.card = n - 1 := by
    rw [hK, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Fintype.card_fin]
  have hm : 2 ≤ K.card := by omega
  have hi₁ : i₁ ∈ K := Finset.mem_erase.2 ⟨fun h => h01 h.symm, Finset.mem_univ i₁⟩
  set u : ℝ := (t - a i₀) / t with hu
  have hupos : 0 < u := div_pos (sub_pos.2 h0t) ht
  set T : ℝ := ∑ k ∈ K, v k with hT
  set S : ℝ := ∑ k ∈ K, 1 / v k with hS
  have hSpos : 0 < S := Finset.sum_pos (fun k hk => by
    have := hvpos k hk; positivity) ⟨i₁, hi₁⟩
  -- the constraint
  have hinv : ∀ k, k ≠ i₀ → 1 / v k = t / (a k - t) := by
    intro k _; rw [hv, one_div_div]
  have hcsum : ∑ k, 1 / v k = -(r : ℝ) := by
    have h := hSig
    rw [ftSigmaReal] at h
    have hterm : ∑ k, 1 / v k = ∑ k, t / (a k - t) :=
      Finset.sum_congr rfl fun k _ => by rw [hv, one_div_div]
    rw [hterm]; linarith
  have hu0 : 1 / v i₀ = -(1 / u) := by
    rw [hv, hu, one_div_div, one_div_div, neg_div', div_eq_div_iff]
    · ring
    · exact sub_ne_zero.2 (ne_of_lt h0t)
    · exact sub_ne_zero.2 (ne_of_gt h0t)
  have hueq : u * (r + S) = 1 := by
    have hsp : 1 / v i₀ + S = -(r : ℝ) := by
      rw [hS, hK, Finset.add_sum_erase _ (fun k => 1 / v k) (Finset.mem_univ i₀)]
      exact hcsum
    rw [hu0] at hsp
    field_simp at hsp ⊢
    linarith [hsp]
  -- the three inputs to the core
  set P : ℝ := ∏ k ∈ K, (1 + v k) with hP
  have hPle : 1 + T ≤ P :=
    one_add_sum_le_prod_one_add K (fun k hk => (hvpos k hk).le)
  have hTS : ((K.card : ℝ)) ^ 2 ≤ T * S := sq_card_le_sum_mul_sum_inv K hvpos
  have hvi : 0 < v i₁ := hvpos i₁ hi₁
  have hvS : v i₁ * S ≤ ((K.card : ℝ)) := by
    have hle : ∀ k ∈ K, 1 / v k ≤ 1 / v i₁ := by
      intro k hk
      refine one_div_le_one_div_of_le hvi ?_
      have hak : a i₁ - t ≤ a k - t := by
        linarith [h1k k (Finset.mem_erase.1 hk).1]
      rw [hv]
      exact div_le_div_of_nonneg_right hak ht.le
    have hsum := Finset.sum_le_sum hle
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [mul_comm]
    calc S * v i₁ ≤ ((K.card : ℝ) * (1 / v i₁)) * v i₁ :=
          mul_le_mul_of_nonneg_right hsum hvi.le
      _ = ((K.card : ℝ)) := by field_simp
  have hcore := sub_one_mul_relative_gap_le hm hvi hSpos
    (by exact_mod_cast hr) hupos hueq hPle hTS hvS
  -- and back to the pencil
  have ha1 : 0 < a i₁ := lt_trans ht ht1
  have hcast : ((K.card : ℝ)) - 1 = (n : ℝ) - 2 := by
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    ring
  have h1v : (0 : ℝ) < 1 + v i₁ := by linarith
  have hratio : (u + v i₁) / (1 + v i₁) = (a i₁ - a i₀) / a i₁ := by
    rw [div_eq_div_iff h1v.ne' (ne_of_gt ha1), hu, hv]
    field
  have hclear : (1 - u) * P = (∏ k, a k) / t ^ n := by
    have h1u : 1 - u = a i₀ / t := by rw [hu]; field
    have hfac : ∀ k, 1 + v k = a k / t := by
      intro k; rw [hv]; field
    rw [h1u, hP, Finset.prod_congr rfl (fun k _ => hfac k), hK,
      Finset.mul_prod_erase _ (fun k => a k / t) (Finset.mem_univ i₀),
      Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hcast, hratio, hclear] at hcore
  exact hcore

/-! ### The indented contour's geometry

An argument principle on the circle `|1+sigma| = 1`, indented outward at the
origin and carried to an honest circle by a homotopy, is one route to the
separation.  **It is not the route the tree takes**, so nothing in this section
has a consumer: `LowerSeparationQuotient` divides the double root out and counts
on an UN-INDENTED circle, which needs no indentation to route around and no
contour to deform.  The analytic hypotheses of
`curveIntegral_add_curveIntegral_eq_of_diffContOnCl` are correspondingly absent,
and no contour integral is evaluated anywhere.

What is here is true and exact, and each declaration carries a line naming which
part of the indented route it holds -- so that a consumer count of zero reads as
the decision it is rather than as dead code.

Two facts, and both are exact rather than estimated.  The indentation lies in
`{‖1+z‖ >= 1}` -- `‖1 + e e^{i psi}‖^2 - 1 = e(e + 2 cos psi)`, nonnegative
exactly when `cos psi >= -e/2`, which the junction angle attains.  And the
deformation that reaches the circle is the MODULUS interpolation rather than a
radial scaling: scaling leaves a scaled indentation behind, while `modInterp`
sends every modulus to `1 + delta` at time one.  Its modulus is
`(1-t)‖w‖ + t(1+delta)`, so on the indented contour it is at least `1 + t*delta`
and the deformation never returns to the unit circle -- which is what keeps it
off `sigma = 0`, the one zero of the integrand that lies on the contour's own
circle. -/
/-- **The indentation lies outside the unit circle.**  `‖1 + εe^{iψ}‖² − 1 =
ε(ε + 2cos ψ)`, so the arc stays in `{‖1+z‖ ≥ 1}` exactly when `cos ψ ≥ -ε/2` --
and the junction angle `π/2 + θ_ε/2`, at which `cos = -sin(θ_ε/2) = -ε/2`, is
where that is attained.  No case analysis.

No consumer: this is the indentation's own geometry, and the separation is
counted on a circle with no indentation in it. -/
theorem one_le_norm_one_add_arc {ε ψ : ℝ} (hε : 0 ≤ ε)
    (hcos : -(ε / 2) ≤ Real.cos ψ) :
    1 ≤ ‖1 + (ε : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ := by
  have hre : (1 + (ε : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)).re
      = 1 + ε * Real.cos ψ := by
    rw [Complex.exp_mul_I]; simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have him : (1 + (ε : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)).im
      = ε * Real.sin ψ := by
    rw [Complex.exp_mul_I]; simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hsq : Complex.normSq (1 + (ε : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      = 1 + 2 * ε * Real.cos ψ + ε ^ 2 := by
    rw [Complex.normSq_apply, hre, him]
    linear_combination (ε ^ 2) * Real.sin_sq_add_cos_sq ψ
  have h1 : (1 : ℝ) ≤ Complex.normSq (1 + (ε : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) := by
    rw [hsq]; nlinarith
  nlinarith [Complex.sq_norm (1 + (ε : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)),
    norm_nonneg (1 + (ε : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))]

/-- The modulus-interpolating homotopy, in the coordinate `w = 1 + σ`: it scales
`w` so that its modulus runs from `‖w‖` to `1 + δ`.

No consumer outside the lemmas immediately below: it deforms a CONTOUR, and the
separation deforms the CONFIGURATION instead, leaving the contour a fixed
circle. -/
noncomputable def modInterp (δ t : ℝ) (w : ℂ) : ℂ :=
  ((((1 - t) * ‖w‖ + t * (1 + δ)) / ‖w‖ : ℝ) : ℂ) * w

/-- The homotopy's identity end.  No consumer: it presents `modInterp` as a
homotopy starting AT the indented contour, and no such contour is built. -/
@[simp] theorem modInterp_zero (δ : ℝ) {w : ℂ} (hw : w ≠ 0) : modInterp δ 0 w = w := by
  have hw0 : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hw
  rw [modInterp]
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  rw [div_self hw0]
  simp

/-- Consumed only inside this section, by `one_add_le_norm_modInterp` and
`norm_modInterp_one`; the section as a whole has no consumer, for the reason on
`modInterp`. -/
theorem norm_modInterp {δ t : ℝ} {w : ℂ} (hw : w ≠ 0)
    (hnn : 0 ≤ (1 - t) * ‖w‖ + t * (1 + δ)) :
    ‖modInterp δ t w‖ = (1 - t) * ‖w‖ + t * (1 + δ) := by
  have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  rw [modInterp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  field_simp

/-- **The homotopy never returns to the unit circle once it has started.**  With
`‖w‖ ≥ 1` on `Γ_ε`, the modulus runs `(1-t)‖w‖ + t(1+δ) ≥ 1 + tδ`, so at every
`t > 0` the image has modulus strictly above `1`.

Consumed only inside this section, by `modInterp_ne_one`.  It is Poincare's
`hφt` for the homotopy, and no homotopy of contours is taken. -/
theorem one_add_le_norm_modInterp {δ t : ℝ} {w : ℂ} (hw : 1 ≤ ‖w‖)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hδ : 0 ≤ δ) :
    1 + t * δ ≤ ‖modInterp δ t w‖ := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw; linarith
  rw [norm_modInterp hw0 (by nlinarith)]
  nlinarith

/-- **`hφt`, in the form the Poincaré lemma consumes**: the homotopy of `Γ_ε`
stays off `σ = 0`, i.e. off `w = 1`, at every positive time.  At `t = 0` it is
`Γ_ε` itself, which misses `σ = 0` by construction.

No consumer: it keeps the deformation off `σ = 0`, which is needed only while
the origin is a POLE of the integrand.  Dividing the double root out removes the
pole, so there is nothing left to stay clear of. -/
theorem modInterp_ne_one {δ t : ℝ} {w : ℂ} (hw : 1 ≤ ‖w‖)
    (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 < δ) : modInterp δ t w ≠ 1 := by
  intro hc
  have h1 := one_add_le_norm_modInterp hw ht.le ht1 hδ.le
  rw [hc] at h1
  simp at h1
  nlinarith

/-- **At `t = 1` the homotopy lands exactly on the circle** `‖w‖ = 1 + δ`, which
is `C(-1, 1+δ)` in `σ`.  So one homotopy suffices: the radial scaling leaves a
scaled indentation, this does not.

The homotopy's circle end has no consumer: the circle it lands on is reached
directly, not as the end of a deformation. -/
theorem norm_modInterp_one {δ : ℝ} {w : ℂ} (hw : w ≠ 0) (hδ : 0 ≤ δ) :
    ‖modInterp δ 1 w‖ = 1 + δ := by
  rw [norm_modInterp hw (by simp; linarith)]
  ring

/-! ### Which factors need the contour split, and which do not

The evaluation of the contour integral runs `F'/F` factor by factor, and each
factor's logarithmic derivative has a principal `Complex.log` as a primitive
exactly where that factor stays off the branch cut.  The two lemmas below settle,
for every factor at once, whether it does.

The answer is asymmetric and it decides the file's shape: **every tail factor
stays in the right half-plane on the whole circle**, so no splitting is needed
for any of them, while the `k = 0` factor's real part `1 - V alpha` crosses zero
at `alpha = 1/V`.  So the only factor whose logarithm needs care along the arc is
the one that winds -- which is the same factor, and the same fact, that carries
`Delta arg G = 2 pi`. -/
/-- **Every tail factor stays in the right half-plane, on the WHOLE circle.**
`Re(1 - σv) = 1 + αv` at `α = -Re σ ≥ 0`, so for `v > 0` the real part never
drops below `1`.  No splitting of the contour is needed for these factors: the
principal `Complex.log` is a primitive of their logarithmic derivative along the
entire arc.

No consumer: it licenses a principal-log primitive for the tail factors, and the
count is taken by the argument principle rather than by evaluating a
logarithm. -/
theorem one_le_re_one_sub_mul {σ : ℂ} (hσ : ‖1 + σ‖ = 1) {w : ℝ} (hw : 0 ≤ w) :
    1 ≤ (1 - σ * (w : ℂ)).re := by
  obtain ⟨-, hα, -⟩ := normSq_eq_two_mul_of_norm_one hσ
  have hre : (1 - σ * (w : ℂ)).re = 1 + w * (-σ.re) := by
    simp [Complex.mul_re]; ring
  rw [hre]
  nlinarith

/-- The same for the distinguished factor, in the opposite direction: `v₀ < 0`
makes `Re(1 - σv₀) = 1 - Vα`, which DOES cross zero -- at `α = 1/V`.  So `k = 0`
is the only factor whose logarithm needs care along the arc, and it is the one
that winds.

No consumer: it isolates the single factor whose logarithm needs a branch, and
no logarithm is evaluated. -/
theorem re_one_sub_mul_neg (σ : ℂ) (V : ℝ) :
    (1 - σ * ((-V : ℝ) : ℂ)).re = 1 - V * (-σ.re) := by
  simp [Complex.mul_re]; ring

/-- **On the main arc the homotopy has no `‖w‖` in it at all.**  There `‖w‖ = 1`,
so `modInterp` collapses to multiplication by the scalar `1 + tδ` -- polynomial
in `t` and independent of the point.  `ContDiffOn ℝ 2` on that piece is therefore
immediate, and the only piece where the norm survives is the indentation.

No consumer: it is half of Poincare's `hcontdiff` for the homotopy. -/
theorem modInterp_of_norm_one {δ t : ℝ} {w : ℂ} (hw : ‖w‖ = 1) :
    modInterp δ t w = ((1 + t * δ : ℝ) : ℂ) * w := by
  rw [modInterp, hw]
  norm_num
  exact Or.inl (by ring)

/-- The indentation is the only piece whose homotopy sees the norm, and there the
norm is bounded away from zero by the contour's own geometry, so it is smooth.

No consumer: it is the other half of that `hcontdiff`. -/
theorem norm_pos_of_one_le {w : ℂ} (hw : 1 ≤ ‖w‖) : 0 < ‖w‖ := by linarith


end ForgacsTran
