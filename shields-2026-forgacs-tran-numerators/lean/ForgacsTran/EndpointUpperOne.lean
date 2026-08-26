/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.InteriorSeparation

/-!
# The upper endpoint at `r = 1`: the pair collides at a finite point

At `2 ≤ r` the viewing arc ends at the origin — `τ → 0`, the whole `r`-cluster
collapses, and the spectral parameter is unbounded.  At `r = 1` none of that
happens.  `FTBranchEndpointUpper.exists_tendsto_ftTau_nhdsLT_pi` gives a positive
limit `L` for the branch radius and identifies `-L` as a zero of `E`, and
`exists_tendsto_ftBranchZ_arc_end_pi` gives a finite limit for `z`.  The principal
point `τ(θ)e^{iθ}` and its conjugate therefore both run into the **same** finite
point `-L` on the negative real axis.

That single geometric fact is what the `r = 1` upper endpoint's three binders all
rest on, and it is why none of them can be imported from the `2 ≤ r` side:

* the retained set needs a circle around a *collision*, not around a collapse;
* `hCbd₁` cannot come from `z t^r` dominating `Q`, because `‖z‖` stays bounded —
  `EndpointSeparation`'s upper circle asks for `ftUpperWindow ≤ ‖z‖` and nothing
  ever clears it here;
* `hamp₁` sees a residue whose denominator vanishes, so the amplitude does not
  vanish at the endpoint the way it does at `2 ≤ r`.

This module proves the fact itself: at the endpoint parameter, the pencil has a
**double** root at `-L`.  Both halves come from the same two identities — the
branch's own `z = -Q(t)/t^r`, and `E(t) = tQ'(t) - rQ(t)` vanishing at `-L`.

`FTMinModulus.UpperEndpoint` is not the place to look for any of this: it is
Proposition 3 Case 3, the `2 ≤ r` collapse, and carries nothing about `r = 1`.

**A separating radius here and one across the interior are the same comparison
with opposite answers, and neither is inferable from the shape.**  Both ask
whether a supremum of `τ` clears an infimum of the next modulus taken at a
*different* angle.  Across the compact interior it fails badly — `inf third /
sup τ` is measured at `0.12` at `2 ≤ r`, which is why that side needs a finite
cover and why the fixed-circle form of the interior block is false there.  Near
this endpoint it holds with an order of magnitude to spare, measured at `8.5` to
`11`.  So a fixed radius is the right construction here and a cover is not
needed; reasoning from the resemblance to the interior case gives the wrong
answer, and reasoning from `r = 1` being "the easy end" gave the wrong answer in
the other direction earlier.  Only the measurement settles it.

## Main statements

* `two_le_rootMultiplicity_ftDen_endpoint_pi` — the collision, as a multiplicity.
* `eval_derivative_prod_sub_neg`, `eval_derivative_two_ftRootPolyReal_pos` — `Q''`
  is strictly positive on the negative axis, by a sign argument on a product.
* `rootMultiplicity_ftDen_endpoint_pi_eq_two` — the collision is exactly double,
  which is the count `n_1 = r - 2 = 0`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `subsec:proof`, `eq:ab-def`.

## Tags

upper endpoint, finite endpoint, double root, Forgács–Tran branch
-/

namespace ForgacsTran

open Polynomial

/-- **The `r = 1` upper endpoint is a collision, as a statement about
multiplicity.**  At the endpoint parameter `b = -Q(-L)/(-L)`, the pencil has a
root of order at least two at `-L`.

Only two facts enter: `b` is the branch's own value there, which makes `-L` a root
at all, and `E(-L) = 0`, which is exactly what makes the derivative vanish too —
`E(t) = tQ'(t) - rQ(t)` at `r = 1` says `Q'(-L) = Q(-L)/(-L) = -b`.  So the double
root is not an extra hypothesis about the pencil; it is the endpoint condition
`exists_tendsto_ftTau_nhdsLT_pi` already delivers, read as a root order. -/
theorem two_le_rootMultiplicity_ftDen_endpoint_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) :
    2 ≤ (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).rootMultiplicity
      ((-L : ℝ) : ℂ) := by
  classical
  set P : Polynomial ℝ := ftRootPolyReal c a with hP
  set b : ℝ := -(P.eval (-L)) / (-L) with hb
  have hLne : (-L : ℝ) ≠ 0 := by intro h; simp at h; linarith
  have hmap : ftRootPoly c a = P.map (algebraMap ℝ ℂ) := by
    rw [hP, ftRootPoly, ftRootPolyReal, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_prod]
    simp
  -- the two values at `-L`, transported from `ℝ`
  have hval : (ftRootPoly c a).eval ((-L : ℝ) : ℂ) = ((P.eval (-L) : ℝ) : ℂ) := by
    rw [hmap, Polynomial.eval_map]
    simpa using Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) (-L : ℝ)
  have hdval : (derivative (ftRootPoly c a)).eval ((-L : ℝ) : ℂ)
      = (((derivative P).eval (-L) : ℝ) : ℂ) := by
    rw [hmap, Polynomial.derivative_map, Polynomial.eval_map]
    simpa using Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) (-L : ℝ)
  -- `E(-L) = 0` is the derivative relation
  have hEr : (-L) * (derivative P).eval (-L) - P.eval (-L) = 0 := by
    simpa using hE
  have hPval : P.eval (-L) = (-L) * (derivative P).eval (-L) := by linarith [hEr]
  have hdb : (derivative P).eval (-L) + b = 0 := by
    rw [hb, hPval]
    field_simp
    ring
  -- the pencil is nonzero, because it does not vanish at the origin
  have hDne : ftDen (ftRootPoly c a) 1 ((b : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hev : (ftDen (ftRootPoly c a) 1 ((b : ℝ) : ℂ)).eval 0 = (ftRootPoly c a).eval 0 := by
      rw [ftDen_eval]; simp
    rw [h0] at hev
    simp only [Polynomial.eval_zero] at hev
    refine absurd hev.symm ?_
    rw [eval_ftRootPoly]
    exact mul_ne_zero (by exact_mod_cast hc)
      (Finset.prod_ne_zero_iff.2 fun k _ => by
        simpa using (by exact_mod_cast (ha k).ne' : ((a k : ℝ) : ℂ) ≠ 0))
  refine (Polynomial.one_lt_rootMultiplicity_iff_isRoot hDne).2 ⟨?_, ?_⟩
  · -- `b` is the branch's own value, so `-L` is a root
    have hLC : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [Polynomial.IsRoot, ftDen_eval, hval, pow_one, hb]
    push_cast
    field_simp
    ring
  · -- and `E(-L) = 0` makes the derivative vanish there too
    rw [Polynomial.IsRoot, eval_derivative_ftDen_eq, hdval]
    simp only [Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
    exact_mod_cast hdb

/-! ### The collision is simple: the multiplicity at `-L` is exactly two

The lower bound above needs only `E(-L) = 0`.  The upper bound needs
`D_b''(-L) != 0`, and at `r = 1` that is `Q''(-L)`, which is a statement about
`Q` alone at a **negative** point.  There every factor `a_k - t` of
`Q = c\prod(a_k - t)` is positive, so the whole thing is a sign argument on a
product and no estimate is involved. -/

/-- A nonempty product of factors `a_i - X`, all of whose roots lie to the right
of `x`, is strictly decreasing at `x`. -/
theorem eval_derivative_prod_sub_neg {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {a : ι → ℝ} {x : ℝ} (ha : ∀ i ∈ s, x < a i) :
    (derivative (∏ i ∈ s, ((Polynomial.C (a i) : ℝ[X]) - Polynomial.X))).eval x < 0 := by
  classical
  have hpos : ∀ t : Finset ι, (∀ i ∈ t, x < a i) →
      0 < (∏ i ∈ t, ((Polynomial.C (a i) : ℝ[X]) - Polynomial.X)).eval x := by
    intro t ht
    rw [Polynomial.eval_prod]
    exact Finset.prod_pos fun i hi => by simpa using sub_pos.2 (ht i hi)
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  have hterm : ∀ i ∈ s,
      (((∏ j ∈ s.erase i, ((Polynomial.C (a j) : ℝ[X]) - Polynomial.X))
        * derivative ((Polynomial.C (a i) : ℝ[X]) - Polynomial.X)).eval x) < 0 := by
    intro i hi
    have := hpos (s.erase i) (fun j hj => ha j (Finset.mem_of_mem_erase hj))
    simp only [derivative_sub, derivative_C, derivative_X, zero_sub,
      Polynomial.eval_neg, mul_neg, mul_one, neg_lt_zero]
    exact this
  exact Finset.sum_neg hterm hs

/-- **`Q''` is strictly positive on the negative axis.**  Two applications of the
product rule leave a sum of products of `a_k - x`, every one of them positive
when `x < 0 < a_k`, and `2 <= n` is what makes the sum nonempty. -/
theorem eval_derivative_two_ftRootPolyReal_pos {n : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {x : ℝ} (hx : x < 0) :
    0 < (derivative (derivative (ftRootPolyReal c a))).eval x := by
  classical
  have haX : ∀ i ∈ (Finset.univ : Finset (Fin n)), x < a i := fun i _ => lt_trans hx (ha i)
  have hcard : 2 ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hn2
  rw [ftRootPolyReal, derivative_C_mul, derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C]
  refine mul_pos hc ?_
  rw [Polynomial.derivative_prod_finset]
  have hsum : derivative (∑ i ∈ (Finset.univ : Finset (Fin n)),
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ((Polynomial.C (a j) : ℝ[X]) - Polynomial.X))
      * derivative ((Polynomial.C (a i) : ℝ[X]) - Polynomial.X))
      = ∑ i ∈ (Finset.univ : Finset (Fin n)),
        -derivative (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ((Polynomial.C (a j) : ℝ[X]) - Polynomial.X)) := by
    rw [derivative_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [derivative_sub]
  rw [hsum, Polynomial.eval_finsetSum]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 < (-derivative (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ((Polynomial.C (a j) : ℝ[X]) - Polynomial.X))).eval x := by
    intro i _
    have hne : ((Finset.univ : Finset (Fin n)).erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i)]
      omega
    have := eval_derivative_prod_sub_neg hne
      (fun j hj => haX j (Finset.mem_of_mem_erase hj))
    simpa using this
  exact Finset.sum_pos hterm ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

/-- **The collision is exactly double.**  With `Q'' > 0` on the negative axis, the
multiplicity at `-L` cannot reach three, so the pencil's roots inside a small
circle about `-L` are the principal pair and nothing else.

This is the count `n_1 = r - 2 = 0` at `r = 1`: the retained upper cluster is the
principal pair alone, and it is *exactly* the pair rather than at least it. -/
theorem rootMultiplicity_ftDen_endpoint_pi_eq_two {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) :
    (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).rootMultiplicity
      ((-L : ℝ) : ℂ) = 2 := by
  classical
  have hlow := two_le_rootMultiplicity_ftDen_endpoint_pi ha hc.ne' hL hE
  refine le_antisymm ?_ hlow
  by_contra hgt
  rw [Nat.not_le] at hgt
  have hroot2 := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 2) hgt
  have hiter : (derivative^[2] (ftDen (ftRootPoly c a) 1
      ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)))
      = derivative^[2] (ftRootPoly c a) := by
    simp [ftDen, Function.iterate_succ_apply', derivative_add]
  rw [hiter, Polynomial.IsRoot, eval_iterate_derivative_ftRootPoly] at hroot2
  have hpos : 0 < (derivative^[2] (ftRootPolyReal c a)).eval (-L) := by
    simpa [Function.iterate_succ_apply'] using
      eval_derivative_two_ftRootPolyReal_pos hn2 ha hc (by linarith : (-L : ℝ) < 0)
  exact absurd (by exact_mod_cast hroot2 : (derivative^[2] (ftRootPolyReal c a)).eval (-L) = 0)
    hpos.ne'

/-! ### How far the remaining roots sit, at `n = 3`

`D_b`'s constant term is `Q(0) = c\prod a_k` and its leading coefficient is
`c(-1)^n`, so the product of all its roots is exactly `\prod a_k`.  The collision
accounts for `(-L)^2 = L^2` of that, and at `n = 3` there is a single root left:
it sits at `\prod a_k / L^2`, and clearing the circle of radius `L` is therefore
the closed condition `\prod a_k > L^3` — no root-finding and no limit.

That condition is AM-GM.  `E(-L) = 0` says `Σ(-L) = 0` — and with
`ftSigmaReal a 1 s = \sum_k s/(a_k - s) + 1`
that is exactly `\sum_k L/(a_k + L) = 1`, which is the hypothesis taken below so
that the arithmetic does not depend on the pencil machinery; writing `u_k` for
those quotients gives `\sum u_k = 1`
and `a_k u_k = L(1 - u_k)`, so `\prod a_k = L^3 \prod(1-u_k)/\prod u_k` and
`1 - u_k` is the sum of the other two.  Hence `\prod a_k \ge 8L^3`, with equality
only when the three coincide — which is why the measured ratios sit just above
eight. -/

/-- `(y+z)(x+z)(x+y) ≥ 8xyz` on the positive reals: three applications of AM-GM
to the pairs, multiplied. -/
theorem eight_mul_prod_le_prod_add {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    8 * (x * y * z) ≤ (y + z) * (x + z) * (x + y) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
    mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, hx.le, hy.le, hz.le,
    mul_nonneg (mul_nonneg hx.le hy.le) hz.le]

/-- **At `n = 3`, the zeros clear the collision radius by a factor of eight.**
The endpoint condition `Σ(-L) = 0` pins `\sum_k L/(a_k+L) = 1`, and AM-GM on that
constraint gives `\prod a_k \ge 8L^3`.

Since the product of `D_b`'s roots is `\prod a_k` and the collision takes `L^2`,
the one remaining root sits at `\prod a_k / L^2 \ge 8L`: it clears the circle of
radius `L` with room, which is what a fixed separating radius near `θ = π` needs.
The bound is sharp at `a_1 = a_2 = a_3`, where every `u_k` is `1/3`. -/
theorem eight_mul_pow_le_prod_of_sum_eq_one {a : Fin 3 → ℝ}
    (ha : ∀ k, 0 < a k) {L : ℝ} (hL : 0 < L) (hsum1 : ∑ k, L / (a k + L) = 1) :
    8 * L ^ 3 ≤ ∏ k, a k := by
  have hpos : ∀ k, 0 < a k + L := fun k => by linarith [ha k]
  set u : Fin 3 → ℝ := fun k => L / (a k + L) with hu
  have hupos : ∀ k, 0 < u k := fun k => div_pos hL (hpos k)
  have hsum : u 0 + u 1 + u 2 = 1 := by
    rw [Fin.sum_univ_three] at hsum1
    exact hsum1
  -- `a k * u k = L * (1 - u k)`
  have hau : ∀ k, a k * u k = L * (1 - u k) := by
    intro k
    rw [hu]
    field_simp [(hpos k).ne']
    ring
  have h0 := hau 0
  have h1 := hau 1
  have h2 := hau 2
  have hprodu : 0 < u 0 * u 1 * u 2 := mul_pos (mul_pos (hupos 0) (hupos 1)) (hupos 2)
  -- the three complements are the pairwise sums
  have hc0 : 1 - u 0 = u 1 + u 2 := by linarith
  have hc1 : 1 - u 1 = u 0 + u 2 := by linarith
  have hc2 : 1 - u 2 = u 0 + u 1 := by linarith
  have hkey := eight_mul_prod_le_prod_add (hupos 0) (hupos 1) (hupos 2)
  rw [Fin.prod_univ_three]
  -- multiply the three relations and compare
  have hmul : (a 0 * a 1 * a 2) * (u 0 * u 1 * u 2)
      = L ^ 3 * ((u 1 + u 2) * (u 0 + u 2) * (u 0 + u 1)) := by
    have := congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2
    simp only [hc0, hc1, hc2] at this
    nlinarith [this]
  nlinarith [hkey, hprodu, hmul, pow_pos hL 3]

/-! ### The count inside a fixed circle, transferred to the endpoint

`InteriorSeparation.card_rootsIn_ftDen_eventuallyEq` holds the root count fixed
near a base *angle*, through `ContinuousAt` of the spectral parameter there.  The
endpoint is not an angle of the branch — `θ = π/r` is outside the open arc, and
what exists there is a *limit* `b`, not a value.  So the same argument is needed
against `Tendsto` along any filter, with the zero-free circle taken at the limit.

The proof is the original's: the count can only change when a zero crosses the
circle, and `‖z θ - b‖` small enough keeps it clear. -/

/-- **The root count near a limit of the spectral parameter.**  Along any filter on
which `z` tends to `b`, the number of zeros inside a circle that `D(·,b)` leaves
clear is eventually the number `D(·,b)` itself has there. -/
theorem card_rootsIn_ftDen_eventuallyEq_of_tendsto {Q : Polynomial ℂ} {r : ℕ} {R : ℝ}
    (hR : 0 < R) {z : ℝ → ℝ} {l : Filter ℝ} {b : ℂ}
    (hz : Filter.Tendsto (fun θ => ((z θ : ℝ) : ℂ)) l (nhds b))
    (hns : ∀ t ∈ Metric.sphere (0 : ℂ) R, (ftDen Q r b).eval t ≠ 0) :
    ∀ᶠ θ in l,
      (Shields.rootsIn (ftDen Q r ((z θ : ℝ) : ℂ)) 0 R).card
        = (Shields.rootsIn (ftDen Q r b) 0 R).card := by
  obtain ⟨m, hmpos, hm⟩ := exists_min_norm_on_sphere hR hns
  have hRr : (0 : ℝ) < R ^ r := pow_pos hR r
  have hball : ∀ᶠ θ in l, ‖((z θ : ℝ) : ℂ) - b‖ < m / R ^ r := by
    have := hz (Metric.ball_mem_nhds b (by positivity : (0 : ℝ) < m / R ^ r))
    filter_upwards [this] with θ hθ
    simpa [Complex.dist_eq] using Metric.mem_ball.1 hθ
  filter_upwards [hball] with θ hθ
  refine (card_rootsIn_ftDen_eq_of_norm_lt hR hm ?_).symm
  rw [← lt_div_iff₀ hRr]
  exact hθ

/-! ### Vieta at the endpoint

The product of `D_b`'s roots is `\prod a_k`, from one coefficient ratio: the
constant term is `Q(0) = c\prod a_k`, the leading coefficient is `c(-1)^n`, and
the two `(-1)^n` cancel.  At `n = 3` the collision takes `L^2` of that product and
there is a single root left, so its modulus is `\prod a_k/L^2` — which
`eight_mul_pow_le_prod_of_sum_eq_one` puts at or above `8L`. -/

/-- The leading coefficient of `Q = c\prod(a_k - X)`: each factor contributes
`-1`. -/
theorem leadingCoeff_ftRootPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    (ftRootPoly c a).leadingCoeff = (c : ℂ) * (-1) ^ n := by
  classical
  rw [ftRootPoly, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_prod]
  congr 1
  have : ∀ k : Fin n, ((Polynomial.C ((a k : ℝ) : ℂ) - Polynomial.X)).leadingCoeff = -1 := by
    intro k
    have h : (Polynomial.C ((a k : ℝ) : ℂ) - Polynomial.X)
        = -(Polynomial.X - Polynomial.C ((a k : ℝ) : ℂ)) := by ring
    rw [h, Polynomial.leadingCoeff_neg, Polynomial.monic_X_sub_C ((a k : ℝ) : ℂ)]
  rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The pencil at `r = 1` has the numerator's degree and leading coefficient once
`2 ≤ n`, because the added term `zX` cannot reach degree `n`. -/
theorem natDegree_and_leadingCoeff_ftDen_one {n : ℕ} {c : ℝ} (hc : c ≠ 0) (a : Fin n → ℝ)
    (hn2 : 2 ≤ n) (z : ℂ) :
    (ftDen (ftRootPoly c a) 1 z).natDegree = n
      ∧ (ftDen (ftRootPoly c a) 1 z).leadingCoeff = (c : ℂ) * (-1) ^ n := by
  classical
  have hQdeg : (ftRootPoly c a).natDegree = n := natDegree_ftRootPoly hc a
  have hsmall : (Polynomial.C z * Polynomial.X ^ 1).degree < (ftRootPoly c a).degree := by
    have hQne : ftRootPoly c a ≠ 0 := by
      intro h0
      rw [h0] at hQdeg
      simp at hQdeg
      omega
    have hdegQ : (ftRootPoly c a).degree = (n : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hQne, hQdeg]
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 1 z) ?_
    rw [hdegQ]
    exact_mod_cast (by omega : (1 : ℕ) < n)
  constructor
  · rw [ftDen, Polynomial.natDegree_add_eq_left_of_degree_lt hsmall, hQdeg]
  · rw [ftDen, Polynomial.leadingCoeff_add_of_degree_lt' hsmall, leadingCoeff_ftRootPoly]

/-- **The product of the pencil's roots is `\prod a_k`, at `r = 1` and `2 ≤ n`.**
One coefficient ratio: the constant term is `Q(0) = c\prod a_k`, the leading
coefficient is `c(-1)^n`, and the sign from `\prod(0 - root)` cancels the sign in
the leading coefficient exactly.  The spectral parameter drops out — `zX` has no
constant term and cannot reach the leading one — so the identity holds along the
whole branch, not only at the endpoint. -/
theorem prod_roots_ftDen_one {n : ℕ} {c : ℝ} (hc : c ≠ 0) {a : Fin n → ℝ}
    (ha : ∀ k, 0 < a k) (hn2 : 2 ≤ n) (z : ℂ) :
    (ftDen (ftRootPoly c a) 1 z).roots.prod = ((∏ k, a k : ℝ) : ℂ) := by
  classical
  obtain ⟨hdeg, hlead⟩ := natDegree_and_leadingCoeff_ftDen_one hc a hn2 z
  set p : Polynomial ℂ := ftDen (ftRootPoly c a) 1 z with hp
  have hpne : p ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
    omega
  have hcard : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits p)
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  -- evaluate the factorization at the origin
  have h0 : p.eval 0 = p.leadingCoeff * ((-1) ^ n * p.roots.prod) := by
    conv_lhs => rw [← hfac]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod]
    congr 1
    rw [Multiset.map_map]
    have hmap : (p.roots.map ((fun q => Polynomial.eval 0 q) ∘
        (fun r => Polynomial.X - Polynomial.C r))) = p.roots.map (fun r => -r) := by
      refine Multiset.map_congr rfl fun r _ => ?_
      simp
    rw [hmap, Multiset.prod_map_neg, hcard, hdeg]
  have hval : p.eval 0 = ((c : ℝ) : ℂ) * ((∏ k, a k : ℝ) : ℂ) := by
    rw [hp, ftDen_eval, eval_ftRootPoly]
    push_cast
    simp
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hsq : ((-1 : ℂ)) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  rw [hval, hlead] at h0
  have hrhs : ((c : ℝ) : ℂ) * ((∏ k, a k : ℝ) : ℂ) = ((c : ℝ) : ℂ) * p.roots.prod := by
    rw [h0]
    calc (((c : ℝ) : ℂ) * (-1) ^ n) * ((-1) ^ n * p.roots.prod)
        = ((c : ℝ) : ℂ) * (((-1 : ℂ)) ^ n * (-1) ^ n) * p.roots.prod := by ring
      _ = ((c : ℝ) : ℂ) * p.roots.prod := by rw [hsq]; ring
  exact (mul_left_cancel₀ hcne hrhs).symm

/-! ### The assembly at `n = 3`

Every ingredient is now proved: the collision is a root of multiplicity exactly
two, the roots multiply to `\prod a_k`, and `\prod a_k \ge 8L^3`.  What is left is
to read off the one remaining root and place it.

Two things are stated concretely rather than existentially on purpose.  The
remaining root is *identified* — `roots.card = 3` against `count(-L) = 2` leaves a
multiset of card one, and membership picks out its element — rather than assumed
to exist; and the separating radius is `2L`, a named number between `L` and `8L`,
rather than "some radius in the gap".  Both are places where a statement with the
quantifier one level out would type-check and say less. -/

/-- **The remaining root's modulus, exactly.**  At `n = 3` the collision uses two
of the three roots, so exactly one is left, and Vieta fixes it: `L^2‖w‖ = ∏ a_k`.

This is the **position-free** half of the placement: it says where the root is
without asserting any margin.  Every clearance statement below follows from it plus
a lower bound on `∏ a_k`, and only that lower bound carries a constant — which is
why the clearance transfers to the lower endpoint and the constant does not. -/
theorem norm_mul_sq_eq_prod_of_mem_roots_endpoint_pi {a : Fin 3 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    {w : ℂ} (hw : w ∈ (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).roots)
    (hne : w ≠ ((-L : ℝ) : ℂ)) :
    L ^ 2 * ‖w‖ = ∏ k, a k := by
  set b : ℝ := -((ftRootPolyReal c a).eval (-L)) / (-L) with hb
  set p : Polynomial ℂ := ftDen (ftRootPoly c a) 1 ((b : ℝ) : ℂ) with hpdef
  have hn2 : (2 : ℕ) ≤ 3 := by norm_num
  obtain ⟨hdeg, -⟩ := natDegree_and_leadingCoeff_ftDen_one hc.ne' a hn2 ((b : ℝ) : ℂ)
  have hcard : p.roots.card = 3 := by
    rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits p), hdeg]
  have hmult : p.roots.count ((-L : ℝ) : ℂ) = 2 := by
    rw [Polynomial.count_roots]
    exact rootMultiplicity_ftDen_endpoint_pi_eq_two hn2 ha hc hL hE
  have hsplit : p.roots.filter (fun r => r = ((-L : ℝ) : ℂ))
      + p.roots.filter (fun r => ¬ (r = ((-L : ℝ) : ℂ))) = p.roots :=
    Multiset.filter_add_not _ _
  have heq : p.roots.filter (fun r => r = ((-L : ℝ) : ℂ))
      = Multiset.replicate 2 ((-L : ℝ) : ℂ) := by
    rw [Multiset.filter_eq', hmult]
  have hrest : (p.roots.filter (fun r => ¬ (r = ((-L : ℝ) : ℂ)))).card = 1 := by
    have hc' := congrArg Multiset.card hsplit
    rw [Multiset.card_add, heq, Multiset.card_replicate, hcard] at hc'
    omega
  obtain ⟨w', hw'⟩ := Multiset.card_eq_one.1 hrest
  have hww : w = w' := by
    have hmem : w ∈ p.roots.filter (fun r => ¬ (r = ((-L : ℝ) : ℂ))) :=
      Multiset.mem_filter.2 ⟨hw, hne⟩
    rw [hw'] at hmem
    simpa using hmem
  -- Vieta, read against the split
  have hprod : p.roots.prod = ((∏ k, a k : ℝ) : ℂ) :=
    prod_roots_ftDen_one hc.ne' ha hn2 _
  have hval : p.roots.prod = ((-L : ℝ) : ℂ) ^ 2 * w' := by
    conv_lhs => rw [← hsplit]
    rw [Multiset.prod_add, heq, Multiset.prod_replicate, hw', Multiset.prod_singleton]
  have hnorm : L ^ 2 * ‖w'‖ = ∏ k, a k := by
    have h1 : ‖((∏ k, a k : ℝ) : ℂ)‖ = ‖((-L : ℝ) : ℂ) ^ 2 * w'‖ := by
      rw [← hprod, hval]
    have hlhs : ‖((∏ k, a k : ℝ) : ℂ)‖ = ∏ k, a k := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Finset.prod_pos fun k _ => ha k)]
    have hrhs : ‖((-L : ℝ) : ℂ) ^ 2 * w'‖ = L ^ 2 * ‖w'‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hL]
    rw [hlhs, hrhs] at h1
    exact h1.symm
  rw [hww]
  exact hnorm

/-- **Every root but the collision clears `8L`.**  At `n = 3` the collision uses
two of the three roots, so exactly one is left; Vieta puts it at
`\prod a_k / L^2`, and the AM-GM bound puts that at or above `8L`.

`hE` and `hsum1` are the same fact — `Σ(-L) = 0` — in the two spellings the
callers have: `FTBranchEndpointUpper.exists_tendsto_ftTau_nhdsLT_pi` returns the
first, and `FTMinModulus.RealCritical.eval_ftCriticalReal_eq_neg_sigma_mul`
converts between them. -/
theorem eight_mul_le_norm_of_mem_roots_endpoint_pi {a : Fin 3 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hsum1 : ∑ k, L / (a k + L) = 1)
    {w : ℂ} (hw : w ∈ (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).roots)
    (hne : w ≠ ((-L : ℝ) : ℂ)) :
    8 * L ≤ ‖w‖ := by
  have hnorm := norm_mul_sq_eq_prod_of_mem_roots_endpoint_pi ha hc hL hE hw hne
  have hAM : 8 * L ^ 3 ≤ ∏ k, a k := eight_mul_pow_le_prod_of_sum_eq_one ha hL hsum1
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  nlinarith [hnorm, hAM, hL2, norm_nonneg w]

/-- **The circle of radius `2L` carries no zero of the endpoint pencil.**  The
roots are the collision at modulus `L` and one root at modulus at least `8L`, and
`2L` is between them.  This is the side condition
`card_rootsIn_ftDen_eventuallyEq_of_tendsto` needs, and it is stated at the same
named radius the count below uses rather than at "some radius in the gap". -/
theorem eval_ne_zero_on_sphere_two_mul_endpoint_pi {a : Fin 3 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hsum1 : ∑ k, L / (a k + L) = 1) :
    ∀ t ∈ Metric.sphere (0 : ℂ) (2 * L),
      (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).eval t ≠ 0 := by
  classical
  intro t ht hzero
  set p : Polynomial ℂ := ftDen (ftRootPoly c a) 1
    ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ) with hpdef
  obtain ⟨hdeg, -⟩ :=
    natDegree_and_leadingCoeff_ftDen_one hc.ne' a (by norm_num : (2 : ℕ) ≤ 3)
      ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)
  rw [← hpdef] at hdeg
  have hpne : p ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
  have hnt : ‖t‖ = 2 * L := by
    simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 ht
  have hmem : t ∈ p.roots := Polynomial.mem_roots'.2 ⟨hpne, hzero⟩
  by_cases hne : t = ((-L : ℝ) : ℂ)
  · rw [hne, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hL] at hnt
    linarith
  · have h8 := eight_mul_le_norm_of_mem_roots_endpoint_pi ha hc hL hE hsum1 hmem hne
    rw [hnt] at h8
    linarith

/-- **The count inside the circle of radius `2L` is two**: the collision, with its
multiplicity, and nothing else.  That is `n_1 = r - 2 = 0` made concrete — the
retained upper cluster at `r = 1` is the principal pair alone.

Combined with `card_rootsIn_ftDen_eventuallyEq_of_tendsto` and the limit
`FTBranchEndpointUpper.exists_tendsto_ftBranchZ_arc_end_pi`, the same count holds
at every angle near `π`, which is the fixed separating radius the retained set
needs. -/
theorem card_rootsIn_endpoint_pi_eq_two {a : Fin 3 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hsum1 : ∑ k, L / (a k + L) = 1) :
    (Shields.rootsIn (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)) 0 (2 * L)).card = 2 := by
  classical
  set p : Polynomial ℂ := ftDen (ftRootPoly c a) 1
    ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ) with hpdef
  have hmult : p.roots.count ((-L : ℝ) : ℂ) = 2 := by
    rw [Polynomial.count_roots]
    exact rootMultiplicity_ftDen_endpoint_pi_eq_two (by norm_num) ha hc hL hE
  have hfil : p.roots.filter (fun r => dist r 0 < 2 * L)
      = p.roots.filter (fun r => r = ((-L : ℝ) : ℂ)) := by
    refine Multiset.filter_congr fun r hr => ?_
    constructor
    · intro hlt
      by_contra hne
      have h8 := eight_mul_le_norm_of_mem_roots_endpoint_pi ha hc hL hE hsum1 hr hne
      rw [dist_zero_right] at hlt
      linarith
    · intro heq
      rw [heq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hL]
      linarith
  rw [Shields.rootsIn, hfil, Multiset.filter_eq', hmult, Multiset.card_replicate]

/-- **The separating radius near the upper endpoint at `r = 1`, `n = 3`.**  On any
filter along which the branch radius tends to `L`, the circle of radius `2L`
eventually contains exactly two zeros of the pencil — the principal pair, with
nothing else.

The limit is taken from `FTMinModulus.UpperEndpoint.tendsto_ftBranchZ_upper_pi`
rather than from `exists_tendsto_ftBranchZ_arc_end_pi`: the latter's existential
discards the value of `b`, and every statement here is about the pencil *at that
value*.  A wrapper that hides the constant is unusable exactly where the constant
is what the rest of the argument names. -/
theorem eventually_card_rootsIn_eq_two_near_pi {a : Fin 3 → ℝ} {c : ℝ} {l : ℕ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} {S : Set ℝ} (hL : 0 < L)
    (hmem : ∀ᶠ θ in nhdsWithin Real.pi S, θ ∈ Set.Ioo 0 Real.pi ∧ FTBranchAt a 1 l θ)
    (hτ : Filter.Tendsto (ftTau a 1 l) (nhdsWithin Real.pi S) (nhds L))
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hsum1 : ∑ k, L / (a k + L) = 1) :
    ∀ᶠ θ in nhdsWithin Real.pi S,
      (Shields.rootsIn (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 l θ : ℝ) : ℂ))
        0 (2 * L)).card = 2 := by
  have hz := tendsto_ftBranchZ_upper_pi (c := c) ha hL hmem hτ
  rw [pow_one] at hz
  have hzC : Filter.Tendsto (fun θ => ((ftBranchZ a c 1 l θ : ℝ) : ℂ))
      (nhdsWithin Real.pi S)
      (nhds ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto _).comp hz
  have hcount := card_rootsIn_ftDen_eventuallyEq_of_tendsto (Q := ftRootPoly c a) (r := 1)
    (by linarith : (0 : ℝ) < 2 * L) hzC
    (eval_ne_zero_on_sphere_two_mul_endpoint_pi ha hc hL hE hsum1)
  filter_upwards [hcount] with θ hθ
  rw [hθ]
  exact card_rootsIn_endpoint_pi_eq_two ha hc hL hE hsum1

/-! ### The separating radius as a parameter

The two statements above pin the radius at the literal `2L`, and at *this* endpoint
that is right: `∏ a_k ≥ 8L^3` is uniform, so `2L` always sits in the gap and a
literal cannot drift.

**At the lower endpoint no such constant exists.**  Writing `v_k = t_a/(a_k - t_a)`,
the endpoint condition `Σ(t_a) = 0` is `∑ v_k = -r`, and the clearance ratio is
`∏ a_k/t_a^3 = ∏(1 + 1/v_k)`.  At `ρ = 1` exactly one `v_k` lies below `-1` — the
zero to the left of `t_a` — and the product can be driven to `1`: on
`a = (1, 1+ε, 1+2ε)` it is `1 + √3 ε + O(ε^2)`, measured at `1.78, 1.169, 1.0173,
1.00173, 1.000173` for `ε = 1/2, 10^{-1}, …, 10^{-4}`.  The infimum is `1`,
unattained, so **no `K > 1` bounds it below and `2·t_a` is simply false on a thin
pencil.**  The confluent limit is `ρ → 3`, so the case is never violated; nothing
uniform survives the approach to it.

Hence the forms below, which take the radius and the two inequalities it must
satisfy.  They say what is true at both endpoints; the literals above are this
statement at one endpoint where a constant happens to exist.  Stating only the
literal form would invite a reader to carry the constant to a place that has
none. -/

/-- **The circle of radius `R` is zero-free**, for any `R` strictly between the
collision radius and the remaining root's modulus `∏ a_k / L^2`. -/
theorem eval_ne_zero_on_sphere_of_radius {a : Fin 3 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    {R : ℝ} (hRlow : L < R) (hRhigh : R < (∏ k, a k) / L ^ 2) :
    ∀ t ∈ Metric.sphere (0 : ℂ) R,
      (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).eval t ≠ 0 := by
  classical
  intro t ht hzero
  set p : Polynomial ℂ := ftDen (ftRootPoly c a) 1
    ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ) with hpdef
  obtain ⟨hdeg, -⟩ :=
    natDegree_and_leadingCoeff_ftDen_one hc.ne' a (by norm_num : (2 : ℕ) ≤ 3)
      ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)
  rw [← hpdef] at hdeg
  have hpne : p ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
  have hnt : ‖t‖ = R := by
    simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 ht
  have hmem : t ∈ p.roots := Polynomial.mem_roots'.2 ⟨hpne, hzero⟩
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  by_cases hne : t = ((-L : ℝ) : ℂ)
  · rw [hne, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hL] at hnt
    linarith
  · have hex := norm_mul_sq_eq_prod_of_mem_roots_endpoint_pi ha hc hL hE hmem hne
    rw [hnt] at hex
    rw [lt_div_iff₀ hL2] at hRhigh
    nlinarith [hex, hRhigh]

/-- **The count inside a circle of radius `R` is two**, for any `R` in the gap.
`card_rootsIn_endpoint_pi_eq_two` is this at `R := 2L`, where `∏ a_k ≥ 8L^3` puts
`2L` in the gap; the lower endpoint has no such constant and must supply its own
`R`. -/
theorem card_rootsIn_eq_two_of_radius {a : Fin 3 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    {R : ℝ} (hRlow : L < R) (hRhigh : R ≤ (∏ k, a k) / L ^ 2) :
    (Shields.rootsIn (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)) 0 R).card = 2 := by
  classical
  set p : Polynomial ℂ := ftDen (ftRootPoly c a) 1
    ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ) with hpdef
  have hmult : p.roots.count ((-L : ℝ) : ℂ) = 2 := by
    rw [Polynomial.count_roots]
    exact rootMultiplicity_ftDen_endpoint_pi_eq_two (by norm_num) ha hc hL hE
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  have hfil : p.roots.filter (fun r => dist r 0 < R)
      = p.roots.filter (fun r => r = ((-L : ℝ) : ℂ)) := by
    refine Multiset.filter_congr fun r hr => ?_
    constructor
    · intro hlt
      by_contra hne
      have hex := norm_mul_sq_eq_prod_of_mem_roots_endpoint_pi ha hc hL hE hr hne
      rw [dist_zero_right] at hlt
      rw [le_div_iff₀ hL2] at hRhigh
      nlinarith [hex, hRhigh]
    · intro heq
      rw [heq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hL]
      linarith
  rw [Shields.rootsIn, hfil, Multiset.filter_eq', hmult, Multiset.card_replicate]

end ForgacsTran
