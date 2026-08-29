/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# The normalized pencil at the origin and on the circle

`LowerSeparationNormalized` normalizes the lower endpoint's separation off the
pencil: with `v_k = t/(a_k - t)` and `σ = w/t - 1`, a root of the endpoint pencil
at the branch's own spectral value satisfies `∏_k (1 - σv_k) = (1+σ)^r`, and the
separation asks that every such `σ ≠ 0` has `|1 + σ| > 1`.  **That statement is
not proved**; its four closed routes are recorded in `banked.txt`.

What is proved is here, and none of it depends on which route eventually closes
the conjecture — these are facts about the admissible class itself, stated over
bare reals with the caller supplying the pencil.  They are the two inputs
`LowerSeparationQuotient` runs its argument principle on.

**Why the coefficients rather than the product.**  Stating the problem through
the coefficients of `ftNormPoly = ∏_k (1 - σv_k) - (1+σ)^r` is what makes the
double root at the origin structural: `c_0` vanishes with no hypothesis at all
and `c_1` vanishes exactly because `∑_k v_k = -r`, so the order-two zero is there
by construction rather than established first.  `c_2 < 0` then holds on the whole
admissible class, which pins the order at exactly two.

**Why the boundary half is exact rather than estimated.**  On `‖1+σ‖ = 1` the
real part and the modulus are locked — `‖σ‖² = 2α` at `α = -Re σ`, with `α` in
`[0,2]` — so each factor's modulus is a closed form `1 + 2wα + 2w²α` at real `w`.
Positive `w` gives at least `1`; `w = v_0 = -V` gives exactly `1 + 2Vα(V-1)`,
above `1` because `V > 1`.  So `‖G‖ > 1` off `σ = 0` and the two sides cannot
agree there.

Together the two say the pencil's zeros on that circle are exactly `σ = 0` with
multiplicity two, which is what makes an ordinary circular contour sufficient and
no indentation necessary.

## Main statements

* `lt_neg_of_sum_eq_neg_of_nonneg`, `lt_neg_of_sum_eq_neg` — `v_0 < -r` from the
  constraint alone, not as a hypothesis; `one_add_ne_zero_of_lt_neg` is the one
  job it does, and `lt_sum_sq_of_lt_neg` is what carries it into `c_2`.
* `norm_le_one_of_mem_confinement`,
  `eq_one_of_mem_confinement_of_norm_eq_one` — the confinement disk lies in the
  closed unit disk and touches the unit circle at one point.
* `ftNormPoly` and `ftNormPoly_coeff_zero`, `ftNormPoly_coeff_one`,
  `ftNormPoly_coeff_two`, `ftNormPoly_coeff_two_neg` — the normalized pencil and
  its first three coefficients: the first two vanish and the third is negative.
* `prod_ne_pow_of_norm_one` — the boundary half, with `one_lt_norm_prod_of_norm_one`
  and `prod_ne_zero_of_norm_one` the two steps it runs on.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
`thm:weighted-dominance`, `subsec:proof`.

## Tags

normalized pencil, lower endpoint, separation, double root
-/

namespace ForgacsTran

open Polynomial

/-! ### The lower endpoint's normalized separation: what is proved

Normalizing `c`, `t_a` and the zeros away turns the lower endpoint's separation
into a statement about bare reals: with `v_k > 0` for `k /= 0` and
`sum_k v_k = -r`, every `sigma /= 0` solving `prod_k (1 - sigma v_k) = (1+sigma)^r`
should satisfy `|1 + sigma| > 1`.  That statement is **not proved** and its four
closed routes are recorded in `banked.txt`.

What IS proved is below, and none of it depends on which route eventually closes
the conjecture -- these are facts about the admissible class itself.  They are
stated over bare reals, with the caller supplying the pencil, for the same reason
`two_le_prod_add_div_of_two_terms` is.

The normalized polynomial is `ftNormPoly`, and stating the problem through its
COEFFICIENTS rather than through the product is what makes the double root
structural: `c_0` and `c_1` vanish identically, the second exactly because
`sum_k v_k = -r`.  A statement built on the product has to establish the double
root before it can start; this one has it by construction. -/

/-- **`v_0` lies below `-r`, and is not a hypothesis.**  The tail is positive and
sums to `-r - v_0`, so `v_0 < -r` follows from the constraint alone.

**This must not be written down as an independent sign hypothesis.**  A reader
who finds one looks for the geometric fact that supplies it, and there is none --
it is arithmetic.  Where the bound genuinely earns its place is
`one_add_ne_zero_of_lt_neg`: it is a non-degeneracy, not a sign condition.

`-r` rather than `-1` is the form to derive.  At `r >= 2` the weaker bound gives
only `sum v^2 > 1`, which is not enough for `ftNormPoly_coeff_two_neg`. -/
theorem lt_neg_of_sum_eq_neg_of_nonneg {n : ℕ} {v : Fin n → ℝ} {r : ℝ} {i₀ j : Fin n}
    (hj : j ≠ i₀) (hjpos : 0 < v j) (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k)
    (hsum : ∑ k, v k = -r) : v i₀ < -r := by
  classical
  have hmem : j ∈ Finset.univ.erase i₀ := Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩
  have htail : 0 < ∑ k ∈ Finset.univ.erase i₀, v k :=
    lt_of_lt_of_le hjpos
      (Finset.single_le_sum (f := v) (fun k hk => hpos k (Finset.mem_erase.1 hk).1) hmem)
  have hsplit : v i₀ + ∑ k ∈ Finset.univ.erase i₀, v k = -r := by
    rw [Finset.add_sum_erase _ v (Finset.mem_univ i₀)]; exact hsum
  linarith

/-- The same, with the whole tail strictly positive.  A second index exists at
`2 ≤ n`, and it witnesses the sum. -/
theorem lt_neg_of_sum_eq_neg {n : ℕ} {v : Fin n → ℝ} {r : ℝ} {i₀ : Fin n}
    (hn : 2 ≤ n) (hpos : ∀ k, k ≠ i₀ → 0 < v k) (hsum : ∑ k, v k = -r) :
    v i₀ < -r := by
  classical
  have hne : (Finset.univ.erase i₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hjmem⟩ := hne
  have hj : j ≠ i₀ := (Finset.mem_erase.1 hjmem).1
  exact lt_neg_of_sum_eq_neg_of_nonneg hj (hpos j hj) (fun k hk => (hpos k hk).le) hsum

/-- **The one job `v_0 < -r` does.**  `1 + v_0 /= 0` is what legalizes the
substitution `p_k = v_k/(1 + v_k)`, under which the sign pattern becomes
`p_0 > 1` and `0 < p_k < 1`.  `v_0 = -1` is the single excluded value. -/
theorem one_add_ne_zero_of_lt_neg {v₀ r : ℝ} (hr : 1 ≤ r) (h : v₀ < -r) :
    1 + v₀ ≠ 0 := by
  intro hc; linarith

/-- **The second power sum exceeds `r`.**  `v_0 < -r` gives `v_0^2 > r^2 >= r` at
`1 <= r`, and the other squares only add.  This is the whole content of the
quadratic coefficient's sign, carried without naming `e_2`. -/
theorem lt_sum_sq_of_lt_neg {n : ℕ} {v : Fin n → ℝ} {r : ℝ} {i₀ : Fin n}
    (hr : 1 ≤ r) (h : v i₀ < -r) : r < ∑ k, (v k) ^ 2 := by
  classical
  have hsq : r < (v i₀) ^ 2 := by nlinarith
  have hrest : (v i₀) ^ 2 ≤ ∑ k, (v k) ^ 2 :=
    Finset.single_le_sum (f := fun k => (v k) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i₀)
  linarith

/-- **The confinement disk lies in the closed unit disk.**  `|1 + V sigma| <= 1`
reads, at `zeta = 1 + sigma`, as `|zeta - q| <= 1/V` with `q = 1 - 1/V` -- and
`1/V = 1 - q` identically, so centre plus radius is `1` for every `V`. -/
theorem norm_le_one_of_mem_confinement {V : ℝ} (hV : 1 ≤ V) {ζ : ℂ}
    (h : ‖ζ - ((1 - 1 / V : ℝ) : ℂ)‖ ≤ 1 / V) : ‖ζ‖ ≤ 1 := by
  have hV0 : (0:ℝ) < V := by linarith
  have hq : (0:ℝ) ≤ 1 - 1 / V := by
    have : 1 / V ≤ 1 := by rw [div_le_one hV0]; linarith
    linarith
  have hz : ζ = (ζ - ((1 - 1/V : ℝ) : ℂ)) + ((1 - 1/V : ℝ) : ℂ) := by ring
  calc ‖ζ‖ = ‖(ζ - ((1 - 1/V : ℝ) : ℂ)) + ((1 - 1/V : ℝ) : ℂ)‖ := by rw [← hz]
    _ ≤ ‖ζ - ((1 - 1/V : ℝ) : ℂ)‖ + ‖((1 - 1/V : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 1/V + (1 - 1/V) := by
        refine add_le_add h ?_
        rw [Complex.norm_real, Real.norm_of_nonneg hq]
    _ = 1 := by ring

/-- **The confinement disk is INTERNALLY TANGENT to the unit circle, and the point
of tangency is `zeta = 1`.**  Its only point of modulus `1` is `1` itself, which
is `sigma = 0`, which is the double root.

This is the geometric reason every contour route degenerates: the region a
violating root must occupy touches the boundary exactly where the polynomial
already vanishes to second order.  The degeneracy is in the geometry, not in the
choice of contour, which is why perturbing the contour does not help in either
direction. -/
theorem eq_one_of_mem_confinement_of_norm_eq_one {V : ℝ} (hV : 1 < V) {ζ : ℂ}
    (h : ‖ζ - ((1 - 1 / V : ℝ) : ℂ)‖ ≤ 1 / V) (hn : ‖ζ‖ = 1) : ζ = 1 := by
  have hV0 : (0:ℝ) < V := by linarith
  set q : ℝ := 1 - 1 / V with hqdef
  have hq0 : 0 < q := by
    rw [hqdef]
    have : 1 / V < 1 := by rw [div_lt_one hV0]; exact hV
    linarith
  have hrad : (1:ℝ) / V = 1 - q := by rw [hqdef]; ring
  have hsq : Complex.normSq (ζ - (q : ℂ)) ≤ (1 - q) ^ 2 := by
    have := h
    rw [hrad] at this
    have h2 : ‖ζ - (q : ℂ)‖ ^ 2 ≤ (1 - q) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    rwa [Complex.sq_norm] at h2
  have hone : Complex.normSq ζ = 1 := by
    rw [← Complex.sq_norm, hn]; norm_num
  have hre : ζ.re = 1 := by
    have hexp : Complex.normSq (ζ - (q : ℂ))
        = Complex.normSq ζ - 2 * q * ζ.re + q ^ 2 := by
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hexp, hone] at hsq
    have hle : ζ.re ≤ 1 := by
      have := Complex.abs_re_le_norm ζ
      rw [hn] at this
      simpa using (abs_le.1 this).2
    nlinarith [hq0]
  have him : ζ.im = 0 := by
    have : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
      rw [← hone]; simp [Complex.normSq_apply]; ring
    rw [hre] at this
    nlinarith [sq_nonneg ζ.im]
  exact Complex.ext hre him


/-- The normalized polynomial, `prod_k (1 - sigma v_k) - (1 + sigma)^r`. -/
noncomputable def ftNormPoly {n : ℕ} (v : Fin n → ℝ) (r : ℕ) : Polynomial ℝ :=
  (∏ k, (1 - Polynomial.C (v k) * Polynomial.X)) - (1 + Polynomial.X) ^ r

/-- `c_0 = 1 - 1 = 0`, with no hypothesis at all. -/
theorem ftNormPoly_coeff_zero {n : ℕ} (v : Fin n → ℝ) (r : ℕ) :
    (ftNormPoly v r).coeff 0 = 0 := by
  rw [ftNormPoly, Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  simp

/-- The first derivative of the product at the origin, over an arbitrary index
set: every factor is `1` at `0`, so only the linear terms survive. -/
theorem eval_zero_derivative_prod {n : ℕ} (v : Fin n → ℝ) :
    (Polynomial.derivative (∏ k, (1 - Polynomial.C (v k) * Polynomial.X))).eval 0
      = -∑ k, v k := by
  classical
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  simp

/-- **`c_1 = 0`, and this IS the constraint.**  The product contributes `-e_1` and
the power contributes `r`, so the linear coefficient is `-e_1 - r`, which vanishes
exactly when `sum_k v_k = -r`.  So `sigma = 0` being a double root is not a fact
to be checked before dividing -- it is the hypothesis, written in coefficients. -/
theorem ftNormPoly_coeff_one {n : ℕ} {v : Fin n → ℝ} {r : ℕ}
    (hsum : ∑ k, v k = -(r : ℝ)) : (ftNormPoly v r).coeff 1 = 0 := by
  have hc : ∀ p : Polynomial ℝ, p.coeff 1 = (Polynomial.derivative p).eval 0 := by
    intro p
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp
  rw [hc, ftNormPoly, Polynomial.derivative_sub, Polynomial.eval_sub,
    eval_zero_derivative_prod, hsum]
  rw [Polynomial.derivative_pow]
  simp

end ForgacsTran


namespace ForgacsTran
open Finset Polynomial

/-- Newton at the second power sum, `e_1^2 = p_2 + 2 e_2`, in the form the
coefficient needs and without naming `e_2`. -/
theorem sum_sum_erase_mul {n : ℕ} (v : Fin n → ℝ) :
    ∑ a, ∑ c ∈ Finset.univ.erase a, v a * v c
      = (∑ k, v k) ^ 2 - ∑ k, (v k) ^ 2 := by
  classical
  have hstep : ∀ a : Fin n, ∑ c ∈ Finset.univ.erase a, v a * v c
      = v a * (∑ k, v k) - (v a) ^ 2 := by
    intro a
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ a)]
    ring
  calc ∑ a, ∑ c ∈ Finset.univ.erase a, v a * v c
      = ∑ a, (v a * (∑ k, v k) - (v a) ^ 2) := Finset.sum_congr rfl fun a _ => hstep a
    _ = (∑ a, v a * (∑ k, v k)) - ∑ a, (v a) ^ 2 := by rw [Finset.sum_sub_distrib]
    _ = (∑ k, v k) ^ 2 - ∑ k, (v k) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- The first derivative of the product at the origin, over an arbitrary index
set: every factor is `1` at `0`, so only the linear terms survive. -/
theorem eval_zero_derivative_prod' {ι : Type*} (s : Finset ι) (v : ι → ℝ) :
    (Polynomial.derivative (∏ k ∈ s, (1 - Polynomial.C (v k) * Polynomial.X))).eval 0
      = -∑ k ∈ s, v k := by
  classical
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  simp

/-- The second derivative of the product at the origin.  Differentiating twice
leaves each ordered pair of distinct indices once, which is `e_1^2 - p_2`. -/
theorem eval_zero_derivative_two_prod {n : ℕ} (v : Fin n → ℝ) :
    (Polynomial.derivative (Polynomial.derivative
        (∏ k, (1 - Polynomial.C (v k) * Polynomial.X)))).eval 0
      = (∑ k, v k) ^ 2 - ∑ k, (v k) ^ 2 := by
  classical
  rw [Polynomial.derivative_prod_finset, map_sum, Polynomial.eval_finsetSum,
    ← sum_sum_erase_mul v]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfa : Polynomial.derivative (1 - Polynomial.C (v a) * Polynomial.X)
      = -Polynomial.C (v a) := by simp
  rw [hfa, Polynomial.derivative_mul, Polynomial.derivative_neg,
    Polynomial.derivative_C, neg_zero, mul_zero, add_zero,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C,
    eval_zero_derivative_prod', ← Finset.mul_sum]
  ring

/-- **`c_2 = (r - p_2)/2`.**  By Newton, `e_2 = (r^2 - p_2)/2` under `e_1 = -r`,
and the power contributes `C(r,2) = r(r-1)/2`; the `r^2` cancels. -/
theorem ftNormPoly_coeff_two {n : ℕ} {v : Fin n → ℝ} {r : ℕ}
    (hsum : ∑ k, v k = -(r : ℝ)) :
    (ftNormPoly v r).coeff 2 = ((r : ℝ) - ∑ k, (v k) ^ 2) / 2 := by
  have hc : ∀ p : Polynomial ℝ,
      p.coeff 2 = (Polynomial.derivative (Polynomial.derivative p)).eval 0 / 2 := by
    intro p
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    push_cast
    ring
  rw [ftNormPoly, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow,
    hc (∏ k, (1 - Polynomial.C (v k) * Polynomial.X)),
    eval_zero_derivative_two_prod, hsum, Nat.cast_choose_two]
  ring

/-- **`c_2 < 0` on the whole admissible class.**  `p_2 > r` from
`lt_sum_sq_of_lt_neg`, and nothing else is needed -- no bound on `n`, no case
analysis, and no appeal to `e_2 < 0`, which is the strictly stronger statement
`p_2 > r^2` and is not what this needs. -/
theorem ftNormPoly_coeff_two_neg {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ j : Fin n}
    (hj : j ≠ i₀) (hjpos : 0 < v j) (hr : 1 ≤ r) (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k)
    (hsum : ∑ k, v k = -(r : ℝ)) : (ftNormPoly v r).coeff 2 < 0 := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hlt : v i₀ < -(r : ℝ) := lt_neg_of_sum_eq_neg_of_nonneg hj hjpos hpos hsum
  have hp2 : (r : ℝ) < ∑ k, (v k) ^ 2 := lt_sum_sq_of_lt_neg hrR hlt
  rw [ftNormPoly_coeff_two hsum]
  linarith

/-! ### The boundary half of the `rho = 1` normalized separation

`prod_k (1 - sigma v_k) = (1+sigma)^r` forces `|1 + sigma| > 1` off
`sigma = 0`, and the boundary half is proved here: on the circle
`|1+sigma| = 1` the two sides cannot agree except at `sigma = 0`.

Together with `ftNormPoly_coeff_two_neg` this says the pencil's zeros on that
circle are exactly `sigma = 0`, with multiplicity two.  **That is what makes an
ordinary circular contour sufficient**, and no indented or otherwise
non-circular contour is needed: a zero of order exactly two, and no other zero
on the circle, is divided out, and the quotient is zero-free there.
`LowerSeparationQuotient` carries the interior count on that basis, over
`Shields.circleIntegral_logDeriv_polynomial` on `C(-1,1)`, and closes the
separation.

Everything below is exact rather than estimated.  On the circle the real part and
the modulus are locked together -- `‖sigma‖^2 = 2 alpha` at `alpha = -Re sigma`,
with `alpha` in `[0,2]` -- which turns each factor's modulus into a closed form:
`1 + 2 w alpha + 2 w^2 alpha` at real `w`.  Positive `w` gives at least `1`;
`w = v_0 = -V` gives exactly `1 + 2 V alpha (V-1)`, above `1` because `V > 1`. -/
/-- On `‖1+σ‖ = 1` the real part and the modulus are locked: `‖σ‖² = 2α` at
`α = -σ.re`, and `α ∈ [0,2]`. -/
theorem normSq_eq_two_mul_of_norm_one {σ : ℂ} (hσ : ‖1 + σ‖ = 1) :
    Complex.normSq σ = 2 * (-σ.re) ∧ 0 ≤ -σ.re ∧ -σ.re ≤ 2 := by
  have h1 : Complex.normSq (1 + σ) = 1 := by
    rw [← Complex.sq_norm, hσ]; norm_num
  have hexp : Complex.normSq (1 + σ) = 1 + 2 * σ.re + Complex.normSq σ := by
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]; ring
  have hkey : Complex.normSq σ = 2 * (-σ.re) := by rw [hexp] at h1; linarith
  -- normSq σ = σ.re² + σ.im², so α² ≤ 2α and both bounds follow at once
  have hre : σ.re ^ 2 + σ.im ^ 2 = 2 * (-σ.re) := by
    rw [← hkey]; simp [Complex.normSq_apply]; ring
  refine ⟨hkey, by nlinarith [sq_nonneg σ.im], by nlinarith [sq_nonneg σ.im]⟩

/-- `‖1 - σw‖² = 1 + 2wα + 2w²α` for real `w`, on the circle. -/
theorem normSq_one_sub_mul_of_norm_one {σ : ℂ} (hσ : ‖1 + σ‖ = 1) (w : ℝ) :
    Complex.normSq (1 - σ * (w : ℂ)) = 1 + 2 * w * (-σ.re) + 2 * w ^ 2 * (-σ.re) := by
  obtain ⟨hns, -, -⟩ := normSq_eq_two_mul_of_norm_one hσ
  have : Complex.normSq (1 - σ * (w : ℂ))
      = 1 - 2 * w * σ.re + w ^ 2 * Complex.normSq σ := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im]
    ring
  rw [this, hns]; ring

/-- **The `k = 0` factor, exactly.**  At `w = -V` the boundary identity reads
`‖1 - σ v₀‖² = 1 + 2Vα(V-1)`, which exceeds `1` for `α > 0` as soon as `V > 1`. -/
theorem normSq_one_sub_mul_neg_of_norm_one {σ : ℂ} (hσ : ‖1 + σ‖ = 1) (V : ℝ) :
    Complex.normSq (1 - σ * ((-V : ℝ) : ℂ))
      = 1 + 2 * V * (-σ.re) * (V - 1) := by
  rw [normSq_one_sub_mul_of_norm_one hσ (-V)]; ring

/-- **Every tail factor has modulus at least one**, from `Re σ ≤ 0` alone; the
sharper `1 + αv` needs `2α ≥ α²`, i.e. `α ≤ 2`, which the circle supplies.

A vanishing `w` is admitted, and the factor is then exactly `1`.  The tail is
allowed to reach zero because the separation's deformation runs to a reference
configuration whose tail is concentrated on a single index. -/
theorem one_le_normSq_one_sub_mul_of_nonneg {σ : ℂ} (hσ : ‖1 + σ‖ = 1) {w : ℝ}
    (hw : 0 ≤ w) : 1 ≤ Complex.normSq (1 - σ * (w : ℂ)) := by
  obtain ⟨-, hα, -⟩ := normSq_eq_two_mul_of_norm_one hσ
  rw [normSq_one_sub_mul_of_norm_one hσ w]
  nlinarith [sq_nonneg w]

/-- **`‖G‖ > 1` on the circle off `σ = 0`.**  The `k = 0` factor is strictly
above `1` and no other factor is below it. -/
theorem one_lt_norm_prod_of_norm_one {n : ℕ} {v : Fin n → ℝ} {r : ℝ} {i₀ j : Fin n}
    (hj : j ≠ i₀) (hjpos : 0 < v j) (hr : 1 ≤ r) (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k)
    (hsum : ∑ k, v k = -r) {σ : ℂ} (hσ : ‖1 + σ‖ = 1) (hσ0 : σ ≠ 0) :
    1 < ‖∏ k, (1 - σ * ((v k : ℝ) : ℂ))‖ := by
  classical
  obtain ⟨hns, hα0, -⟩ := normSq_eq_two_mul_of_norm_one hσ
  have hαpos : 0 < -σ.re := by
    rcases hα0.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.normSq_eq_zero.1 (by rw [hns, ← h]; ring)) hσ0
  have hV : v i₀ < -r := lt_neg_of_sum_eq_neg_of_nonneg hj hjpos hpos hsum
  have hV1 : (1 : ℝ) < -v i₀ := by linarith
  -- the distinguished factor
  have hi₀ : 1 < Complex.normSq (1 - σ * ((v i₀ : ℝ) : ℂ)) := by
    have hrw : ((v i₀ : ℝ) : ℂ) = ((-(-v i₀) : ℝ) : ℂ) := by push_cast; ring
    rw [hrw, normSq_one_sub_mul_neg_of_norm_one hσ]
    have h1 : (0 : ℝ) < 2 * (-v i₀) := by linarith
    have h2 : (0 : ℝ) < 2 * (-v i₀) * (-σ.re) := mul_pos h1 hαpos
    have h3 : (0 : ℝ) < 2 * (-v i₀) * (-σ.re) * ((-v i₀) - 1) :=
      mul_pos h2 (by linarith)
    linarith
  -- the rest
  have hrest : ∀ k ∈ Finset.univ.erase i₀,
      1 ≤ Complex.normSq (1 - σ * ((v k : ℝ) : ℂ)) := fun k hk =>
    one_le_normSq_one_sub_mul_of_nonneg hσ (hpos k (Finset.mem_erase.1 hk).1)
  have hprodSq : 1 < Complex.normSq (∏ k, (1 - σ * ((v k : ℝ) : ℂ))) := by
    rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
    have hone : (1 : ℝ) ≤ ∏ k ∈ Finset.univ.erase i₀,
        Complex.normSq (1 - σ * ((v k : ℝ) : ℂ)) :=
      Finset.one_le_prod hrest
    nlinarith
  have := Complex.sq_norm (∏ k, (1 - σ * ((v k : ℝ) : ℂ)))
  nlinarith [norm_nonneg (∏ k, (1 - σ * ((v k : ℝ) : ℂ)))]

/-- **Step 2′: `G` has no zero on the circle.**  Off `σ = 0` because `‖G‖ > 1`,
and at `σ = 0` because `G(0) = 1`.  Needed for `Δarg G` to be defined at all --
and the one interior zero of `G`, at `1/v₀`, is what refutes the naive Rouché
count, so its being strictly off the circle is a fact to state rather than a
discrepancy to explain. -/
theorem prod_ne_zero_of_norm_one {n : ℕ} {v : Fin n → ℝ} {r : ℝ} {i₀ j : Fin n}
    (hj : j ≠ i₀) (hjpos : 0 < v j) (hr : 1 ≤ r) (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k)
    (hsum : ∑ k, v k = -r) {σ : ℂ} (hσ : ‖1 + σ‖ = 1) :
    (∏ k, (1 - σ * ((v k : ℝ) : ℂ))) ≠ 0 := by
  rcases eq_or_ne σ 0 with rfl | hσ0
  · simp
  · have := one_lt_norm_prod_of_norm_one hj hjpos hr hpos hsum hσ hσ0
    intro hc
    rw [hc] at this
    simp at this
    linarith

/-- **The boundary half of the separation.**  On `‖1+σ‖ = 1` the two sides of the
normalized identity cannot agree off `σ = 0`: the product has modulus above `1`
and `(1+σ)^r` has modulus exactly `1`.

Combined with the double root, this says the roots of `G - H` on the unit circle
are exactly `σ = 0`, with multiplicity two. -/
theorem prod_ne_pow_of_norm_one {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ j : Fin n}
    (hj : j ≠ i₀) (hjpos : 0 < v j) (hr : 1 ≤ r) (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k)
    (hsum : ∑ k, v k = -(r : ℝ)) {σ : ℂ} (hσ : ‖1 + σ‖ = 1) (hσ0 : σ ≠ 0) :
    (∏ k, (1 - σ * ((v k : ℝ) : ℂ))) ≠ (1 + σ) ^ r := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hlt := one_lt_norm_prod_of_norm_one hj hjpos hrR hpos hsum hσ hσ0
  have hpow : ‖(1 + σ) ^ r‖ = 1 := by rw [norm_pow, hσ, one_pow]
  intro hc
  rw [hc, hpow] at hlt
  exact absurd hlt (lt_irrefl 1)

end ForgacsTran
