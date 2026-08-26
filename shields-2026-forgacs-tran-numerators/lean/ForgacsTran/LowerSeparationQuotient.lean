/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Shields.Analysis.Complex.ArgumentPrinciple.Polynomial
import ForgacsTran.EndpointCollision

/-!
# The lower endpoint's separation, by dividing out the double root

`thm:weighted-dominance` carries one named hypothesis, `hsep`, and this is it:
under `sum_k v_k = -r` with the tail nonnegative and `v_{i0} < -r`, the
normalized identity `prod_k (1 - sigma v_k) = (1 + sigma)^r` forces
`|1 + sigma| > 1` at every `sigma` other than the origin.

## Why no indentation is needed

`EndpointCollision` proves the two facts that decide the shape of the argument:
the pencil `F_v = prod_k (1 - sigma v_k) - (1 + sigma)^r` vanishes at the origin
to order **exactly** two (`ftNormPoly_coeff_zero`, `ftNormPoly_coeff_one`,
`ftNormPoly_coeff_two_neg`), and on the circle `|1 + sigma| = 1` it vanishes
**nowhere else** (`prod_ne_pow_of_norm_one`).

The obstruction to a circular argument principle is therefore a single zero
sitting on the contour, and it is removed by dividing it out rather than by
bending the contour around it.  `ftQuotC v r`, the polynomial with
`F_v = X^2 * ftQuotC v r`, is zero-free on the whole circle -- off the origin
because `F_v` is, and at the origin because its value there is `c_2 /= 0`.  So
`Shields.circleIntegral_logDeriv_polynomial` applies with no indentation, no
homotopy of contours, and no non-circular contour.

## How the count is pinned

By deforming the **configuration** rather than the contour.  The admissible set
`{v : tail nonnegative, sum v = -r}` is convex, so `v` travels to a reference
configuration along a segment, and `ftQuotC` stays zero-free on the circle at
every point of it.  A root count in an open disc that never meets the boundary
cannot jump: `card_rootsIn_eq_of_continuous_family` is that statement, proved
from the argument principle exactly as `Shields.card_rootsIn_add_eq` proves
Rouche.

At the reference the whole tail sits on one index, so the product is quadratic
and every coefficient of the quotient above the constant one is a binomial
coefficient of `(1 + X)^r`.  The reference's tail value is chosen larger than
what those can reach on the disc, so the constant term dominates and the count
is zero there -- hence zero at `v`.

This is not Rouche.  A Rouche comparison of `prod_k (1 - sigma v_k)` against
`(1 + sigma)^r` fails at exactly one point, `sigma = 0`, where the two moduli
are equal, and the resulting count is off by one.  That equality is the double
root on the contour, and `X^2` is what removes it.

## The clearance is not uniform, and nothing here claims it is

The margin `|1 + sigma| - 1` has no positive lower bound over the admissible
class: it degenerates as `v_{i0} -> -infinity`, where the roots collapse onto
the origin like `1/v_k`.  Nothing below supplies a constant valid for all `v`.
The count argument is topological -- it needs `ftQuotC` nonzero pointwise at
each configuration and each point of the circle, and no more -- and the one
uniform bound proved here is at the single fixed reference configuration, which
says nothing about a general `v`.
-/

namespace ForgacsTran

open Polynomial

/-! ### Root counts along a continuous family of polynomials -/

/-- **Evaluation is jointly continuous along a family whose coefficients move
continuously.**  A uniform degree bound turns the evaluation into a finite sum
of `coeff i * z^i`, and each summand is continuous in the pair. -/
theorem continuous_eval_of_continuous_coeff {P : ℝ → Polynomial ℂ} {N : ℕ}
    (hdeg : ∀ t, (P t).natDegree < N)
    (hc : ∀ i, Continuous fun t => (P t).coeff i) :
    Continuous fun p : ℝ × ℂ => (P p.1).eval p.2 := by
  have hsum : Continuous fun p : ℝ × ℂ =>
      ∑ i ∈ Finset.range N, (P p.1).coeff i * p.2 ^ i :=
    continuous_finsetSum _ fun i _ =>
      ((hc i).comp continuous_fst).mul (continuous_snd.pow i)
  exact hsum.congr fun p => (Polynomial.eval_eq_sum_range' (hdeg p.1) p.2).symm

/-- Differentiating shifts the coefficients and scales them, so continuity of the
coefficients passes to the derivative. -/
theorem continuous_coeff_derivative {P : ℝ → Polynomial ℂ}
    (hc : ∀ i, Continuous fun t => (P t).coeff i) (i : ℕ) :
    Continuous fun t => (Polynomial.derivative (P t)).coeff i := by
  simp only [Polynomial.coeff_derivative]
  exact (hc (i + 1)).mul continuous_const

/-- **A root count in an open disc cannot jump along a family that never puts a
root on the boundary circle.**  The count is the contour integral of the
logarithmic derivative over `2 pi i`, which moves continuously in the parameter,
and a continuous integer-valued function on `[0,1]` is constant.

This is `Shields.card_rootsIn_add_eq`'s argument with the affine Rouche family
replaced by an arbitrary continuous one; the hypotheses are stated for every
real `t` so that the caller supplies a family already retracted onto `[0,1]`. -/
theorem card_rootsIn_eq_of_continuous_family {c : ℂ} {R : ℝ} (hR : 0 < R)
    {P : ℝ → Polynomial ℂ} {N : ℕ}
    (hdeg : ∀ t, (P t).natDegree < N)
    (hc : ∀ i, Continuous fun t => (P t).coeff i)
    (hne : ∀ t : ℝ, ∀ z ∈ Metric.sphere c R, (P t).eval z ≠ 0) :
    (Shields.rootsIn (P 0) c R).card = (Shields.rootsIn (P 1) c R).card := by
  have habs : |R| = R := abs_of_pos hR
  have hsph : (c + (R : ℂ)) ∈ Metric.sphere c R := by
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, habs]
  have hP0 : ∀ t : ℝ, P t ≠ 0 := by
    intro t h0
    exact hne t _ hsph (by rw [h0]; simp)
  have hns : ∀ t : ℝ, ∀ x ∈ (P t).roots, x ∉ Metric.sphere c R := by
    intro t x hx hmem
    exact hne t x hmem (Polynomial.mem_roots'.mp hx).2
  set Nc : ℝ → ℤ := fun t => ((Shields.rootsIn (P t) c R).card : ℤ) with hNc
  have hcount : ∀ t : ℝ,
      (∮ z in C(c, R), (Polynomial.derivative (P t)).eval z / (P t).eval z)
        = (Nc t : ℂ) * (2 * Real.pi * Complex.I) := by
    intro t
    rw [Shields.circleIntegral_logDeriv_polynomial (hP0 t) hR (hns t), hNc]
    norm_cast
  have hg : Continuous fun p : ℝ × ℝ => ((p.1, circleMap c R p.2) : ℝ × ℂ) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hnum : Continuous fun p : ℝ × ℝ =>
      (Polynomial.derivative (P p.1)).eval (circleMap c R p.2) :=
    (continuous_eval_of_continuous_coeff
      (P := fun t => Polynomial.derivative (P t)) (N := N)
      (fun t => lt_of_le_of_lt
        ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)) (hdeg t))
      (continuous_coeff_derivative hc)).comp hg
  have hden : Continuous fun p : ℝ × ℝ => (P p.1).eval (circleMap c R p.2) :=
    (continuous_eval_of_continuous_coeff hdeg hc).comp hg
  have hjoint : Continuous fun p : ℝ × ℝ =>
      (Polynomial.derivative (P p.1)).eval (circleMap c R p.2)
        / (P p.1).eval (circleMap c R p.2) :=
    hnum.div hden fun p => hne p.1 _ (circleMap_mem_sphere c hR.le p.2)
  have hI : Continuous fun t : ℝ =>
      ∮ z in C(c, R), (Polynomial.derivative (P t)).eval z / (P t).eval z :=
    Shields.continuous_circleIntegral_param _ hjoint
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hstep : Continuous fun t : ℝ => ((Nc t : ℂ) * (2 * Real.pi * Complex.I)) := by
    simpa only [hcount] using hI
  have hcast : Continuous fun t : ℝ => ((Nc t : ℂ)) := by
    simpa [mul_div_assoc, div_self h2pi] using
      hstep.div_const (2 * (Real.pi : ℂ) * Complex.I)
  have hreal : Continuous fun t : ℝ => ((Nc t : ℝ)) := by
    have h := Complex.continuous_re.comp hcast
    refine h.congr fun t => ?_
    simp [Function.comp]
  have hfin := Shields.int_eq_of_continuousOn_Icc Nc
    (Shields.continuous_int_of_continuous_cast hreal).continuousOn
  rw [hNc] at hfin
  simpa using hfin

/-! ### The pencil and its quotient by the double root -/

/-- The normalized pencil over `ℂ`. -/
noncomputable def ftNormPolyC {n : ℕ} (v : Fin n → ℝ) (r : ℕ) : Polynomial ℂ :=
  (ftNormPoly v r).map (algebraMap ℝ ℂ)

theorem ftNormPolyC_coeff {n : ℕ} (v : Fin n → ℝ) (r i : ℕ) :
    (ftNormPolyC v r).coeff i = (((ftNormPoly v r).coeff i : ℝ) : ℂ) := by
  simp [ftNormPolyC]

theorem ftNormPolyC_eq {n : ℕ} (v : Fin n → ℝ) (r : ℕ) :
    ftNormPolyC v r
      = (∏ k, (1 - Polynomial.C ((v k : ℝ) : ℂ) * Polynomial.X))
        - (1 + Polynomial.X) ^ r := by
  rw [ftNormPolyC, ftNormPoly]
  simp [Polynomial.map_prod]

/-- The seam between the polynomial and the bare complex product the boundary
theorems of `EndpointCollision` are stated against. -/
theorem ftNormPolyC_eval {n : ℕ} (v : Fin n → ℝ) (r : ℕ) (z : ℂ) :
    (ftNormPolyC v r).eval z
      = (∏ k, (1 - z * ((v k : ℝ) : ℂ))) - (1 + z) ^ r := by
  rw [ftNormPolyC_eq, Polynomial.eval_sub, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by
    rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, mul_comm]

theorem natDegree_ftNormPolyC_lt {n : ℕ} (v : Fin n → ℝ) (r : ℕ) :
    (ftNormPolyC v r).natDegree < n + r + 1 := by
  have hprod : (∏ k, (1 - Polynomial.C ((v k : ℝ) : ℂ) * Polynomial.X)).natDegree ≤ n := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have : ∀ k : Fin n,
        (1 - Polynomial.C ((v k : ℝ) : ℂ) * Polynomial.X).natDegree ≤ 1 := by
      intro k
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      simpa using Polynomial.natDegree_C_mul_le ((v k : ℝ) : ℂ) Polynomial.X
    have hle : ∑ k : Fin n, (1 - Polynomial.C ((v k : ℝ) : ℂ) * Polynomial.X).natDegree
        ≤ ∑ _k : Fin n, (1 : ℕ) := Finset.sum_le_sum fun k _ => this k
    simpa using hle
  have hpow : (((1 : Polynomial ℂ) + Polynomial.X) ^ r).natDegree ≤ r := by
    refine (Polynomial.natDegree_pow_le).trans ?_
    have : ((1 : Polynomial ℂ) + Polynomial.X).natDegree ≤ 1 := by
      simpa using Polynomial.natDegree_add_le (1 : Polynomial ℂ) Polynomial.X
    calc r * ((1 : Polynomial ℂ) + Polynomial.X).natDegree ≤ r * 1 :=
          Nat.mul_le_mul_left r this
      _ = r := by ring
  rw [ftNormPolyC_eq]
  exact lt_of_le_of_lt ((Polynomial.natDegree_sub_le _ _).trans (max_le_max hprod hpow))
    (by omega)

/-- The pencil with its double root at the origin divided out. -/
noncomputable def ftQuotC {n : ℕ} (v : Fin n → ℝ) (r : ℕ) : Polynomial ℂ :=
  (ftNormPolyC v r).divX.divX

theorem ftQuotC_coeff {n : ℕ} (v : Fin n → ℝ) (r i : ℕ) :
    (ftQuotC v r).coeff i = (ftNormPolyC v r).coeff (i + 2) := by
  rw [ftQuotC, Polynomial.coeff_divX, Polynomial.coeff_divX]

theorem natDegree_ftQuotC_lt {n : ℕ} (v : Fin n → ℝ) (r : ℕ) :
    (ftQuotC v r).natDegree < n + r + 1 :=
  lt_of_le_of_lt
    (Polynomial.natDegree_divX_le.trans Polynomial.natDegree_divX_le)
    (natDegree_ftNormPolyC_lt v r)

/-- **`F = X^2 Q`.**  The double root at the origin, written as a factorization:
the two vanishing coefficients are `ftNormPoly_coeff_zero` and
`ftNormPoly_coeff_one`, and the second of those IS the constraint `sum v = -r`. -/
theorem X_sq_mul_ftQuotC {n : ℕ} {v : Fin n → ℝ} {r : ℕ} (hsum : ∑ k, v k = -(r : ℝ)) :
    Polynomial.X ^ 2 * ftQuotC v r = ftNormPolyC v r := by
  have h0 : (ftNormPolyC v r).coeff 0 = 0 := by
    rw [ftNormPolyC_coeff, ftNormPoly_coeff_zero]; simp
  have h1 : (ftNormPolyC v r).coeff 1 = 0 := by
    rw [ftNormPolyC_coeff, ftNormPoly_coeff_one hsum]; simp
  have e1 : Polynomial.X * (ftNormPolyC v r).divX = ftNormPolyC v r := by
    have h := Polynomial.X_mul_divX_add (ftNormPolyC v r)
    rw [h0] at h; simpa using h
  have h1' : ((ftNormPolyC v r).divX).coeff 0 = 0 := by
    rw [Polynomial.coeff_divX]; simpa using h1
  have e2 : Polynomial.X * ((ftNormPolyC v r).divX).divX = (ftNormPolyC v r).divX := by
    have h := Polynomial.X_mul_divX_add ((ftNormPolyC v r).divX)
    rw [h1'] at h; simpa using h
  calc Polynomial.X ^ 2 * ftQuotC v r
      = Polynomial.X * (Polynomial.X * ((ftNormPolyC v r).divX).divX) := by
        rw [ftQuotC]; ring
    _ = ftNormPolyC v r := by rw [e2, e1]

theorem sq_mul_ftQuotC_eval {n : ℕ} {v : Fin n → ℝ} {r : ℕ}
    (hsum : ∑ k, v k = -(r : ℝ)) (z : ℂ) :
    z ^ 2 * (ftQuotC v r).eval z = (∏ k, (1 - z * ((v k : ℝ) : ℂ))) - (1 + z) ^ r := by
  rw [← ftNormPolyC_eval, ← X_sq_mul_ftQuotC hsum]
  simp

theorem ftQuotC_eval_zero {n : ℕ} (v : Fin n → ℝ) (r : ℕ) :
    (ftQuotC v r).eval 0 = (((ftNormPoly v r).coeff 2 : ℝ) : ℂ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, ftQuotC_coeff, ftNormPolyC_coeff]

/-! ### The quotient is zero-free on the circle -/

theorem mem_sphere_neg_one_iff {z : ℂ} :
    z ∈ Metric.sphere (-1 : ℂ) 1 ↔ ‖1 + z‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_neg_eq_add, add_comm]

/-- **The quotient has no zero on `|1 + sigma| = 1`.**  Off the origin because
the pencil has none there, and AT the origin because the quotient's value there
is `c_2`, which is strictly negative on the whole admissible class.  This is the
single fact that makes a circular contour legal, and it is why no indentation
is needed. -/
theorem ftQuotC_eval_ne_zero_of_norm_one {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ j : Fin n}
    (hj : j ≠ i₀) (hjpos : 0 < v j) (hr : 1 ≤ r) (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k)
    (hsum : ∑ k, v k = -(r : ℝ)) {z : ℂ} (hz : ‖1 + z‖ = 1) :
    (ftQuotC v r).eval z ≠ 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [ftQuotC_eval_zero]
    exact Complex.ofReal_ne_zero.mpr (ftNormPoly_coeff_two_neg hj hjpos hr hpos hsum).ne
  · intro hc
    have h := sq_mul_ftQuotC_eval hsum z
    rw [hc, mul_zero] at h
    exact prod_ne_pow_of_norm_one hj hjpos hr hpos hsum hz hz0 (sub_eq_zero.mp h.symm)


/-! ### Coefficients move continuously with the configuration -/

theorem continuous_coeff_one_sub {g : ℝ → ℝ} (hg : Continuous g) (m : ℕ) :
    Continuous fun t => ((1 : Polynomial ℝ) - Polynomial.C (g t) * Polynomial.X).coeff m := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X]
  exact continuous_const.sub (hg.mul continuous_const)

theorem continuous_coeff_prod_family {ι : Type*} (s : Finset ι) (f : ι → ℝ → Polynomial ℝ)
    (hf : ∀ i m, Continuous fun t => (f i t).coeff m) (m : ℕ) :
    Continuous fun t => (∏ i ∈ s, f i t).coeff m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty => simp only [Finset.prod_empty]; exact continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
    exact continuous_finsetSum _ fun x _ => (hf a x.1).mul (ih x.2)

theorem continuous_coeff_ftNormPoly {n : ℕ} {w : ℝ → Fin n → ℝ}
    (hw : ∀ k, Continuous fun t => w t k) (r m : ℕ) :
    Continuous fun t => (ftNormPoly (w t) r).coeff m := by
  simp only [ftNormPoly, Polynomial.coeff_sub]
  exact (continuous_coeff_prod_family Finset.univ
    (fun k t => 1 - Polynomial.C (w t k) * Polynomial.X)
    (fun k m => continuous_coeff_one_sub (hw k) m) m).sub continuous_const

theorem continuous_coeff_ftQuotC {n : ℕ} {w : ℝ → Fin n → ℝ}
    (hw : ∀ k, Continuous fun t => w t k) (r i : ℕ) :
    Continuous fun t => (ftQuotC (w t) r).coeff i := by
  simp only [ftQuotC_coeff, ftNormPolyC_coeff]
  exact Complex.continuous_ofReal.comp (continuous_coeff_ftNormPoly hw r (i + 2))

/-! ### The reference configuration

The whole tail on a single index.  Its value is chosen to exceed what the
quotient's higher coefficients -- which are binomial coefficients of
`(1 + X)^r`, since the product is quadratic here -- can reach on the disc, so
the quotient's constant term dominates and the count is zero. -/

/-- The reference configuration's tail value: one more than the bound its own
higher coefficients reach at `|sigma| <= 2`, which is the disc's diameter. -/
noncomputable def ftRefTail (n r : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n + r + 1), ((r.choose (i + 3) : ℝ) * 2 ^ (i + 1))

theorem one_le_ftRefTail (n r : ℕ) : 1 ≤ ftRefTail n r := by
  have : (0 : ℝ) ≤ ∑ i ∈ Finset.range (n + r + 1), ((r.choose (i + 3) : ℝ) * 2 ^ (i + 1)) :=
    Finset.sum_nonneg fun i _ => by positivity
  rw [ftRefTail]; linarith

/-- The reference configuration. -/
noncomputable def ftRef {n : ℕ} (r : ℕ) (i₀ j : Fin n) : Fin n → ℝ := fun k =>
  (if k = i₀ then -((r : ℝ) + ftRefTail n r) else 0)
    + (if k = j then ftRefTail n r else 0)

theorem ftRef_i₀ {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) :
    ftRef r i₀ j i₀ = -((r : ℝ) + ftRefTail n r) := by
  simp [ftRef, Ne.symm hj]

theorem ftRef_j {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) :
    ftRef r i₀ j j = ftRefTail n r := by
  simp [ftRef, hj]

theorem ftRef_eq_zero {n : ℕ} {r : ℕ} {i₀ j k : Fin n} (hk₀ : k ≠ i₀) (hkj : k ≠ j) :
    ftRef r i₀ j k = 0 := by
  simp [ftRef, hk₀, hkj]

theorem ftRef_nonneg {n : ℕ} {r : ℕ} {i₀ j k : Fin n} (hk : k ≠ i₀) :
    0 ≤ ftRef r i₀ j k := by
  rcases eq_or_ne k j with rfl | hkj
  · rw [ftRef, if_neg hk, if_pos rfl]
    linarith [one_le_ftRefTail n r]
  · rw [ftRef_eq_zero hk hkj]

/-- A function supported on two indices sums to its two values. -/
theorem sum_eq_of_support_pair {n : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) (f : Fin n → ℝ)
    (hf : ∀ k, k ≠ i₀ → k ≠ j → f k = 0) : ∑ k, f k = f i₀ + f j := by
  classical
  have hsub : ∑ k ∈ ({i₀, j} : Finset (Fin n)), f k = ∑ k, f k := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hf x hx.1 hx.2
  rw [← hsub, Finset.sum_pair (Ne.symm hj)]

theorem sum_ftRef {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) :
    ∑ k, ftRef r i₀ j k = -(r : ℝ) := by
  rw [sum_eq_of_support_pair hj _ fun k h1 h2 => ftRef_eq_zero h1 h2,
    ftRef_i₀ hj, ftRef_j hj]
  ring

theorem sum_sq_ftRef {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) :
    ∑ k, (ftRef r i₀ j k) ^ 2
      = ((r : ℝ) + ftRefTail n r) ^ 2 + (ftRefTail n r) ^ 2 := by
  rw [sum_eq_of_support_pair hj (fun k => (ftRef r i₀ j k) ^ 2)
    (fun k h1 h2 => by rw [ftRef_eq_zero h1 h2]; ring), ftRef_i₀ hj, ftRef_j hj]
  ring

/-! ### The reference count is zero -/

/-- At the reference the product is quadratic: every factor but two is `1`. -/
theorem natDegree_prod_ftRef_le {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) :
    (∏ k, (1 - Polynomial.C (ftRef r i₀ j k) * Polynomial.X)).natDegree ≤ 2 := by
  classical
  have hsub : ∏ k ∈ ({i₀, j} : Finset (Fin n)),
      (1 - Polynomial.C (ftRef r i₀ j k) * Polynomial.X)
      = ∏ k, (1 - Polynomial.C (ftRef r i₀ j k) * Polynomial.X) := by
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [ftRef_eq_zero hx.1 hx.2]
    simp
  have h1 : ∀ a : ℝ, (1 - Polynomial.C a * Polynomial.X).natDegree ≤ 1 := by
    intro a
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    simpa using Polynomial.natDegree_C_mul_le a Polynomial.X
  rw [← hsub, Finset.prod_pair (Ne.symm hj)]
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (h1 _) (h1 _))

/-- Above the quadratic coefficient the product contributes nothing, so the
pencil's coefficient is the binomial one. -/
theorem ftNormPoly_ftRef_coeff_of_lt {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) {m : ℕ}
    (hm : 2 < m) : (ftNormPoly (ftRef r i₀ j) r).coeff m = -(r.choose m : ℝ) := by
  rw [ftNormPoly, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_prod_ftRef_le hj) hm)]
  ring

theorem norm_coeff_ftQuotC_ftRef_succ {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) (i : ℕ) :
    ‖(ftQuotC (ftRef r i₀ j) r).coeff (i + 1)‖ = (r.choose (i + 3) : ℝ) := by
  have hc : (ftQuotC (ftRef r i₀ j) r).coeff (i + 1)
      = ((-(r.choose (i + 3) : ℝ) : ℝ) : ℂ) := by
    rw [ftQuotC_coeff, ftNormPolyC_coeff]
    congr 1
    have h3 : i + 1 + 2 = i + 3 := by ring
    rw [h3]
    exact ftNormPoly_ftRef_coeff_of_lt hj (by omega)
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (r.choose (i + 3) : ℝ))]

theorem sq_ftRefTail_le_norm_coeff_zero {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) :
    (ftRefTail n r) ^ 2 ≤ ‖(ftQuotC (ftRef r i₀ j) r).coeff 0‖ := by
  have hw : 1 ≤ ftRefTail n r := one_le_ftRefTail n r
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hc2 : (ftNormPoly (ftRef r i₀ j) r).coeff 2
      = ((r : ℝ) - (((r : ℝ) + ftRefTail n r) ^ 2 + (ftRefTail n r) ^ 2)) / 2 := by
    rw [ftNormPoly_coeff_two (sum_ftRef hj), sum_sq_ftRef hj]
  have hval : (ftQuotC (ftRef r i₀ j) r).coeff 0
      = (((ftNormPoly (ftRef r i₀ j) r).coeff 2 : ℝ) : ℂ) := by
    rw [ftQuotC_coeff, ftNormPolyC_coeff]
  rw [hval, Complex.norm_real, Real.norm_eq_abs, hc2]
  rw [abs_of_nonpos (by nlinarith)]
  nlinarith

/-- **The reference has no root in the disc.**  The constant coefficient is at
least `w^2` and everything above it sums to at most `w - 1` at `|sigma| <= 2`,
which is the diameter of `|1 + sigma| <= 1`. -/
theorem ftQuotC_ftRef_eval_ne_zero {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀)
    {z : ℂ} (hz : ‖1 + z‖ < 1) : (ftQuotC (ftRef r i₀ j) r).eval z ≠ 0 := by
  set w := ftRefTail n r with hwdef
  have hw : 1 ≤ w := one_le_ftRefTail n r
  -- the disc has diameter two
  have hz2 : ‖z‖ ≤ 2 := by
    have : ‖z‖ ≤ ‖1 + z‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_sub_le (1 + z) (1 : ℂ)
    simp only [norm_one] at this
    linarith
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  -- split the evaluation at its constant term
  have hsplit : (ftQuotC (ftRef r i₀ j) r).eval z
      = (∑ i ∈ Finset.range (n + r), (ftQuotC (ftRef r i₀ j) r).coeff (i + 1) * z ^ (i + 1))
        + (ftQuotC (ftRef r i₀ j) r).coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (natDegree_ftQuotC_lt _ _) z]
    simpa using Finset.sum_range_succ'
      (fun i => (ftQuotC (ftRef r i₀ j) r).coeff i * z ^ i) (n + r)
  -- the tail is smaller than the reference's own tail value
  have htail : ‖∑ i ∈ Finset.range (n + r),
      (ftQuotC (ftRef r i₀ j) r).coeff (i + 1) * z ^ (i + 1)‖ ≤ w - 1 := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range (n + r),
        ‖(ftQuotC (ftRef r i₀ j) r).coeff (i + 1) * z ^ (i + 1)‖
          ≤ (r.choose (i + 3) : ℝ) * 2 ^ (i + 1) := by
      intro i _
      rw [norm_mul, norm_pow, norm_coeff_ftQuotC_ftRef_succ hj]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz2 _) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    have hmono : ∑ i ∈ Finset.range (n + r), ((r.choose (i + 3) : ℝ) * 2 ^ (i + 1))
        ≤ ∑ i ∈ Finset.range (n + r + 1), ((r.choose (i + 3) : ℝ) * 2 ^ (i + 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega) fun i _ _ => by positivity
    rw [hwdef, ftRefTail]
    linarith
  -- and the constant term is at least `w^2`
  have hconst := sq_ftRefTail_le_norm_coeff_zero (r := r) hj
  rw [← hwdef] at hconst
  intro hc
  rw [hc] at hsplit
  have : ‖(ftQuotC (ftRef r i₀ j) r).coeff 0‖
      = ‖∑ i ∈ Finset.range (n + r),
          (ftQuotC (ftRef r i₀ j) r).coeff (i + 1) * z ^ (i + 1)‖ := by
    rw [show (ftQuotC (ftRef r i₀ j) r).coeff 0
        = -(∑ i ∈ Finset.range (n + r),
            (ftQuotC (ftRef r i₀ j) r).coeff (i + 1) * z ^ (i + 1)) by linear_combination -hsplit,
      norm_neg]
  nlinarith

theorem card_rootsIn_ftQuotC_ftRef_eq_zero {n : ℕ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀) :
    (Shields.rootsIn (ftQuotC (ftRef r i₀ j) r) (-1) 1).card = 0 := by
  rw [Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
  intro z hzmem
  rw [Shields.mem_rootsIn] at hzmem
  obtain ⟨hroot, hball⟩ := hzmem
  rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm] at hball
  exact ftQuotC_ftRef_eval_ne_zero hj hball (Polynomial.mem_roots'.mp hroot).2

/-! ### The deformation, and the separation -/

/-- The segment from the given configuration to the reference, retracted onto
`[0,1]` so that the family is defined and admissible at every real parameter. -/
noncomputable def ftPath {n : ℕ} (v : Fin n → ℝ) (r : ℕ) (i₀ j : Fin n) (t : ℝ) :
    Fin n → ℝ := fun k =>
  (1 - Shields.clamp01 t) * v k + Shields.clamp01 t * ftRef r i₀ j k

theorem ftPath_zero {n : ℕ} (v : Fin n → ℝ) (r : ℕ) (i₀ j : Fin n) :
    ftPath v r i₀ j 0 = v := by
  funext k; simp [ftPath]

theorem ftPath_one {n : ℕ} (v : Fin n → ℝ) (r : ℕ) (i₀ j : Fin n) :
    ftPath v r i₀ j 1 = ftRef r i₀ j := by
  funext k; simp [ftPath]

theorem continuous_ftPath {n : ℕ} (v : Fin n → ℝ) (r : ℕ) (i₀ j : Fin n) (k : Fin n) :
    Continuous fun t => ftPath v r i₀ j t k :=
  ((continuous_const.sub Shields.continuous_clamp01).mul continuous_const).add
    (Shields.continuous_clamp01.mul continuous_const)

theorem sum_ftPath {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀)
    (hsum : ∑ k, v k = -(r : ℝ)) (t : ℝ) : ∑ k, ftPath v r i₀ j t k = -(r : ℝ) := by
  simp only [ftPath, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, sum_ftRef hj]
  ring

theorem ftPath_nonneg {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ j : Fin n}
    (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k) (t : ℝ) {k : Fin n} (hk : k ≠ i₀) :
    0 ≤ ftPath v r i₀ j t k := by
  obtain ⟨h0, h1⟩ := Shields.clamp01_mem t
  exact add_nonneg (mul_nonneg (by linarith) (hpos k hk))
    (mul_nonneg h0 (ftRef_nonneg hk))

theorem ftPath_pos {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ j : Fin n} (hj : j ≠ i₀)
    (hjpos : 0 < v j) (t : ℝ) : 0 < ftPath v r i₀ j t j := by
  obtain ⟨h0, h1⟩ := Shields.clamp01_mem t
  have hw : 1 ≤ ftRefTail n r := one_le_ftRefTail n r
  rw [ftPath, ftRef_j hj]
  rcases lt_or_eq_of_le h1 with h | h
  · nlinarith
  · rw [h]; nlinarith

/-- **The root count in the disc is zero at every admissible configuration.**
It cannot move along the segment to the reference, because the quotient never
puts a root on the circle, and it is zero at the reference. -/
theorem card_rootsIn_ftQuotC_eq_zero {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ j : Fin n}
    (hj : j ≠ i₀) (hjpos : 0 < v j) (hr : 1 ≤ r) (hpos : ∀ k, k ≠ i₀ → 0 ≤ v k)
    (hsum : ∑ k, v k = -(r : ℝ)) :
    (Shields.rootsIn (ftQuotC v r) (-1) 1).card = 0 := by
  have hfam := card_rootsIn_eq_of_continuous_family (c := (-1 : ℂ)) (R := (1 : ℝ)) one_pos
    (P := fun t => ftQuotC (ftPath v r i₀ j t) r) (N := n + r + 1)
    (fun t => natDegree_ftQuotC_lt _ _)
    (continuous_coeff_ftQuotC (w := ftPath v r i₀ j) (continuous_ftPath v r i₀ j) r)
    (fun t z hzs => ftQuotC_eval_ne_zero_of_norm_one (i₀ := i₀) (j := j) hj
      (ftPath_pos hj hjpos t) hr (fun k hk => ftPath_nonneg hpos t hk)
      (sum_ftPath hj hsum t) (mem_sphere_neg_one_iff.mp hzs))
  rw [ftPath_zero, ftPath_one] at hfam
  rw [hfam]
  exact card_rootsIn_ftQuotC_ftRef_eq_zero hj

/-- **The lower endpoint's separation** (`thm:weighted-dominance`, the `hsep`
hypothesis).  Under the constraint `sum_k v_k = -r` with a strictly positive
tail, the normalized identity forces `|1 + sigma| > 1` off the origin.

No uniform clearance is asserted, and none is available: the margin degenerates
as `v_{i0} -> -infinity`. -/
theorem one_lt_norm_one_add_of_prod_eq_pow {n : ℕ} {v : Fin n → ℝ} {r : ℕ} {i₀ : Fin n}
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hpos : ∀ k, k ≠ i₀ → 0 < v k)
    (hsum : ∑ k, v k = -(r : ℝ)) {σ : ℂ} (hσ0 : σ ≠ 0)
    (heq : (∏ k, (1 - σ * ((v k : ℝ) : ℂ))) = (1 + σ) ^ r) :
    1 < ‖1 + σ‖ := by
  classical
  obtain ⟨j, hjmem⟩ : (Finset.univ.erase i₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hj : j ≠ i₀ := (Finset.mem_erase.1 hjmem).1
  have hjpos : 0 < v j := hpos j hj
  have hpos' : ∀ k, k ≠ i₀ → 0 ≤ v k := fun k hk => (hpos k hk).le
  by_contra hcon
  rcases eq_or_lt_of_le (not_lt.mp hcon) with heq1 | hlt
  · exact prod_ne_pow_of_norm_one hj hjpos hr hpos' hsum heq1 hσ0 heq
  · have hval : (ftQuotC v r).eval σ = 0 := by
      have h := sq_mul_ftQuotC_eval hsum σ
      rw [heq, sub_self] at h
      rcases mul_eq_zero.mp h with h2 | h2
      · exact absurd (by simpa using h2 : σ = 0) hσ0
      · exact h2
    have hQne : ftQuotC v r ≠ 0 := fun h0 =>
      ftQuotC_eval_ne_zero_of_norm_one hj hjpos hr hpos' hsum (z := 0) (by simp)
        (by rw [h0]; simp)
    have hmem : σ ∈ Shields.rootsIn (ftQuotC v r) (-1) 1 := by
      rw [Shields.mem_rootsIn]
      refine ⟨Polynomial.mem_roots'.mpr ⟨hQne, hval⟩, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm]
      exact hlt
    have hzero := card_rootsIn_ftQuotC_eq_zero hj hjpos hr hpos' hsum
    rw [Multiset.card_eq_zero] at hzero
    rw [hzero] at hmem
    exact absurd hmem (Multiset.notMem_zero σ)


/-! ### Non-vacuity

Every hypothesis is satisfiable at once, at a NONZERO `sigma`, so the statement
is not vacuous on the side that matters.  The configuration is `n = 3`, `r = 1`,
`v = (-2, 1/2, 1/2)`, where the pencil is `sigma^2 (sigma/2 - 7/4)` and the one
root off the origin is `7/2`.  That is the configuration at which a naive
Rouche count comes out one too large, so it is the one worth pinning. -/
theorem one_lt_norm_one_add_witness : (1 : ℝ) < ‖1 + (7 / 2 : ℂ)‖ :=
  one_lt_norm_one_add_of_prod_eq_pow (n := 3) (v := ![(-2 : ℝ), 1 / 2, 1 / 2])
    (r := 1) (i₀ := 0) (σ := 7 / 2)
    (hn := by norm_num) (hr := by norm_num)
    (hpos := by
      intro k hk
      fin_cases k
      · exact absurd rfl hk
      · norm_num
      · norm_num)
    (hsum := by simp [Fin.sum_univ_three]; norm_num)
    (hσ0 := by norm_num)
    (heq := by simp [Fin.prod_univ_three]; norm_num)

end ForgacsTran
