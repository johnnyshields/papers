/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Rigidity of a meromorphic symbol with positive zeros and negative poles

Fix `γ ≥ 0` and two finite families of positive reals `α : Fin a → ℝ`, `β : Fin b → ℝ`, and put

  `A(z) = e^{-γz} ∏_i (1 - α_i z)`,  `C(z) = ∏_j (1 + β_j z)`,  `f = A / C`.

So `f` is meromorphic on `ℂ` with zeros at the positive points `α_i^{-1}` and poles at the
negative points `-β_j^{-1}`, and `f(0) = 1`.  This is the generating function of a finite
Pólya frequency sequence, and the two rigidity statements proved here are what pin down its
critical points and its level sets.

The whole file runs off one identity, `Shields.im_pickR`: writing `R(z) = -z f'(z)/f(z)`,

  `Im R(z) = Im z · (γ + ∑_i α_i/|1 - α_i z|² + ∑_j β_j/|1 + β_j z|²)`,

with the bracket strictly positive wherever `f` is finite and nonzero.  So `R` is a Pick
function, `R` restricted to the real axis is strictly increasing, and neither fact needs a
Herglotz representation.

## Main results

* `Shields.im_pickR` -- the identity above, carrying both the Pick property off the real axis
  and the positivity of `R'` on it.
* `Shields.pick_rigidity` -- **every nonzero critical point of `f` is real**, stated in the
  Wronskian form `A'C - AC' = 0`.  A nonreal critical point would make `R` vanish off the real
  axis, where `Im R ≠ 0`.
* `Shields.iteratedDeriv_two_symbolF`, `Shields.iteratedDeriv_two_symbolF_ne_zero` -- at a
  critical point `f''(τ) = -f(τ) R'(τ)/τ`, nonzero when `τ` is real and nonzero, so every
  critical point is nondegenerate.
* `Shields.circular_rigidity` -- **two points of one circle at which `|f|` agrees, with `f`
  finite and nonzero at one of them, are equal or complex conjugate.**  Along a fixed circle
  `‖z‖ = r` the squared modulus of each factor depends on `z` only through `Re z`, strictly
  decreasing for a zero factor and strictly increasing for a pole factor, so `|f|` is strictly
  decreasing in `Re z`; equal moduli therefore force equal real parts.
* `Shields.levelFn_order_two`, `Shields.eq_of_levelFn_eq_zero_of_norm_eq` -- the two
  consequences for a level set.  At a nonzero real critical point `τ` the level function
  `g_c = A - cC` at `c = f(τ)` has a zero of multiplicity exactly two, and `τ` is the only
  point of the circle `‖z‖ = ‖τ‖` at that level.

## Implementation notes

`pick_rigidity` asks less than the classical statement, which restricts to critical points with
`0 < |f(τ)| < ∞`: no `A(τ) ≠ 0` appears.  Nothing is lost, because the roots of `A` are the real
points `α_i^{-1}`, so a nonreal point is never one.  **The restriction cannot be dropped for a
general numerator with real Taylor coefficients**: `A = (z² + 1)²` has a double zero at `i`, so
`A'C - AC'` vanishes there with `C = 1`, and the point is not real.

`circular_rigidity` takes the *modulus* hypothesis `‖A(w)C(t)‖ = ‖A(t)C(w)‖`, cross-multiplied
so that no quotient appears; equality of the two `f`-values gives it at once, so this is the
weaker hypothesis and the stronger statement.

The comparison is algebraic throughout: `sq_norm_numerA` and `sq_norm_denomC` present each
squared modulus as a function of `‖z‖` and `Re z`, so neither the derivative of `arg` nor any
trigonometry enters.

## References

The Pick, Herglotz or Nevanlinna class and its rigidity are classical; see Donoghue, *Monotone
Matrix Functions and Analytic Continuation*, Ch. II.  Mathlib carries no Pick class -- its
`Nevanlinna` files are value-distribution theory, a different subject.

## Tags

Pick function, Herglotz, Nevanlinna, critical point, rigidity, Pólya frequency, level set
-/

open Set Filter Topology

namespace Shields

variable {a b : ℕ} {γ : ℝ} {α : Fin a → ℝ} {β : Fin b → ℝ} {c z τ : ℂ}

/-! ## The symbol, its numerator and its denominator -/

/-- The numerator `A(z) = e^{-γz} ∏_i (1 - α_i z)`, whose zeros are the `α_i^{-1}`. -/
noncomputable def numerA (γ : ℝ) (α : Fin a → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(γ : ℂ) * z) * ∏ i, (1 - (α i : ℂ) * z)

/-- The denominator `C(z) = ∏_j (1 + β_j z)`, whose zeros are the `-β_j^{-1}`. -/
noncomputable def denomC (β : Fin b → ℝ) (z : ℂ) : ℂ := ∏ j, (1 + (β j : ℂ) * z)

/-- The symbol `f = A/C`. -/
noncomputable def symbolF (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (z : ℂ) : ℂ :=
  numerA γ α z / denomC β z

theorem differentiable_numerA : Differentiable ℂ (numerA γ α) :=
  ((differentiable_id.const_mul _).cexp).mul
    (Differentiable.fun_finsetProd fun _ _ =>
      (differentiable_const (1 : ℂ)).sub (differentiable_id.const_mul _))

theorem differentiable_denomC : Differentiable ℂ (denomC β) :=
  Differentiable.fun_finsetProd fun _ _ =>
    (differentiable_const (1 : ℂ)).add (differentiable_id.const_mul _)

theorem differentiableAt_symbolF (hC : denomC β z ≠ 0) :
    DifferentiableAt ℂ (symbolF γ α β) z :=
  (differentiable_numerA z).div (differentiable_denomC z) hC

/-- A zero of a numerator factor is a zero of `A`. -/
theorem numerA_eq_zero_of_factor {i : Fin a} (h : (1 : ℂ) - (α i : ℂ) * z = 0) :
    numerA γ α z = 0 := by
  rw [numerA, Finset.prod_eq_zero (Finset.mem_univ i) h, mul_zero]

/-- A zero of a denominator factor is a zero of `C`. -/
theorem denomC_eq_zero_of_factor {j : Fin b} (h : (1 : ℂ) + (β j : ℂ) * z = 0) :
    denomC β z = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j) h

theorem one_sub_ne_zero_of_numerA (hA : numerA γ α z ≠ 0) (i : Fin a) :
    (1 : ℂ) - (α i : ℂ) * z ≠ 0 := fun h => hA (numerA_eq_zero_of_factor h)

theorem one_add_ne_zero_of_denomC (hC : denomC β z ≠ 0) (j : Fin b) :
    (1 : ℂ) + (β j : ℂ) * z ≠ 0 := fun h => hC (denomC_eq_zero_of_factor h)

theorem symbolF_ne_zero (hA : numerA γ α z ≠ 0) (hC : denomC β z ≠ 0) :
    symbolF γ α β z ≠ 0 := div_ne_zero hA hC

/-! ## The Pick function `R = -z f'/f` -/

/-- The logarithmic derivative `f'/f = -γ - ∑_i α_i/(1-α_i z) - ∑_j β_j/(1+β_j z)`. -/
noncomputable def logDerivF (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (z : ℂ) : ℂ :=
  -(γ : ℂ) - (∑ i, (α i : ℂ) / (1 - (α i : ℂ) * z))
    - ∑ j, (β j : ℂ) / (1 + (β j : ℂ) * z)

/-- `R(z) = -z f'(z)/f(z)`, written out as
`γz + ∑_i α_i z/(1-α_i z) + ∑_j β_j z/(1+β_j z)`.  In the zero and pole coordinates
`x_i = α_i^{-1}`, `y_j = β_j^{-1}` this is `γz - ∑ z/(z-x_i) + ∑ z/(z+y_j)`. -/
noncomputable def pickR (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (z : ℂ) : ℂ :=
  (γ : ℂ) * z + (∑ i, (α i : ℂ) * z / (1 - (α i : ℂ) * z))
    + ∑ j, (β j : ℂ) * z / (1 + (β j : ℂ) * z)

/-- The derivative of `R`. -/
noncomputable def pickDeriv (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (z : ℂ) : ℂ :=
  (γ : ℂ) + (∑ i, (α i : ℂ) / (1 - (α i : ℂ) * z) ^ 2)
    + ∑ j, (β j : ℂ) / (1 + (β j : ℂ) * z) ^ 2

/-- The weight `γ + ∑_i α_i/|1-α_i z|² + ∑_j β_j/|1+β_j z|²`.  On the real axis it is `R'`,
and off it `Im R = (Im z) ·` this. -/
noncomputable def pickWeight (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (z : ℂ) : ℝ :=
  γ + (∑ i, α i / Complex.normSq (1 - (α i : ℂ) * z))
    + ∑ j, β j / Complex.normSq (1 + (β j : ℂ) * z)

theorem pickR_eq_neg_mul_logDerivF (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (z : ℂ) :
    pickR γ α β z = -z * logDerivF γ α β z := by
  have h1 : ∀ i : Fin a, (α i : ℂ) * z / (1 - (α i : ℂ) * z)
      = z * ((α i : ℂ) / (1 - (α i : ℂ) * z)) := fun i => by ring
  have h2 : ∀ j : Fin b, (β j : ℂ) * z / (1 + (β j : ℂ) * z)
      = z * ((β j : ℂ) / (1 + (β j : ℂ) * z)) := fun j => by ring
  simp only [pickR, logDerivF, h1, h2, ← Finset.mul_sum]
  ring

/-! ### The imaginary part of `R` -/

theorem im_mul_div_one_sub (c : ℝ) (z : ℂ) :
    ((c : ℂ) * z / (1 - (c : ℂ) * z)).im = c * z.im / Complex.normSq (1 - (c : ℂ) * z) := by
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_mul,
    add_zero, sub_zero, zero_sub]
  ring

theorem im_mul_div_one_add (c : ℝ) (z : ℂ) :
    ((c : ℂ) * z / (1 + (c : ℂ) * z)).im = c * z.im / Complex.normSq (1 + (c : ℂ) * z) := by
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_mul,
    add_zero, sub_zero, zero_add]
  ring

/-- **The imaginary part of `R`.**  It factors as `Im R(z) = (Im z) · W(z)` with `W` the
weight `pickWeight`.  The Pick property off the real axis and the positivity of `R'` on it are
both readings of this one identity. -/
theorem im_pickR (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (z : ℂ) :
    (pickR γ α β z).im = z.im * pickWeight γ α β z := by
  rw [pickR, pickWeight, Complex.add_im, Complex.add_im, Complex.im_sum, Complex.im_sum]
  simp only [im_mul_div_one_sub, im_mul_div_one_add, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun j _ => by ring

/-! ### Positivity of the weight -/

theorem pickWeight_nonneg_terms (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (z : ℂ) :
    (0 ≤ ∑ i, α i / Complex.normSq (1 - (α i : ℂ) * z)) ∧
      0 ≤ ∑ j, β j / Complex.normSq (1 + (β j : ℂ) * z) :=
  ⟨Finset.sum_nonneg fun i _ =>
      div_nonneg (hα i).le (Complex.normSq_nonneg _),
    Finset.sum_nonneg fun j _ =>
      div_nonneg (hβ j).le (Complex.normSq_nonneg _)⟩

/-- The weight is strictly positive wherever the symbol is nonconstant and `z` is neither a
zero nor a pole. -/
theorem pickWeight_pos (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) {z : ℂ}
    (hzα : ∀ i, (1 : ℂ) - (α i : ℂ) * z ≠ 0)
    (hzβ : ∀ j, (1 : ℂ) + (β j : ℂ) * z ≠ 0) :
    0 < pickWeight γ α β z := by
  obtain ⟨h1, h2⟩ := pickWeight_nonneg_terms hα hβ z
  rw [pickWeight]
  rcases hnd with hg | ha | hb
  · linarith
  · have : Nonempty (Fin a) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero ha)
    have hpos : 0 < ∑ i, α i / Complex.normSq (1 - (α i : ℂ) * z) :=
      Finset.sum_pos (fun i _ =>
        div_pos (hα i) (Complex.normSq_pos.mpr (hzα i))) Finset.univ_nonempty
    linarith
  · have : Nonempty (Fin b) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hb)
    have hpos : 0 < ∑ j, β j / Complex.normSq (1 + (β j : ℂ) * z) :=
      Finset.sum_pos (fun j _ =>
        div_pos (hβ j) (Complex.normSq_pos.mpr (hzβ j))) Finset.univ_nonempty
    linarith

theorem one_sub_ne_zero_of_im_ne_zero {c : ℝ} (hc : c ≠ 0) (hz : z.im ≠ 0) :
    (1 : ℂ) - (c : ℂ) * z ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_sub, Complex.zero_im, neg_eq_zero] at this
  exact (mul_eq_zero.mp this).resolve_left hc

theorem one_add_ne_zero_of_im_ne_zero {c : ℝ} (hc : c ≠ 0) (hz : z.im ≠ 0) :
    (1 : ℂ) + (c : ℂ) * z ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at this
  exact (mul_eq_zero.mp this).resolve_left hc

/-- **The Pick property.**  `R` maps the upper half-plane into itself. -/
theorem im_pickR_pos (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    0 < (pickR γ α β z).im := by
  rw [im_pickR]
  exact mul_pos hz (pickWeight_pos hγ hα hβ hnd
    (fun i => one_sub_ne_zero_of_im_ne_zero (hα i).ne' hz.ne')
    (fun j => one_add_ne_zero_of_im_ne_zero (hβ j).ne' hz.ne'))

/-- The Pick property in the lower half-plane, by reflection. -/
theorem im_pickR_neg (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) {z : ℂ} (hz : z.im < 0) :
    (pickR γ α β z).im < 0 := by
  rw [im_pickR]
  exact mul_neg_of_neg_of_pos hz (pickWeight_pos hγ hα hβ hnd
    (fun i => one_sub_ne_zero_of_im_ne_zero (hα i).ne' hz.ne)
    (fun j => one_add_ne_zero_of_im_ne_zero (hβ j).ne' hz.ne))

/-- On the real axis `R'` is the weight, hence real and — under the hypotheses of
`pickWeight_pos` — strictly positive. -/
theorem pickDeriv_ofReal (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (t : ℝ) :
    pickDeriv γ α β (t : ℂ) = ((pickWeight γ α β (t : ℂ) : ℝ) : ℂ) := by
  have key : ∀ (c : ℝ) (s : ℝ), (0 : ℂ) = 0 →
      (c : ℂ) / ((s : ℝ) : ℂ) ^ 2 = ((c / Complex.normSq ((s : ℝ) : ℂ) : ℝ) : ℂ) := by
    intro c s _
    rw [Complex.normSq_ofReal, Complex.ofReal_div, ← Complex.ofReal_pow]
    congr 2
    ring
  rw [pickDeriv, pickWeight]
  push_cast
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hr : (1 : ℂ) - (α i : ℂ) * (t : ℂ) = ((1 - α i * t : ℝ) : ℂ) := by norm_cast
    rw [hr, key (α i) (1 - α i * t) rfl]
    push_cast
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hr : (1 : ℂ) + (β j : ℂ) * (t : ℂ) = ((1 + β j * t : ℝ) : ℂ) := by norm_cast
    rw [hr, key (β j) (1 + β j * t) rfl]
    push_cast
    ring

/-! ## `R` as the logarithmic derivative of `f` -/

theorem hasDerivAt_pickR {z : ℂ} (hzα : ∀ i, (1 : ℂ) - (α i : ℂ) * z ≠ 0)
    (hzβ : ∀ j, (1 : ℂ) + (β j : ℂ) * z ≠ 0) :
    HasDerivAt (pickR γ α β) (pickDeriv γ α β z) z := by
  have h0 : HasDerivAt (fun w : ℂ => (γ : ℂ) * w) (γ : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (γ : ℂ)
  have h1 : ∀ i : Fin a, HasDerivAt (fun w : ℂ => (α i : ℂ) * w / (1 - (α i : ℂ) * w))
      ((α i : ℂ) / (1 - (α i : ℂ) * z) ^ 2) z := by
    intro i
    have hn : HasDerivAt (fun w : ℂ => (α i : ℂ) * w) (α i : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul ((α i : ℂ))
    have hd : HasDerivAt (fun w : ℂ => 1 - (α i : ℂ) * w) (-(α i : ℂ)) z := hn.const_sub 1
    refine (hn.div hd (hzα i)).congr_deriv ?_
    field
  have h2 : ∀ j : Fin b, HasDerivAt (fun w : ℂ => (β j : ℂ) * w / (1 + (β j : ℂ) * w))
      ((β j : ℂ) / (1 + (β j : ℂ) * z) ^ 2) z := by
    intro j
    have hn : HasDerivAt (fun w : ℂ => (β j : ℂ) * w) (β j : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul ((β j : ℂ))
    have hd : HasDerivAt (fun w : ℂ => 1 + (β j : ℂ) * w) ((β j : ℂ)) z := hn.const_add 1
    refine (hn.div hd (hzβ j)).congr_deriv ?_
    field
  exact (h0.add (HasDerivAt.fun_sum fun i _ => h1 i)).add (HasDerivAt.fun_sum fun j _ => h2 j)

theorem differentiableAt_logDerivF {z : ℂ} (hzα : ∀ i, (1 : ℂ) - (α i : ℂ) * z ≠ 0)
    (hzβ : ∀ j, (1 : ℂ) + (β j : ℂ) * z ≠ 0) :
    DifferentiableAt ℂ (logDerivF γ α β) z := by
  refine ((differentiableAt_const _).sub (DifferentiableAt.fun_sum fun i _ => ?_)).sub
    (DifferentiableAt.fun_sum fun j _ => ?_)
  · exact (differentiableAt_const _).div
      ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)) (hzα i)
  · exact (differentiableAt_const _).div
      ((differentiableAt_const _).add (differentiableAt_id.const_mul _)) (hzβ j)

theorem logDeriv_exp_linear (c z : ℂ) :
    logDeriv (fun w : ℂ => Complex.exp (c * w)) z = c := by
  have h : HasDerivAt (fun w : ℂ => Complex.exp (c * w)) (Complex.exp (c * z) * c) z := by
    simpa using ((hasDerivAt_id z).const_mul c).cexp
  rw [logDeriv_apply, h.deriv, mul_comm, mul_div_assoc,
    div_self (Complex.exp_ne_zero _), mul_one]

theorem logDeriv_one_sub (c : ℝ) {z : ℂ} :
    logDeriv (fun w : ℂ => 1 - (c : ℂ) * w) z = -(c : ℂ) / (1 - (c : ℂ) * z) := by
  have hn : HasDerivAt (fun w : ℂ => (c : ℂ) * w) (c : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul ((c : ℂ))
  have hd : HasDerivAt (fun w : ℂ => 1 - (c : ℂ) * w) (-(c : ℂ)) z := hn.const_sub 1
  rw [logDeriv_apply, hd.deriv]

theorem logDeriv_one_add (c : ℝ) {z : ℂ} :
    logDeriv (fun w : ℂ => 1 + (c : ℂ) * w) z = (c : ℂ) / (1 + (c : ℂ) * z) := by
  have hn : HasDerivAt (fun w : ℂ => (c : ℂ) * w) (c : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul ((c : ℂ))
  have hd : HasDerivAt (fun w : ℂ => 1 + (c : ℂ) * w) ((c : ℂ)) z := hn.const_add 1
  rw [logDeriv_apply, hd.deriv]

theorem logDeriv_numerA {z : ℂ} (hA : numerA γ α z ≠ 0) :
    logDeriv (numerA γ α) z = -(γ : ℂ) - ∑ i, (α i : ℂ) / (1 - (α i : ℂ) * z) := by
  have hzα := one_sub_ne_zero_of_numerA hA
  have hprod : (∏ i, (1 - (α i : ℂ) * z)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hzα i
  have hmul : logDeriv (numerA γ α) z
      = logDeriv (fun w : ℂ => Complex.exp (-(γ : ℂ) * w)) z
        + logDeriv (fun w : ℂ => ∏ i, (1 - (α i : ℂ) * w)) z :=
    logDeriv_mul z (Complex.exp_ne_zero _) hprod
      ((differentiable_id.const_mul _).cexp z)
      (DifferentiableAt.fun_finsetProd fun i _ =>
        (differentiableAt_const _).sub (differentiableAt_id.const_mul _))
  have hsum : ∑ i, logDeriv (fun w : ℂ => 1 - (α i : ℂ) * w) z
      = -∑ i, (α i : ℂ) / (1 - (α i : ℂ) * z) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [logDeriv_one_sub]; ring
  rw [hmul, logDeriv_exp_linear,
    logDeriv_prod (fun i _ => hzα i)
      (fun i _ => (differentiableAt_const _).sub (differentiableAt_id.const_mul _)), hsum]
  ring

theorem logDeriv_denomC {z : ℂ} (hC : denomC β z ≠ 0) :
    logDeriv (denomC β) z = ∑ j, (β j : ℂ) / (1 + (β j : ℂ) * z) := by
  have hzβ := one_add_ne_zero_of_denomC hC
  rw [show (denomC β) = (fun w : ℂ => ∏ j, (1 + (β j : ℂ) * w)) from rfl,
    logDeriv_prod (fun j _ => hzβ j)
      (fun j _ => (differentiableAt_const _).add (differentiableAt_id.const_mul _))]
  exact Finset.sum_congr rfl fun j _ => logDeriv_one_add (β j)

/-- The logarithmic derivative of the symbol is
`f'/f = -γ - ∑ α_i/(1-α_i z) - ∑ β_j/(1+β_j z)`, so `R = -z f'/f` is `pickR`. -/
theorem logDeriv_symbolF {z : ℂ} (hA : numerA γ α z ≠ 0) (hC : denomC β z ≠ 0) :
    logDeriv (symbolF γ α β) z = logDerivF γ α β z := by
  rw [show (symbolF γ α β) = (fun w : ℂ => numerA γ α w / denomC β w) from rfl,
    logDeriv_div z hA hC (differentiable_numerA z) (differentiable_denomC z),
    logDeriv_numerA hA, logDeriv_denomC hC, logDerivF]

/-- `f' = f · (f'/f)` in the form used to differentiate a second time. -/
theorem deriv_symbolF {z : ℂ} (hA : numerA γ α z ≠ 0) (hC : denomC β z ≠ 0) :
    deriv (symbolF γ α β) z = symbolF γ α β z * logDerivF γ α β z := by
  have h := logDeriv_symbolF hA hC
  rw [logDeriv_apply, div_eq_iff (symbolF_ne_zero hA hC)] at h
  rw [h, mul_comm]

/-- At a critical point the logarithmic derivative — hence `R` — vanishes. -/
theorem logDerivF_eq_zero_of_deriv_eq_zero {z : ℂ} (hA : numerA γ α z ≠ 0)
    (hC : denomC β z ≠ 0) (hcrit : deriv (symbolF γ α β) z = 0) :
    logDerivF γ α β z = 0 := by
  have h := deriv_symbolF hA hC
  rw [hcrit] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (symbolF_ne_zero hA hC)

/-! ## Reality of the critical points -/

/-- Off the real axis the numerator cannot vanish: its roots `1/α_i` are real. -/
theorem numerA_ne_zero_of_im_ne_zero (hα : ∀ i, 0 < α i) {z : ℂ} (hz : z.im ≠ 0) :
    numerA γ α z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _)
    (Finset.prod_ne_zero_iff.mpr fun i _ => one_sub_ne_zero_of_im_ne_zero (hα i).ne' hz)

/-- Off the real axis the denominator cannot vanish: its roots `-1/β_j` are real. -/
theorem denomC_ne_zero_of_im_ne_zero (hβ : ∀ j, 0 < β j) {z : ℂ} (hz : z.im ≠ 0) :
    denomC β z ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => one_add_ne_zero_of_im_ne_zero (hβ j).ne' hz

/-- **Every critical point of `f` is real.**  A nonreal one would make `R` vanish off the
real axis, where `Im R ≠ 0`. -/
theorem im_eq_zero_of_deriv_eq_zero (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) {z : ℂ}
    (hcrit : deriv (symbolF γ α β) z = 0) :
    z.im = 0 := by
  by_contra him
  have hA := numerA_ne_zero_of_im_ne_zero (γ := γ) hα him
  have hC := denomC_ne_zero_of_im_ne_zero hβ him
  have hL := logDerivF_eq_zero_of_deriv_eq_zero hA hC hcrit
  have hR : pickR γ α β z = 0 := by rw [pickR_eq_neg_mul_logDerivF, hL, mul_zero]
  have hw : 0 < pickWeight γ α β z :=
    pickWeight_pos hγ hα hβ hnd
      (fun i => one_sub_ne_zero_of_im_ne_zero (hα i).ne' him)
      (fun j => one_add_ne_zero_of_im_ne_zero (hβ j).ne' him)
  have := im_pickR γ α β z
  rw [hR, Complex.zero_im] at this
  exact him ((mul_eq_zero.mp this.symm).resolve_right hw.ne')

/-- The quotient rule for `f = A/C`, in Wronskian form. -/
theorem deriv_symbolF_eq_wronskian {z : ℂ} (hC : denomC β z ≠ 0) :
    deriv (symbolF γ α β) z
      = (deriv (numerA γ α) z * denomC β z - numerA γ α z * deriv (denomC β) z)
        / denomC β z ^ 2 :=
  (((differentiable_numerA (γ := γ) (α := α)) z).hasDerivAt.div
    (((differentiable_denomC (β := β)) z).hasDerivAt) hC).deriv

/-- **Critical rigidity, in Wronskian form**: a nonzero point at which `A'C - AC'` vanishes
is real.

This asks less than the classical statement, which restricts to critical points with
`0 < |f(τ)| < ∞`: no `numerA γ α t ≠ 0` appears.  Nothing is lost, because off the real axis
`numerA` cannot vanish at all — its roots `1/αᵢ` are real — and the proof is by contradiction
on `t.im ≠ 0`.  The restriction is not removable for a general numerator with real Taylor
coefficients: `A = (z² + 1)²` has a double zero at `i`. -/
theorem pick_rigidity (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) :
    ∀ t : ℂ, t ≠ 0 → denomC β t ≠ 0 →
      deriv (numerA γ α) t * denomC β t - numerA γ α t * deriv (denomC β) t = 0 →
      t.im = 0 := by
  intro t _ hC hw
  refine im_eq_zero_of_deriv_eq_zero hγ hα hβ hnd ?_
  rw [deriv_symbolF_eq_wronskian hC, hw, zero_div]

/-- **Nondegeneracy, the exact value.**  At a nonzero critical point,
`f''(τ) = -f(τ) R'(τ)/τ`. -/
theorem iteratedDeriv_two_symbolF {z : ℂ} (hz : z ≠ 0) (hA : numerA γ α z ≠ 0)
    (hC : denomC β z ≠ 0) (hcrit : deriv (symbolF γ α β) z = 0) :
    iteratedDeriv 2 (symbolF γ α β) z
      = -(symbolF γ α β z * pickDeriv γ α β z) / z := by
  have hzα := one_sub_ne_zero_of_numerA hA
  have hzβ := one_add_ne_zero_of_denomC hC
  have hLdiff : DifferentiableAt ℂ (logDerivF γ α β) z := differentiableAt_logDerivF hzα hzβ
  have hL0 := logDerivF_eq_zero_of_deriv_eq_zero hA hC hcrit
  -- the identity `f' = f L` holds on a neighborhood
  have hAev : ∀ᶠ w in 𝓝 z, numerA γ α w ≠ 0 :=
    (differentiable_numerA (γ := γ) (α := α)).continuous.continuousAt.eventually_ne hA
  have hCev : ∀ᶠ w in 𝓝 z, denomC β w ≠ 0 :=
    (differentiable_denomC (β := β)).continuous.continuousAt.eventually_ne hC
  have heq : deriv (symbolF γ α β) =ᶠ[𝓝 z] fun w => symbolF γ α β w * logDerivF γ α β w := by
    filter_upwards [hAev, hCev] with w hw1 hw2 using deriv_symbolF hw1 hw2
  -- the derivative of `L` at `z` is `-R'(z)/z`
  have hR1 : HasDerivAt (pickR γ α β) (pickDeriv γ α β z) z := hasDerivAt_pickR hzα hzβ
  have hR2 : HasDerivAt (pickR γ α β)
      (-1 * logDerivF γ α β z + -z * deriv (logDerivF γ α β) z) z := by
    rw [show (pickR γ α β) = (fun w : ℂ => -w * logDerivF γ α β w) from
      funext (pickR_eq_neg_mul_logDerivF γ α β)]
    exact ((hasDerivAt_id z).neg).mul hLdiff.hasDerivAt
  have hLp : pickDeriv γ α β z = -z * deriv (logDerivF γ α β) z := by
    have := hR1.unique hR2
    rw [hL0] at this
    linear_combination this
  -- second differentiation
  have hf : HasDerivAt (symbolF γ α β) 0 z := by
    have := (differentiableAt_symbolF hC).hasDerivAt (f := symbolF γ α β)
    rwa [hcrit] at this
  have hmul : HasDerivAt (fun w => symbolF γ α β w * logDerivF γ α β w)
      (0 * logDerivF γ α β z + symbolF γ α β z * deriv (logDerivF γ α β) z) z :=
    hf.mul hLdiff.hasDerivAt
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq, hmul.deriv, hLp]
  field

/-- **Nondegeneracy.**  At a nonzero *real* critical point, `f''(τ) ≠ 0`. -/
theorem iteratedDeriv_two_symbolF_ne_zero (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i)
    (hβ : ∀ j, 0 < β j) (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) {t : ℝ} (ht : t ≠ 0)
    (hA : numerA γ α (t : ℂ) ≠ 0) (hC : denomC β (t : ℂ) ≠ 0)
    (hcrit : deriv (symbolF γ α β) (t : ℂ) = 0) :
    iteratedDeriv 2 (symbolF γ α β) (t : ℂ) ≠ 0 := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hw : 0 < pickWeight γ α β (t : ℂ) :=
    pickWeight_pos hγ hα hβ hnd (one_sub_ne_zero_of_numerA hA) (one_add_ne_zero_of_denomC hC)
  have hR : pickDeriv γ α β (t : ℂ) ≠ 0 := by
    rw [pickDeriv_ofReal]
    exact Complex.ofReal_ne_zero.mpr hw.ne'
  rw [iteratedDeriv_two_symbolF htC hA hC hcrit]
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (symbolF_ne_zero hA hC) hR)) htC

/-! ## The double level point

The solutions of `f = c` are the zeros of `g_c = A - cC`.  Two facts follow from the rigidity
above: at a critical point `τ` with `c = f(τ)` the zero of `g_c` at `τ` has multiplicity
exactly two, and `τ` is the only point of the circle `|z| = |τ|` carrying the value `c`.
Together they say that exactly two zeros of `g_c`, counted with multiplicity, lie on
`|z| = |τ|`. -/

/-- `g_c = A - cC`, whose zeros are the solutions of `f = c`. -/
noncomputable def levelFn (γ : ℝ) (α : Fin a → ℝ) (β : Fin b → ℝ) (c z : ℂ) : ℂ :=
  numerA γ α z - c * denomC β z

theorem differentiable_levelFn : Differentiable ℂ (levelFn γ α β c) :=
  differentiable_numerA.sub ((differentiable_denomC).const_mul c)

/-- No pole of `f` is a level root: `g_c(-1/β_j) = A(-1/β_j) ≠ 0`. -/
theorem levelFn_ne_zero_of_denomC_eq_zero (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    {z : ℂ} (hC : denomC β z = 0) : levelFn γ α β c z ≠ 0 := by
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hC
  have hz : z = -(1 / (β j : ℂ)) := by
    have hβj : (β j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hβ j).ne'
    field_simp at hj ⊢
    linear_combination hj
  have hA : numerA γ α z ≠ 0 := by
    refine mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    have hpos : (0 : ℝ) < 1 + α i / β j := by
      have := div_pos (hα i) (hβ j); linarith
    have hcast : (1 : ℂ) - (α i : ℂ) * z = ((1 + α i / β j : ℝ) : ℂ) := by
      rw [hz]; push_cast; field
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [levelFn, hC, mul_zero, sub_zero]
  exact hA

/-- The level function at the critical level vanishes at the critical point. -/
theorem levelFn_self_eq_zero {z : ℂ} (hC : denomC β z ≠ 0) :
    levelFn γ α β (symbolF γ α β z) z = 0 := by
  rw [levelFn, symbolF, div_mul_cancel₀ _ hC, sub_self]

/-- The first derivative of `g_c` vanishes at a critical point of `f`. -/
theorem deriv_levelFn_eq_zero {z : ℂ} (hC : denomC β z ≠ 0)
    (hcrit : deriv (symbolF γ α β) z = 0) :
    deriv (levelFn γ α β (symbolF γ α β z)) z = 0 := by
  have hw : deriv (numerA γ α) z * denomC β z - numerA γ α z * deriv (denomC β) z = 0 := by
    have h := deriv_symbolF_eq_wronskian (γ := γ) (α := α) hC
    rw [hcrit] at h
    exact (div_eq_zero_iff.mp h.symm).resolve_right (pow_ne_zero 2 hC)
  have hd : deriv (levelFn γ α β (symbolF γ α β z)) z
      = deriv (numerA γ α) z - symbolF γ α β z * deriv (denomC β) z :=
    ((differentiable_numerA (γ := γ) (α := α) z).hasDerivAt.sub
      ((differentiable_denomC (β := β) z).hasDerivAt.const_mul _)).deriv
  rw [hd, symbolF]
  field_simp
  linear_combination hw

theorem analyticAt_symbolF {z : ℂ} (hC : denomC β z ≠ 0) :
    AnalyticAt ℂ (symbolF γ α β) z :=
  (differentiable_numerA.analyticAt z).div (differentiable_denomC.analyticAt z) hC

/-- `g_c = C·(f - c)` with `f(τ) = c` and `f'(τ) = 0`, so the second derivatives agree up to
the factor `C(τ)`: `g_c''(τ) = C(τ) f''(τ)`. -/
theorem iteratedDeriv_two_levelFn {τ : ℂ} (hC : denomC β τ ≠ 0)
    (hcrit : deriv (symbolF γ α β) τ = 0) :
    iteratedDeriv 2 (levelFn γ α β (symbolF γ α β τ)) τ
      = denomC β τ * iteratedDeriv 2 (symbolF γ α β) τ := by
  set c := symbolF γ α β τ with hc
  have hCev : ∀ᶠ w in 𝓝 τ, denomC β w ≠ 0 :=
    (differentiable_denomC (β := β)).continuous.continuousAt.eventually_ne hC
  have hd1 : deriv (levelFn γ α β c) =ᶠ[𝓝 τ]
      fun w => deriv (denomC β) w * (symbolF γ α β w - c)
        + denomC β w * deriv (symbolF γ α β) w := by
    filter_upwards [hCev.eventually_nhds] with w hw
    have hfac : levelFn γ α β c =ᶠ[𝓝 w] fun v => denomC β v * (symbolF γ α β v - c) := by
      filter_upwards [hw] with v hv
      rw [levelFn, symbolF]
      field_simp
    rw [hfac.deriv_eq]
    exact ((differentiable_denomC (β := β) w).hasDerivAt.mul
      ((differentiableAt_symbolF hw.self_of_nhds).hasDerivAt.sub_const c)).deriv
  have hCd : DifferentiableAt ℂ (deriv (denomC β)) τ :=
    ((differentiable_denomC (β := β)).analyticAt τ).deriv.differentiableAt
  have hfd : DifferentiableAt ℂ (deriv (symbolF γ α β)) τ :=
    (analyticAt_symbolF hC).deriv.differentiableAt
  have hsub : HasDerivAt (fun w => symbolF γ α β w - c) 0 τ := by
    have := (differentiableAt_symbolF hC).hasDerivAt (f := symbolF γ α β)
    rw [hcrit] at this
    exact this.sub_const c
  have hprod : HasDerivAt
      (fun w => deriv (denomC β) w * (symbolF γ α β w - c)
        + denomC β w * deriv (symbolF γ α β) w)
      ((deriv (deriv (denomC β)) τ * (symbolF γ α β τ - c) + deriv (denomC β) τ * 0)
        + (deriv (denomC β) τ * deriv (symbolF γ α β) τ
          + denomC β τ * deriv (deriv (symbolF γ α β)) τ)) τ :=
    (hCd.hasDerivAt.mul hsub).add
      ((differentiable_denomC (β := β) τ).hasDerivAt.mul hfd.hasDerivAt)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1.deriv_eq, hprod.deriv, hcrit,
    iteratedDeriv_succ, iteratedDeriv_one, hc]
  ring

/-- **The level function has a double zero at a critical point.**  At a nonzero real
critical point `τ` is a zero of `g_c` of multiplicity exactly two: `g_c(τ) = g_c'(τ) = 0` and
`g_c''(τ) ≠ 0`, the last clause being the nondegeneracy above. -/
theorem levelFn_order_two (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) {t : ℝ} (ht : t ≠ 0)
    (hA : numerA γ α (t : ℂ) ≠ 0) (hC : denomC β (t : ℂ) ≠ 0)
    (hcrit : deriv (symbolF γ α β) (t : ℂ) = 0) :
    levelFn γ α β (symbolF γ α β (t : ℂ)) (t : ℂ) = 0
      ∧ deriv (levelFn γ α β (symbolF γ α β (t : ℂ))) (t : ℂ) = 0
      ∧ iteratedDeriv 2 (levelFn γ α β (symbolF γ α β (t : ℂ))) (t : ℂ) ≠ 0 := by
  refine ⟨levelFn_self_eq_zero hC, deriv_levelFn_eq_zero hC hcrit, ?_⟩
  rw [iteratedDeriv_two_levelFn hC hcrit]
  exact mul_ne_zero hC
    (iteratedDeriv_two_symbolF_ne_zero hγ hα hβ hnd ht hA hC hcrit)

/-- **A real critical point is alone on its circle at the critical level.**  A second point
would be `τ` or `conj τ = τ`; equal levels give equal moduli, which is all `hcirc` asks.  With
the double zero above, exactly two zeros of `g_c`, counted with multiplicity, lie on
`|z| = |τ|`.

`hcirc` is the circular rigidity, taken here as a hypothesis; `circular_rigidity` below
discharges it. -/
theorem eq_of_levelFn_eq_zero_of_norm_eq
    (hcirc : ∀ w t : ℂ, ‖w‖ = ‖t‖ → denomC β w ≠ 0 → denomC β t ≠ 0 → numerA γ α w ≠ 0 →
      ‖numerA γ α w * denomC β t‖ = ‖numerA γ α t * denomC β w‖ →
      w = t ∨ w = (starRingEnd ℂ) t)
    {t : ℝ} (hC : denomC β (t : ℂ) ≠ 0) (hA : numerA γ α (t : ℂ) ≠ 0)
    {w : ℂ} (hw : ‖w‖ = ‖(t : ℂ)‖) (hCw : denomC β w ≠ 0)
    (hlev : levelFn γ α β (symbolF γ α β (t : ℂ)) w = 0) :
    w = (t : ℂ) := by
  have hc : symbolF γ α β (t : ℂ) ≠ 0 := symbolF_ne_zero hA hC
  have hAw : numerA γ α w = symbolF γ α β (t : ℂ) * denomC β w := by
    have := hlev
    rw [levelFn, sub_eq_zero] at this
    exact this
  have hAwne : numerA γ α w ≠ 0 := by rw [hAw]; exact mul_ne_zero hc hCw
  have hcross : numerA γ α w * denomC β (t : ℂ) = numerA γ α (t : ℂ) * denomC β w := by
    rw [hAw, symbolF]
    field_simp
  rcases hcirc w (t : ℂ) hw hCw hC hAwne (congrArg norm hcross) with h | h
  · exact h
  · rwa [Complex.conj_ofReal] at h

/-- `‖A(z)‖²` as a function of `r = ‖z‖` and `x = Re z`. -/
noncomputable def numerSq (γ : ℝ) (α : Fin a → ℝ) (r x : ℝ) : ℝ :=
  Real.exp (-(2 * γ * x)) * ∏ i, (1 - 2 * α i * x + α i ^ 2 * r ^ 2)

/-- `‖C(z)‖²` as a function of `r = ‖z‖` and `x = Re z`. -/
noncomputable def denomSq (β : Fin b → ℝ) (r x : ℝ) : ℝ :=
  ∏ j, (1 + 2 * β j * x + β j ^ 2 * r ^ 2)

private theorem sq_norm_one_sub (c : ℝ) (z : ℂ) :
    ‖1 - (c : ℂ) * z‖ ^ 2 = 1 - 2 * c * z.re + c ^ 2 * ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem sq_norm_one_add (c : ℝ) (z : ℂ) :
    ‖1 + (c : ℂ) * z‖ ^ 2 = 1 + 2 * c * z.re + c ^ 2 * ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The squared modulus of the numerator sees `z` only through `‖z‖` and `Re z`. -/
theorem sq_norm_numerA (z : ℂ) : ‖numerA γ α z‖ ^ 2 = numerSq γ α ‖z‖ z.re := by
  rw [numerA, norm_mul, mul_pow, Complex.norm_exp, norm_prod, ← Finset.prod_pow, numerSq]
  congr 1
  · rw [sq, ← Real.exp_add]
    congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, neg_zero, zero_mul, sub_zero]
    ring
  · exact Finset.prod_congr rfl fun i _ => sq_norm_one_sub _ _

/-- The squared modulus of the denominator. -/
theorem sq_norm_denomC (z : ℂ) : ‖denomC β z‖ ^ 2 = denomSq β ‖z‖ z.re := by
  rw [denomC, norm_prod, ← Finset.prod_pow, denomSq]
  exact Finset.prod_congr rfl fun j _ => sq_norm_one_add _ _

/-- **Angular monotonicity, cross-multiplied.**  Moving `Re z` up along a fixed circle
strictly decreases `‖A‖²` and strictly increases `‖C‖²`, so it strictly decreases `‖f‖²`.  The
positivity hypotheses are exactly what `A(z) ≠ 0` and `C(z) ≠ 0` supply at the two points, so
no bound on `x` and `y` is needed. -/
theorem numerSq_mul_denomSq_lt (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) {r x y : ℝ} (hxy : x < y)
    (hNx : ∀ i, 0 < 1 - 2 * α i * x + α i ^ 2 * r ^ 2)
    (hNy : ∀ i, 0 < 1 - 2 * α i * y + α i ^ 2 * r ^ 2)
    (hQx : ∀ j, 0 < 1 + 2 * β j * x + β j ^ 2 * r ^ 2)
    (hQy : ∀ j, 0 < 1 + 2 * β j * y + β j ^ 2 * r ^ 2) :
    numerSq γ α r y * denomSq β r x < numerSq γ α r x * denomSq β r y := by
  set PX := ∏ i, (1 - 2 * α i * x + α i ^ 2 * r ^ 2) with hPX
  set PY := ∏ i, (1 - 2 * α i * y + α i ^ 2 * r ^ 2) with hPY
  have hPXpos : 0 < PX := Finset.prod_pos fun i _ => hNx i
  have hPYpos : 0 < PY := Finset.prod_pos fun i _ => hNy i
  have hQXpos : 0 < denomSq β r x := Finset.prod_pos fun j _ => hQx j
  have hQYpos : 0 < denomSq β r y := Finset.prod_pos fun j _ => hQy j
  have hNXpos : 0 < numerSq γ α r x := mul_pos (Real.exp_pos _) hPXpos
  -- termwise monotonicity, strict in each individual factor
  have hPle : PY ≤ PX :=
    Finset.prod_le_prod (fun i _ => (hNy i).le) fun i _ => by nlinarith [hα i]
  have hQle : denomSq β r x ≤ denomSq β r y :=
    Finset.prod_le_prod (fun j _ => (hQx j).le) fun j _ => by nlinarith [hβ j]
  have hexple : Real.exp (-(2 * γ * y)) ≤ Real.exp (-(2 * γ * x)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hNle : numerSq γ α r y ≤ numerSq γ α r x :=
    mul_le_mul hexple hPle hPYpos.le (Real.exp_pos _).le
  -- `hnd` upgrades one of the two inequalities to a strict one
  have key : numerSq γ α r y < numerSq γ α r x ∨ denomSq β r x < denomSq β r y := by
    rcases hnd with hg | ha | hb
    · exact Or.inl ((mul_lt_mul_of_pos_right (Real.exp_lt_exp.2 (by nlinarith)) hPYpos).trans_le
        (mul_le_mul_of_nonneg_left hPle (Real.exp_pos _).le))
    · have hPlt : PY < PX := Finset.prod_lt_prod_of_nonempty (fun i _ => hNy i)
        (fun i _ => by nlinarith [hα i])
        (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero ha)))
      exact Or.inl ((mul_le_mul_of_nonneg_right hexple hPYpos.le).trans_lt
        (mul_lt_mul_of_pos_left hPlt (Real.exp_pos _)))
    · exact Or.inr (Finset.prod_lt_prod_of_nonempty (fun j _ => hQx j)
        (fun j _ => by nlinarith [hβ j])
        (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero hb))))
  rcases key with h | h
  · exact (mul_lt_mul_of_pos_right h hQXpos).trans_le
      (mul_le_mul_of_nonneg_left hQle hNXpos.le)
  · exact (mul_le_mul_of_nonneg_right hNle hQXpos.le).trans_lt
      (mul_lt_mul_of_pos_left h hNXpos)

/-- **Equal modulus and equal real part leave the imaginary part up to sign.**  Two points of the
same circle with the same real part are equal or conjugate, which is what turns the strict
monotonicity of the profiles in `Re z` into rigidity. -/
theorem im_eq_or_eq_neg_of_norm_eq_of_re_eq {w t : ℂ} (hn : ‖w‖ = ‖t‖) (hre : w.re = t.re) :
    w.im = t.im ∨ w.im = -t.im := by
  have hsq : w.im ^ 2 = t.im ^ 2 := by
    have hw := Complex.sq_norm w
    have ht := Complex.sq_norm t
    rw [Complex.normSq_apply] at hw ht
    rw [hn, hre] at hw
    nlinarith [hw, ht]
  rcases mul_eq_zero.1 (show (w.im - t.im) * (w.im + t.im) = 0 by nlinarith [hsq]) with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **Circular rigidity.**  Two points of one circle at which `|f|` takes the same value,
finite and nonzero at one of them, are equal or conjugate.  The hypothesis is the *modulus*
one, which is the weaker: equal `f`-values give it at once.  This discharges the `hcirc`
hypothesis of `eq_of_levelFn_eq_zero_of_norm_eq`. -/
theorem circular_rigidity (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0) :
    ∀ w t : ℂ, ‖w‖ = ‖t‖ → denomC β w ≠ 0 → denomC β t ≠ 0 → numerA γ α w ≠ 0 →
      ‖numerA γ α w * denomC β t‖ = ‖numerA γ α t * denomC β w‖ →
      w = t ∨ w = (starRingEnd ℂ) t := by
  intro w t hnorm hCw hCt hAw hcross
  have hAt : numerA γ α t ≠ 0 := by
    intro h
    rw [h, zero_mul, norm_zero] at hcross
    exact (mul_ne_zero hAw hCt) (norm_eq_zero.mp hcross)
  -- every factor of `A` and of `C` is nonzero at both points, which is the positivity the
  -- comparison lemma consumes
  have hfacA : ∀ (z : ℂ), numerA γ α z ≠ 0 →
      ∀ i, 0 < 1 - 2 * α i * z.re + α i ^ 2 * ‖z‖ ^ 2 := by
    intro z hz i
    have hne := one_sub_ne_zero_of_numerA hz i
    rw [← sq_norm_one_sub]
    positivity
  have hfacC : ∀ (z : ℂ), denomC β z ≠ 0 →
      ∀ j, 0 < 1 + 2 * β j * z.re + β j ^ 2 * ‖z‖ ^ 2 := by
    intro z hz j
    have hne := one_add_ne_zero_of_denomC hz j
    rw [← sq_norm_one_add]
    positivity
  -- the cross relation, squared, is an equality of the two profiles
  have hprof : numerSq γ α ‖t‖ w.re * denomSq β ‖t‖ t.re
      = numerSq γ α ‖t‖ t.re * denomSq β ‖t‖ w.re := by
    have h := congrArg (fun u : ℝ => u ^ 2) hcross
    simp only [norm_mul, mul_pow] at h
    rw [sq_norm_numerA, sq_norm_denomC, sq_norm_numerA, sq_norm_denomC, hnorm] at h
    exact h
  -- all four positivity packets, stated against the common radius `‖t‖`
  have hAw' : ∀ i, 0 < 1 - 2 * α i * w.re + α i ^ 2 * ‖t‖ ^ 2 := by
    rw [← hnorm]; exact hfacA w hAw
  have hAt' : ∀ i, 0 < 1 - 2 * α i * t.re + α i ^ 2 * ‖t‖ ^ 2 := hfacA t hAt
  have hCw' : ∀ j, 0 < 1 + 2 * β j * w.re + β j ^ 2 * ‖t‖ ^ 2 := by
    rw [← hnorm]; exact hfacC w hCw
  have hCt' : ∀ j, 0 < 1 + 2 * β j * t.re + β j ^ 2 * ‖t‖ ^ 2 := hfacC t hCt
  -- the real parts must agree
  have hre : w.re = t.re := by
    rcases lt_trichotomy w.re t.re with hlt | heq | hgt
    · exact absurd hprof.symm (ne_of_lt (numerSq_mul_denomSq_lt hγ hα hβ hnd hlt
        hAw' hAt' hCw' hCt'))
    · exact heq
    · exact absurd hprof (ne_of_lt (numerSq_mul_denomSq_lt hγ hα hβ hnd hgt
        hAt' hAw' hCt' hCw'))
  -- equal modulus and equal real part leave the imaginary part up to sign
  have him := im_eq_or_eq_neg_of_norm_eq_of_re_eq hnorm hre
  rcases him with h | h
  · exact Or.inl (Complex.ext hre h)
  · exact Or.inr (Complex.ext (by rw [Complex.conj_re]; exact hre)
      (by rw [Complex.conj_im]; exact h))

/-- **A real critical point is alone on its circle at the critical level**, unconditionally:
`eq_of_levelFn_eq_zero_of_norm_eq` with its rigidity hypothesis discharged by
`circular_rigidity`. -/
theorem eq_of_levelFn_eq_zero_of_norm_eq_of_pos (hγ : 0 ≤ γ) (hα : ∀ i, 0 < α i)
    (hβ : ∀ j, 0 < β j) (hnd : 0 < γ ∨ a ≠ 0 ∨ b ≠ 0)
    {t : ℝ} (hC : denomC β (t : ℂ) ≠ 0) (hA : numerA γ α (t : ℂ) ≠ 0)
    {w : ℂ} (hw : ‖w‖ = ‖(t : ℂ)‖) (hCw : denomC β w ≠ 0)
    (hlev : levelFn γ α β (symbolF γ α β (t : ℂ)) w = 0) :
    w = (t : ℂ) :=
  eq_of_levelFn_eq_zero_of_norm_eq (circular_rigidity hγ hα hβ hnd) hC hA hw hCw hlev


/-! ### Axiom footprint -/

/-- info: 'Shields.pick_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pick_rigidity

/-- info: 'Shields.circular_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms circular_rigidity

/-- info: 'Shields.levelFn_order_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelFn_order_two

/-- info: 'Shields.eq_of_levelFn_eq_zero_of_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_of_levelFn_eq_zero_of_norm_eq

end Shields
