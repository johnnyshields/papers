/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchZMono

/-!
# `eq:principal-simple` on the general branch

Every nonreal zero of the pencil `D(·,z) = Q + zX^r` is a *simple* zero, for any
`Q` in the admissible class `eq:Q-hypotheses` and any `z`, real or not.  This is
the hypothesis carried through the dominance chain as `hsp`/`hsm`, and until now
it was witnessed only at concrete pencils.

The argument is the manuscript's.  `Geometry.ftCritical_ftDen` says the critical
polynomial `E(t) = tQ'(t) - rQ(t)` is unchanged by the pencil, so at a zero `t`
of `D(·,z)` one has `t·D'(t,z) = E(t)`; a double zero therefore forces `E(t)=0`.
`FTBranchZMono.eval_ftCritical_ftRootPoly` factors `E = -Σ·Q`, and on either open
half plane `Σ` has imaginary part of the sign of `Im t`, while `Q` has only real
zeros.  Neither factor vanishes, so neither does `t·D'(t,z)`.

The consequence needs no lower bound on `r` beyond `1 ≤ r`, no reality of `z`,
and no relation between `z` and `t` other than `t` being a zero: `E` is what
survives the elimination, and it does not see `z` at all.

## Containment

`eval_derivative_ftDen_ftRootPoly_ne_zero` relates `derivative (ftDen …)`, the
point `t`, and the data `c, a, r, z`.  No hypothesis mentions a derivative of the
pencil: `hroot` is a *vanishing* statement about `ftDen` itself, `ht` constrains
only `Im t`, and `ha`, `hc`, `hr`, `hn` constrain only the admissible class.  The
nonvanishing is produced from `Geometry.ftCritical_ftDen` and
`eval_ftCritical_ftRootPoly_ne_zero`, which is where its content sits.  The
hypotheses are jointly satisfiable — `FTBranchPencil.exists_ftDen_root_on_arc`
produces such a `t` at every angle of the viewing arc — so the statement is not
vacuous.

## Main statements

* `ftSigma_im_pos` — the upper-half-plane companion of `ftSigma_im_neg`.
* `eval_ftCritical_ftRootPoly_ne_zero` — every critical point of `g` is real,
  which is the whole content.
* `eval_derivative_ftDen_ftRootPoly_ne_zero` — `eq:principal-simple` at any
  nonreal zero of the pencil, at any `z`.
* `eval_derivative_ftDen_fiber_ne_zero` — the same at `z = g(t)`.
* `eval_derivative_ftDen_ne_zero_of_arg` — the same in the polar form
  `t = τe^{iθ}` the dominance chain states `hsp` in.
* `eval_derivative_ftDen_conj_ne_zero_of_arg` — its conjugate, `hsm`.

## References

Formalizes `eq:principal-simple` of the manuscript, whose proof is the sign of
`Im (tQ'(t)/Q(t))` on the upper half plane.

## Tags

simple zero, pencil, principal branch
-/

namespace ForgacsTran

open Real Set Polynomial Complex

/-- **The upper-half-plane companion of `ftSigma_im_neg`.**  Each summand of `Σ`
carries the sign of `Im t`, so on the open upper half plane `Σ` has strictly
positive imaginary part. -/
theorem ftSigma_im_pos {n r : ℕ} (hn : 0 < n) {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {t : ℂ}
    (ht : 0 < t.im) : 0 < (ftSigma a r t).im := by
  have hne : ∀ k, ((a k : ℂ)) - t ≠ 0 := by
    intro k hk
    have := congrArg Complex.im hk
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at this
    exact absurd this (ne_of_gt ht)
  rw [ftSigma_im a r hne]
  refine Finset.sum_pos (fun k _ => ?_) (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  exact div_pos (mul_pos (ha k) ht) (Complex.normSq_pos.2 (hne k))

/-- `Σ ≠ 0` off the real axis, in either half plane. -/
theorem ftSigma_ne_zero_of_im_ne {n r : ℕ} (hn : 0 < n) {a : Fin n → ℝ} (ha : ∀ k, 0 < a k)
    {t : ℂ} (ht : t.im ≠ 0) : ftSigma a r t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with h | h
  · exact ftSigma_ne_zero hn ha h
  · intro hz
    have := ftSigma_im_pos (r := r) hn ha h
    rw [hz] at this
    simp at this

/-- The admissible pencil's `Q` has only real zeros, so it does not vanish off
the real axis. -/
theorem eval_ftRootPoly_ne_zero {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hc : c ≠ 0) {t : ℂ}
    (ht : t.im ≠ 0) : (ftRootPoly c a).eval t ≠ 0 := by
  rw [eval_ftRootPoly]
  refine mul_ne_zero (by exact_mod_cast hc) (Finset.prod_ne_zero_iff.2 fun k _ hk => ?_)
  have := congrArg Complex.im hk
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at this
  exact ht this

/-- **Every critical point of `g(t) = -Q(t)/t^r` is real.**  This is stronger
than `eq:principal-simple` needs and is where its whole content sits: the
critical polynomial factors as `E = -Σ·Q`, `Σ` has imaginary part of the sign of
`Im t` on either open half plane, and `Q` has only real zeros.  Neither factor
vanishes off the real axis, and no property of the branch is used. -/
theorem eval_ftCritical_ftRootPoly_ne_zero {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} {t : ℂ} (ht : t.im ≠ 0) :
    (ftCritical (ftRootPoly c a) r).eval t ≠ 0 := by
  have hne : ∀ k, ((a k : ℂ)) - t ≠ 0 := by
    intro k hk
    have := congrArg Complex.im hk
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at this
    exact ht this
  rw [eval_ftCritical_ftRootPoly c a r hne]
  exact mul_ne_zero (neg_ne_zero.2 (ftSigma_ne_zero_of_im_ne (r := r) hn ha ht))
    (eval_ftRootPoly_ne_zero hc ht)

/-- **`eq:principal-simple`.**  A nonreal zero of `D(·,z) = Q + zX^r` is simple,
for every admissible `Q` and every `z`.  A double zero would put `t` on the
critical set of `g`, and `ftCritical_ftDen` says the critical polynomial is the
pencil's `z`-free invariant `E = tQ' - rQ`, which
`eval_ftCritical_ftRootPoly_ne_zero` keeps off the real axis.

The pencil parameter is unrestricted — `z` need not be real, and need not be the
fiber value `g(t)` — because `E` does not see it. -/
theorem eval_derivative_ftDen_ftRootPoly_ne_zero {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z t : ℂ} (ht : t.im ≠ 0)
    (hroot : (ftDen (ftRootPoly c a) r z).eval t = 0) :
    (derivative (ftDen (ftRootPoly c a) r z)).eval t ≠ 0 := by
  intro hd
  refine eval_ftCritical_ftRootPoly_ne_zero (r := r) hn ha hc ht ?_
  rw [← ftCritical_ftDen (ftRootPoly c a) hr z, eval_ftCritical, hd, hroot]
  ring

/-- **`eq:principal-simple` at the fiber value.**  The same statement with `z`
taken to be `g(t) = -Q(t)/t^r`, which is the spelling that reads directly off
`eq:Dprime-identity`: `∂_tD(t,g(t)) = Q'(t) - rQ(t)/t = -t^rg'(t)`. -/
theorem eval_derivative_ftDen_fiber_ne_zero {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {t : ℂ} (ht : t.im ≠ 0) :
    (derivative (ftDen (ftRootPoly c a) r
      (-(ftRootPoly c a).eval t / t ^ r))).eval t ≠ 0 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
  refine eval_derivative_ftDen_ftRootPoly_ne_zero hn ha hc hr ht ?_
  rw [ftDen_eval, div_mul_cancel₀ _ (pow_ne_zero r ht0)]
  ring

/-- **`hsp`, on the general branch.**  The polar form the dominance chain states
`eq:principal-simple` in: at `t = τe^{iθ}` with `τ > 0` and `0 < θ < π`, the
point lies in the open upper half plane. -/
theorem eval_derivative_ftDen_ne_zero_of_arg {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z : ℂ} {τ θ : ℝ} (hτ : 0 < τ)
    (hθ : θ ∈ Ioo 0 π)
    (hroot : (ftDen (ftRootPoly c a) r z).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0) :
    (derivative (ftDen (ftRootPoly c a) r z)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ≠ 0 := by
  refine eval_derivative_ftDen_ftRootPoly_ne_zero hn ha hc hr ?_ hroot
  have him : (((τ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)).im = τ * Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
  rw [him]
  exact ne_of_gt (mul_pos hτ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))

/-- **`hsm`, on the general branch.**  The conjugate point `τe^{-iθ}` lies in the
open lower half plane under the same hypotheses. -/
theorem eval_derivative_ftDen_conj_ne_zero_of_arg {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z : ℂ} {τ θ : ℝ} (hτ : 0 < τ)
    (hθ : θ ∈ Ioo 0 π)
    (hroot : (ftDen (ftRootPoly c a) r z).eval ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) = 0) :
    (derivative (ftDen (ftRootPoly c a) r z)).eval ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) ≠ 0 := by
  refine eval_derivative_ftDen_ftRootPoly_ne_zero hn ha hc hr ?_ hroot
  have him : (((τ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I)).im = -(τ * Real.sin θ) := by
    simp only [← Complex.ofReal_neg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, Real.sin_neg]
    ring
  rw [him]
  exact ne_of_lt (neg_neg_of_pos (mul_pos hτ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)))

end ForgacsTran
