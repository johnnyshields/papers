/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointCollision
import ForgacsTran.LowerSeparationQuotient

/-!
# The lower endpoint's separation, normalized off the pencil

The `ρ = 1` retained group needs a radius `R₀` fixed across its window, with
`sup τ < R₀ < inf_j |w_j|`.  Both sides converge to the endpoint as `δ → 0`, so
such an `R₀` exists exactly when

  `t_a < |w|` **strictly**, for every root `w ≠ t_a` of the endpoint pencil.

**What it does not need is a constant.**  A quantitative bound in the relative gap
`g = (a₁-a₀)/a₁` is available — `min_j|w_j|/t ≥ 1 + c_n g` — but its constant
decays with no positive floor (`scripts/check_lower_per_root_asymptotic.py`), so a
radius in that form collapses onto the collision radius as the pencil grows.  The
strict inequality carries no `n` and is all the group consumes.

**The normalization.**  A root of the pencil at the branch's own endpoint value
satisfies `Q(w)/w^r = Q(t)/t^r`.  Writing `s = w/t` and `v_k = t/(a_k - t)`, that
becomes

  `∏_k (1 - σ v_k) = (1 + σ)^r`,   `σ = s - 1`,

and `c`, `t` and the `a_k` all leave.  This is the lower endpoint's counterpart of
the simplex normalization `∏(1 - u_k s) = 1 - s` on `∑u_k = 1` that
`EndpointUpperGeneralN` runs on; here the constraint is `∑_k v_k = -r`, which is
`Σ(t) = 0`, and `σ = 0` is the collision — a double root, since `-∑v_k = r` matches
the derivative too.

**The hypothesis to carry is the positive tail, and `v₀ < -1` is not a second
one.**  `a_k > t` gives `v_k > 0`, and that is genuine geometric input — it says
where the critical point sits relative to every zero above the smallest.  From it
`v₀ < -1` follows twice over and must not be written down as an independent sign
hypothesis: arithmetically, `v₀ = -r - ∑_{k≥1} v_k < -r ≤ -1` once the tail is
positive and `r ≥ 1`; and geometrically, `v₀ = t/(a₀ - t)` with `0 < a₀ < t`.  The
region `v₀ ∈ (-1,0)` with a positive tail summing to `-r` is empty, so nothing can
be measured in it.

Where `v₀ < -1` does earn a mention is as the non-degeneracy `1 + v₀ ≠ 0`, which
is what would legalize the substitution `p_k = v_k/(1+v_k)`; `v₀ = -1` is the
single value the arithmetic above excludes.  That is a consequence to be derived
at the point of use, not a binder.

## Main statements

* `prod_one_sub_mul_eq_of_root_endpoint` — the reduction, exactly: a root of the
  endpoint pencil satisfies the normalized equation.
* `lt_norm_of_root_endpoint_of_separation` — the separation the retained group
  consumes, from the normalized inequality.  The inequality itself is the
  hypothesis, and is the one thing here not yet proved.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:ab-def`, `eq:principal-pair`, `subsec:proof`.

## Tags

lower endpoint, separation, retained set, normalization, rho = 1
-/

namespace ForgacsTran

open Polynomial

/-- **The reduction.**  A root `w` of the pencil at the branch's own endpoint value
satisfies `∏_k (1 - σ v_k) = (1 + σ)^r` with `σ = w/t - 1` and `v_k = t/(a_k - t)`.

Nothing is assumed about where `t` sits beyond `t ≠ 0` and `t` missing every `a_k`,
so this is an identity about the pencil rather than a statement about the
endpoint. -/
theorem prod_one_sub_mul_eq_of_root_endpoint {n r : ℕ} {a : Fin n → ℝ} {c t : ℝ}
    (hc : c ≠ 0) (ht : t ≠ 0) (hne : ∀ k, a k - t ≠ 0) {w : ℂ}
    (hw : (ftDen (ftRootPoly c a)
      r ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ)).eval w = 0) :
    ∏ k, (1 - (w / (t : ℂ) - 1) * ((t / (a k - t) : ℝ) : ℂ)) = (w / (t : ℂ)) ^ r := by
  classical
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hneC : ∀ k, ((a k : ℂ) - (t : ℂ)) ≠ 0 := by
    intro k
    have h := hne k
    have h' : ((a k - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    simpa using h'
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hTne : ((t : ℂ)) ^ r ≠ 0 := pow_ne_zero _ htC
  have hprodne : (∏ k, ((a k : ℂ) - (t : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => hneC k
  rw [ftDen_eval, eval_ftRootPoly, eval_ftRootPolyReal] at hw
  have hexp : (((-(c * ∏ k, (a k - t)) / t ^ r : ℝ)) : ℂ)
      = -(((c : ℝ) : ℂ) * (∏ k, ((a k : ℂ) - (t : ℂ))) / (t : ℂ) ^ r) := by
    push_cast
    ring
  rw [hexp] at hw
  -- clear the one division in the pencil condition, once, and stay polynomial
  have hpoly : (∏ k, ((a k : ℂ) - w)) * (t : ℂ) ^ r
      = (∏ k, ((a k : ℂ) - (t : ℂ))) * w ^ r := by
    have h2 : ((c : ℝ) : ℂ) * ((∏ k, ((a k : ℂ) - w)) * (t : ℂ) ^ r)
        = ((c : ℝ) : ℂ) * ((∏ k, ((a k : ℂ) - (t : ℂ))) * w ^ r) := by
      have h3 := hw
      field_simp at h3
      linear_combination h3
    exact mul_left_cancel₀ hcC h2
  -- each factor is the corresponding root ratio
  have hstep : ∀ k, (1 - (w / (t : ℂ) - 1) * ((t / (a k - t) : ℝ) : ℂ))
      = ((a k : ℂ) - w) / ((a k : ℂ) - (t : ℂ)) := by
    intro k
    have hcast : ((t / (a k - t) : ℝ) : ℂ) = (t : ℂ) / ((a k : ℂ) - (t : ℂ)) := by
      push_cast
      ring
    rw [hcast, eq_div_iff (hneC k), sub_mul, one_mul, mul_assoc,
      div_mul_cancel₀ _ (hneC k), sub_mul, div_mul_cancel₀ _ htC]
    ring
  rw [Finset.prod_congr rfl (fun k _ => hstep k), Finset.prod_div_distrib, div_pow,
    div_eq_div_iff hprodne hTne]
  linear_combination hpoly

/-- **The separation the retained group consumes.**  `t < ‖w‖` for every root of
the endpoint pencil other than the collision, given the normalized inequality.

`1 + σ` is `w/t`, so `1 < ‖1 + σ‖` *is* `t < ‖w‖`; the content is entirely in the
hypothesis, and the hypothesis names no pencil.  `σ ≠ 0` is `w ≠ t`, which is what
separates a genuine second root from the collision. -/
theorem lt_norm_of_root_endpoint_of_separation {n r : ℕ} {a : Fin n → ℝ} {c t : ℝ}
    (hc : c ≠ 0) (ht : 0 < t) (hne : ∀ k, a k - t ≠ 0)
    (hsep : ∀ σ : ℂ, σ ≠ 0 →
      (∏ k, (1 - σ * ((t / (a k - t) : ℝ) : ℂ)) = (1 + σ) ^ r) → 1 < ‖1 + σ‖)
    {w : ℂ} (hwne : w ≠ ((t : ℝ) : ℂ))
    (hw : (ftDen (ftRootPoly c a)
      r ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ)).eval w = 0) :
    t < ‖w‖ := by
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  set σ : ℂ := w / (t : ℂ) - 1 with hσ
  have hσne : σ ≠ 0 := by
    intro h0
    apply hwne
    have h1 : w / ((t : ℝ) : ℂ) = 1 := by
      have h2 : w / ((t : ℝ) : ℂ) - 1 = 0 := by rw [hσ] at h0; exact h0
      linear_combination h2
    field_simp at h1
    exact h1
  have heq : ∏ k, (1 - σ * ((t / (a k - t) : ℝ) : ℂ)) = (1 + σ) ^ r := by
    have := prod_one_sub_mul_eq_of_root_endpoint hc ht.ne' hne hw
    rw [hσ]
    simpa [mul_comm] using this
  have h1 := hsep σ hσne heq
  have hws : (1 : ℂ) + σ = w / (t : ℂ) := by rw [hσ]; ring
  rw [hws, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    lt_div_iff₀ ht] at h1
  linarith

/-! ### The collision is the constraint, not a fact to be checked

The normalized equation's two lowest coefficients vanish identically: the constant
because both sides are `1` at `σ = 0`, and the linear one because `∑ v_k = -r`.
So `σ = 0` being a DOUBLE root is the endpoint condition written out, and a route
that re-establishes it is redoing what the hypothesis already gives.

Recorded here because every route tried so far has spent effort on it. -/

@[simp] theorem normalized_at_zero {n r : ℕ} (v : Fin n → ℝ) :
    (∏ k, (1 - (0 : ℂ) * ((v k : ℝ) : ℂ))) - (1 + (0 : ℂ)) ^ r = 0 := by
  simp

/-- **The linear coefficient vanishes, and it vanishes BECAUSE `∑ v_k = -r`.**  The
product contributes `-∑ v_k` and the power contributes `r`, so the endpoint
condition is exactly the statement that they cancel.

This is the second half of the double root at `σ = 0`; `normalized_at_zero` is the
first, and that one needs no hypothesis at all. -/
theorem hasDerivAt_normalized_zero {n r : ℕ} (v : Fin n → ℝ)
    (hsum : ∑ k, v k = -(r : ℝ)) :
    HasDerivAt (fun σ : ℂ => (∏ k, (1 - σ * ((v k : ℝ) : ℂ))) - (1 + σ) ^ r) 0 0 := by
  classical
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      HasDerivAt (fun σ : ℂ => 1 - σ * ((v k : ℝ) : ℂ)) (-((v k : ℝ) : ℂ)) 0 := by
    intro k _
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((v k : ℝ) : ℂ)).const_sub 1
  have hp := HasDerivAt.fun_finsetProd hf
  have h1 : HasDerivAt (fun σ : ℂ => 1 + σ) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add 1
  have hq : HasDerivAt (fun σ : ℂ => (1 + σ) ^ r) ((r : ℂ)) 0 := by
    simpa using h1.fun_pow r
  have hsub := hp.sub hq
  refine hsub.congr_deriv ?_
  have hprod : ∀ k : Fin n, (∏ j ∈ (Finset.univ : Finset (Fin n)).erase k,
      (1 - (0 : ℂ) * ((v j : ℝ) : ℂ))) = 1 := by
    intro k
    simp
  have hsumC : ∑ k, ((v k : ℝ) : ℂ) = -(r : ℂ) := by
    have : ((∑ k, v k : ℝ) : ℂ) = ((-(r : ℝ) : ℝ) : ℂ) := by rw [hsum]
    push_cast at this
    simpa using this
  simp only [hprod, smul_eq_mul, one_mul]
  rw [Finset.sum_neg_distrib, hsumC]
  ring

/-! ### The bridge: `hsep` in the paper's variables

`LowerSeparationQuotient.one_lt_norm_one_add_of_prod_eq_pow` is stated about
`v`, `σ` and a bare product; `hsep` is stated about `a`, `c`, `t`, `w`, `ftDen` and
`ftCriticalReal`.  **Those are two terms for one fact, and each type-checks
alone** — the family that has cost this tree repeatedly — so the seam is written
out here rather than left for a call site to guess at.

Three places it could go wrong quietly, all pinned below:

* the sign convention is `a_k - X`, not `X - a_k`.  Against the other one the
  normalization picks up a `(-1)^n`, which is invisible at even `n`;
* `w ≠ t` is `σ ≠ 0` only because `t ≠ 0`, and that is what separates the double
  root from the roots being separated;
* the **first-gap** clause is what supplies the one-negative configuration:
  `t < a_k` for `k ≠ i` gives `a_k - t > 0` hence `v_k > 0`, and the critical
  equation then forces `v_i < 0`.  The clause added to `hsep` for vacuity is the
  same clause that makes this bridge land. -/

/-- **`Σ(t) = 0` from the critical equation**, away from the zeros of `Q`.  This is
the constraint `∑_k v_k = -r` in the tree's own notation, since
`ftSigmaReal a r t = (∑_k t/(a_k - t)) + r`. -/
theorem ftSigmaReal_eq_zero_of_eval_ftCriticalReal {n r : ℕ} {a : Fin n → ℝ} {c t : ℝ}
    (hc : c ≠ 0) (hne : ∀ k, a k - t ≠ 0)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval t = 0) :
    ftSigmaReal a r t = 0 := by
  have hQ : (ftRootPolyReal c a).eval t ≠ 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun k _ => hne k)
  have hfac := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := r) hne
  rw [hE] at hfac
  rcases mul_eq_zero.1 hfac.symm with h | h
  · exact neg_eq_zero.1 h
  · exact absurd h hQ

/-- **`hsep` discharged.**  At a positive critical point lying in the first gap and
missing every zero of `Q`, every root of the endpoint pencil other than the
collision is strictly outside.

This is `thm:weighted-dominance`'s lower-endpoint separation in the paper's
variables, and it is now a theorem rather than a hypothesis. -/
theorem lt_norm_of_root_endpoint_of_first_gap {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (hr : 1 ≤ r) (hc : c ≠ 0) {i : Fin n} :
    ∀ t : ℝ, 0 < t → (∀ k, a k - t ≠ 0) → (∀ k, k ≠ i → t < a k) →
      (ftCriticalReal (ftRootPolyReal c a) r).eval t = 0 →
      ∀ w : ℂ, (ftDen (ftRootPoly c a) r
          ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ)).eval w = 0 →
        w ≠ ((t : ℝ) : ℂ) → t < ‖w‖ := by
  intro t ht hne hgap hE w hw hwne
  -- the tail is positive because the critical point sits below every other zero
  have hpos : ∀ k, k ≠ i → 0 < t / (a k - t) :=
    fun k hk => div_pos ht (by linarith [hgap k hk])
  -- and the critical equation is the coordinate sum
  have hsum : ∑ k, t / (a k - t) = -(r : ℝ) := by
    have hsig := ftSigmaReal_eq_zero_of_eval_ftCriticalReal hc hne hE
    rw [ftSigmaReal] at hsig
    linarith
  refine lt_norm_of_root_endpoint_of_separation hc ht hne ?_ hwne hw
  intro σ hσ0 heq
  exact one_lt_norm_one_add_of_prod_eq_pow (v := fun k => t / (a k - t)) (i₀ := i)
    hn2 hr hpos hsum hσ0 heq

end ForgacsTran
