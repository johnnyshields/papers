/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The analytic Morse lemma in one complex variable

At a **quadratic critical point** — a point `\tau` where an analytic `f` has `f'(\tau) = 0` and
`f''(\tau) \ne 0` — the function is analytically equivalent to a square.  Three statements, in
increasing strength:

* `f(t) - c = (t - \tau)^2 g(t)` with `g` analytic and `g(\tau) = f''(\tau)/2 \ne 0`;
* `f(t) - c = \kappa \cdot H(t)^2` with `H` analytic, `H(\tau) = 0`, `H'(\tau) \ne 0`, and
  `\kappa = f''(\tau)/2`;
* `f(\psi(w)) = c + \kappa w^2` for an analytic local inverse `\psi` with `\psi(0) = \tau` —
  the **Morse coordinate**.

The third exhibits the two solutions of `f(t) = c + \kappa w^2` near `\tau` outright, as
`\psi(w)` and `\psi(-w)`, so a local root count near a collision comes from the normal form
rather than from a winding-number argument.

## Main results

* `Shields.exists_quadratic_factor`
* `Shields.exists_morse_square`
* `Shields.exists_morse_inverse`

## Implementation notes

The square root of the analytic non-vanishing `g` is taken through `Complex.log`, which is
analytic on the slit plane; normalizing to `g/g(\tau)` puts the value `1` there, and
`Shields.exists_analytic_sqrt` is that step on its own.  The local inverse is Mathlib's
`AnalyticAt.analyticAt_localInverse`, applied to `H`, whose derivative at `\tau` is nonzero.

## References

* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.

## Tags

Morse lemma, quadratic critical point, normal form, local inverse, analytic
-/

open Filter

open scoped Topology

namespace Shields

variable {f : ℂ → ℂ} {τ c : ℂ}

/-- **Order-two factorization at a quadratic critical point.**  If `f` is analytic at `τ` with
`f τ = c`, `f' τ = 0` and `f'' τ ≠ 0`, then near `τ` one has `f t - c = (t - τ)^2 • g t` with `g`
analytic at `τ` and `g τ = f''(τ)/2 ≠ 0`. -/
theorem exists_quadratic_factor (hf : AnalyticAt ℂ f τ) (hm : f τ = c)
    (h1 : deriv f τ = 0) (h2 : iteratedDeriv 2 f τ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g τ ∧ g τ = iteratedDeriv 2 f τ / 2 ∧ g τ ≠ 0 ∧
      ∀ᶠ t in 𝓝 τ, f t - c = (t - τ) ^ 2 • g t := by
  have hF : AnalyticAt ℂ (fun t => f t - c) τ := hf.sub analyticAt_const
  have hd : ∀ k : ℕ, 0 < k → iteratedDeriv k (fun t => f t - c) τ = iteratedDeriv k f τ :=
    fun k hk => by simpa [sub_eq_neg_add] using iteratedDeriv_const_add (f := f) (x := τ) hk (-c)
  have hord : analyticOrderAt (fun t => f t - c) τ = (2 : ℕ) := by
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hF]
    refine ⟨fun k hk => ?_, by rw [hd 2 (by norm_num)]; exact h2⟩
    interval_cases k <;> simp_all [hd 1 one_pos, iteratedDeriv_one]
  obtain ⟨g, hg, hg0, hgeq⟩ := hF.analyticOrderAt_eq_natCast.mp hord
  refine ⟨g, hg, ?_, hg0, hgeq⟩
  have hFeq : (fun t => f t - c) =ᶠ[𝓝 τ] fun t => (t - τ) ^ 2 * g t := by
    filter_upwards [hgeq] with t ht; simpa using ht
  have hsq : ∀ u : ℂ, HasDerivAt (fun s : ℂ => (s - τ) ^ 2) (2 * (u - τ)) u := fun u =>
    (((hasDerivAt_id u).sub_const τ).pow 2).congr_deriv (by norm_num)
  have hd1 : deriv (fun t => (t - τ) ^ 2 * g t)
      =ᶠ[𝓝 τ] fun t => 2 * (t - τ) * g t + (t - τ) ^ 2 * deriv g t := by
    filter_upwards [hg.eventually_analyticAt] with t hgt
    exact ((hsq t).mul hgt.differentiableAt.hasDerivAt).deriv
  have hlin : HasDerivAt (fun t : ℂ => 2 * (t - τ)) 2 τ :=
    (((hasDerivAt_id τ).sub_const τ).const_mul (2 : ℂ)).congr_deriv (by ring)
  have hd2 : HasDerivAt (fun t : ℂ => 2 * (t - τ) * g t + (t - τ) ^ 2 * deriv g t)
      (2 * g τ) τ :=
    ((hlin.mul hg.differentiableAt.hasDerivAt).add
      ((hsq τ).mul hg.deriv.differentiableAt.hasDerivAt)).congr_deriv (by ring)
  rw [← hd 2 (by norm_num), hFeq.iteratedDeriv_eq 2, iteratedDeriv_succ,
    iteratedDeriv_one, hd1.deriv_eq, hd2.deriv]; ring

/-- **A holomorphic square root exists wherever the value is `1`.**  If `q` is analytic at `τ`
with `q τ = 1`, then `s = exp (log q / 2)` is analytic at `τ`, equals `1` there, and squares to `q`
near `τ`.

The value `1` is what makes the branch canonical: it puts `q τ` in the slit plane, where
`Complex.log` is analytic, and it fixes `s τ = 1` rather than `± 1`.  This is the only place the
Morse normal form needs a square root, and it needs it of `g / g τ` for exactly this reason. -/
theorem exists_analytic_sqrt {q : ℂ → ℂ} {τ : ℂ} (hq : AnalyticAt ℂ q τ) (hqτ : q τ = 1) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s τ ∧ s τ = 1 ∧ ∀ᶠ t in 𝓝 τ, s t ^ 2 = q t := by
  have hlog : AnalyticAt ℂ (fun t => Complex.log (q t)) τ :=
    (analyticAt_clog (by rw [hqτ]; exact Complex.one_mem_slitPlane)).comp hq
  refine ⟨fun t => Complex.exp (Complex.log (q t) / 2), (hlog.div_const).cexp, by simp [hqτ], ?_⟩
  have hqne : ∀ᶠ t in 𝓝 τ, q t ≠ 0 :=
    hq.continuousAt.eventually_ne (by rw [hqτ]; exact one_ne_zero)
  filter_upwards [hqne] with t ht
  rw [← Complex.exp_nat_mul,
    show (2 : ℕ) * (Complex.log (q t) / 2) = Complex.log (q t) by push_cast; ring]
  exact Complex.exp_log ht

/-- **The Morse square.**  `g/κ` has a holomorphic square root `s` with `s τ = 1`, so
`H t = (t-τ) s t` satisfies `f t - c = κ H t ²` with `H τ = 0`, `H' τ = 1`. -/
theorem exists_morse_square (hf : AnalyticAt ℂ f τ) (hm : f τ = c)
    (h1 : deriv f τ = 0) (h2 : iteratedDeriv 2 f τ ≠ 0) :
    ∃ (H : ℂ → ℂ) (κ : ℂ), κ = iteratedDeriv 2 f τ / 2 ∧ κ ≠ 0 ∧ AnalyticAt ℂ H τ ∧
      H τ = 0 ∧ deriv H τ = 1 ∧ ∀ᶠ t in 𝓝 τ, f t - c = κ * H t ^ 2 := by
  obtain ⟨g, hg, hgκ, hg0, hgeq⟩ := exists_quadratic_factor hf hm h1 h2
  obtain ⟨s, hs, hsτ, hsq⟩ := exists_analytic_sqrt hg.div_const (div_self hg0)
  refine ⟨fun t => (t - τ) * s t, g τ, hgκ, hg0,
    ((analyticAt_id.sub analyticAt_const).mul hs), ?_, ?_, ?_⟩
  · simp
  · have hds : HasDerivAt s (deriv s τ) τ := hs.differentiableAt.hasDerivAt
    have hdl : HasDerivAt (fun t : ℂ => t - τ) 1 τ := (hasDerivAt_id τ).sub_const τ
    have hmul : HasDerivAt (fun t : ℂ => (t - τ) * s t)
        (1 * s τ + (τ - τ) * deriv s τ) τ := hdl.mul hds
    rw [hmul.deriv]; simp [hsτ]
  · filter_upwards [hgeq, hsq] with t ht hts
    rw [ht, mul_pow, hts]
    simp only [smul_eq_mul]
    field_simp

/-- **The Morse inverse `ψ`.**  Since `H τ = 0` and `H' τ = 1 ≠ 0`, `H` has a local analytic
inverse `ψ` with `ψ 0 = τ`, `ψ' 0 = 1`, and `f (ψ w) = c + κ w²` near `0`. -/
theorem exists_morse_inverse (hf : AnalyticAt ℂ f τ) (hm : f τ = c)
    (h1 : deriv f τ = 0) (h2 : iteratedDeriv 2 f τ ≠ 0) :
    ∃ (ψ : ℂ → ℂ) (κ : ℂ), κ = iteratedDeriv 2 f τ / 2 ∧ κ ≠ 0 ∧ AnalyticAt ℂ ψ 0 ∧
      ψ 0 = τ ∧ deriv ψ 0 = 1 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), f (ψ w) = c + κ * w ^ 2) ∧
      ∃ s ∈ 𝓝 (0 : ℂ), Set.InjOn ψ s := by
  obtain ⟨H, κ, hκv, hκ, hH, hH0, hH1, hHeq⟩ := exists_morse_square hf hm h1 h2
  have hne : deriv H τ ≠ 0 := by rw [hH1]; exact one_ne_zero
  set ψ := hH.hasStrictDerivAt.localInverse _ _ _ hne with hψdef
  have hψa : AnalyticAt ℂ ψ (H τ) := hH.analyticAt_localInverse hne
  have hψ0 : ψ (H τ) = τ := HasStrictFDerivAt.localInverse_apply_image ..
  have hright : ∀ᶠ w in 𝓝 (H τ), H (ψ w) = w := hH.hasStrictDerivAt.eventually_right_inverse ..
  have hψd : deriv ψ (H τ) = 1 := by
    rw [(hH.hasStrictDerivAt.to_localInverse (hf' := hne)).hasDerivAt.deriv, hH1, inv_one]
  rw [hH0] at hψa hψ0 hright hψd
  refine ⟨ψ, κ, hκv, hκ, hψa, hψ0, hψd, ?_, ?_⟩
  swap
  · obtain ⟨s, hs, hsub⟩ := Filter.eventually_iff_exists_mem.mp hright
    exact ⟨s, hs, fun u hu v hv huv => by rw [← hsub u hu, ← hsub v hv, huv]⟩
  have hmem : ∀ᶠ w in 𝓝 (0 : ℂ), f (ψ w) - c = κ * H (ψ w) ^ 2 :=
    (hψ0 ▸ hψa.continuousAt : Filter.Tendsto ψ (𝓝 0) (𝓝 τ)).eventually hHeq
  filter_upwards [hmem, hright] with w hw hrw
  rw [hrw] at hw
  linear_combination hw


/-! ### Axiom footprint -/

/-- info: 'Shields.exists_morse_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_morse_inverse

end Shields
