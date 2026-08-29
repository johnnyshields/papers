/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperOneBinders
import ForgacsTran.PencilIndex

/-!
# The `r = 1` upper endpoint at a numerator of any order

`EndpointUpperOneBinders.eventually_le_ftPrincipalAmp_of_rootMultiplicity_le_one`
proves the amplitude floor at `ord_{t_b}(B) ≤ 1` and says, correctly, that at
`ord ≥ 2` its conclusion is **false** — the amplitude vanishes at the collision and
no constant floor holds.  That restriction then rode all the way up to
`ft_weighted_dominance_one` and `ft_weighted_dominance_rho_one`, which is a
hypothesis the manuscript does not carry: `lem:amplitude-divisor` gives
`p = ν - (k-1)` at **every** `ν`, and `k = 2` at the finite upper endpoint of an
`r = 1` arc.  This module removes it.

**What was missing was a lower bound on the splitting, and it is not the
splitting rate.**  `|W| = |t_+| · d^{ν-1} · |B_1(t_+)|/|E_1(t_+)|` with
`d = |t_+ - t_b|`, so the floor at `ν ≥ 2` needs `d` bounded **below** linearly in
`η`.  A two-sided rate `d ≍ η` would need the local geometry of the double root;
one side needs nothing of the kind.  **`t_b` is real and `t_+` is not**: the
principal point is `τ e^{iθ}`, its imaginary part is `τ sin θ`, and a real point
is at least that far from it.  At `θ = π - η` that is `τ(π-η) sin η`, which is
linear in `η` because `τ → L > 0`.

So the ingredient is `|Im t_+| ≤ ‖t_+ - t_b‖`, which holds for **any** real `t_b`,
and `2η/π ≤ sin η` on `[0, π/2]`.  Nothing about the pencil enters.

## Main statements

* `eventually_linear_separation_endpoint_pi` — the principal point stays linearly
  clear of every real point at the `π` endpoint.
* `eventually_le_ftPrincipalAmp_of_rootMultiplicity` — the floor
  `A η^{ν-1} ≤ |W|` at every `ν`, from that separation.
* `ftPrincipalAmp_floor_of_endpoint_pi_any_multiplicity` — the same at the
  Forgács–Tran branch, with every hypothesis but the admissible class discharged.

**The exponent is `ν - 1` in `ℕ`, and the truncation is the mathematics rather
than an accident.**  At `ν = 0` the amplitude *diverges* and at `ν = 1` it tends
to a positive constant, so a constant floor — `η^0` — is what holds in both, and
`0 - 1 = 0` delivers exactly that.  Checked at both boundary values in
`../scripts/check_upper_endpoint_multiplicity.py`, not reasoned from the formula.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`,
`thm:weighted-dominance`, `lem:amplitude-divisor`, `eq:W-endpoint-form`,
`eq:W-on-g`.

## Tags

weighted dominance, upper endpoint, amplitude floor, numerator multiplicity
-/

namespace ForgacsTran

open Real Set Filter Polynomial Complex
open scoped Topology

/-! ### The principal point is linearly clear of the real axis -/

/-- **A real point is at least `|Im t_+|` away, and that is linear in `η`.**
The principal point is `τ(θ)e^{iθ}`, so its imaginary part is `τ(θ) sin θ`; at
`θ = π - η` that is `τ(π-η) sin η`, and `τ → L > 0`.  Every real `t_b` is at
least that far from it.

**This is one side of the splitting and it is the side the floor needs.**  The
two-sided rate `‖t_+ - t_b‖ ≍ η` is a statement about the local geometry of the
double root; the lower bound is a statement about the imaginary axis, and the
pencil does not enter it at all — `t_b` is an arbitrary real number here, not the
collision point. -/
theorem eventually_linear_separation_endpoint_pi {τ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hτ : Tendsto (fun η : ℝ => τ (π - η)) (𝓝[>] (0 : ℝ)) (𝓝 L)) (tb : ℝ) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ),
      L / π * η ≤ ‖ftPrincipal τ (π - η) - ((tb : ℝ) : ℂ)‖ := by
  have hhalf : ∀ᶠ η in 𝓝[>] (0 : ℝ), L / 2 ≤ τ (π - η) :=
    hτ.eventually_const_le (by linarith)
  have hsmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ≤ π / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < π / 2)] with η hη
    exact hη.2.le
  filter_upwards [hhalf, hsmall, self_mem_nhdsWithin] with η h1 h2 h3
  have hη0 : (0 : ℝ) < η := h3
  have him : (ftPrincipal τ (π - η) - ((tb : ℝ) : ℂ)).im
      = τ (π - η) * Real.sin η := by
    rw [ftPrincipal, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, Complex.ofReal_im,
      Real.sin_pi_sub]
    ring
  have hsin : 2 / π * η ≤ Real.sin η := Real.mul_le_sin hη0.le h2
  have hτpos : (0 : ℝ) < τ (π - η) := by linarith
  have hkey : L / π * η ≤ τ (π - η) * Real.sin η := by
    have h2π : (0 : ℝ) < π := pi_pos
    have hnn : (0 : ℝ) ≤ 2 / π * η := by positivity
    have : L / 2 * (2 / π * η) ≤ τ (π - η) * Real.sin η :=
      mul_le_mul h1 hsin hnn hτpos.le
    calc L / π * η = L / 2 * (2 / π * η) := by field_simp
      _ ≤ τ (π - η) * Real.sin η := this
  calc L / π * η ≤ τ (π - η) * Real.sin η := hkey
    _ = |(ftPrincipal τ (π - η) - ((tb : ℝ) : ℂ)).im| := by
        rw [him, abs_of_nonneg (mul_nonneg hτpos.le (Real.sin_nonneg_of_nonneg_of_le_pi
          hη0.le (by linarith [pi_pos])))]
    _ ≤ ‖ftPrincipal τ (π - η) - ((tb : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _

/-! ### The floor at every numerator order -/

/-- **`eq:W-endpoint-form`'s floor at the upper collision, at every order of
vanishing.**  `eq:W-on-g` writes the amplitude as `-tB(t)/E(t)` with `E = XQ' - rQ`
carrying no `z`, so with `ord_{t_b}(E) = 1` and `ord_{t_b}(B) = m`,

  `|W| = |t_+| · d^{m-1} · |B_1(t_+)|/|E_1(t_+)|`,   `d = |t_+ - t_b|`,

and the second factor tends to a positive limit.  What decides the floor is `d`,
and the only thing asked of it is that it not collapse faster than `η`.

**`m - 1` is truncated subtraction, and both boundary values are the mathematics
rather than a coincidence.**  At `m = 0` the amplitude *diverges* and at `m = 1` it
tends to a positive constant, so `η^0` — a constant floor — is what holds in both,
and that is what `0 - 1 = 0` and `1 - 1 = 0` deliver.  The truncation is checked at
those two values rather than inferred from the closed form; § the module header.

`hsep` is what `eventually_le_ftPrincipalAmp_of_rootMultiplicity_le_one` avoided
needing, and it is why that theorem stopped at `m ≤ 1`: below that order the factor
`d^{m-1}` is bounded below by `d ≤ 1` alone and no rate is used.  At `m ≥ 2` it is
not, and the missing statement was never the two-sided splitting rate — only this
one side. -/
theorem eventually_le_ftPrincipalAmp_of_rootMultiplicity
    {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {b : ℝ} {z τ : ℝ → ℝ} {tb : ℂ} {κ : ℝ}
    (hB0 : B ≠ 0) (hE0 : ftCritical Q r ≠ 0) (htb : tb ≠ 0)
    (hEmult : (ftCritical Q r).rootMultiplicity tb = 1)
    (hκ : 0 < κ)
    (hsep : ∀ᶠ η in 𝓝[>] (0 : ℝ), κ * η ≤ ‖ftPrincipal τ (b - η) - tb‖)
    (hγ : Tendsto (fun η : ℝ => ftPrincipal τ (b - η)) (𝓝[>] (0 : ℝ)) (𝓝 tb))
    (hpne : ∀ᶠ η in 𝓝[>] (0 : ℝ), ftPrincipal τ (b - η) ≠ 0)
    (hroot : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftDen Q r ((z (b - η) : ℝ) : ℂ)).eval (ftPrincipal τ (b - η)) = 0)
    (hEne : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftCritical Q r).eval (ftPrincipal τ (b - η)) ≠ 0) :
    ∃ A > (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ),
      A * η ^ (B.rootMultiplicity tb - 1) ≤ ftPrincipalAmp Q B r z τ (b - η) := by
  classical
  set E : Polynomial ℂ := ftCritical Q r with hEdef
  set m : ℕ := B.rootMultiplicity tb with hmdef
  set B₁ : Polynomial ℂ := B /ₘ (X - C tb) ^ m with hB₁def
  set E₁ : Polynomial ℂ := E /ₘ (X - C tb) ^ E.rootMultiplicity tb with hE₁def
  have hB₁ne : B₁.eval tb ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero tb hB0
  have hE₁ne : E₁.eval tb ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero tb hE0
  have hBfac : ∀ t : ℂ, B.eval t = (t - tb) ^ m * B₁.eval t := by
    intro t
    conv_lhs => rw [← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq B tb]
    simp [hB₁def, hmdef]
  have hEfac : ∀ t : ℂ, E.eval t = (t - tb) * E₁.eval t := by
    intro t
    conv_lhs => rw [← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq E tb]
    simp [hE₁def, hEmult]
  set Lm : ℝ := ‖tb‖ * ‖B₁.eval tb‖ / ‖E₁.eval tb‖ with hLmdef
  have hLm : 0 < Lm := by
    refine div_pos (mul_pos ?_ ?_) ?_ <;> simp [norm_pos_iff, htb, hB₁ne, hE₁ne]
  have hcont : Tendsto (fun η : ℝ =>
      ‖ftPrincipal τ (b - η)‖ * ‖B₁.eval (ftPrincipal τ (b - η))‖
        / ‖E₁.eval (ftPrincipal τ (b - η))‖) (𝓝[>] (0 : ℝ)) (𝓝 Lm) :=
    ((hγ.norm).mul (((B₁.continuous.tendsto tb).comp hγ).norm)).div
      (((E₁.continuous.tendsto tb).comp hγ).norm) (by simpa using hE₁ne)
  refine ⟨Lm / 2 * κ ^ (m - 1), by positivity, ?_⟩
  filter_upwards [hpne, hroot, hEne, hsep, self_mem_nhdsWithin,
    Metric.tendsto_nhds.mp hγ 1 one_pos,
    Metric.tendsto_nhds.mp hcont (Lm / 2) (by linarith)] with η hp0 hr0 hE hsp hη0 hd hL
  set t : ℂ := ftPrincipal τ (b - η) with htdef
  have hηpos : (0 : ℝ) < η := hη0
  have htne : t - tb ≠ 0 := by
    intro h0
    refine hE ?_
    rw [sub_eq_zero.1 h0, hEfac tb]
    simp
  have hd1 : ‖t - tb‖ ≤ 1 := by rw [← Complex.dist_eq]; exact hd.le
  have hdpos : 0 < ‖t - tb‖ := norm_pos_iff.2 htne
  have hE₁t : E₁.eval t ≠ 0 := fun h0 => hE (by rw [hEfac, h0, mul_zero])
  have hE₁pos : 0 < ‖E₁.eval t‖ := norm_pos_iff.2 hE₁t
  have hamp : ftPrincipalAmp Q B r z τ (b - η)
      = ‖t‖ * (‖t - tb‖ ^ m * ‖B₁.eval t‖) / (‖t - tb‖ * ‖E₁.eval t‖) := by
    rw [ftPrincipalAmp, ftAmp_eq_ftCritical hr hp0 hr0, norm_div, norm_neg, norm_mul,
      ← hEdef, hEfac, hBfac, norm_mul, norm_mul, norm_pow]
  have hL' : Lm / 2 < ‖t‖ * ‖B₁.eval t‖ / ‖E₁.eval t‖ := by
    rw [Real.dist_eq, abs_lt] at hL
    linarith [hL.1]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  -- `m = 0`: the amplitude DIVERGES, and `d <= 1` alone carries the constant floor
  · rw [hamp, hm0]
    simp only [Nat.zero_sub, pow_zero, one_mul, mul_one]
    have hkey : ‖t‖ * ‖B₁.eval t‖ / ‖E₁.eval t‖
        ≤ ‖t‖ * ‖B₁.eval t‖ / (‖t - tb‖ * ‖E₁.eval t‖) := by
      rw [div_le_div_iff₀ hE₁pos (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hd1
        (by positivity : (0 : ℝ) ≤ ‖t‖ * ‖B₁.eval t‖ * ‖E₁.eval t‖)]
    linarith
  -- `m >= 1`: the surviving factor is `d^{m-1}`, and `d >= kappa*eta` is what bounds it
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hmk : m - 1 = k := by omega
    have hsplit : ‖t‖ * (‖t - tb‖ ^ m * ‖B₁.eval t‖) / (‖t - tb‖ * ‖E₁.eval t‖)
        = (‖t‖ * ‖B₁.eval t‖ / ‖E₁.eval t‖) * ‖t - tb‖ ^ k := by
      rw [hk, pow_succ]
      field_simp
    have hpow : (κ * η) ^ k ≤ ‖t - tb‖ ^ k :=
      pow_le_pow_left₀ (by positivity) hsp k
    rw [hamp, hmk, hsplit]
    calc Lm / 2 * κ ^ k * η ^ k = Lm / 2 * (κ * η) ^ k := by rw [mul_pow]; ring
      _ ≤ (‖t‖ * ‖B₁.eval t‖ / ‖E₁.eval t‖) * ‖t - tb‖ ^ k := by
          exact mul_le_mul hL'.le hpow (by positivity) (by positivity)

/-! ### The floor at the Forgács–Tran branch -/

/-- **`hamp₁` at the branch, at every order of vanishing at the collision.**  The
drop-in replacement for
`EndpointUpperOneBinders.ftPrincipalAmp_floor_of_endpoint_pi_of_multiplicity`, with
`ord_{-L}(B) ≤ 1` dropped and the exponent the paper's own `p_1 = ν - (k-1)` at
`k = 2`.

**`B(-L) ≠ 0` is not asked either.**  A numerator vanishing at the collision to any
order is admissible, which is `lem:amplitude-divisor` verbatim; `B ≠ 0` is all that
is needed, since it is what makes the cofactor `B_1` nonvanishing there. -/
theorem ftPrincipalAmp_floor_of_endpoint_pi_any_multiplicity {n : ℕ} {a : Fin n → ℝ}
    {c x₁ : ℝ} {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hτ : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L))
    (hz : Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[<] π)
      (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L))))
    (hB0 : B ≠ 0) :
    ∃ A₁ > (0 : ℝ), ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ (B.rootMultiplicity ((-L : ℝ) : ℂ) - 1)
        ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 (n - 1))
          (ftTauArc a 1 (n - 1) x₁) (π - η) := by
  obtain ⟨hγ, -, hbr⟩ := branch_data_endpoint_pi (x₁ := x₁) hn2 ha hc hτ hz
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hE0 : ftCritical (ftRootPoly c a) 1 ≠ 0 := by
    intro h0
    exact eval_ftCritical_zero_ne_zero le_rfl hQ0 (by rw [h0]; simp)
  have hEne : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftCritical (ftRootPoly c a) 1).eval
        (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - η)) ≠ 0 := by
    filter_upwards [hbr] with η h h0
    refine h.2.2 ?_
    rw [eval_derivative_ftDen_eq_ftCritical_div le_rfl h.1 h.2.1, h0, zero_div]
  -- the arc's radius runs into `L`, which is what makes the separation linear
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  have harc : ∀ᶠ η in 𝓝[>] (0 : ℝ), π - η ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT pi_pos] with η hηπ
    rw [hcast]
    exact ⟨by linarith [hηπ.2], by linarith [hηπ.1]⟩
  have hTArc : Tendsto (fun η : ℝ => ftTauArc a 1 (n - 1) x₁ (π - η))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    refine (hτ.comp tendsto_sub_nhdsGT_zero_nhdsLT).congr' ?_
    filter_upwards [harc] with η hη
    exact (ftTauArc_agree a 1 (n - 1) x₁ hη.1 hη.2).symm
  obtain ⟨A₁, hA₁, hev⟩ := eventually_le_ftPrincipalAmp_of_rootMultiplicity
    (Q := ftRootPoly c a) (B := B) (r := 1) (b := π)
    (z := ftBranchZ a c 1 (n - 1)) (τ := ftTauArc a 1 (n - 1) x₁) (κ := L / π)
    le_rfl hB0 hE0 (by exact_mod_cast (by linarith : (-L : ℝ) ≠ 0))
    (rootMultiplicity_ftCritical_endpoint_pi_eq_one hn2 ha hc hL hE)
    (by positivity) (eventually_linear_separation_endpoint_pi hL hTArc (-L)) hγ
    (hbr.mono fun η h => h.1) (hbr.mono fun η h => h.2.1) hEne
  obtain ⟨e, he, hwin⟩ := window_of_eventually hev
  exact ⟨A₁, hA₁, e, he, fun η hη hηe => hwin η hη hηe⟩

end ForgacsTran
