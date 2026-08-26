/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Scaling

/-!
# The three-term digamma sandwich

`shields-2026-turan-bessel.tex`, `sec:scaling`: the primitive that
`eq:Sm-asymptotic` and every gamma-ratio expansion in `lem:central-moments` run
on.  DLMF §5.11(i) states it as an asymptotic series; what is proved here is the
two-sided form with an explicit remainder,

```
  0 ≤ ψ(x) - log x + 1/(2x) + 1/(12x²) ≤ 1/(60x³)      (x > 0).
```

Mathlib carries no digamma or log-gamma asymptotic expansion, but it does not
have to: `Scaling.abs_trigamma_sub_cubic_le` sandwiches `ψ₁` to order `x⁻⁴`, and
`ψ' = ψ₁` (`ParameterCalculus.deriv_realDigamma_eq_trigamma`) turns that into a
sign condition on the derivative of the gap.  The gap is then antitone, the gap
minus `1/(60x³)` is monotone, and both are pinned at infinity by
`ψ(1+k) = -γ + H_k` against Mathlib's `H_k - log k → γ`.  So the constant of
integration is identified rather than assumed, which is the step an asymptotic
series states without proof.

Sorry-free.
-/

namespace TuranBessel

open Filter Topology

variable {x : ℝ}

/-- `ψ(x) - log x + 1/(2x) + 1/(12x²)`, the gap between `ψ` and its three-term
asymptotic form. -/
noncomputable def digammaGap (x : ℝ) : ℝ :=
  realDigamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2)

/-- `ψ` is differentiable with derivative `ψ₁`. -/
theorem hasDerivAt_realDigamma_trigamma (hx : 0 < x) :
    HasDerivAt realDigamma (trigamma x) x :=
  (hasDerivAt_realDigamma' hx).congr_deriv (deriv_realDigamma_eq_trigamma hx)

theorem hasDerivAt_digammaGap (hx : 0 < x) :
    HasDerivAt digammaGap
      (trigamma x - (1 / x + 1 / (2 * x ^ 2) + 1 / (6 * x ^ 3))) x := by
  have hxne : x ≠ 0 := hx.ne'
  have h1 : HasDerivAt realDigamma (trigamma x) x := hasDerivAt_realDigamma_trigamma hx
  have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hxne
  have h3 : HasDerivAt (fun t : ℝ => 1 / (2 * t)) (-(1 / (2 * x ^ 2))) x := by
    have hg : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h2x : (2 : ℝ) * x ≠ 0 := by positivity
    have := (hasDerivAt_const x (1 : ℝ)).div hg h2x
    refine this.congr_deriv ?_
    field
  have h4 : HasDerivAt (fun t : ℝ => 1 / (12 * t ^ 2)) (-(1 / (6 * x ^ 3))) x := by
    have hg : HasDerivAt (fun t : ℝ => 12 * t ^ 2) (24 * x) x := by
      have := (hasDerivAt_pow 2 x).const_mul (12 : ℝ)
      refine this.congr_deriv ?_
      push_cast
      ring
    have h12 : (12 : ℝ) * x ^ 2 ≠ 0 := by positivity
    have := (hasDerivAt_const x (1 : ℝ)).div hg h12
    refine this.congr_deriv ?_
    field
  have := ((h1.sub h2).add h3).add h4
  refine this.congr_deriv ?_
  rw [one_div x]
  ring

theorem deriv_digammaGap (hx : 0 < x) :
    deriv digammaGap x = trigamma x - (1 / x + 1 / (2 * x ^ 2) + 1 / (6 * x ^ 3)) :=
  (hasDerivAt_digammaGap hx).deriv

theorem digammaGap_deriv_nonpos (hx : 0 < x) : deriv digammaGap x ≤ 0 := by
  have h := trigamma_le_cubicMaj hx
  rw [cubicMaj] at h
  rw [deriv_digammaGap hx]
  linarith

theorem digammaGap_deriv_ge (hx : 0 < x) : -(1 / (20 * x ^ 4)) ≤ deriv digammaGap x := by
  have h := cubicMin_le_trigamma hx
  rw [cubicMin] at h
  rw [deriv_digammaGap hx]
  linarith

theorem differentiableOn_digammaGap : DifferentiableOn ℝ digammaGap (Set.Ioi (0 : ℝ)) :=
  fun _y hy => ((hasDerivAt_digammaGap (Set.mem_Ioi.1 hy)).differentiableAt).differentiableWithinAt

theorem continuousOn_digammaGap : ContinuousOn digammaGap (Set.Ioi (0 : ℝ)) :=
  fun _y hy =>
    ((hasDerivAt_digammaGap (Set.mem_Ioi.1 hy)).differentiableAt).continuousAt.continuousWithinAt

theorem digammaGap_antitoneOn : AntitoneOn digammaGap (Set.Ioi (0 : ℝ)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) continuousOn_digammaGap ?_ ?_
  · rw [interior_Ioi]; exact differentiableOn_digammaGap
  · intro y hy
    rw [interior_Ioi] at hy
    exact digammaGap_deriv_nonpos (Set.mem_Ioi.1 hy)

/-- The gap with the remainder subtracted; monotone rather than antitone. -/
noncomputable def digammaGap' (x : ℝ) : ℝ := digammaGap x - 1 / (60 * x ^ 3)

theorem hasDerivAt_digammaGap' (hx : 0 < x) :
    HasDerivAt digammaGap'
      (trigamma x - (1 / x + 1 / (2 * x ^ 2) + 1 / (6 * x ^ 3)) + 1 / (20 * x ^ 4)) x := by
  have h1 := hasDerivAt_digammaGap hx
  have hg : HasDerivAt (fun t : ℝ => 60 * t ^ 3) (180 * x ^ 2) x := by
    have := (hasDerivAt_pow 3 x).const_mul (60 : ℝ)
    refine this.congr_deriv ?_
    push_cast
    ring
  have h60 : (60 : ℝ) * x ^ 3 ≠ 0 := by positivity
  have h2 : HasDerivAt (fun t : ℝ => 1 / (60 * t ^ 3)) (-(1 / (20 * x ^ 4))) x := by
    have := (hasDerivAt_const x (1 : ℝ)).div hg h60
    refine this.congr_deriv ?_
    field
  have := h1.sub h2
  refine this.congr_deriv ?_
  ring

theorem digammaGap'_monotoneOn : MonotoneOn digammaGap' (Set.Ioi (0 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun _y hy =>
      ((hasDerivAt_digammaGap' (Set.mem_Ioi.1 hy)).differentiableAt).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun _y hy =>
      ((hasDerivAt_digammaGap' (Set.mem_Ioi.1 hy)).differentiableAt).differentiableWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    have hy' : (0 : ℝ) < y := Set.mem_Ioi.1 hy
    rw [(hasDerivAt_digammaGap' hy').deriv]
    have h := cubicMin_le_trigamma hy'
    rw [cubicMin] at h
    linarith

/-! ### Pinning the constant at infinity -/

/-- `ψ(1+k) = -γ + H_k`, the recurrence run from `ψ(1) = -γ`. -/
theorem realDigamma_one_add_nat (k : ℕ) :
    realDigamma (1 + (k : ℝ)) = -Real.eulerMascheroniConstant + (harmonic k : ℝ) := by
  rw [realDigamma_add_nat one_pos k, realDigamma_one]
  congr 1
  rw [harmonic, Rat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [one_div]
  congr 1
  ring

private theorem tendsto_one_add_cast : Tendsto (fun k : ℕ => 1 + (k : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
  linarith

private theorem tendsto_one_add_cast_pow (p : ℕ) (hp : 1 ≤ p) :
    Tendsto (fun k : ℕ => (1 + (k : ℝ)) ^ p) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_one_add_cast
  have h1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  calc (1 : ℝ) + (k : ℝ) = (1 + (k : ℝ)) ^ 1 := by ring
    _ ≤ (1 + (k : ℝ)) ^ p := pow_le_pow_right₀ h1 hp

private theorem tendsto_inv_pow (c : ℝ) (hc : 0 < c) (p : ℕ) (hp : 1 ≤ p) :
    Tendsto (fun k : ℕ => 1 / (c * (1 + (k : ℝ)) ^ p)) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds ((tendsto_one_add_cast_pow p hp).const_mul_atTop hc)

theorem tendsto_digammaGap_atTop :
    Tendsto (fun k : ℕ => digammaGap (1 + (k : ℝ))) atTop (𝓝 0) := by
  have hharm : Tendsto (fun k : ℕ => (harmonic k : ℝ) - Real.log (k : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hlog : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ => 1 / (2 * (1 + (k : ℝ)))) atTop (𝓝 0) := by
    have := tendsto_inv_pow 2 (by norm_num) 1 le_rfl
    simpa using this
  have hinv2 : Tendsto (fun k : ℕ => 1 / (12 * (1 + (k : ℝ)) ^ 2)) atTop (𝓝 0) :=
    tendsto_inv_pow 12 (by norm_num) 2 (by norm_num)
  have hcomb : Tendsto (fun k : ℕ =>
      ((harmonic k : ℝ) - Real.log (k : ℝ)) - Real.eulerMascheroniConstant
        - (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ))
        + 1 / (2 * (1 + (k : ℝ))) + 1 / (12 * (1 + (k : ℝ)) ^ 2)) atTop (𝓝 0) := by
    have := ((hharm.sub_const Real.eulerMascheroniConstant).sub hlog).add hinv
    have h2 := this.add hinv2
    simpa using h2
  refine hcomb.congr fun k => ?_
  rw [digammaGap, realDigamma_one_add_nat k,
    show (1 : ℝ) + (k : ℝ) = (k : ℝ) + 1 from by ring]
  ring

theorem digammaGap_nonneg (hx : 0 < x) : 0 ≤ digammaGap x := by
  refine le_of_tendsto tendsto_digammaGap_atTop ?_
  filter_upwards [eventually_ge_atTop ⌈x⌉₊] with k hk
  have hkx : x ≤ 1 + (k : ℝ) := by
    have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have h2 : ((⌈x⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
    linarith
  exact digammaGap_antitoneOn (Set.mem_Ioi.2 hx)
    (Set.mem_Ioi.2 (by linarith : (0:ℝ) < 1 + (k : ℝ))) hkx

theorem digammaGap_le (hx : 0 < x) : digammaGap x ≤ 1 / (60 * x ^ 3) := by
  have htend : Tendsto (fun k : ℕ => digammaGap' (1 + (k : ℝ))) atTop (𝓝 0) := by
    have hr : Tendsto (fun k : ℕ => 1 / (60 * (1 + (k : ℝ)) ^ 3)) atTop (𝓝 0) :=
      tendsto_inv_pow 60 (by norm_num) 3 (by norm_num)
    have := tendsto_digammaGap_atTop.sub hr
    simpa [digammaGap'] using this
  have hle : digammaGap' x ≤ 0 := by
    refine ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop ⌈x⌉₊] with k hk
    have hkx : x ≤ 1 + (k : ℝ) := by
      have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      have h2 : ((⌈x⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
      linarith
    exact digammaGap'_monotoneOn (Set.mem_Ioi.2 hx)
      (Set.mem_Ioi.2 (by linarith : (0:ℝ) < 1 + (k : ℝ))) hkx
  rw [digammaGap'] at hle
  linarith

/-- **The three-term digamma sandwich** (DLMF §5.11(i) with an explicit
remainder): `0 ≤ ψ(x) - log x + 1/(2x) + 1/(12x²) ≤ 1/(60x³)` for every `x > 0`. -/
theorem digamma_sandwich (hx : 0 < x) :
    0 ≤ realDigamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2)
      ∧ realDigamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) ≤ 1 / (60 * x ^ 3) := by
  have h1 := digammaGap_nonneg hx
  have h2 := digammaGap_le hx
  rw [digammaGap] at h1 h2
  exact ⟨h1, h2⟩

/-- The sandwich in absolute-value form: `|ψ(x) - log x + 1/(2x) + 1/(12x²)| ≤ 1/(60x³)`. -/
theorem abs_digamma_sub_three_term_le (hx : 0 < x) :
    |realDigamma x - (Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2))| ≤ 1 / (60 * x ^ 3) := by
  obtain ⟨h1, h2⟩ := digamma_sandwich hx
  rw [abs_le]
  constructor <;> [linarith; linarith]

end TuranBessel
