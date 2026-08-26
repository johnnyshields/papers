/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Amplitude

/-!
# Global and local zero laws

The three results of `sec:consequences` all consume the angular discrepancy
`eq:angular-discrepancy` of `prop:angular-discrepancy` (`sec:dominance`), which
is not formalized anywhere in this tree; each theorem below therefore takes the
discrepancy bound it uses as an explicit numeric hypothesis, and what is proved
is the derivation the paper's own proofs carry out.

## Main statements

* `equidistribution_of_angular_discrepancy` — `eq:normalized-angular-discrepancy`.
* `angular_rigidity`, `angular_clock` — `eq:angular-clock`.
* `local_clock_spacing` — `eq:local-strong-clock`, the two-term law, with the
  `ψ'` correction earning the `M^{-3}` residual.
* `numerator_clock_correction` — `eq:numerator-clock-correction`, the `ψ'`
  split into a numerator term and a term with no `B` in it.
* `norm_le_of_mul_eq` — the change of variable of `eq:C1-interior-remainder`,
  where `du/dθ ≍ M` absorbs the `M` prefactor.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:zero-bulk`, `subsec:strong-clock`,
`prop:equidistribution`, `cor:angular-rigidity`, `prop:local-strong-clock`).

## Tags

zero distribution, clock spacing, local zero law, equidistribution
-/

namespace ForgacsTran

open Polynomial Real

/-! ### `subsec:zero-bulk` — normalization and the angular clock -/

/-- **`eq:normalized-angular-discrepancy`.**  Dividing the angular discrepancy
`eq:angular-discrepancy` by `deg P_m = ⌊M/r⌋` costs one unit: writing
`M = r d + s` with `0 ≤ s < r`, the reindexing error
`((M+1)/d - r)(β-α)/π = (s+1)(β-α)/(dπ)` is at most `1/d` because
`β - α ≤ π/r` and `s + 1 ≤ r`. -/
theorem equidistribution_of_angular_discrepancy {Z : ℝ} {M r d s : ℕ} {α β C : ℝ}
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : M = r * d + s) (hs : s < r)
    (hab : 0 ≤ β - α) (hab' : β - α ≤ π / r)
    (hdisc : |Z - ((M : ℝ) + 1) * (β - α) / π| ≤ C) :
    |Z / (d : ℝ) - (r : ℝ) * (β - α) / π| ≤ (C + 1) / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hMr : ((M : ℝ) + 1) = (r : ℝ) * d + ((s : ℝ) + 1) := by
    rw [hM]; push_cast; ring
  -- the reindexing term
  have hreidx : ((s : ℝ) + 1) * (β - α) / π ≤ 1 := by
    have h1 : ((s : ℝ) + 1) ≤ (r : ℝ) := by exact_mod_cast hs
    have h2 : (β - α) / π ≤ 1 / r := by
      rw [div_le_div_iff₀ pi_pos hr0]
      calc (β - α) * r ≤ (π / r) * r := by
            exact mul_le_mul_of_nonneg_right hab' hr0.le
        _ = π := by field_simp
        _ = 1 * π := (one_mul _).symm
    calc ((s : ℝ) + 1) * (β - α) / π = ((s : ℝ) + 1) * ((β - α) / π) := by ring
      _ ≤ (r : ℝ) * (1 / r) := by
          refine mul_le_mul h1 h2 (by positivity) hr0.le
      _ = 1 := by field_simp
  have hsplit : Z / (d : ℝ) - (r : ℝ) * (β - α) / π
      = (Z - ((M : ℝ) + 1) * (β - α) / π) / d + ((s : ℝ) + 1) * (β - α) / π / d := by
    rw [hMr]; field_simp; ring
  rw [hsplit]
  have h1 : |(Z - ((M : ℝ) + 1) * (β - α) / π) / d| ≤ C / d := by
    rw [abs_div, abs_of_pos hd0]
    exact div_le_div_of_nonneg_right hdisc hd0.le
  have h2 : |((s : ℝ) + 1) * (β - α) / π / d| ≤ 1 / d := by
    rw [abs_div, abs_of_pos hd0]
    refine div_le_div_of_nonneg_right ?_ hd0.le
    rw [abs_of_nonneg (by positivity)]
    exact hreidx
  calc |(Z - ((M : ℝ) + 1) * (β - α) / π) / d + ((s : ℝ) + 1) * (β - α) / π / d|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ C / d + 1 / d := add_le_add h1 h2
    _ = (C + 1) / d := by ring

/-- **`cor:angular-rigidity`, the index localization.**  If the counts of zeros
strictly below and at most at the angle `θ` both sit within `Δ` of the nominal
`Lθ/π`, then so does every index belonging to that zero.  Two-sided hypotheses
give `Δ` outright; the paper's `Δ + 1` in `eq:angular-clock` is slack. -/
theorem angular_rigidity {jm jp j : ℕ} {θ Δ L : ℝ}
    (hjm : |(jm : ℝ) - L * θ / π| ≤ Δ) (hjp : |(jp : ℝ) - L * θ / π| ≤ Δ)
    (h1 : jm < j) (h2 : j ≤ jp) :
    |(j : ℝ) - L * θ / π| ≤ Δ := by
  have hjm' : ((jm : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast h1
  have hjp' : (j : ℝ) ≤ (jp : ℝ) := by exact_mod_cast h2
  rw [abs_le] at hjm hjp ⊢
  constructor
  · linarith [hjm.1]
  · linarith [hjp.2]

/-- **`eq:angular-clock`.**  The index bound rearranged into the angular one:
every bulk-zero angle sits within `π(Δ+1)/L` of the uniform clock `πj/L`. -/
theorem angular_clock {j : ℕ} {θ Δ L : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ)
    (h : |(j : ℝ) - L * θ / π| ≤ Δ) :
    |θ - π * (j : ℝ) / L| ≤ π * (Δ + 1) / L := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hrw : θ - π * (j : ℝ) / L = -(π / L) * ((j : ℝ) - L * θ / π) := by
    field_simp; ring
  rw [hrw, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < π / L)]
  calc π / L * |(j : ℝ) - L * θ / π| ≤ π / L * Δ :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ π * (Δ + 1) / L := by
        rw [div_mul_eq_mul_div, mul_comm π Δ]
        refine div_le_div_of_nonneg_right ?_ hL.le
        nlinarith [hπ]


/-! ### `subsec:strong-clock` — the local strong-clock law -/

/-- **`eq:C1-interior-remainder`, the change of variable.**  The `C^1` bound on
the remainder carries a factor `M`, and `du/dθ ≍ M`; the chain rule divides one
by the other, so in the `u` coordinate the derivative bound is `O(σ^M)` with no
`M` left.  This is the step the paper flags as "exactly absorbed". -/
theorem norm_le_of_mul_eq {dR du dε C c σ : ℝ} {M : ℕ} (hM : 1 ≤ M) (hc : 0 < c)
    (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hR : |dR| ≤ C * (M : ℝ) * σ ^ M)
    (hu : c * (M : ℝ) ≤ |du|) (hchain : dε * du = dR) :
    |dε| ≤ (C / c) * σ ^ M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hdu : 0 < |du| := lt_of_lt_of_le (by positivity) hu
  have h1 : |dε| * |du| ≤ C * (M : ℝ) * σ ^ M := by rw [← abs_mul, hchain]; exact hR
  have h2 : |dε| * (c * (M : ℝ)) ≤ C * (M : ℝ) * σ ^ M :=
    le_trans (mul_le_mul_of_nonneg_left hu (abs_nonneg dε)) h1
  have hmc : 0 < c * (M : ℝ) := by positivity
  calc |dε| ≤ C * (M : ℝ) * σ ^ M / (c * (M : ℝ)) := (le_div_iff₀ hmc).2 h2
    _ = (C / c) * σ ^ M := by field_simp

/-- **`eq:local-strong-clock`.**  The two-term spacing law, from the phase
quantization at two consecutive zeros.  `hquant` is the difference of the two
instances of `eq:local-phase-quantization`, `hmvt` and `htaylor` are the
mean-value and first-order Taylor estimates for `ψ` that `eq:phase-derivative-bound`
and real-analyticity of `W` on a zero-free subarc supply.

Both error terms are `O(L^{-3})` once `E = O(σ^M)`: the first because
`Δ = O(L^{-1})` is derived here and squared, the second because the `ψ'`
correction has removed the `O(L^{-2})` term.  Dropping `π dψ / L^2` would leave
that term, which is the content of the paper's claim that the correction is what
buys the third order.
**Differs from the paper's route.**  The paper obtains the first-order bound `Δ_M = O(M^{-1})` from
`Φ_M' ≍ M`.  Here it is derived from the quantization identity together with the
mean-value bound on `ψ`, so `Φ_M'` is never formed; both give
`Δ ≤ (π + 2E)/(L - κ)`.
-/
theorem local_clock_spacing {L Δ dψ κ κ₂ E ek ek1 ψk ψk1 : ℝ}
    (hκ0 : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hE : 0 ≤ E) (hL : κ + 1 ≤ L) (hΔ0 : 0 < Δ)
    (hdψ : |dψ| ≤ κ) (hek : |ek| ≤ E) (hek1 : |ek1| ≤ E)
    (hquant : π + (ek1 - ek) = L * Δ - (ψk1 - ψk))
    (hmvt : |ψk1 - ψk| ≤ κ * Δ)
    (htaylor : |ψk1 - ψk - dψ * Δ| ≤ κ₂ * Δ ^ 2) :
    Δ ≤ (π + 2 * E) / (L - κ) ∧
      |Δ - π / L - π * dψ / L ^ 2|
        ≤ (2 * E + κ₂ * ((π + 2 * E) / (L - κ)) ^ 2) / (L - κ)
          + π * κ ^ 2 / (L ^ 2 * (L - κ)) := by
  have hLκ0 : (0 : ℝ) < L - κ := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨hdψ1, hdψ2⟩ := abs_le.1 hdψ
  obtain ⟨hek1a, hek1b⟩ := abs_le.1 hek
  obtain ⟨hek2a, hek2b⟩ := abs_le.1 hek1
  obtain ⟨hmvt1, hmvt2⟩ := abs_le.1 hmvt
  obtain ⟨htay1, htay2⟩ := abs_le.1 htaylor
  have hLd : (0 : ℝ) < L - dψ := by linarith
  have hfirst : Δ ≤ (π + 2 * E) / (L - κ) := by
    rw [le_div_iff₀ hLκ0]
    nlinarith
  refine ⟨hfirst, ?_⟩
  have hkey : π - (L - dψ) * Δ = -(ek1 - ek) - (ψk1 - ψk - dψ * Δ) := by
    linear_combination hquant
  have hrho : |π - (L - dψ) * Δ| ≤ 2 * E + κ₂ * Δ ^ 2 := by
    rw [hkey, abs_le]; constructor <;> linarith
  have hstep1 : |Δ - π / (L - dψ)| ≤ (2 * E + κ₂ * Δ ^ 2) / (L - κ) := by
    have hX : (0:ℝ) ≤ 2 * E + κ₂ * Δ ^ 2 := by positivity
    have hrw : Δ - π / (L - dψ) = -(π - (L - dψ) * Δ) / (L - dψ) := by
      field_simp; ring
    rw [hrw, abs_div, abs_neg, abs_of_pos hLd]
    calc |π - (L - dψ) * Δ| / (L - dψ) ≤ (2 * E + κ₂ * Δ ^ 2) / (L - dψ) :=
          div_le_div_of_nonneg_right hrho hLd.le
      _ ≤ (2 * E + κ₂ * Δ ^ 2) / (L - κ) := by
          rw [div_le_div_iff₀ hLd hLκ0]
          nlinarith [mul_nonneg hX (sub_nonneg.2 hdψ2)]
  have hstep2 : |π / (L - dψ) - (π / L + π * dψ / L ^ 2)| ≤ π * κ ^ 2 / (L ^ 2 * (L - κ)) := by
    have hrw : π / (L - dψ) - (π / L + π * dψ / L ^ 2) = π * dψ ^ 2 / (L ^ 2 * (L - dψ)) := by
      field_simp; ring
    rw [hrw, abs_div, abs_of_pos (show (0:ℝ) < L ^ 2 * (L - dψ) by positivity),
      abs_of_nonneg (show (0:ℝ) ≤ π * dψ ^ 2 by positivity)]
    have hdd : dψ ^ 2 ≤ κ ^ 2 := by
      have h2 := mul_self_le_mul_self (abs_nonneg dψ) hdψ
      rw [← sq_abs dψ]; nlinarith [h2]
    have hnum : π * dψ ^ 2 ≤ π * κ ^ 2 :=
      mul_le_mul_of_nonneg_left hdd pi_pos.le
    calc π * dψ ^ 2 / (L ^ 2 * (L - dψ)) ≤ π * κ ^ 2 / (L ^ 2 * (L - dψ)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ π * κ ^ 2 / (L ^ 2 * (L - κ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ π * κ ^ 2 by positivity)
            (show (0:ℝ) ≤ L ^ 2 by positivity)) (sub_nonneg.2 hdψ2)]
  calc |Δ - π / L - π * dψ / L ^ 2|
      = |(Δ - π / (L - dψ)) + (π / (L - dψ) - (π / L + π * dψ / L ^ 2))| := by
        congr 1; ring
    _ ≤ |Δ - π / (L - dψ)| + |π / (L - dψ) - (π / L + π * dψ / L ^ 2)| := abs_add_le _ _
    _ ≤ (2 * E + κ₂ * Δ ^ 2) / (L - κ) + π * κ ^ 2 / (L ^ 2 * (L - κ)) :=
        add_le_add hstep1 hstep2
    _ ≤ (2 * E + κ₂ * ((π + 2 * E) / (L - κ)) ^ 2) / (L - κ)
          + π * κ ^ 2 / (L ^ 2 * (L - κ)) := by
        have hsq : Δ ^ 2 ≤ ((π + 2 * E) / (L - κ)) ^ 2 := by
          have := pow_le_pow_left₀ hΔ0.le hfirst 2
          exact this
        have hnum : 2 * E + κ₂ * Δ ^ 2 ≤ 2 * E + κ₂ * ((π + 2 * E) / (L - κ)) ^ 2 := by
          nlinarith
        have := div_le_div_of_nonneg_right hnum hLκ0.le
        linarith

/-- **`eq:numerator-clock-correction`.**  Along the branch, `W_N = B_N(γ)·D` with
`D` the denominator-only factor `1/(γ^r g'(γ))` of `eq:W-on-g`.  Logarithmic
derivatives add, so `ψ_N' = Im(W_N'/W_N)` splits into the numerator term
`Im(B_N'(γ)γ'/B_N(γ))` and a term in which `B_N` does not appear — which is why
the leading clock is denominator-universal and the weight first enters at order
`M^{-2}`. -/
theorem numerator_clock_correction {B : Polynomial ℂ} {γ D : ℝ → ℂ} {γ' D' : ℂ} {θ : ℝ}
    (hγ : HasDerivAt γ γ' θ) (hD : HasDerivAt D D' θ)
    (hB0 : B.eval (γ θ) ≠ 0) (hD0 : D θ ≠ 0) :
    (deriv (fun s : ℝ => B.eval (γ s) * D s) θ / (B.eval (γ θ) * D θ)).im
      = ((B.derivative.eval (γ θ) * γ') / B.eval (γ θ)).im + (D' / D θ).im := by
  have hB : HasDerivAt (fun s : ℝ => B.eval (γ s)) (B.derivative.eval (γ θ) * γ') θ := by
    simpa [Function.comp_def, mul_comm] using (B.hasDerivAt (γ θ)).comp θ hγ
  have hW : HasDerivAt (fun s : ℝ => B.eval (γ s) * D s)
      (B.derivative.eval (γ θ) * γ' * D θ + B.eval (γ θ) * D') θ := hB.mul hD
  rw [hW.deriv, show (B.derivative.eval (γ θ) * γ' * D θ + B.eval (γ θ) * D')
      / (B.eval (γ θ) * D θ)
      = (B.derivative.eval (γ θ) * γ') / B.eval (γ θ) + D' / D θ by field_simp]
  exact Complex.add_im _ _


/-! ### `eq:local-phase-quantization` — one simple zero per half-integer phase point -/

/-- A strictly monotone function with a sign change has exactly one zero, and its
derivative there is nonzero, so the zero is simple. -/
theorem exists_unique_zero_of_deriv_pos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < f' x) (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ x ∈ Set.Ioo a b, f x = 0 ∧ ∀ y ∈ Set.Icc a b, f y = 0 → y = x := by
  have hcont : ContinuousOn f (Set.Icc a b) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) hcont ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x (Set.mem_Icc_of_Ioo hx)).deriv]
    exact hpos x (Set.mem_Icc_of_Ioo hx)
  obtain ⟨x, hx, hfx⟩ :=
    intermediate_value_Ioo hab.le hcont (Set.mem_Ioo.2 ⟨hfa, hfb⟩)
  refine ⟨x, hx, hfx, fun y hy hfy => ?_⟩
  exact hmono.injOn hy (Set.mem_Icc_of_Ioo hx) (by rw [hfx, hfy])

/-- **`eq:local-phase-quantization` and the simplicity of `eq:local-strong-clock`.**
At a phase point `u₀` — a zero of `cos`, i.e. a half-integer multiple of `π` —
the perturbed cosine `cos + ε` has exactly one zero within `δ ≤ π/4`, and it is
simple.  The two hypotheses are the paper's: `‖ε‖_∞ < sin δ` beats the value of
`cos` at the endpoints of the window, and `‖ε'‖_∞ ≤ 1/4` cannot beat
`|cos v| ≥ cos(π/4)` inside it, so the sum stays strictly monotone.
**Differs from the paper's route.**  The paper indexes the phase points as `(k+1/2)π` and splits on
the
parity of `k`.  Here the window is keyed to `cos u₀ = 0`, from which
`sin u₀ = ±1` follows, so that value carries the sign and no parity case analysis
appears.
-/
theorem exists_unique_zero_near_phase_point {e de : ℝ → ℝ} {u₀ δ : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ π / 4) (hcos : Real.cos u₀ = 0)
    (hd : ∀ v ∈ Set.Icc (u₀ - δ) (u₀ + δ), HasDerivAt e (de v) v)
    (hde : ∀ v ∈ Set.Icc (u₀ - δ) (u₀ + δ), |de v| ≤ 1 / 4)
    (he : ∀ v ∈ Set.Icc (u₀ - δ) (u₀ + δ), |e v| < Real.sin δ) :
    ∃ u ∈ Set.Ioo (u₀ - δ) (u₀ + δ), Real.cos u + e u = 0 ∧
      ∀ w ∈ Set.Icc (u₀ - δ) (u₀ + δ), Real.cos w + e w = 0 → w = u := by
  set σ : ℝ := Real.sin u₀ with hσdef
  have hσ2 : σ ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq u₀
    rw [hcos] at h; nlinarith [h]
  have hσabs : |σ| = 1 := by rw [← Real.sqrt_sq_eq_abs, hσ2, Real.sqrt_one]
  have hσne : σ ≠ 0 := by intro h; rw [h] at hσ2; norm_num at hσ2
  have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by nlinarith [pi_pos])
  have hsq2 : (0.7 : ℝ) < Real.sqrt 2 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hcosv : ∀ v : ℝ, |v| ≤ δ → Real.sqrt 2 / 2 ≤ Real.cos v := by
    intro v hv
    rw [← Real.cos_pi_div_four, ← Real.cos_abs v]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg v)
      (by nlinarith [pi_pos]) (hv.trans hδ4)
  have hgd : ∀ u ∈ Set.Icc (u₀ - δ) (u₀ + δ),
      HasDerivAt (fun u => -σ * (Real.cos u + e u)) (-σ * (-Real.sin u + de u)) u := by
    intro u hu
    exact ((Real.hasDerivAt_cos u).add (hd u hu)).const_mul (-σ)
  have hgpos : ∀ u ∈ Set.Icc (u₀ - δ) (u₀ + δ), 0 < -σ * (-Real.sin u + de u) := by
    intro u hu
    have hv : |u - u₀| ≤ δ := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsu : Real.sin u = σ * Real.cos (u - u₀) := by
      have h := Real.sin_add u₀ (u - u₀)
      rw [hcos, show u₀ + (u - u₀) = u by ring] at h
      rw [h]; ring
    have hcv : (0.7 : ℝ) < Real.cos (u - u₀) := lt_of_lt_of_le hsq2 (hcosv (u - u₀) hv)
    have hbd : |σ * de u| ≤ 1 / 4 := by
      rw [abs_mul, hσabs, one_mul]; exact hde u hu
    have hbd' := abs_le.1 hbd
    rw [hsu, show -σ * (-(σ * Real.cos (u - u₀)) + de u)
        = σ ^ 2 * Real.cos (u - u₀) - σ * de u from by ring, hσ2, one_mul]
    linarith [hbd'.2]
  have hga : -σ * (Real.cos (u₀ - δ) + e (u₀ - δ)) < 0 := by
    have hcv : Real.cos (u₀ - δ) = σ * Real.sin δ := by
      rw [Real.cos_sub, hcos]; ring
    have hmem : u₀ - δ ∈ Set.Icc (u₀ - δ) (u₀ + δ) := ⟨le_refl _, by linarith⟩
    have hbd : |σ * e (u₀ - δ)| < Real.sin δ := by
      rw [abs_mul, hσabs, one_mul]; exact he _ hmem
    have hbd' := abs_lt.1 hbd
    rw [hcv, show -σ * (σ * Real.sin δ + e (u₀ - δ))
        = -(σ ^ 2 * Real.sin δ) - σ * e (u₀ - δ) from by ring, hσ2, one_mul]
    linarith [hbd'.1]
  have hgb : 0 < -σ * (Real.cos (u₀ + δ) + e (u₀ + δ)) := by
    have hcv : Real.cos (u₀ + δ) = -(σ * Real.sin δ) := by
      rw [Real.cos_add, hcos]; ring
    have hmem : u₀ + δ ∈ Set.Icc (u₀ - δ) (u₀ + δ) := ⟨by linarith, le_refl _⟩
    have hbd : |σ * e (u₀ + δ)| < Real.sin δ := by
      rw [abs_mul, hσabs, one_mul]; exact he _ hmem
    have hbd' := abs_lt.1 hbd
    rw [hcv, show -σ * (-(σ * Real.sin δ) + e (u₀ + δ))
        = σ ^ 2 * Real.sin δ - σ * e (u₀ + δ) from by ring, hσ2, one_mul]
    linarith [hbd'.2]
  obtain ⟨x, hx, hgx, huniq⟩ :=
    exists_unique_zero_of_deriv_pos (f := fun u => -σ * (Real.cos u + e u))
      (f' := fun u => -σ * (-Real.sin u + de u)) (by linarith : u₀ - δ < u₀ + δ)
      hgd hgpos hga hgb
  refine ⟨x, hx, ?_, fun w hw hfw => ?_⟩
  · rcases mul_eq_zero.1 hgx with h | h
    · exact absurd (neg_eq_zero.1 h) hσne
    · exact h
  · exact huniq w hw (by simp [hfw])


/-! ### `eq:C1-interior-remainder` — where the `M` prefactor comes from -/

/-- **`eq:C1-interior-remainder`.**  `R_M(θ) = τ(θ)^{M+1}F(θ)` with `F = E_M ∘ z`.
Differentiating produces two terms, and only the first carries a factor of `M`:
it is `(M+1)(τ'/τ)·R_M`, so the `M` comes from differentiating `τ^{M+1}` and from
nothing else.  The second term is `τ^{M+1}∂_zE_M·z'`, bounded by the *same*
exponential through Cauchy's estimate on a fixed disk, with no `M`.

The `M` is exhibited separately in the conclusion rather than absorbed into a
constant, which is what makes `norm_le_of_mul_eq`'s absorption meaningful: the
change of variable divides by `du/dθ ≍ M` and cancels exactly this factor. -/
theorem deriv_scaled_remainder_eq {M : ℕ} {τ : ℝ → ℝ} {F : ℝ → ℂ} {θ : ℝ}
    {τ' : ℝ} {F' : ℂ}
    (hτd : HasDerivAt τ τ' θ) (hFd : HasDerivAt F F' θ) (hτpos : 0 < τ θ) :
    deriv (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F s) θ
      = (((((M : ℝ) + 1) * τ' / τ θ : ℝ)) : ℂ) * (((τ θ : ℂ)) ^ (M + 1) * F θ)
        + ((τ θ : ℂ)) ^ (M + 1) * F' := by
  have hτne : ((τ θ : ℂ)) ≠ 0 := by simpa using hτpos.ne'
  have hpow : HasDerivAt (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1))
      (((((M : ℝ) + 1) * τ θ ^ M * τ' : ℝ)) : ℂ) θ := by
    have h := (hτd.pow (M + 1)).ofReal_comp
    simpa [Complex.ofReal_pow] using h
  have hd : HasDerivAt (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F s)
      ((((((M : ℝ) + 1) * τ θ ^ M * τ' : ℝ)) : ℂ) * F θ
        + ((τ θ : ℂ)) ^ (M + 1) * F') θ := hpow.mul hFd
  rw [hd.deriv]
  congr 1
  push_cast
  field

/-- The slope factor `|(M+1)τ'/τ|` in `deriv_scaled_remainder_eq`. -/
private theorem abs_slope_factor {M : ℕ} {τ' t : ℝ} (ht : 0 < t) :
    |((M : ℝ) + 1) * τ' / t| = ((M : ℝ) + 1) * (|τ'| / t) := by
  rw [abs_div, abs_of_pos ht, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (M : ℝ) + 1),
    mul_div_assoc]

/-- **`eq:C1-interior-remainder`, upper half.**  Only the first term of
`deriv_scaled_remainder_eq` carries a factor of `M`, and it carries exactly one:
the `M` comes from differentiating `τ^{M+1}` and from nothing else.  The second
term is `τ^{M+1}∂_zE_M·z'`, bounded by the *same* exponential through Cauchy's
estimate on a fixed disk, with no `M`. -/
theorem norm_deriv_scaled_remainder_le {M : ℕ} {τ : ℝ → ℝ} {F : ℝ → ℂ} {θ : ℝ}
    {τ' : ℝ} {F' : ℂ} {A Aτ Bd σ : ℝ}
    (hτd : HasDerivAt τ τ' θ) (hFd : HasDerivAt F F' θ) (hτpos : 0 < τ θ)
    (hslope : |τ'| / τ θ ≤ Aτ) (hAτ : 0 ≤ Aτ) (hσ : 0 ≤ σ)
    (hC0 : ‖((τ θ : ℂ)) ^ (M + 1) * F θ‖ ≤ A * σ ^ M)
    (hC1 : ‖((τ θ : ℂ)) ^ (M + 1) * F'‖ ≤ Bd * σ ^ M) :
    ‖deriv (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F s) θ‖
      ≤ (((M : ℝ) + 1) * Aτ * A + Bd) * σ ^ M := by
  have habs : |((M : ℝ) + 1) * τ' / τ θ| ≤ ((M : ℝ) + 1) * Aτ := by
    rw [abs_slope_factor hτpos]
    exact mul_le_mul_of_nonneg_left hslope (by positivity)
  rw [deriv_scaled_remainder_eq hτd hFd hτpos]
  calc ‖(((((M : ℝ) + 1) * τ' / τ θ : ℝ)) : ℂ) * (((τ θ : ℂ)) ^ (M + 1) * F θ)
        + ((τ θ : ℂ)) ^ (M + 1) * F'‖
      ≤ ‖(((((M : ℝ) + 1) * τ' / τ θ : ℝ)) : ℂ) * (((τ θ : ℂ)) ^ (M + 1) * F θ)‖
        + ‖((τ θ : ℂ)) ^ (M + 1) * F'‖ := norm_add_le _ _
    _ ≤ (((M : ℝ) + 1) * Aτ) * (A * σ ^ M) + Bd * σ ^ M := by
        refine add_le_add ?_ hC1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul habs hC0 (norm_nonneg _) (by positivity)
    _ = (((M : ℝ) + 1) * Aτ * A + Bd) * σ ^ M := by ring

/-- **`eq:C1-interior-remainder`, lower half — the prefactor is real.**  The `M`
in the derivative bound is not an artefact of estimating: the first term of
`deriv_scaled_remainder_eq` is genuinely `(M+1)(τ'/τ)` times `R_M`, so once
`|τ'/τ|` is bounded *below* the derivative is at least `(M+1)a_τ‖R_M‖` minus the
`M`-free second term.  With the upper half this sandwiches
`‖R_M'‖/(M‖R_M‖)` between two positive constants, which is what
`check_local_clock.py` (A) measures when it asserts the ratio stays in a narrow
band rather than merely being bounded above. -/
theorem norm_deriv_scaled_remainder_ge {M : ℕ} {τ : ℝ → ℝ} {F : ℝ → ℂ} {θ : ℝ}
    {τ' : ℝ} {F' : ℂ} {aτ : ℝ}
    (hτd : HasDerivAt τ τ' θ) (hFd : HasDerivAt F F' θ) (hτpos : 0 < τ θ)
    (haτ : 0 ≤ aτ) (hslope : aτ ≤ |τ'| / τ θ) :
    ((M : ℝ) + 1) * aτ * ‖((τ θ : ℂ)) ^ (M + 1) * F θ‖
        - ‖((τ θ : ℂ)) ^ (M + 1) * F'‖
      ≤ ‖deriv (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F s) θ‖ := by
  set X : ℂ := ((τ θ : ℂ)) ^ (M + 1) * F θ with hX
  set Y : ℂ := ((τ θ : ℂ)) ^ (M + 1) * F' with hY
  set cS : ℝ := ((M : ℝ) + 1) * τ' / τ θ with hcS
  have habs : ((M : ℝ) + 1) * aτ ≤ |cS| := by
    rw [hcS, abs_slope_factor hτpos]
    exact mul_le_mul_of_nonneg_left hslope (by positivity)
  have hsplit : ‖((cS : ℝ) : ℂ) * X‖ ≤ ‖((cS : ℝ) : ℂ) * X + Y‖ + ‖Y‖ := by
    have h := norm_add_le (((cS : ℝ) : ℂ) * X + Y) (-Y)
    simpa using h
  have hnorm : ‖((cS : ℝ) : ℂ) * X‖ = |cS| * ‖X‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hlow : ((M : ℝ) + 1) * aτ * ‖X‖ ≤ ‖((cS : ℝ) : ℂ) * X‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg _)
  rw [deriv_scaled_remainder_eq hτd hFd hτpos, ← hX, ← hY, ← hcS]
  linarith

/-- **`eq:C1-interior-remainder`, both halves at once.**  On a compact zero-free
subarc the derivative of the normalized remainder is squeezed between
`((M+1)a_τA₀ - B)σ^M` and `(M+1)(A_τA + B)σ^M`: the `M` prefactor is present in
both, so `‖R_M‖_{C¹}` is `Θ(Mσ^M)` and not merely `O` of it. -/
theorem c1_prefactor_two_sided {M : ℕ} {τ : ℝ → ℝ} {F : ℝ → ℂ} {θ : ℝ}
    {τ' : ℝ} {F' : ℂ} {A A₀ aτ Aτ Bd σ : ℝ}
    (hτd : HasDerivAt τ τ' θ) (hFd : HasDerivAt F F' θ) (hτpos : 0 < τ θ)
    (haτ : 0 ≤ aτ) (hAτ : 0 ≤ Aτ) (hσ : 0 ≤ σ)
    (hlo : aτ ≤ |τ'| / τ θ) (hhi : |τ'| / τ θ ≤ Aτ)
    (hA₀ : A₀ * σ ^ M ≤ ‖((τ θ : ℂ)) ^ (M + 1) * F θ‖)
    (hC0 : ‖((τ θ : ℂ)) ^ (M + 1) * F θ‖ ≤ A * σ ^ M)
    (hC1 : ‖((τ θ : ℂ)) ^ (M + 1) * F'‖ ≤ Bd * σ ^ M) :
    (((M : ℝ) + 1) * aτ * A₀ - Bd) * σ ^ M
        ≤ ‖deriv (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F s) θ‖ ∧
      ‖deriv (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F s) θ‖
        ≤ (((M : ℝ) + 1) * Aτ * A + Bd) * σ ^ M := by
  refine ⟨le_trans ?_ (norm_deriv_scaled_remainder_ge hτd hFd hτpos haτ hlo),
    norm_deriv_scaled_remainder_le hτd hFd hτpos hhi hAτ hσ hC0 hC1⟩
  have h1 : ((M : ℝ) + 1) * aτ * (A₀ * σ ^ M)
      ≤ ((M : ℝ) + 1) * aτ * ‖((τ θ : ℂ)) ^ (M + 1) * F θ‖ :=
    mul_le_mul_of_nonneg_left hA₀ (by positivity)
  nlinarith [hC1, h1]

/-! ### `eq:numerator-clock-correction` — the denominator term is weight-free -/

/-- **`eq:numerator-clock-correction`, the residue.**  Removing the numerator's
logarithmic derivative from `ψ' = Im(W'/W)` leaves exactly `Im(D'/D)`, in which
`B` does not appear at all. -/
theorem clock_denominator_term {B : Polynomial ℂ} {γ D : ℝ → ℂ} {γ' D' : ℂ} {θ : ℝ}
    (hγ : HasDerivAt γ γ' θ) (hD : HasDerivAt D D' θ)
    (hB0 : B.eval (γ θ) ≠ 0) (hD0 : D θ ≠ 0) :
    (deriv (fun s : ℝ => B.eval (γ s) * D s) θ / (B.eval (γ θ) * D θ)).im
        - ((B.derivative.eval (γ θ) * γ') / B.eval (γ θ)).im
      = (D' / D θ).im := by
  rw [numerator_clock_correction hγ hD hB0 hD0]
  ring

/-- **`eq:numerator-clock-correction`, the claim.**  Two different weights give
the *same* denominator term.  This is the content of the row — that the leading
clock is denominator-universal and the weight first reaches the spacing at order
`M^{-2}` through its own logarithmic derivative — and a split that did not
exhibit the first term as weight-free would not have established it. -/
theorem clock_denominator_term_indep_of_weight {B₁ B₂ : Polynomial ℂ} {γ D : ℝ → ℂ}
    {γ' D' : ℂ} {θ : ℝ} (hγ : HasDerivAt γ γ' θ) (hD : HasDerivAt D D' θ)
    (hB₁ : B₁.eval (γ θ) ≠ 0) (hB₂ : B₂.eval (γ θ) ≠ 0) (hD0 : D θ ≠ 0) :
    (deriv (fun s : ℝ => B₁.eval (γ s) * D s) θ / (B₁.eval (γ θ) * D θ)).im
        - ((B₁.derivative.eval (γ θ) * γ') / B₁.eval (γ θ)).im
      = (deriv (fun s : ℝ => B₂.eval (γ s) * D s) θ / (B₂.eval (γ θ) * D θ)).im
        - ((B₂.derivative.eval (γ θ) * γ') / B₂.eval (γ θ)).im := by
  rw [clock_denominator_term hγ hD hB₁ hD0, clock_denominator_term hγ hD hB₂ hD0]

/-- **A constant weight kills the correction.**  So at `B` constant the phase
derivative *is* the denominator term — the non-vacuity check that makes the split
above a statement rather than a tautology. -/
theorem clock_correction_of_const (c : ℂ) {γ : ℝ → ℂ} {γ' : ℂ} {θ : ℝ} :
    (((Polynomial.C c).derivative.eval (γ θ) * γ') / (Polynomial.C c).eval (γ θ)) = 0 := by
  simp


/-- **`eq:C1-interior-remainder`, assembled.**  On a compact zero-free subarc,
`R_M(θ) = τ(θ)^{M+1}F(θ)` satisfies `‖R_M‖_{C⁰} ≤ Aσ^M` and
`‖R_M‖_{C¹} ≤ (M+1)(A_τA + B)σ^M`: the value bound carries no `M` and the
derivative bound carries exactly one factor of `M+1`.

The prefactor is kept out of the constant on purpose.  It is not the whole story
— the `σ^M` is what makes the bound useful — and it is not absent either, which
is why the change of variable of `norm_le_of_mul_eq` has something to cancel. -/
theorem c1_interior_remainder_bound {a b σ Aτ A Bd : ℝ} {τ τ' : ℝ → ℝ} {F F' : ℕ → ℝ → ℂ}
    (hσ : 0 ≤ σ) (hAτ : 0 ≤ Aτ) (hBd : 0 ≤ Bd)
    (hτd : ∀ θ ∈ Set.Icc a b, HasDerivAt τ (τ' θ) θ)
    (hFd : ∀ M : ℕ, ∀ θ ∈ Set.Icc a b, HasDerivAt (F M) (F' M θ) θ)
    (hτpos : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hslope : ∀ θ ∈ Set.Icc a b, |τ' θ| / τ θ ≤ Aτ)
    (hC0 : ∀ M : ℕ, ∀ θ ∈ Set.Icc a b, ‖((τ θ : ℂ)) ^ (M + 1) * F M θ‖ ≤ A * σ ^ M)
    (hC1 : ∀ M : ℕ, ∀ θ ∈ Set.Icc a b, ‖((τ θ : ℂ)) ^ (M + 1) * F' M θ‖ ≤ Bd * σ ^ M) :
    ∀ M : ℕ, ∀ θ ∈ Set.Icc a b,
      ‖((τ θ : ℂ)) ^ (M + 1) * F M θ‖ ≤ A * σ ^ M ∧
        ‖deriv (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F M s) θ‖
          ≤ ((M : ℝ) + 1) * (Aτ * A + Bd) * σ ^ M := by
  intro M θ hθ
  refine ⟨hC0 M θ hθ, ?_⟩
  refine le_trans (norm_deriv_scaled_remainder_le (hτd θ hθ) (hFd M θ hθ) (hτpos θ hθ)
    (hslope θ hθ) hAτ hσ (hC0 M θ hθ) (hC1 M θ hθ)) ?_
  have hM : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hcoef : ((M : ℝ) + 1) * Aτ * A + Bd ≤ ((M : ℝ) + 1) * (Aτ * A + Bd) := by
    nlinarith [hBd, hM]
  exact mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- **`eq:C1-interior-remainder`, one constant.**  `‖R_M‖_{C¹(J₀)} = O(Mσ^M)`
with a single `C` serving both bounds and the `M` appearing only as the explicit
`(M+1)` on the derivative — the shape the change of variable to the phase
coordinate consumes. -/
theorem exists_c1_interior_remainder_bound {a b σ Aτ A Bd : ℝ} {τ τ' : ℝ → ℝ}
    {F F' : ℕ → ℝ → ℂ} (hσ : 0 ≤ σ) (hAτ : 0 ≤ Aτ) (hBd : 0 ≤ Bd)
    (hτd : ∀ θ ∈ Set.Icc a b, HasDerivAt τ (τ' θ) θ)
    (hFd : ∀ M : ℕ, ∀ θ ∈ Set.Icc a b, HasDerivAt (F M) (F' M θ) θ)
    (hτpos : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hslope : ∀ θ ∈ Set.Icc a b, |τ' θ| / τ θ ≤ Aτ)
    (hC0 : ∀ M : ℕ, ∀ θ ∈ Set.Icc a b, ‖((τ θ : ℂ)) ^ (M + 1) * F M θ‖ ≤ A * σ ^ M)
    (hC1 : ∀ M : ℕ, ∀ θ ∈ Set.Icc a b, ‖((τ θ : ℂ)) ^ (M + 1) * F' M θ‖ ≤ Bd * σ ^ M) :
    ∃ C ≥ (0 : ℝ), ∀ M : ℕ, ∀ θ ∈ Set.Icc a b,
      ‖((τ θ : ℂ)) ^ (M + 1) * F M θ‖ ≤ C * σ ^ M ∧
        ‖deriv (fun s : ℝ => ((τ s : ℂ)) ^ (M + 1) * F M s) θ‖
          ≤ ((M : ℝ) + 1) * C * σ ^ M := by
  rcases Set.eq_empty_or_nonempty (Set.Icc a b) with hemp | ⟨θ₀, hθ₀⟩
  · exact ⟨0, le_refl 0, fun M θ hθ => absurd hθ (by rw [hemp]; exact fun h => h)⟩
  have hA0 : 0 ≤ A := by
    have := le_trans (norm_nonneg _) (hC0 0 θ₀ hθ₀)
    simpa using this
  refine ⟨max A (Aτ * A + Bd), le_trans hA0 (le_max_left _ _), fun M θ hθ => ?_⟩
  obtain ⟨h0, h1⟩ := c1_interior_remainder_bound hσ hAτ hBd hτd hFd hτpos hslope hC0 hC1 M θ hθ
  have hM : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  refine ⟨le_trans h0 (by
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), ?_⟩
  refine le_trans h1 ?_
  have : (Aτ * A + Bd) ≤ max A (Aτ * A + Bd) := le_max_right _ _
  calc ((M : ℝ) + 1) * (Aτ * A + Bd) * σ ^ M
      ≤ ((M : ℝ) + 1) * max A (Aτ * A + Bd) * σ ^ M := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left this hM
    _ = ((M : ℝ) + 1) * max A (Aτ * A + Bd) * σ ^ M := rfl

end ForgacsTran
