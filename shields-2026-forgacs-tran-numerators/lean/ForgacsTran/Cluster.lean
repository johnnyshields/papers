/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.AttractorPole

/-!
# The endpoint clusters

The lower endpoint of the Forgács--Tran interval, when the smallest zero `x_1` of
`Q` has multiplicity `ρ > 1`, carries a cluster of `ρ` denominator roots
`t_j(θ) = x_1 + α_jθ + O(θ^2)` with
`α_j = -x_1ω_j/sin(π/ρ)`, `ω_j = e^{(2j-1)π i/ρ}`.
This module proves what is unconditional about that cluster and the residue
comparison built on it.

## Main statements

* `clusterAngle`, `clusterOmega`, `clusterAlpha` — the directions of
  `eq:lower-cluster-expansion`.
* `clusterOmega_pow` — the directions are the `ρ`-th roots of `-1`.
* `norm_clusterAlpha` — every direction has modulus `x_1/sin(π/ρ)`, which
  is what makes the residue ratio unimodular in the limit.
* `clusterOmega_injOn` — the directions are pairwise distinct over one period, so
  the cluster members are pairwise distinct for small `θ`.
* `cluster_root_eq`, `norm_cluster_root` — the exact cluster equation
  `(t-x_1)^ρ q(t) = -zt^r`: the `ρ`-th-root structure the expansion reads
  off, with no asymptotics assumed.
* `cos_clusterAngle_lt`, `exists_lower_cluster_gap_coeff` — `eq:lower-cluster-gap`:
  every nonprincipal direction has `Reω_j < cos(π/ρ)`, so its linear
  gap coefficient is positive, and one positive `c_0` serves the whole cluster.
  The principal pair `j = 1`, `j = ρ` is exactly where the coefficient
  vanishes.
* `tendsto_residue_ratio`, `tendsto_residue_ratio_cluster` — the residue
  comparison, `eq:lower-residue-ratio` and `eq:upper-residue-ratio`, from the
  leading behavior of the numerator and of `∂_tD` along each branch.
* `norm_residue_ratio_limit` — the limiting ratio is unimodular.
* `eventually_cluster_amplitude_le` — **the constant `C_W = 2`.**  A finite
  family of amplitudes whose ratios to `W` are unimodular in the limit satisfies
  `|W_j| ≤ 2|W|` eventually, uniformly over the family.  This is what
  `Dominance.cluster_sum_le` takes as `C_W`.

## Implementation notes

**Scope.**  The expansion `eq:lower-cluster-expansion` itself is the paper's
citation of `\cite[Prop.~3]{Forgacs2017RationalDenominator}`, and the
parametrization `τ,z` of `thm:FT-geometry` is its Lemmas~2--6; neither is
formalized, so the residue-comparison theorems take the leading behavior along
each branch as an ordinary hypothesis in their type rather than deriving it.
Everything about the *directions* — that there are `ρ` of them, that they are
distinct, that they share one modulus, and which of them carry a strictly
positive gap coefficient — is proved here unconditionally.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `eq:lower-cluster-expansion`,
`eq:lower-cluster-gap`, `eq:lower-residue-ratio`, `eq:upper-residue-ratio`).

## Tags

endpoint cluster, denominator zeros, residue
-/

namespace ForgacsTran

open Polynomial Complex Filter Topology

/-! ### The lower-endpoint cluster directions -/

/-- Paper `eq:lower-cluster-expansion` — the argument `(2j-1)π/ρ` of the
`j`-th cluster direction. -/
noncomputable def clusterAngle (ρ j : ℕ) : ℝ := (2 * (j : ℝ) - 1) * Real.pi / ρ

/-- Paper `eq:lower-cluster-expansion` — `ω_j = e^{(2j-1)π i/ρ}`.  The
index `j = 0` (equivalently `j = ρ`) is the principal upper branch
`ω_+ = e^{-iπ/ρ}`. -/
noncomputable def clusterOmega (ρ j : ℕ) : ℂ := Complex.exp (clusterAngle ρ j * Complex.I)

/-- Paper `eq:lower-cluster-expansion` —
`α_j = -x_1ω_j/sin(π/ρ)`. -/
noncomputable def clusterAlpha (x₁ : ℝ) (ρ j : ℕ) : ℂ :=
  -(x₁ : ℂ) * clusterOmega ρ j / (Real.sin (Real.pi / ρ) : ℂ)

/-- **`ω_1 = \overline{ω_0}`.**  The two angles are `±π/ρ`, so the manuscript's
indices `0` and `1` are the principal pair — the upper branch and its conjugate —
at every multiplicity.  That is why the retained cluster is indexed by
`2, …, ρ-1` and has `ρ - 2` members rather than `ρ - 1`. -/
theorem conj_clusterOmega_zero (ρ : ℕ) :
    (starRingEnd ℂ) (clusterOmega ρ 0) = clusterOmega ρ 1 := by
  rw [clusterOmega, clusterOmega, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, clusterAngle, clusterAngle]
  push_cast
  ring

/-- `α_1 = \overline{α_0}`: the scalars `-x_1` and `1/\sin(π/ρ)` are real. -/
theorem conj_clusterAlpha_zero (x₁ : ℝ) (ρ : ℕ) :
    (starRingEnd ℂ) (clusterAlpha x₁ ρ 0) = clusterAlpha x₁ ρ 1 := by
  rw [clusterAlpha, clusterAlpha, map_div₀, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_ofReal, conj_clusterOmega_zero]

@[simp] theorem norm_clusterOmega (ρ j : ℕ) : ‖clusterOmega ρ j‖ = 1 := by
  simp [clusterOmega, Complex.norm_exp]

theorem clusterOmega_re (ρ j : ℕ) : (clusterOmega ρ j).re = Real.cos (clusterAngle ρ j) := by
  simp [clusterOmega, Complex.exp_ofReal_mul_I_re]

theorem clusterOmega_ne_zero (ρ j : ℕ) : clusterOmega ρ j ≠ 0 := Complex.exp_ne_zero _

/-- **Paper `eq:lower-cluster-expansion`.**  The cluster directions are the
`ρ`-th roots of `-1`, which is why a zero of `Q` of multiplicity `ρ`
produces `ρ` branches. -/
theorem clusterOmega_pow {ρ : ℕ} (hρ : 1 ≤ ρ) (j : ℕ) : (clusterOmega ρ j) ^ ρ = -1 := by
  have hρ0 : (ρ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [clusterOmega, ← Complex.exp_nat_mul]
  have harg : (ρ : ℂ) * ((clusterAngle ρ j : ℝ) * Complex.I)
      = (2 * (j : ℂ)) * (Real.pi * Complex.I) - Real.pi * Complex.I := by
    simp only [clusterAngle]
    push_cast
    field_simp
  rw [harg, Complex.exp_sub, Complex.exp_pi_mul_I]
  have hnum : Complex.exp ((2 * (j : ℂ)) * (Real.pi * Complex.I)) = 1 := by
    rw [show (2 * (j : ℂ)) * (Real.pi * Complex.I) = (j : ℤ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hnum]
  norm_num

/-- For `ρ ≥ 2` the normalization `sin(π/ρ)` of
`eq:lower-cluster-expansion` is positive. -/
theorem sin_pi_div_pos {ρ : ℕ} (hρ : 2 ≤ ρ) : 0 < Real.sin (Real.pi / ρ) := by
  have hρ0 : (0 : ℝ) < ρ := by
    have : (0 : ℕ) < ρ := by omega
    exact_mod_cast this
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  rw [div_lt_iff₀ hρ0]
  have h1 : (1 : ℝ) < ρ := by exact_mod_cast (by omega : 1 < ρ)
  nlinarith [Real.pi_pos]

/-- **Paper `eq:lower-cluster-expansion`.**  Every cluster direction has the same
modulus `|α_j| = x_1/sin(π/ρ)`.  This is what makes the residue ratio
of `eq:lower-residue-ratio` tend to `1` in modulus. -/
theorem norm_clusterAlpha {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) (j : ℕ) :
    ‖clusterAlpha x₁ ρ j‖ = x₁ / Real.sin (Real.pi / ρ) := by
  have hs := sin_pi_div_pos hρ
  rw [clusterAlpha, norm_div, norm_mul, norm_clusterOmega, mul_one, norm_neg,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hx, abs_of_pos hs]

theorem clusterAlpha_ne_zero {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) (j : ℕ) :
    clusterAlpha x₁ ρ j ≠ 0 := by
  intro h
  have := norm_clusterAlpha hx hρ j
  rw [h, norm_zero] at this
  have hs := sin_pi_div_pos hρ
  have : (0 : ℝ) < x₁ / Real.sin (Real.pi / ρ) := by positivity
  linarith [this, (norm_clusterAlpha hx hρ j).symm]

/-- **Paper `eq:lower-residue-ratio`.**  Every ratio of cluster directions, to
any integer power, has modulus one. -/
theorem norm_clusterAlpha_zpow_ratio {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) (j k : ℕ)
    (n : ℤ) : ‖(clusterAlpha x₁ ρ j / clusterAlpha x₁ ρ k) ^ n‖ = 1 := by
  have hk := clusterAlpha_ne_zero hx hρ k
  have h1 : ‖clusterAlpha x₁ ρ j / clusterAlpha x₁ ρ k‖ = 1 := by
    rw [norm_div, norm_clusterAlpha hx hρ j, norm_clusterAlpha hx hρ k]
    have hs := sin_pi_div_pos hρ
    field_simp
  rw [norm_zpow, h1, one_zpow]

/-- **Paper `eq:lower-cluster-expansion`.**  The cluster directions are pairwise
distinct over one period, so the cluster members are pairwise distinct for small
`θ`. -/
theorem clusterOmega_injOn {ρ : ℕ} (hρ : 1 ≤ ρ) {j k : ℕ} (hj : j ∈ Finset.Icc 1 ρ)
    (hk : k ∈ Finset.Icc 1 ρ) (h : clusterOmega ρ j = clusterOmega ρ k) : j = k := by
  rw [Finset.mem_Icc] at hj hk
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast (by omega : 0 < ρ)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hre : clusterAngle ρ j = clusterAngle ρ k + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa [Complex.add_im, Complex.mul_im] using this
  have hang : (2 * (j : ℝ) - 1) * Real.pi / ρ - (2 * (k : ℝ) - 1) * Real.pi / ρ
      = n * (2 * Real.pi) := by
    simp only [clusterAngle] at hre
    linarith
  have hjk : (j : ℝ) - k = n * ρ := by
    have hπ := Real.pi_pos
    field_simp at hang
    nlinarith [hang]
  have hZ : (j : ℤ) - k = n * ρ := by exact_mod_cast hjk
  have hjb1 : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj.1
  have hjb2 : (j : ℤ) ≤ (ρ : ℤ) := by exact_mod_cast hj.2
  have hkb1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
  have hkb2 : (k : ℤ) ≤ (ρ : ℤ) := by exact_mod_cast hk.2
  have hρZ : (1 : ℤ) ≤ (ρ : ℤ) := by exact_mod_cast hρ
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hneg | hzero | hpos
    · have hb : n * (ρ : ℤ) ≤ -(ρ : ℤ) := by nlinarith
      omega
    · exact hzero
    · have hb : (ρ : ℤ) ≤ n * (ρ : ℤ) := by nlinarith
      omega
  rw [hn0] at hZ
  omega

/-! ### The linear modulus gap at the lower endpoint -/

/-- **Paper `eq:lower-cluster-gap`.**  Every nonprincipal cluster direction has
`Reω_j < cos(π/ρ)`, so its linear coefficient
`(cos(π/ρ) - Reω_j)/sin(π/ρ)` is strictly positive.  This is
the sign of the gap `|ζ_j(θ)| ≥ 1 + c_0θ`; the principal pair,
`j = 1` and `j = ρ`, is exactly where the coefficient vanishes.

**Differs from the paper's route.**  The paper reads the sign off the position of
`ω_j` on the unit circle.  Here it is the strict monotonicity of `cos` on
`[0,π]` applied twice, the angles above `π` reflected through
`cos x = cos(2π - x)`. -/
theorem cos_clusterAngle_lt {ρ j : ℕ} (hρ : 2 ≤ ρ) (hj : 2 ≤ j) (hjρ : j ≤ ρ - 1) :
    Real.cos (clusterAngle ρ j) < Real.cos (Real.pi / ρ) := by
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast (by omega : 0 < ρ)
  set p : ℝ := Real.pi / ρ with hp
  have hppos : 0 < p := by rw [hp]; positivity
  have hπ : (ρ : ℝ) * p = Real.pi := by rw [hp]; field_simp
  have hx : clusterAngle ρ j = (2 * (j : ℝ) - 1) * p := by
    rw [clusterAngle, hp]; ring
  have hj3 : (3 : ℝ) ≤ 2 * (j : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hjup : 2 * (j : ℝ) - 1 ≤ 2 * (ρ : ℝ) - 3 := by
    have : (j : ℝ) ≤ (ρ : ℝ) - 1 := by
      have : (j : ℕ) ≤ ρ - 1 := hjρ
      have h2 : (j : ℝ) + 1 ≤ (ρ : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ ρ)
      linarith
    linarith
  have h1 : 3 * p ≤ clusterAngle ρ j := by rw [hx]; nlinarith
  have h2 : clusterAngle ρ j ≤ 2 * Real.pi - 3 * p := by
    rw [hx]
    nlinarith
  have hlow : p < clusterAngle ρ j := by linarith
  rcases le_or_gt (clusterAngle ρ j) Real.pi with hle | hgt
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hppos.le hle hlow
  · have hsub : Real.cos (2 * Real.pi - clusterAngle ρ j) = Real.cos (clusterAngle ρ j) := by
      rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
      ring
    rw [← hsub]
    refine Real.cos_lt_cos_of_nonneg_of_le_pi hppos.le (by linarith) (by linarith)

/-- **Paper `eq:lower-cluster-gap`.**  One positive constant `c_0` serves the
whole nonprincipal cluster. -/
theorem exists_lower_cluster_gap_coeff {ρ : ℕ} (hρ : 2 ≤ ρ) :
    ∃ c₀ > (0 : ℝ), ∀ j ∈ Finset.Icc 2 (ρ - 1),
      c₀ ≤ (Real.cos (Real.pi / ρ) - Real.cos (clusterAngle ρ j)) / Real.sin (Real.pi / ρ) := by
  have hs := sin_pi_div_pos hρ
  set F : ℕ → ℝ :=
    fun j => (Real.cos (Real.pi / ρ) - Real.cos (clusterAngle ρ j)) / Real.sin (Real.pi / ρ)
    with hF
  have hpos : ∀ j ∈ Finset.Icc 2 (ρ - 1), 0 < F j := by
    intro j hjmem
    rw [Finset.mem_Icc] at hjmem
    have := cos_clusterAngle_lt hρ hjmem.1 hjmem.2
    rw [hF]
    exact div_pos (by linarith) hs
  rcases (Finset.Icc 2 (ρ - 1)).eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, one_pos, by simp [hemp]⟩
  · refine ⟨(Finset.Icc 2 (ρ - 1)).inf' hne F, ?_, fun j hj => Finset.inf'_le F hj⟩
    rw [gt_iff_lt, Finset.lt_inf'_iff]
    exact hpos

/-! ### The cluster equation -/

/-- **Paper `eq:lower-cluster-expansion`, the exact form.**  If `x_1` is a zero of
`Q` of multiplicity `ρ`, `Q = (t-x_1)^ρ q`, then every denominator zero
satisfies `(t-x_1)^ρ q(t) = -zt^r` exactly.  This is the `ρ`-th-root
structure the expansion `t_j = x_1 + α_jθ + O(θ^2)` reads off:
`(t - x_1)^ρ` is proportional to `z` to leading order, so the `ρ` branches
are separated by the `ρ`-th roots of `-1`. -/
theorem cluster_root_eq {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ} (hQ : Q = (X - C x₁) ^ ρ * q)
    {z t : ℂ} (hroot : (ftDen Q r z).eval t = 0) :
    (t - x₁) ^ ρ * q.eval t = -(z * t ^ r) := by
  rw [ftDen_eval, hQ] at hroot
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hroot
  linear_combination hroot

/-- The modulus form: `|t - x_1|^ρ|q(t)| = |z||t|^r`, so the cluster members
approach `x_1` at rate `|z|^{1/ρ}`. -/
theorem norm_cluster_root {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ} (hQ : Q = (X - C x₁) ^ ρ * q)
    {z t : ℂ} (hroot : (ftDen Q r z).eval t = 0) :
    ‖t - x₁‖ ^ ρ * ‖q.eval t‖ = ‖z‖ * ‖t‖ ^ r := by
  have h := cluster_root_eq hQ hroot
  have := congrArg norm h
  rwa [norm_mul, norm_pow, norm_neg, norm_mul, norm_pow] at this

/-! ### The residue ratio -/

/-- **Paper `eq:lower-residue-ratio` and `eq:upper-residue-ratio` — the algebraic
core.**  The amplitude is `𝒲 = -B/∂_tD`.  Given the leading
behavior of the numerator and of the denominator derivative along the `j`-th
cluster member and along the principal branch, measured against a common
parameter power, the ratio of amplitudes converges to the ratio of the four
limits.

The two endpoints are the two instantiations.  At the lower endpoint take
`m = ν`, `n = ρ - 1`, `L_{B,j} = c_Bα_j^ν` and
`L_{E,j} = c_Qα_j^{ρ-1}`, which is `tendsto_residue_ratio_cluster`
below; at the upper endpoint take `m = 0`, `n = -1`,
`L_{B,j} = B(0)` and `L_{E,j} = -rQ(0)/ζ_j`, giving the
`eq:upper-residue-ratio` limit `ζ_j/ζ_+`.

Nothing here is assumed about *why* the expansions hold: the numerator one is
Taylor's theorem at a zero of order `ν`, the denominator one is
`eq:Dprime-identity` with Taylor at a zero of order `ρ`, and both are read off
the cluster expansion the paper cites. -/
theorem tendsto_residue_ratio {ι : Type*} {l : Filter ι} {Bj Bp Ej Ep θ : ι → ℂ}
    {m n : ℤ} {LBj LBp LEj LEp : ℂ}
    (hLBp : LBp ≠ 0) (hLEj : LEj ≠ 0) (hLEp : LEp ≠ 0)
    (hθ : ∀ᶠ x in l, θ x ≠ 0)
    (hBj : Tendsto (fun x => Bj x / θ x ^ m) l (𝓝 LBj))
    (hBp : Tendsto (fun x => Bp x / θ x ^ m) l (𝓝 LBp))
    (hEj : Tendsto (fun x => Ej x / θ x ^ n) l (𝓝 LEj))
    (hEp : Tendsto (fun x => Ep x / θ x ^ n) l (𝓝 LEp)) :
    Tendsto (fun x => (-Bj x / Ej x) / (-Bp x / Ep x)) l (𝓝 (LBj * LEp / (LBp * LEj))) := by
  have hlim : Tendsto (fun x => (Bj x / θ x ^ m) * (Ep x / θ x ^ n) /
      ((Bp x / θ x ^ m) * (Ej x / θ x ^ n))) l (𝓝 (LBj * LEp / (LBp * LEj))) :=
    (hBj.mul hEp).div (hBp.mul hEj) (mul_ne_zero hLBp hLEj)
  refine hlim.congr' ?_
  have hBpne : ∀ᶠ x in l, Bp x / θ x ^ m ≠ 0 := hBp.eventually_ne hLBp
  have hEjne : ∀ᶠ x in l, Ej x / θ x ^ n ≠ 0 := hEj.eventually_ne hLEj
  have hEpne : ∀ᶠ x in l, Ep x / θ x ^ n ≠ 0 := hEp.eventually_ne hLEp
  filter_upwards [hθ, hBpne, hEjne, hEpne] with x hx hbp hej hep
  have hθm : θ x ^ m ≠ 0 := zpow_ne_zero _ hx
  have hθn : θ x ^ n ≠ 0 := zpow_ne_zero _ hx
  have hBpx : Bp x ≠ 0 := fun h => hbp (by rw [h, zero_div])
  have hEjx : Ej x ≠ 0 := fun h => hej (by rw [h, zero_div])
  have hEpx : Ep x ≠ 0 := fun h => hep (by rw [h, zero_div])
  field_simp

/-- **Paper `eq:lower-residue-ratio`.**  With the cluster expansion's leading
constants, the amplitude ratio tends to `(α_j/α_+)^{ν-ρ+1}`. -/
theorem tendsto_residue_ratio_cluster {ι : Type*} {l : Filter ι} {Bj Bp Ej Ep θ : ι → ℂ}
    {ν k : ℕ} {cB cQ aj ap : ℂ}
    (hcB : cB ≠ 0) (hcQ : cQ ≠ 0) (haj : aj ≠ 0) (hap : ap ≠ 0)
    (hθ : ∀ᶠ x in l, θ x ≠ 0)
    (hBj : Tendsto (fun x => Bj x / θ x ^ (ν : ℤ)) l (𝓝 (cB * aj ^ ν)))
    (hBp : Tendsto (fun x => Bp x / θ x ^ (ν : ℤ)) l (𝓝 (cB * ap ^ ν)))
    (hEj : Tendsto (fun x => Ej x / θ x ^ (k : ℤ)) l (𝓝 (cQ * aj ^ k)))
    (hEp : Tendsto (fun x => Ep x / θ x ^ (k : ℤ)) l (𝓝 (cQ * ap ^ k))) :
    Tendsto (fun x => (-Bj x / Ej x) / (-Bp x / Ep x)) l
      (𝓝 ((aj / ap) ^ ((ν : ℤ) - k))) := by
  have hlim := tendsto_residue_ratio (mul_ne_zero hcB (pow_ne_zero _ hap))
    (mul_ne_zero hcQ (pow_ne_zero _ haj)) (mul_ne_zero hcQ (pow_ne_zero _ hap))
    hθ hBj hBp hEj hEp
  have hval : cB * aj ^ ν * (cQ * ap ^ k) / (cB * ap ^ ν * (cQ * aj ^ k))
      = (aj / ap) ^ ((ν : ℤ) - k) := by
    rw [zpow_sub₀ (div_ne_zero haj hap), zpow_natCast, zpow_natCast, div_pow, div_pow]
    field_simp
  rwa [hval] at hlim

/-- **Paper `eq:lower-residue-ratio`, the modulus.**  All the cluster directions
have one modulus, so the limiting ratio is unimodular whatever `ν` and `ρ`
are. -/
theorem norm_residue_ratio_limit {aj ap : ℂ} {n : ℤ} (hap : ap ≠ 0)
    (hnorm : ‖aj‖ = ‖ap‖) : ‖(aj / ap) ^ n‖ = 1 := by
  have hn : (0 : ℝ) < ‖ap‖ := norm_pos_iff.mpr hap
  have h1 : ‖aj / ap‖ = 1 := by rw [norm_div, hnorm]; field_simp
  rw [norm_zpow, h1, one_zpow]

/-- **Paper `eq:lower-residue-ratio`, the constant `C_W = 2`.**  A finite family
of cluster amplitudes whose ratios to the principal amplitude are unimodular in
the limit is eventually bounded by `2|W|`, uniformly over the family.  This is
what supplies the `C_W` that `Dominance.cluster_sum_le` consumes; the paper's
"after decreasing `ε` we may assume `|W_j| ≤ 2|W|`" is exactly this
statement. -/
theorem eventually_cluster_amplitude_le {ι κ : Type*} {l : Filter ι} {W : ι → ℂ}
    {s : Finset κ} {Wf : κ → ι → ℂ} {L : κ → ℂ}
    (hW : ∀ᶠ x in l, W x ≠ 0)
    (h : ∀ i ∈ s, Tendsto (fun x => Wf i x / W x) l (𝓝 (L i)))
    (hL : ∀ i ∈ s, ‖L i‖ = 1) :
    ∀ᶠ x in l, ∀ i ∈ s, ‖Wf i x‖ ≤ 2 * ‖W x‖ := by
  have hstep : ∀ i ∈ s, ∀ᶠ x in l, ‖Wf i x‖ ≤ 2 * ‖W x‖ := by
    intro i hi
    have hn : Tendsto (fun x => ‖Wf i x / W x‖) l (𝓝 ‖L i‖) := (h i hi).norm
    rw [hL i hi] at hn
    have hev : ∀ᶠ x in l, ‖Wf i x / W x‖ ≤ 2 := by
      exact hn.eventually_le_const (by norm_num : (1 : ℝ) < 2)
    filter_upwards [hW, hev] with x hx hle
    have : ‖Wf i x‖ = ‖Wf i x / W x‖ * ‖W x‖ := by
      rw [← norm_mul, div_mul_cancel₀ _ hx]
    rw [this]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  exact (Filter.eventually_all_finset s).mpr hstep

end ForgacsTran
