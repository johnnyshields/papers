/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.CubicWitnessCluster

/-!
# The upper cluster's witness: Q = 1 - t, r = 3

`weighted_dominance_of_branch`'s upper-endpoint cluster binders — `hexp₁`,
`hωne₁`, `hωne'₁`, `hratio₁` — quantify over `Fin n₁`, the retained set at the
upper endpoint with the principal pair removed.  The upper cluster tends to the
`r`th roots of `-1` and the principal pair is `e^{±iπ/r}`, so

| `r` | roots of `-1` | principal | `n₁` |
|---|---|---|---|
| 1 | `-1` | none | 0 |
| 2 | `±i` | both | 0 |
| 3 | `e^{±iπ/3}, -1` | the pair | 1 |

`r = 3` is the smallest `r` whose upper cluster has a nonprincipal member —
exactly as `ρ = 3` is for the lower one, and for the same reason.  `CubicWitness`
has `r = 1`, so the upper block has never been instantiated non-vacuously
anywhere in the tree, and at `r ≤ 2` it cannot be.

**The pencil is `Q(t) = 1 - t` with `r = 3`, chosen for tractability.**  `deg Q = 1`
makes `deg D = 3`, so the retained set holds at most three members and `n₁ = 1`
is a *counting* fact rather than a numerical observation.  And the branch is not
merely algebraic but closed-form: `z = (t-1)/t³` is real iff
`Im((t-1)\bar t³) = 0`, which at `t = τe^{iθ}` reads `τ sin 2θ = sin 3θ` — linear
in `τ`, because `deg Q = 1` makes the numerator linear in `t`.  So

`τ(θ) = sin 3θ / sin 2θ`

is a *definition*, not a root, and no existence or uniqueness lemma is needed —
where the lower witness's `2τ³cos θ = 3τ² - 1` is genuinely cubic and needed
both.

**The nonprincipal zero is `-2τcos θ`.**  `1 - t + zt³` has no `t²` term, so the
three roots sum to zero and the third is minus the principal pair's sum.  Its
normalized modulus is therefore `2cos θ`, and `hexp₁` — which bounds
`|‖g₁/τ‖ - (1 + cδ)|`, the *modulus* form, unlike `hexp₀`'s complex difference —
becomes a second-order Taylor bound on `2cos(π/3 - δ)` at `0`.

`scripts/check_upper_cluster_witness.py` checks the vacuity and the convergence
at the real objects before any of this.

## Implementation notes

Sorry-free.

## Tags

witness, upper cluster, non-vacuity
-/

namespace ForgacsTran

open Polynomial Complex

/-- The witness pencil's numerator: `Q(t) = 1 - t`. -/
noncomputable def upperQ : Polynomial ℂ := 1 - Polynomial.X

theorem upperQ_eval_zero : upperQ.eval 0 = 1 := by simp [upperQ]

/-- The Forgács--Tran branch at this pencil, in closed form: `τ = sin3θ/sin2θ`.
A definition rather than a root, because `deg Q = 1` makes the reality condition
linear in `τ`. -/
noncomputable def upperTau (θ : ℝ) : ℝ := Real.sin (3 * θ) / Real.sin (2 * θ)

/-- **The normalized nonprincipal modulus.**  The third zero is `-2τcos θ`, so
its modulus over `τ` is `2cos θ`; at the upper endpoint `θ = π/3 - δ` that is
the function `hexp₁` expands. -/
noncomputable def upperClusterRatio (δ : ℝ) : ℝ := 2 * Real.cos (Real.pi / 3 - δ)

/-- The derivative of `upperClusterRatio`, in closed form, so the mean-value step of the
expansion has something explicit to bound. -/
noncomputable def upperClusterRatioDeriv (δ : ℝ) : ℝ := 2 * Real.sin (Real.pi / 3 - δ)

/-- The second derivative of `upperClusterRatio`.  Bounding it on the window is what makes
`hexp₁`'s expansion second order rather than first. -/
noncomputable def upperClusterRatioDeriv2 (δ : ℝ) : ℝ := -(2 * Real.cos (Real.pi / 3 - δ))

private theorem hasDerivAt_upperShift (δ : ℝ) :
    HasDerivAt (fun s : ℝ => Real.pi / 3 - s) (-1) δ := by
  simpa using (hasDerivAt_id δ).const_sub (Real.pi / 3)

theorem hasDerivAt_upperClusterRatio (δ : ℝ) :
    HasDerivAt upperClusterRatio (upperClusterRatioDeriv δ) δ :=
  ((((Real.hasDerivAt_cos _).comp δ (hasDerivAt_upperShift δ))).const_mul 2).congr_deriv (by
    rw [upperClusterRatioDeriv]; ring)

theorem hasDerivAt_upperClusterRatioDeriv (δ : ℝ) :
    HasDerivAt upperClusterRatioDeriv (upperClusterRatioDeriv2 δ) δ :=
  ((((Real.hasDerivAt_sin _).comp δ (hasDerivAt_upperShift δ))).const_mul 2).congr_deriv (by
    rw [upperClusterRatioDeriv2]; ring)

/-- `|f''| ≤ 2` everywhere, since `f'' = -2cos`. -/
theorem abs_upperClusterRatioDeriv2_le (δ : ℝ) : |upperClusterRatioDeriv2 δ| ≤ 2 := by
  rw [upperClusterRatioDeriv2, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have := Real.abs_cos_le_one (Real.pi / 3 - δ)
  linarith

/-- The endpoint values: `f(0) = 1` and `f'(0) = √3`, which is
`(cos(π/3) - Re ω₂)/sin(π/3)` at `ω₂ = -1` — the same coefficient as the lower
endpoint, because `ρ = r = 3` at both. -/
theorem upperClusterRatio_zero : upperClusterRatio 0 = 1 := by
  rw [upperClusterRatio, sub_zero, Real.cos_pi_div_three]; norm_num

theorem upperClusterRatioDeriv_zero : upperClusterRatioDeriv 0 = Real.sqrt 3 := by
  rw [upperClusterRatioDeriv, sub_zero, Real.sin_pi_div_three]; ring

/-- **`hexp₁`'s inequality at the witness.**  A second-order Taylor bound on
`2cos(π/3 - δ)`, off `phase_taylor_bound` — the mean value theorem twice, the
same lemma the lower witness and the strong clock both run on. -/
theorem upperCluster_taylor {e₁ : ℝ} (he₁ : 0 < e₁) {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e₁) :
    |upperClusterRatio δ - upperClusterRatio 0 - upperClusterRatioDeriv 0 * δ|
      ≤ 2 * δ ^ 2 := by
  have h := phase_taylor_bound (ψ := upperClusterRatio) (dψ := upperClusterRatioDeriv)
    (ddψ := upperClusterRatioDeriv2) (a := 0) (b := e₁) (κ₂ := 2)
    (fun θ _ => hasDerivAt_upperClusterRatio θ)
    (fun θ _ => hasDerivAt_upperClusterRatioDeriv θ)
    (fun θ _ => abs_upperClusterRatioDeriv2_le θ)
    ⟨le_rfl, he₁.le⟩ ⟨hδ.le, hδe⟩ hδ.le
  simpa using h

/-- **`hexp₁` in the binder's own shape**, with the coefficient written as
`weighted_dominance_of_branch` writes it — `(cos(π/r) - Re(clusterOmega r (idx₁ i)))/sin(π/r)`
at `r = 3` and `idx₁ i = 2`.

`clusterOmega_three_two` is what pins the index: the principal directions
`j = 1, 3` are nonreal, and landing on one would leave `hexp₁` true with the
linear term wrong. -/
theorem upperCluster_hexp {e₁ : ℝ} (he₁ : 0 < e₁) (_i : Fin 1)
    {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e₁) :
    |upperClusterRatio δ
        - (1 + ((Real.cos (Real.pi / (3 : ℕ)) - (clusterOmega 3 2).re)
            / Real.sin (Real.pi / (3 : ℕ))) * δ)| ≤ 2 * δ ^ 2 := by
  have hc : ((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) - (clusterOmega 3 2).re)
      / Real.sin (Real.pi / ((3 : ℕ) : ℝ))) = Real.sqrt 3 := by
    rw [clusterOmega_three_two]
    norm_num
    rw [div_eq_iff (by positivity)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h := upperCluster_taylor he₁ hδ hδe
  rw [upperClusterRatio_zero, upperClusterRatioDeriv_zero] at h
  rw [hc, show upperClusterRatio δ - (1 + Real.sqrt 3 * δ)
      = upperClusterRatio δ - 1 - Real.sqrt 3 * δ by ring]
  exact h

/-- **The upper cluster's expansion block at the witness.**  `hexp₁` on one `e₁`,
with the constant produced.

The set-theoretic binders are not here: `upperWitness_cluster_block` carries
`hginj₁`, `hgmem₁` and `hgcard₁` alongside `hexp₁` on one window.

The `Fin 1` binder is `hexp₁`'s own shape at `n₁ = 1` rather than a spare: the
consumer quantifies over `Fin n₁` and indexes the direction by `idx₁ i`.  This
pencil has one nonprincipal member and its direction is `clusterOmega 3 2`
outright, so the body does not mention the index while the clause still has to be
the indexed family. -/
theorem upperWitness_expansion_block :
    ∃ e₁ Cexp₁ : ℝ, 0 < e₁ ∧ 0 ≤ Cexp₁ ∧
      (∀ _i : Fin 1, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        |upperClusterRatio δ
            - (1 + ((Real.cos (Real.pi / (3 : ℕ)) - (clusterOmega 3 2).re)
                / Real.sin (Real.pi / (3 : ℕ))) * δ)| ≤ Cexp₁ * δ ^ 2) := by
  refine ⟨1, 2, one_pos, by norm_num, fun i δ hδ hδe => ?_⟩
  exact upperCluster_hexp one_pos i hδ hδe

/-! ### The upper retained set

Vieta makes the whole set algebraic in `cos θ`.  `τ sin2θ = sin3θ` with
`sin3θ = sinθ(4cos²θ - 1)` and `sin2θ = 2 sinθ cosθ` gives

`τ(θ) = (4cos²θ - 1)/(2cos θ)`,

and the third zero is `-2τcos θ = 1 - 4cos²θ` — a polynomial in `cos θ`, with no
square root and nothing transcendental left.  The principal pair is `τe^{±iθ}`.

**The two endpoint expansion binders differ in shape, and this is a fact about
the theorem rather than about the route here.**  `hexp₀` bounds a *complex*
difference `‖g₀/τ - (1 + cδ)‖`; `hexp₁` bounds `|‖g₁/τ‖ - (1 + cδ)|`, taking the
modulus first.  At the upper endpoint the normalized nonprincipal member tends to
`-1`, so the complex form would be *false* here while the modulus form is true —
building the upper block by symmetry with the lower one proves a false statement,
not a vacuous one. -/

theorem cos_gt_half {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    1 / 2 < Real.cos θ := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le (by linarith [Real.pi_pos]) hθ.2
  rwa [Real.cos_pi_div_three] at h

/-- `τ` in algebraic form on the open arc: no sine survives. -/
theorem upperTau_eq {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    upperTau θ = (4 * Real.cos θ ^ 2 - 1) / (2 * Real.cos θ) := by
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) (cos_gt_half hθ)
  have hs : (0 : ℝ) < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
  have h3 : Real.sin (3 * θ) = Real.sin θ * (4 * Real.cos θ ^ 2 - 1) := by
    rw [Real.sin_three_mul]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]
  have h2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  rw [upperTau, h3, h2]
  field_simp

theorem upperTau_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) : 0 < upperTau θ := by
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) (cos_gt_half hθ)
  have hh := cos_gt_half hθ
  rw [upperTau_eq hθ]
  apply div_pos _ (by linarith)
  nlinarith [hh, hc]

/-- The nonprincipal zero, `1 - 4cos²θ`. -/
noncomputable def upperThird (θ : ℝ) : ℝ := 1 - 4 * Real.cos θ ^ 2

theorem upperThird_neg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) : upperThird θ < 0 := by
  have hh := cos_gt_half hθ
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) hh
  rw [upperThird]; nlinarith [hh, hc]

/-- The principal zero `τe^{iθ}`. -/
noncomputable def upperPrincipal (θ : ℝ) : ℂ :=
  ((upperTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)

theorem upperPrincipal_im {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    0 < (upperPrincipal θ).im := by
  have hs : (0 : ℝ) < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
  have hτ := upperTau_pos hθ
  rw [upperPrincipal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
  have : upperTau θ * Real.sin θ + 0 * Real.cos θ = upperTau θ * Real.sin θ := by ring
  rw [this]
  positivity

/-- The retained set at the upper endpoint: the principal pair and the third
zero.  Three members, because `deg D = 3`. -/
noncomputable def upperRootSet (θ : ℝ) : Finset ℂ :=
  {upperPrincipal θ, (starRingEnd ℂ) (upperPrincipal θ), ((upperThird θ : ℝ) : ℂ)}

theorem card_upperRootSet {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    (upperRootSet θ).card = 3 := by
  classical
  have him := upperPrincipal_im hθ
  have hne1 : upperPrincipal θ ≠ (starRingEnd ℂ) (upperPrincipal θ) := by
    intro h
    have : (upperPrincipal θ).im = -(upperPrincipal θ).im := by
      conv_lhs => rw [h]
      simp
    linarith
  have hne2 : upperPrincipal θ ≠ ((upperThird θ : ℝ) : ℂ) := by
    intro h
    have : (upperPrincipal θ).im = 0 := by rw [h]; simp
    linarith
  have hne3 : (starRingEnd ℂ) (upperPrincipal θ) ≠ ((upperThird θ : ℝ) : ℂ) := by
    intro h
    have : (-(upperPrincipal θ).im) = 0 := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  rw [upperRootSet]
  rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]),
    Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]

/-- Erasing the principal pair leaves the third zero alone: `n₁ = 1`, as a Lean
`card` clause rather than a counting observation. -/
theorem upperRootSet_erase_pair {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    ((upperRootSet θ).erase (upperPrincipal θ)).erase
        ((starRingEnd ℂ) (upperPrincipal θ))
      = {((upperThird θ : ℝ) : ℂ)} := by
  classical
  have him := upperPrincipal_im hθ
  have hne2 : ((upperThird θ : ℝ) : ℂ) ≠ upperPrincipal θ := by
    intro h
    have : (upperPrincipal θ).im = 0 := by rw [← h]; simp
    linarith
  have hne3 : ((upperThird θ : ℝ) : ℂ) ≠ (starRingEnd ℂ) (upperPrincipal θ) := by
    intro h
    have : (-(upperPrincipal θ).im) = 0 := by
      have := congrArg Complex.im h.symm
      simpa using this
    linarith
  ext w
  simp only [Finset.mem_erase, upperRootSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hp, h | h | h⟩
    · exact absurd h hp
    · exact absurd h hc
    · exact h
  · rintro rfl
    exact ⟨hne3, hne2, by tauto⟩

/-- The enumeration of the nonprincipal cluster, over `Fin 1`. -/
noncomputable def upperNonprincipal (θ : ℝ) : Fin 1 → ℂ :=
  fun _ => ((upperThird θ : ℝ) : ℂ)

/-- The signed ratio: `(1 - 4cos²θ)/τ = -2cos θ`, negative because the third
zero is. -/
theorem upperThird_div_upperTau {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    upperThird θ / upperTau θ = -(2 * Real.cos θ) := by
  have hh := cos_gt_half hθ
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) hh
  have hne : 4 * Real.cos θ ^ 2 - 1 ≠ 0 := by nlinarith
  rw [upperThird, upperTau_eq hθ]
  field

/-- `‖g₁/τ‖ = 2cos θ`, which is `upperClusterRatio` at `θ = π/3 - δ`.  This is
where the modulus in `hexp₁`'s shape does its work: the third zero is negative,
so the signed ratio is `-2cos θ` and only its modulus matches `1 + cδ`. -/
theorem norm_upperNonprincipal_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (i : Fin 1) :
    ‖upperNonprincipal θ i / ((upperTau θ : ℝ) : ℂ)‖ = 2 * Real.cos θ := by
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) (cos_gt_half hθ)
  have hτ := upperTau_pos hθ
  rw [upperNonprincipal, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    upperThird_div_upperTau hθ, abs_neg,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.cos θ)]

/-! ### The upper binders on one window -/

/-- `hωne₁`: the cluster direction is not the upper principal one. -/
theorem clusterOmega_three_two_ne_principal :
    clusterOmega 3 2 ≠ Complex.exp (((Real.pi / ((3 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
  intro h
  have hre := congrArg Complex.re h
  rw [clusterOmega_three_two] at hre
  simp only [Complex.neg_re, Complex.one_re, Complex.exp_ofReal_mul_I_re] at hre
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, Real.cos_pi_div_three] at hre
  norm_num at hre

/-- `hωne'₁`: nor its conjugate. -/
theorem clusterOmega_three_two_ne_principal_conj :
    clusterOmega 3 2
      ≠ Complex.exp (((-(Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  intro h
  have hre := congrArg Complex.re h
  rw [clusterOmega_three_two] at hre
  simp only [Complex.neg_re, Complex.one_re, Complex.exp_ofReal_mul_I_re] at hre
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, Real.cos_neg, Real.cos_pi_div_three] at hre
  norm_num at hre

/-- `t_+` at this pencil is `ftPrincipal`'s value. -/
theorem upperPrincipal_eq_ftPrincipal (θ : ℝ) :
    upperPrincipal θ = ftPrincipal upperTau θ := rfl

/-- The conjugate member in the binder's own form, `τe^{-iθ}`. -/
theorem conj_upperPrincipal (θ : ℝ) :
    (starRingEnd ℂ) (upperPrincipal θ)
      = ((upperTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  rw [upperPrincipal, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp

/-- `‖g₁/τ‖` at `θ = π/3 - δ` is exactly the scalar `upperClusterRatio` expands. -/
theorem norm_upperNonprincipal_div_shift {e₁ : ℝ} (he₁ : e₁ < Real.pi / 3)
    {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e₁) (i : Fin 1) :
    ‖upperNonprincipal (Real.pi / 3 - δ) i
        / ((upperTau (Real.pi / 3 - δ) : ℝ) : ℂ)‖ = upperClusterRatio δ := by
  have hθ : Real.pi / 3 - δ ∈ Set.Ioo 0 (Real.pi / 3) :=
    ⟨by linarith, by linarith⟩
  rw [norm_upperNonprincipal_div hθ i, upperClusterRatio]

/-- **The upper cluster block at the witness: `hωne₁`, `hωne'₁`, `hginj₁`,
`hgmem₁`, `hgcard₁` and `hexp₁` together.**

The window is what joins them.  `hgmem₁` and `hgcard₁` need `θ = π/3 - δ` inside
the open arc, `hexp₁` needs the same `δ` range for its Taylor bound, and the
`e₁ < π/3` clause is where that single requirement is discharged once rather
than six times.  Six binders on six windows prove six things.

The two `clusterOmega` clauses carry no `δ`, and they are here rather than
separately because they are what pins the index: `idx₁ i = 2` sends the binders
to `ω₂ = -1`, and at either principal index `hexp₁` would still be *true* with
the linear term wrong. -/
theorem upperWitness_cluster_block :
    ∃ e₁ Cexp₁ : ℝ, 0 < e₁ ∧ e₁ < Real.pi / 3 ∧ 0 ≤ Cexp₁ ∧
      (∀ _i : Fin 1, clusterOmega 3 2
        ≠ Complex.exp (((Real.pi / ((3 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) ∧
      (∀ _i : Fin 1, clusterOmega 3 2
        ≠ Complex.exp (((-(Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        Function.Injective (upperNonprincipal (Real.pi / 3 - δ))) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i : Fin 1,
        upperNonprincipal (Real.pi / 3 - δ) i ∈
          ((upperRootSet (Real.pi / 3 - δ)).erase
              (ftPrincipal upperTau (Real.pi / 3 - δ))).erase
            (((upperTau (Real.pi / 3 - δ) : ℝ) : ℂ)
              * Complex.exp (-((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I))) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        (((upperRootSet (Real.pi / 3 - δ)).erase
            (ftPrincipal upperTau (Real.pi / 3 - δ))).erase
          (((upperTau (Real.pi / 3 - δ) : ℝ) : ℂ)
            * Complex.exp (-((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I))).card = 1) ∧
      (∀ i : Fin 1, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        |‖upperNonprincipal (Real.pi / 3 - δ) i
              / ((upperTau (Real.pi / 3 - δ) : ℝ) : ℂ)‖
            - (1 + ((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) - (clusterOmega 3 2).re)
                / Real.sin (Real.pi / ((3 : ℕ) : ℝ))) * δ)| ≤ Cexp₁ * δ ^ 2) := by
  have he₁ : (1 : ℝ) < Real.pi / 3 := by linarith [Real.pi_gt_three]
  refine ⟨1, 2, one_pos, he₁, by norm_num,
    fun _ => clusterOmega_three_two_ne_principal,
    fun _ => clusterOmega_three_two_ne_principal_conj, ?_, ?_, ?_, ?_⟩
  · intro δ _ _ a b _
    exact Subsingleton.elim a b
  · intro δ hδ hδe i
    have hθ : Real.pi / 3 - δ ∈ Set.Ioo 0 (Real.pi / 3) := ⟨by linarith, by linarith⟩
    rw [← upperPrincipal_eq_ftPrincipal, ← conj_upperPrincipal,
      upperRootSet_erase_pair hθ, Finset.mem_singleton]
    rfl
  · intro δ hδ hδe
    have hθ : Real.pi / 3 - δ ∈ Set.Ioo 0 (Real.pi / 3) := ⟨by linarith, by linarith⟩
    rw [← upperPrincipal_eq_ftPrincipal, ← conj_upperPrincipal,
      upperRootSet_erase_pair hθ, Finset.card_singleton]
  · intro i δ hδ hδe
    rw [norm_upperNonprincipal_div_shift he₁ hδ hδe i]
    exact upperCluster_hexp one_pos i hδ hδe

/-! ### Anchoring the retained set to the pencil

`upperRootSet` is a *definition*, and on its own the four binders above are met
by any three-element `Finset` of that shape.  What makes it the pencil's own
retained set are `hroot₁` and `huniq₁`, which tie `sfun₁` to `ftDen`, and they
come from one factorization.

Vieta's product relation fixes the spectral parameter: `t₊t₋t₃ = -1/z` with
`t₊t₋ = τ²` and `t₃ = -2τcos θ` gives `z = 1/(2τ³cos θ)`, and then

`1 - t + zt³ = z(t - t₊)(t - t₋)(t - t₃)`

is an identity, checked in `scripts/check_upper_cluster_witness.py`.  `huniq₁`
needs no modulus bound at all once it is available — the product is zero exactly
when a factor is, since `z ≠ 0`. -/

/-- The spectral parameter along this branch, `z = 1/(2τ³cos θ)`. -/
noncomputable def upperZ (θ : ℝ) : ℝ := 1 / (2 * upperTau θ ^ 3 * Real.cos θ)

theorem upperZ_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) : 0 < upperZ θ := by
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) (cos_gt_half hθ)
  have hτ := upperTau_pos hθ
  rw [upperZ]; positivity

/-- The third zero as minus the principal pair's sum: `1 - 4cos²θ = -2τcos θ`.
The cubic has no `t²` term, so the three zeros sum to zero. -/
theorem upperThird_eq_neg_sum {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    upperThird θ = -(2 * upperTau θ * Real.cos θ) := by
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) (cos_gt_half hθ)
  rw [upperThird, upperTau_eq hθ]
  field

/-- Vieta's product relation in the form the factorization consumes. -/
theorem upperZ_mul_prod {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    upperZ θ * upperTau θ ^ 2 * (2 * upperTau θ * Real.cos θ) = 1 := by
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) (cos_gt_half hθ)
  have hτ := upperTau_pos hθ
  rw [upperZ]
  field_simp

theorem upperPrincipal_add_conj (θ : ℝ) :
    upperPrincipal θ + (starRingEnd ℂ) (upperPrincipal θ)
      = ((2 * upperTau θ * Real.cos θ : ℝ) : ℂ) := by
  rw [conj_upperPrincipal, upperPrincipal, ← mul_add]
  rw [show Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)
      = 2 * Complex.cos ((θ : ℝ) : ℂ) from (Complex.two_cos _).symm]
  rw [← Complex.ofReal_cos]
  push_cast
  ring

theorem upperPrincipal_mul_conj (θ : ℝ) :
    upperPrincipal θ * (starRingEnd ℂ) (upperPrincipal θ)
      = ((upperTau θ ^ 2 : ℝ) : ℂ) := by
  rw [conj_upperPrincipal, upperPrincipal]
  rw [show ((upperTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
        * (((upperTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I))
      = ((upperTau θ : ℝ) : ℂ) * ((upperTau θ : ℝ) : ℂ)
        * (Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
            * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) by ring]
  rw [← Complex.exp_add,
    show ((θ : ℝ) : ℂ) * Complex.I + -((θ : ℝ) : ℂ) * Complex.I = 0 by ring,
    Complex.exp_zero]
  push_cast
  ring

/-- **The pencil factors over the retained set.**  `Q = 1 - t`, `r = 3`,
`z = upperZ θ`. -/
theorem upperDen_eval {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) (t : ℂ) :
    (ftDen upperQ 3 ((upperZ θ : ℝ) : ℂ)).eval t
      = ((upperZ θ : ℝ) : ℂ) * (t - upperPrincipal θ)
          * (t - (starRingEnd ℂ) (upperPrincipal θ))
          * (t - ((upperThird θ : ℝ) : ℂ)) := by
  have hs := upperPrincipal_add_conj θ
  have hp := upperPrincipal_mul_conj θ
  have h3 : ((upperThird θ : ℝ) : ℂ) = -((2 * upperTau θ * Real.cos θ : ℝ) : ℂ) := by
    rw [upperThird_eq_neg_sum hθ]; push_cast; ring
  have hz : ((upperZ θ : ℝ) : ℂ) * ((upperTau θ ^ 2 : ℝ) : ℂ)
      * ((2 * upperTau θ * Real.cos θ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, upperZ_mul_prod hθ]
    norm_num
  have hexpand : ((upperZ θ : ℝ) : ℂ) * (t - upperPrincipal θ)
        * (t - (starRingEnd ℂ) (upperPrincipal θ))
        * (t - ((upperThird θ : ℝ) : ℂ))
      = ((upperZ θ : ℝ) : ℂ) * t ^ 3
        - ((upperZ θ : ℝ) : ℂ)
            * (upperPrincipal θ + (starRingEnd ℂ) (upperPrincipal θ)
                + ((upperThird θ : ℝ) : ℂ)) * t ^ 2
        + ((upperZ θ : ℝ) : ℂ)
            * (upperPrincipal θ * (starRingEnd ℂ) (upperPrincipal θ)
                + (upperPrincipal θ + (starRingEnd ℂ) (upperPrincipal θ))
                    * ((upperThird θ : ℝ) : ℂ)) * t
        - ((upperZ θ : ℝ) : ℂ) * (upperPrincipal θ
            * (starRingEnd ℂ) (upperPrincipal θ) * ((upperThird θ : ℝ) : ℂ)) := by
    ring
  have hvr : upperTau θ ^ 2 - (2 * upperTau θ * Real.cos θ) ^ 2
      = -(upperTau θ ^ 2 * (2 * upperTau θ * Real.cos θ)) := by
    have h := upperThird_eq_neg_sum hθ
    rw [upperThird] at h
    linear_combination (upperTau θ ^ 2) * h
  have hv : ((upperTau θ ^ 2 : ℝ) : ℂ) - ((2 * upperTau θ * Real.cos θ : ℝ) : ℂ) ^ 2
      = -(((upperTau θ ^ 2 : ℝ) : ℂ) * ((2 * upperTau θ * Real.cos θ : ℝ) : ℂ)) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hvr
  rw [hexpand, hs, hp, h3, ftDen_eval, upperQ]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  linear_combination (-(((upperZ θ : ℝ) : ℂ) * t)) * hv + (t - 1) * hz

/-- **`hroot₁` and `huniq₁` together**: the pencil's zeros are exactly the
retained set, with no modulus bound needed on either side.  `huniq₁` asks only
for the forward direction, and it is available for every `t` because a product
vanishes exactly when a factor does. -/
theorem upperDen_eval_eq_zero_iff {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (t : ℂ) :
    (ftDen upperQ 3 ((upperZ θ : ℝ) : ℂ)).eval t = 0 ↔ t ∈ upperRootSet θ := by
  have hz : ((upperZ θ : ℝ) : ℂ) ≠ 0 := by
    have := upperZ_pos hθ
    simpa using this.ne'
  rw [upperDen_eval hθ t, upperRootSet]
  simp only [Finset.mem_insert, Finset.mem_singleton, mul_eq_zero, hz, false_or,
    sub_eq_zero]
  tauto

theorem upperDen_eval_zero_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    {a : ℂ} (ha : a ∈ upperRootSet θ) :
    (ftDen upperQ 3 ((upperZ θ : ℝ) : ℂ)).eval a = 0 :=
  (upperDen_eval_eq_zero_iff hθ a).mpr ha

/-- **`haR₁`**: one fixed radius holds the whole retained set over the whole arc.
`‖t₃‖ = 4cos²θ - 1` is the larger of the two moduli and it approaches `3` as
`θ → 0`, so `τmax` is not a radius for this set. -/
theorem norm_lt_four_of_mem_upperRootSet {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) {a : ℂ} (ha : a ∈ upperRootSet θ) :
    ‖a‖ < 4 := by
  have hh := cos_gt_half hθ
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) hh
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hτ := upperTau_pos hθ
  have hτle : upperTau θ < 4 := by
    rw [upperTau_eq hθ]
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [hc, hc1]
  have hnp : ‖upperPrincipal θ‖ = upperTau θ := by
    rw [upperPrincipal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτ, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [upperRootSet] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · rw [hnp]; exact hτle
  · rw [RCLike.norm_conj, hnp]; exact hτle
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (upperThird_neg hθ),
      upperThird]
    nlinarith [hc, hc1]

theorem upperDen_deriv_eval (θ : ℝ) (t : ℂ) :
    (derivative (ftDen upperQ 3 ((upperZ θ : ℝ) : ℂ))).eval t
      = -1 + 3 * ((upperZ θ : ℝ) : ℂ) * t ^ 2 := by
  rw [ftDen, upperQ]
  simp
  ring

/-- **`hsimple₁`**: every retained zero is simple, by two different mechanisms.
The third zero is real and `D'` there is `6cos θ/τ - 1`, positive because
`τ < 6cos θ` on the arc; the principal pair is caught by its imaginary part,
`±3zτ²sin 2θ`, which is nonzero because `2θ ∈ (0, 2π/3)`. -/
theorem upperDen_deriv_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    {a : ℂ} (ha : a ∈ upperRootSet θ) :
    (derivative (ftDen upperQ 3 ((upperZ θ : ℝ) : ℂ))).eval a ≠ 0 := by
  have hh := cos_gt_half hθ
  have hc : (0 : ℝ) < Real.cos θ := lt_trans (by norm_num) hh
  have hτ := upperTau_pos hθ
  have hz := upperZ_pos hθ
  have hs2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [Real.pi_pos, hθ.2])
  -- the principal pair, by the imaginary part
  have hpair : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      ((-1 : ℂ) + 3 * ((upperZ θ : ℝ) : ℂ)
        * (((upperTau θ : ℝ) : ℂ) * Complex.exp (((ε * θ : ℝ) : ℂ) * Complex.I)) ^ 2).im
      = ε * (3 * upperZ θ * upperTau θ ^ 2 * Real.sin (2 * θ)) := by
    intro ε hε
    have hsin : Real.sin (2 * (ε * θ)) = ε * Real.sin (2 * θ) := by
      rcases hε with rfl | rfl
      · norm_num
      · rw [show 2 * ((-1 : ℝ) * θ) = -(2 * θ) by ring, Real.sin_neg]; ring
    have h2 : 2 * Real.sin (ε * θ) * Real.cos (ε * θ) = ε * Real.sin (2 * θ) := by
      rw [← Real.sin_two_mul, hsin]
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.neg_im, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    linear_combination (3 * upperZ θ * upperTau θ ^ 2) * h2
  rw [upperDen_deriv_eval]
  rw [upperRootSet] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  have hpos : 0 < 3 * upperZ θ * upperTau θ ^ 2 * Real.sin (2 * θ) := by positivity
  rcases ha with rfl | rfl | rfl
  · intro h
    have := congrArg Complex.im h
    rw [upperPrincipal, show ((θ : ℝ) : ℂ) = (((1 : ℝ) * θ : ℝ) : ℂ) by norm_num] at this
    rw [hpair 1 (Or.inl rfl)] at this
    simp only [one_mul, zero_im, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ne_eq,
      not_false_eq_true, pow_eq_zero_iff] at this
    rcases this with (h' | h') | h' <;> linarith
  · intro h
    have := congrArg Complex.im h
    rw [conj_upperPrincipal,
      show -((θ : ℝ) : ℂ) = ((((-1 : ℝ)) * θ : ℝ) : ℂ) by push_cast; ring] at this
    rw [hpair (-1) (Or.inr rfl)] at this
    simp only [neg_mul, one_mul, zero_im, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
      false_or, ne_eq, not_false_eq_true, pow_eq_zero_iff] at this
    rcases this with (h' | h') | h' <;> linarith
  · -- the third zero is real: `3z t₃² = 6cos θ/τ > 1`
    have h6 : upperTau θ < 6 * Real.cos θ := by
      rw [upperTau_eq hθ, div_lt_iff₀ (by linarith)]
      nlinarith [hc, hh]
    have hsq : upperThird θ ^ 2 = 4 * upperTau θ ^ 2 * Real.cos θ ^ 2 := by
      rw [upperThird_eq_neg_sum hθ]; ring
    have hid : 3 * upperZ θ * upperThird θ ^ 2 = 6 * Real.cos θ / upperTau θ := by
      rw [hsq, upperZ]
      field
    have hgt : 1 < 3 * upperZ θ * upperThird θ ^ 2 := by
      rw [hid, lt_div_iff₀ hτ]
      linarith
    intro h
    rw [show (-1 : ℂ) + 3 * ((upperZ θ : ℝ) : ℂ) * ((upperThird θ : ℝ) : ℂ) ^ 2
        = ((3 * upperZ θ * upperThird θ ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_eq_zero] at h
    linarith

/-- **`hrootplus₁`**: the principal point is a zero of the pencil. -/
theorem upperDen_eval_principal {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    (ftDen upperQ 3 ((upperZ θ : ℝ) : ℂ)).eval (ftPrincipal upperTau θ) = 0 := by
  rw [← upperPrincipal_eq_ftPrincipal]
  exact upperDen_eval_zero_of_mem hθ (by rw [upperRootSet]; simp)

/-- **`hne₁`**: the principal point is not its own conjugate, because
`Im t₊ = τ sin θ > 0`. -/
theorem upperPrincipal_ne_conj {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    ftPrincipal upperTau θ
      ≠ ((upperTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  rw [← upperPrincipal_eq_ftPrincipal, ← conj_upperPrincipal]
  intro h
  have him := upperPrincipal_im hθ
  have : (upperPrincipal θ).im = -(upperPrincipal θ).im := by
    conv_lhs => rw [h]
    simp
  linarith

end ForgacsTran
