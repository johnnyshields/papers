/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchZRate

/-!
# The upper endpoint of the arc

Prop. 3 Case 3 needs the branch at `θ → (π/r)⁻`.  The behaviour there is a
**dichotomy in `r`**, and only one side of it is proved here.

## Main statements

* `tendsto_ftTau_nhdsLT_upper` — for `r ≥ 2` the radius collapses, `τ(θ) → 0`.
* `tendsto_pow_mul_ftBranchZ_nhdsLT_upper` — hence `τ(θ)^r · z(θ) → c·∏ a k`,
  which is the exact relation `t^r = -Q(t)/z` read at the endpoint.
* `tendsto_ftTau_div_nhdsLT_upper` — the *rate* of that collapse,
  `τ(θ)/(π/r - θ) → r/(sin(π/r)·∑ 1/a_k)`.  The `∑ 1/a_k` is load-bearing: the
  member expansion's coefficient is free of the pencil only because this factor
  cancels against the `∑ 1/a_k` in `Q(t)/Q(0) = 1 - t∑1/a_k + O(t²)`.  A pencil
  with `∑ 1/a_k = 1` cannot distinguish this from `r/sin(π/r)`.
* `exists_bound_ftTau_upper` — the pointwise second-order form of that rate,
  `|τ(π/r - δ) - mδ| ≤ Cδ²`.

The estimate rests on four comparisons of the chord `a_k - τ cos θ` with its
endpoint value `a_k`, each stated on its own and each holding on the one window
`τ ≤ a_k/2`:

* `chord_mem_Icc`, `chord_pos` — `a/2 ≤ a - τ cos θ ≤ 3a/2`, whatever `θ` is.
* `sum_inv_chord_mem_Icc` — the chord-reciprocal sum stays between `2/3` and `2`
  times the endpoint sum, which is what keeps the angle-count coefficient away
  from `0`.
* `abs_inv_chord_sub_inv_le`, `abs_sum_inv_chord_sub_sum_inv_le` — that sum moves
  by at most `2τ·∑(a_k⁻¹)²` off its endpoint value, and
  `abs_sin_mul_sum_inv_chord_sub_le` carries the sine factor along with it.
* `ftArccot_arg_pos`, `inv_ftArccot_arg_le`, `abs_sum_ftArccot_err_le` — the
  complement errors are `O(τ³)` with a pencil-free constant, which is what makes
  the rate second order rather than first.
* `abs_sub_linear_le_of_perturbed_relation` — the algebra those two bounds meet
  in: from `τG + E = mδg₀` with `G` bounded below, a linear bound on `G - g₀`
  and a quadratic one on `E` force `τ - mδ = O(δ²)`.

## Implementation notes

`tendsto_arctan_div_nhdsNE_zero` and `tendsto_ftArccot_mul_atTop` are
Mathlib-level and carry nothing specific to this paper; the same holds for
`tendsto_sin_div_nhdsGT_zero` and `tendsto_one_sub_cos_div_sq_nhdsGT_zero` in
`FTBranchZRate`.  Any of the four is reusable as it stands.

**At `r = 1` the collapse does not happen, and the `r ≥ 2` statement is FALSE
there — not merely unproved.**  The endpoint is `θ = π`, where `sin θ` is no
longer bounded below and the mechanism of the argument is simply absent; the
radius tends to a finite positive limit instead of to `0`, measured at
`0.8793852416` for `Q(t) = (1-t)(2-t)(3-t)`, with `|z| → 23.8726`, both finite.
So `r = 1` is **handled and different**, not unhandled: the hypothesis `2 ≤ r`
excludes it because it must, and no later pass should read the exclusion as a
gap to be closed.

This is **not** the `cos(π/r) = 0` mechanism recorded in `banked.txt` BANK-35,
which is `r = 2` and only `r = 2`.  Here `cos π = -1`, as far from vanishing as
a cosine gets, and it is the sine that goes.  Different quantity, different
vanishing, different consequence — an order gain there, no collapse at all
here.

**Differs from the paper's route.**  `Forgacs2017RationalDenominator` reaches the
endpoint through the critical polynomial.  The collapse is proved here from the
angle count alone: every angle is below `π`, so the sum `∑ θ_k` is below `nπ`
by a margin that a *fixed* radius cannot give up, while the branch equation
forces the sum to `rθ + (n-1)π → nπ`.  The radius therefore cannot stay bounded
away from `0`.  No derivative and no critical point enters.

A note on tactics, since it cost a pass.  Inside `exists_bound_ftTau_upper` the
context carries a dozen sums and constants, and there `linarith`'s Gauss phase
times out at the default heartbeat budget on goals as trivial as
`τ·|cos θ| ≤ τ`.  Every step in that estimate is a deterministic `calc` for that
reason; raising `maxHeartbeats` buys a slower failure rather than a proof, since
the search space and not the budget is what grows.

The convergence order at this endpoint is **not uniform in `r`**: `cos(π/2) = 0`
kills the cross term `-2a_kτcos θ`, so `r = 2` is one order better than `r ≥ 3`.
`banked.txt` BANK-35 records the mechanism and the three checks that met it.

Sorry-free.

## Tags

upper endpoint, branch radius, collapse rate
-/

namespace ForgacsTran

open Real Set Filter Topology

/-- **The radius collapses at the upper endpoint, for `r ≥ 2`.**  `r = 1` is
excluded and is false there; see the module header. -/
theorem tendsto_ftTau_nhdsLT_upper_of_pos {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    Tendsto (ftTau a r (n - 1)) (𝓝[<] (π / r)) (𝓝 0) := by
  classical
  have hπ : 0 < π := pi_pos
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hupper : π / r ≤ π / 2 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hhalf0 : 0 < π / (2 * r) := by positivity
  have hhalflt : π / (2 * r) < π / r := by
    rw [div_lt_div_iff₀ (by positivity) hr0]; nlinarith
  have hs₀ : 0 < Real.sin (π / (2 * r)) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf0 (by linarith [hupper])
  -- the arc membership every θ in the window enjoys
  have harc : ∀ θ ∈ Ioo (π / (2 * r)) (π / r), θ ∈ Ioo 0 (π / r) := fun θ hθ =>
    ⟨lt_trans hhalf0 hθ.1, hθ.2⟩
  refine tendsto_order.2 ⟨fun b hb => ?_, fun δ hδ => ?_⟩
  · filter_upwards [Ioo_mem_nhdsLT hhalflt] with θ hθ
    exact lt_trans hb (ftTau_pos (ftBranchAt_of_arc_principal hn ha hr1 (Or.inr hr) (harc θ hθ)))
  -- the fixed radius `δ` cannot keep the angle sum up
  set M : ℝ := ∑ k, ftArccot ((-1 - a k / δ) / Real.sin (π / (2 * r))) with hM
  have hMlt : M < (n : ℝ) * π := by
    have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin n)))
      (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
      (f := fun k => ftArccot ((-1 - a k / δ) / Real.sin (π / (2 * r))))
      (g := fun _ => π) (fun k _ => (ftArccot_mem_Ioo _).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hlin : Tendsto (fun θ : ℝ => (r : ℝ) * θ + ((n - 1 : ℕ) : ℝ) * π)
      (𝓝[<] (π / r)) (𝓝 ((n : ℝ) * π)) := by
    have hc : Tendsto (fun θ : ℝ => (r : ℝ) * θ + ((n - 1 : ℕ) : ℝ) * π)
        (𝓝 (π / r)) (𝓝 ((r : ℝ) * (π / r) + ((n - 1 : ℕ) : ℝ) * π)) :=
      ((continuous_const.mul continuous_id).add continuous_const).tendsto _
    have heq : (r : ℝ) * (π / r) + ((n - 1 : ℕ) : ℝ) * π = (n : ℝ) * π := by
      rw [Nat.cast_sub (by omega)]
      field
    rw [heq] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  filter_upwards [hlin.eventually (eventually_gt_nhds hMlt), Ioo_mem_nhdsLT hhalflt]
    with θ hMθ hθ
  have hθarc : θ ∈ Ioo 0 (π / r) := harc θ hθ
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr1 hθarc
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr1 (Or.inr hr) hθarc
  have hsin : Real.sin (π / (2 * r)) ≤ Real.sin θ := by
    rcases eq_or_lt_of_le hθ.1.le with h | h
    · rw [h]
    · exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hhalf0])
        (by linarith [hθ.2, hupper]) h).le
  -- every angle at radius `δ` is capped by a constant below `π`
  have hcap : ftAngleSum a δ θ ≤ M := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hsθ : 0 < Real.sin θ := lt_of_lt_of_le hs₀ hsin
    have hN0 : (-1 : ℝ) - a k / δ < 0 := by
      have := div_pos (ha k) hδ; linarith
    have heqA : ftAngle (a k) δ θ = ftArccot ((Real.cos θ - a k / δ) / Real.sin θ) := by
      rw [ftAngle]
      congr 1
      field_simp
    rw [heqA]
    refine ftArccot_strictAnti.antitone ?_
    have hstep : (-1 - a k / δ) / Real.sin (π / (2 * r))
        ≤ (-1 - a k / δ) / Real.sin θ := by
      rw [div_le_div_iff₀ hs₀ hsθ]
      nlinarith
    have hstep2 : (-1 - a k / δ) / Real.sin θ
        ≤ (Real.cos θ - a k / δ) / Real.sin θ := by
      gcongr
      linarith [Real.neg_one_le_cos θ]
    linarith
  by_contra hcon
  rw [not_lt] at hcon
  have hmono : ftAngleSum a (ftTau a r (n - 1) θ) θ ≤ ftAngleSum a δ θ :=
    ftAngleSum_le_of_le hn ha hθπ hδ hcon
  rw [ftAngleSum_ftTau hb] at hmono
  linarith


/-- `tendsto_ftTau_nhdsLT_upper_of_pos` at `2 ≤ n`, the form consumers were
written against.  At `r ≥ 2` the branch exists for every `n ≥ 1`, so the bound on
`n` was never what the collapse consumed. -/
theorem tendsto_ftTau_nhdsLT_upper {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    Tendsto (ftTau a r (n - 1)) (𝓝[<] (π / r)) (𝓝 0) :=
  tendsto_ftTau_nhdsLT_upper_of_pos (by omega) ha hr
/-- With the radius collapsing, every chord tends to its own zero. -/
theorem tendsto_ftChordProd_nhdsLT_upper {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    Tendsto (fun θ => ftChordProd a (ftTau a r (n - 1) θ) θ) (𝓝[<] (π / r))
      (𝓝 (∏ k, a k)) := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hT := tendsto_ftTau_nhdsLT_upper hn2 ha hr
  have hcos : Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[<] (π / r)) (𝓝 (Real.cos (π / r))) :=
    (Real.continuous_cos.tendsto _).mono_left nhdsWithin_le_nhds
  have hchord : ∀ k ∈ (Finset.univ : Finset (Fin n)), Tendsto
      (fun θ => Real.sqrt (a k ^ 2 - 2 * a k * ftTau a r (n - 1) θ * Real.cos θ
        + ftTau a r (n - 1) θ ^ 2)) (𝓝[<] (π / r)) (𝓝 (a k)) := by
    intro k _
    have hin : Tendsto (fun θ => a k ^ 2 - 2 * a k * ftTau a r (n - 1) θ * Real.cos θ
        + ftTau a r (n - 1) θ ^ 2) (𝓝[<] (π / r))
        (𝓝 (a k ^ 2 - 2 * a k * 0 * Real.cos (π / r) + 0 ^ 2)) :=
      (tendsto_const_nhds.sub ((hT.const_mul (2 * a k)).mul hcos)).add (hT.pow 2)
    have heq : a k ^ 2 - 2 * a k * 0 * Real.cos (π / r) + (0 : ℝ) ^ 2 = a k ^ 2 := by ring
    rw [heq] at hin
    have := (Real.continuous_sqrt.tendsto (a k ^ 2)).comp hin
    rwa [Function.comp_def, Real.sqrt_sq (ha k).le] at this
  simpa [ftChordProd] using tendsto_finsetProd Finset.univ hchord

/-- **The endpoint form of `t^r = -Q(t)/z`.**  `τ(θ)^r · z(θ) → c·∏ a k`, the
exact relation read where the radius has collapsed, so `Q(t) → Q(0)`.  The
direction is carried separately: `t = τ e^{-iθ}` and `θ → π/r`, so `t^r` points
along `e^{-iπ} = -1`. -/
theorem tendsto_pow_mul_ftBranchZ_nhdsLT_upper {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) (c : ℝ) :
    Tendsto (fun θ => ftTau a r (n - 1) θ ^ r * ftBranchZ a c r (n - 1) θ)
      (𝓝[<] (π / r)) (𝓝 (c * ∏ k, a k)) := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hr0 : (0 : ℝ) < r := by positivity
  have h := (tendsto_ftChordProd_nhdsLT_upper hn2 ha hr).const_mul c
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (div_pos pi_pos hr0)] with θ hθarc
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr1 hθarc
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr1 (Or.inl hn2) hθarc
  have hTpos : 0 < ftTau a r (n - 1) θ := ftTau_pos hb
  have hpar : Even (n + (n - 1) + 1) := ⟨n, by omega⟩
  rw [ftBranchZ_eq_chordProd ha hpar hθπ hb rfl]
  field_simp

/-- **The complex endpoint form.**  `t(θ)^r · z(θ) → -c·∏ a k`, where
`t = τ e^{-iθ}`.  The sign is the direction: `t^r = τ^r e^{-irθ}` and
`rθ → π`, so `t^r` arrives along `e^{-iπ} = -1`.  This is `t^r = -Q(0)/z`
with both sides in hand, and it is the form the rescaled cluster consumes —
the `r`th roots of `-Q(0)/z` are the `r`th roots of `-1` scaled. -/
theorem tendsto_ftArcPoint_pow_mul_ftBranchZ_nhdsLT_upper {n r : ℕ} {a : Fin n → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) (c : ℝ) :
    Tendsto (fun θ => ftArcPoint (ftTau a r (n - 1) θ) θ ^ r
        * ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))
      (𝓝[<] (π / r)) (𝓝 (-((c * ∏ k, a k : ℝ) : ℂ))) := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hr0 : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have h1 : Tendsto
      (fun θ : ℝ => ((ftTau a r (n - 1) θ ^ r * ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))
      (𝓝[<] (π / r)) (𝓝 (((c * ∏ k, a k : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.tendsto _).comp
      (tendsto_pow_mul_ftBranchZ_nhdsLT_upper hn2 ha hr c)
  have hlin : Tendsto (fun θ : ℝ => ((r : ℝ) * θ : ℝ)) (𝓝[<] (π / r)) (𝓝 π) := by
    have hc : Tendsto (fun θ : ℝ => (r : ℝ) * θ) (𝓝 (π / r)) (𝓝 ((r : ℝ) * (π / r))) :=
      (continuous_const.mul continuous_id).tendsto _
    rw [show (r : ℝ) * (π / r) = π by field_simp] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun θ : ℝ => Complex.exp (-(((r : ℝ) * θ : ℝ) : ℂ) * Complex.I))
      (𝓝[<] (π / r)) (𝓝 (-1 : ℂ)) := by
    have hcont : Continuous fun x : ℝ => Complex.exp (-((x : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.neg).mul continuous_const)
    have := (hcont.tendsto π).comp hlin
    rw [Function.comp_def] at this
    have hval : Complex.exp (-((π : ℝ) : ℂ) * Complex.I) = -1 := by
      rw [show (-((π : ℝ) : ℂ) * Complex.I) = -((π : ℂ) * Complex.I) by ring,
        Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rwa [hval] at this
  have h3 := h1.mul h2
  rw [show (((c * ∏ k, a k : ℝ) : ℂ)) * (-1 : ℂ) = -((c * ∏ k, a k : ℝ) : ℂ) by ring] at h3
  refine h3.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (div_pos pi_pos hr0)] with θ hθarc
  have hexp : Complex.exp (-(θ : ℂ) * Complex.I) ^ r
      = Complex.exp (-(((r : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [ftArcPoint, mul_pow, hexp]
  push_cast
  ring

/-- `arctan u / u → 1` at `0`, from the derivative of `arctan` there. -/
theorem tendsto_arctan_div_nhdsNE_zero :
    Tendsto (fun u : ℝ => Real.arctan u / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h : HasDerivAt Real.arctan 1 0 := by simpa using Real.hasDerivAt_arctan 0
  refine (hasDerivAt_iff_tendsto_slope.1 h).congr fun u => ?_
  simp [slope_def_field, div_eq_inv_mul]

/-- `ftArccot Y · Y → 1` at `+∞`: the complement angle is asymptotically `1/Y`. -/
theorem tendsto_ftArccot_mul_atTop :
    Tendsto (fun Y : ℝ => ftArccot Y * Y) atTop (𝓝 1) := by
  have hinv : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_inv_atTop_zero ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact ne_of_gt (inv_pos.2 hY)
  refine (tendsto_arctan_div_nhdsNE_zero.comp hinv).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  simp only [Function.comp_def]
  rw [Real.arctan_inv_of_pos hY, ftArccot, div_eq_mul_inv, inv_inv]

/-- **The rate of the collapse at the upper endpoint.**  With `δ = π/r - θ`,
`τ(θ)/δ → r/(sin(π/r)·∑ 1/a_k)`.

**Differs from the paper's route.**  This is the angle count once more, and the
substitution removes the analysis exactly as `x₁/τ = cos θ - sin θ cot β` does at
the lower endpoint.  The complements `π - θ_k` sum to `π - rθ = rδ` **exactly**;
each is `ftArccot` of an argument growing like `a_k/(τ sin(π/r))`, hence is
asymptotically `τ sin(π/r)/a_k`; and the sum gives `rδ = τ sin(π/r)∑1/a_k`.  No
derivative and no critical point enters. -/
theorem tendsto_ftTau_div_nhdsLT_upper {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    Tendsto (fun θ => ftTau a r (n - 1) θ / (π / r - θ)) (𝓝[<] (π / r))
      (𝓝 ((r : ℝ) / (Real.sin (π / r) * ∑ k, (a k)⁻¹))) := by
  classical
  have hπ : 0 < π := pi_pos
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hupper : π / r ≤ π / 2 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hmem : π / r ∈ Ioo 0 π := ⟨div_pos hπ hr0, by linarith⟩
  have hsr : 0 < Real.sin (π / r) := Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2
  set l : Filter ℝ := 𝓝[<] (π / r) with hl
  set T : ℝ → ℝ := fun θ => ftTau a r (n - 1) θ with hT
  have hT0 : Tendsto T l (𝓝 0) := tendsto_ftTau_nhdsLT_upper hn2 ha hr
  have hcos : Tendsto (fun θ : ℝ => Real.cos θ) l (𝓝 (Real.cos (π / r))) :=
    (Real.continuous_cos.tendsto _).mono_left nhdsWithin_le_nhds
  have hsin : Tendsto (fun θ : ℝ => Real.sin θ) l (𝓝 (Real.sin (π / r))) :=
    (Real.continuous_sin.tendsto _).mono_left nhdsWithin_le_nhds
  have hwin : ∀ᶠ θ in l, θ ∈ Ioo 0 (π / r) := Ioo_mem_nhdsLT (div_pos hπ hr0)
  have hbranch : ∀ᶠ θ in l, FTBranchAt a r (n - 1) θ := by
    filter_upwards [hwin] with θ hθ
    exact ftBranchAt_of_arc_principal hn ha hr1 (Or.inl hn2) hθ
  have hTpos : ∀ᶠ θ in l, 0 < T θ := by
    filter_upwards [hbranch] with θ hb using ftTau_pos hb
  have hTgt : Tendsto T l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hT0 (by
      filter_upwards [hTpos] with θ h using h)
  have hinvT : Tendsto (fun θ => (T θ)⁻¹) l atTop := tendsto_inv_nhdsGT_zero.comp hTgt
  have hsinθ : ∀ᶠ θ in l, Real.sin θ ≠ 0 := by
    filter_upwards [hwin] with θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
      (lt_of_lt_of_le hθ.2 (by linarith)))
  -- each complement, divided by the radius
  have hkey : ∀ k : Fin n, Tendsto (fun θ => (π - ftAngle (a k) (T θ) θ) / T θ) l
      (𝓝 (Real.sin (π / r) / a k)) := by
    intro k
    have hak : 0 < a k := ha k
    have hc : (0 : ℝ) < a k / Real.sin (π / r) := div_pos hak hsr
    have hTY : Tendsto (fun θ => T θ * ((a k / T θ - Real.cos θ) / Real.sin θ)) l
        (𝓝 (a k / Real.sin (π / r))) := by
      have hlim : Tendsto (fun θ => (a k - T θ * Real.cos θ) / Real.sin θ) l
          (𝓝 ((a k - 0 * Real.cos (π / r)) / Real.sin (π / r))) :=
        (tendsto_const_nhds.sub (hT0.mul hcos)).div hsin (ne_of_gt hsr)
      rw [show a k - 0 * Real.cos (π / r) = a k by ring] at hlim
      refine hlim.congr' ?_
      filter_upwards [hTpos, hsinθ] with θ hpos hs
      field_simp
    -- the argument is eventually positive, from `T·Y → c > 0` and `T > 0`
    have hYpos : ∀ᶠ θ in l, 0 < (a k / T θ - Real.cos θ) / Real.sin θ := by
      filter_upwards [hTY.eventually (eventually_gt_nhds (by linarith : a k /
        Real.sin (π / r) / 2 < a k / Real.sin (π / r))), hTpos] with θ hgt hpos
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    -- so its reciprocal tends to `0` from off `0`, which is all the arctan slope needs
    have hinvY : Tendsto (fun θ => ((a k / T θ - Real.cos θ) / Real.sin θ)⁻¹) l
        (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hdiv := hT0.div hTY (ne_of_gt hc)
        rw [zero_div] at hdiv
        refine hdiv.congr' ?_
        filter_upwards [hTpos, hYpos] with θ hpos hYp
        simp only [Pi.div_apply]
        field_simp
      · filter_upwards [hYpos] with θ hYp
        exact mem_compl_singleton_iff.2 (inv_ne_zero (ne_of_gt hYp))
    have hnum : Tendsto (fun θ => ftArccot ((a k / T θ - Real.cos θ) / Real.sin θ)
        * ((a k / T θ - Real.cos θ) / Real.sin θ)) l (𝓝 1) := by
      refine (tendsto_arctan_div_nhdsNE_zero.comp hinvY).congr' ?_
      filter_upwards [hYpos] with θ hYp
      simp only [Function.comp_def]
      rw [Real.arctan_inv_of_pos hYp, ftArccot, div_eq_mul_inv, inv_inv]
    have hres := hnum.div hTY (ne_of_gt hc)
    rw [show (1 : ℝ) / (a k / Real.sin (π / r)) = Real.sin (π / r) / a k by
      field_simp] at hres
    refine hres.congr' ?_
    filter_upwards [hTpos, hsinθ, hYpos, hwin] with θ hpos hs hYp hθ
    have hsp : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (lt_of_lt_of_le hθ.2 (by linarith))
    have h1 : 0 < a k / T θ - Real.cos θ := by
      rcases div_pos_iff.1 hYp with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · linarith
    have heq : T θ * (a k / T θ - Real.cos θ) = a k - T θ * Real.cos θ := by field_simp
    have hnz : a k - T θ * Real.cos θ ≠ 0 := by
      have := mul_pos hpos h1
      rw [heq] at this
      exact ne_of_gt this
    have hcompl : π - ftAngle (a k) (T θ) θ
        = ftArccot ((a k / T θ - Real.cos θ) / Real.sin θ) := by
      rw [ftAngle, pi_sub_ftArccot]
      congr 1
      field
    rw [hcompl]
    simp only [Pi.div_apply]
    field_simp
  -- the complements sum to `rδ`, exactly
  have hsum : ∀ᶠ θ in l, ∑ k, (π - ftAngle (a k) (T θ) θ) = (r : ℝ) * (π / r - θ) := by
    filter_upwards [hbranch] with θ hb
    have h := ftAngleSum_ftTau hb
    rw [ftAngleSum] at h
    rw [Finset.sum_sub_distrib, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub (by omega)]
    push_cast
    field
  have hSpos : 0 < ∑ k, (a k)⁻¹ :=
    Finset.sum_pos (fun k _ => inv_pos.2 (ha k))
      (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  have hsumdiv : Tendsto (fun θ => (r : ℝ) * (π / r - θ) / T θ) l
      (𝓝 (Real.sin (π / r) * ∑ k, (a k)⁻¹)) := by
    have hs := tendsto_finsetSum Finset.univ fun k (_ : k ∈ Finset.univ) => hkey k
    rw [show ∑ k, Real.sin (π / r) / a k = Real.sin (π / r) * ∑ k, (a k)⁻¹ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => div_eq_mul_inv _ _] at hs
    refine hs.congr' ?_
    filter_upwards [hsum, hTpos] with θ he hpos
    rw [← he, Finset.sum_div]
  have hlimpos : 0 < Real.sin (π / r) * ∑ k, (a k)⁻¹ := mul_pos hsr hSpos
  refine ((tendsto_const_nhds (x := (r : ℝ))).div hsumdiv (ne_of_gt hlimpos)).congr' ?_
  filter_upwards [hTpos, hwin] with θ hpos hθ
  have hd : π / r - θ ≠ 0 := by linarith [hθ.2]
  simp only [Pi.div_apply]
  field

/-- `x - x³/3 ≤ arctan x` for `x ≥ 0`.  The difference has derivative
`x⁴/(1+x²) ≥ 0`, so it is nondecreasing from `0`. -/
theorem sub_cube_div_three_le_arctan {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  set f : ℝ → ℝ := fun y => Real.arctan y - y + y ^ 3 / 3 with hf
  have hd : ∀ y : ℝ, HasDerivAt f (y ^ 4 / (1 + y ^ 2)) y := by
    intro y
    have h1 := Real.hasDerivAt_arctan y
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (3 * y ^ 2 / 3) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 3
    have hsum := (h1.sub (hasDerivAt_id y)).add h3
    refine hsum.congr_deriv ?_
    have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
    field
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => ((hd y).differentiableAt).differentiableWithinAt) ?_
    intro y _
    rw [(hd y).deriv]
    positivity
  have hle := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [hf, Real.arctan_zero] at hle
  norm_num at hle
  linarith

/-- **The two-sided arccot estimate.**  `|ftArccot Y - Y⁻¹| ≤ Y⁻³/3` for `Y > 0`,
the sharpening of `ftArccot_le_inv` and `inv_two_mul_le_ftArccot` at the rate a
second-order sum needs. -/
theorem abs_ftArccot_sub_inv_le {Y : ℝ} (hY : 0 < Y) :
    |ftArccot Y - Y⁻¹| ≤ Y⁻¹ ^ 3 / 3 := by
  have hx : (0 : ℝ) ≤ Y⁻¹ := le_of_lt (inv_pos.2 hY)
  have he : ftArccot Y = Real.arctan Y⁻¹ := by
    rw [ftArccot, ← Real.arctan_inv_of_pos hY]
  rw [he, abs_le]
  refine ⟨by linarith [sub_cube_div_three_le_arctan hx], ?_⟩
  have h1 : Real.arctan Y⁻¹ ≤ Y⁻¹ := arctan_le_self hx
  have h2 : (0 : ℝ) ≤ Y⁻¹ ^ 3 / 3 := by positivity
  linarith

/-- **The angle count with the complements resolved into reciprocals.**  The
complements sum to `π - rθ` exactly; writing each as `Y_k⁻¹` plus its own error
puts the count in the form the second-order estimate consumes. -/
theorem ftTau_mul_sum_inv_add_err {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hd : ∀ k, 0 < a k - ftTau a r (n - 1) θ * Real.cos θ) :
    ftTau a r (n - 1) θ
        * (Real.sin θ * ∑ k, (a k - ftTau a r (n - 1) θ * Real.cos θ)⁻¹)
      + ∑ k, (ftArccot ((a k / ftTau a r (n - 1) θ - Real.cos θ) / Real.sin θ)
              - ((a k / ftTau a r (n - 1) θ - Real.cos θ) / Real.sin θ)⁻¹)
      = π - r * θ := by
  classical
  have hn : 0 < n := by omega
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  have hτ : 0 < ftTau a r (n - 1) θ := ftTau_pos hb
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  set τ := ftTau a r (n - 1) θ with hτdef
  -- each complement is the `ftArccot` of the reciprocal-friendly argument
  have hcompl : ∀ k, π - ftAngle (a k) τ θ
      = ftArccot ((a k / τ - Real.cos θ) / Real.sin θ) := by
    intro k
    rw [ftAngle, pi_sub_ftArccot]
    congr 1
    field
  have hYinv : ∀ k, ((a k / τ - Real.cos θ) / Real.sin θ)⁻¹
      = τ * Real.sin θ / (a k - τ * Real.cos θ) := by
    intro k
    rw [show (a k / τ - Real.cos θ) / Real.sin θ
        = (a k - τ * Real.cos θ) / (τ * Real.sin θ) by field_simp]
    rw [inv_div]
  -- the count itself
  have hsum : ∑ k, (π - ftAngle (a k) τ θ) = π - r * θ := by
    have h := ftAngleSum_ftTau hb
    rw [ftAngleSum] at h
    rw [Finset.sum_sub_distrib, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hsplit : ∑ k, (π - ftAngle (a k) τ θ)
      = (∑ k, ((a k / τ - Real.cos θ) / Real.sin θ)⁻¹)
        + ∑ k, (ftArccot ((a k / τ - Real.cos θ) / Real.sin θ)
                - ((a k / τ - Real.cos θ) / Real.sin θ)⁻¹) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hcompl k]; ring
  have hfirst : (∑ k, ((a k / τ - Real.cos θ) / Real.sin θ)⁻¹)
      = τ * (Real.sin θ * ∑ k, (a k - τ * Real.cos θ)⁻¹) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hYinv k, div_eq_mul_inv]
    ring
  rw [← hsum, hsplit, hfirst]

/-! ### The chord reciprocals against their endpoint values

The angle count produces the chord reciprocals `(a k - τ cos θ)⁻¹`; the constant
the endpoint rate is stated with is built from `(a k)⁻¹`.  Every estimate below
compares the two under the one window hypothesis `τ ≤ a k / 2`, which pins the
chord between `a k / 2` and `3 a k / 2` whatever `cos θ` does. -/

/-- **The chord is comparable to its endpoint value.**  `a/2 ≤ a - τ cos θ ≤ 3a/2`
once `0 < τ ≤ a/2`, with no constraint on `θ`. -/
theorem chord_mem_Icc {a τ θ : ℝ} (hτ : 0 < τ) (hτa : τ ≤ a / 2) :
    a / 2 ≤ a - τ * Real.cos θ ∧ a - τ * Real.cos θ ≤ 3 * a / 2 :=
  ⟨by nlinarith [Real.cos_le_one θ], by nlinarith [Real.neg_one_le_cos θ]⟩

/-- The chord is positive on that window. -/
theorem chord_pos {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hτa : τ ≤ a / 2) :
    0 < a - τ * Real.cos θ :=
  lt_of_lt_of_le (half_pos ha) (chord_mem_Icc hτ hτa).1

/-- **The chord-reciprocal sum stays within a factor of the endpoint sum.**
`(2/3)·∑ (a k)⁻¹ ≤ ∑ (a k - τ cos θ)⁻¹ ≤ 2·∑ (a k)⁻¹` when the radius is at most
half of every `a k`.  This is what keeps the angle-count coefficient
`G = sin θ · ∑ (a k - τ cos θ)⁻¹` bounded away from `0` on the endpoint window,
which is the one place the final division can go wrong. -/
theorem sum_inv_chord_mem_Icc {n : ℕ} {a : Fin n → ℝ} {τ θ : ℝ}
    (ha : ∀ k, 0 < a k) (hτ : 0 < τ) (hτa : ∀ k, τ ≤ a k / 2) :
    2 / 3 * ∑ k, (a k)⁻¹ ≤ ∑ k, (a k - τ * Real.cos θ)⁻¹ ∧
      ∑ k, (a k - τ * Real.cos θ)⁻¹ ≤ 2 * ∑ k, (a k)⁻¹ := by
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h2 : (3 * a k / 2)⁻¹ ≤ (a k - τ * Real.cos θ)⁻¹ := by
      have := one_div_le_one_div_of_le (chord_pos (θ := θ) (ha k) hτ (hτa k))
        (chord_mem_Icc (θ := θ) hτ (hτa k)).2
      rwa [one_div, one_div] at this
    have heq : 2 / 3 * (a k)⁻¹ = (3 * a k / 2)⁻¹ := by rw [inv_div]; field_simp
    rw [heq]; exact h2
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hak := ha k
    have h2 : (a k - τ * Real.cos θ)⁻¹ ≤ (a k / 2)⁻¹ := by
      have := one_div_le_one_div_of_le (by linarith : (0:ℝ) < a k / 2)
        (chord_mem_Icc (θ := θ) hτ (hτa k)).1
      rwa [one_div, one_div] at this
    have heq : (a k / 2)⁻¹ = 2 * (a k)⁻¹ := by rw [inv_div]; field_simp
    rw [← heq]; exact h2

/-- **First-order perturbation of a chord reciprocal.**
`|(a - τ cos θ)⁻¹ - a⁻¹| ≤ 2τ·(a⁻¹)²`.  The difference is
`τ cos θ / (a·(a - τ cos θ))`; the numerator is at most `τ` and the window bounds
the denominator below by `a²/2`. -/
theorem abs_inv_chord_sub_inv_le {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hτa : τ ≤ a / 2) :
    |(a - τ * Real.cos θ)⁻¹ - a⁻¹| ≤ 2 * τ * ((a)⁻¹) ^ 2 := by
  have hdk := chord_pos (θ := θ) ha hτ hτa
  have hd2 := (chord_mem_Icc (θ := θ) hτ hτa).1
  have hrw : (a - τ * Real.cos θ)⁻¹ - a⁻¹
      = τ * Real.cos θ / (a * (a - τ * Real.cos θ)) := by
    field
  rw [hrw, abs_div, abs_of_pos (by positivity : (0:ℝ) < a * (a - τ * Real.cos θ)),
    div_le_iff₀ (by positivity)]
  have h1 : |τ * Real.cos θ| ≤ τ := by
    rw [abs_mul, abs_of_pos hτ]
    calc τ * |Real.cos θ| ≤ τ * 1 :=
          mul_le_mul_of_nonneg_left (abs_cos_le_one θ) hτ.le
      _ = τ := mul_one τ
  have h2 : 2 * τ * ((a)⁻¹) ^ 2 * (a * (a - τ * Real.cos θ))
      = 2 * τ * (a - τ * Real.cos θ) / a := by field_simp
  rw [h2, le_div_iff₀ ha]
  have e1 : |τ * Real.cos θ| * a ≤ τ * a := mul_le_mul_of_nonneg_right h1 ha.le
  have e2 := mul_le_mul_of_nonneg_left hd2 (show (0:ℝ) ≤ 2 * τ by linarith)
  have e3 : 2 * τ * (a / 2) = τ * a := by ring
  linarith

/-- The sum form of `abs_inv_chord_sub_inv_le`: the whole chord-reciprocal sum
moves by at most `2τ·∑ (a k⁻¹)²` off its endpoint value. -/
theorem abs_sum_inv_chord_sub_sum_inv_le {n : ℕ} {a : Fin n → ℝ} {τ θ : ℝ}
    (ha : ∀ k, 0 < a k) (hτ : 0 < τ) (hτa : ∀ k, τ ≤ a k / 2) :
    |∑ k, (a k - τ * Real.cos θ)⁻¹ - ∑ k, (a k)⁻¹| ≤ 2 * τ * ∑ k, ((a k)⁻¹) ^ 2 := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => abs_inv_chord_sub_inv_le (ha k) hτ (hτa k)

/-- The argument `ftArccot` is applied to is positive on the arc. -/
theorem ftArccot_arg_pos {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hτa : τ ≤ a / 2)
    (hs : 0 < Real.sin θ) : 0 < (a / τ - Real.cos θ) / Real.sin θ := by
  have h1 : 1 < a / τ := by
    rw [lt_div_iff₀ hτ, one_mul]
    exact lt_of_le_of_lt hτa (half_lt_self ha)
  have : 0 < a / τ - Real.cos θ := by linarith [Real.cos_le_one θ]
  positivity

/-- **The arccot argument's reciprocal is `O(τ)`.**  `((a/τ - cos θ)/sin θ)⁻¹ ≤ 2τ/a`
on the arc, because that reciprocal is `τ sin θ / (a - τ cos θ)` and the window
bounds the chord below by `a/2`.  Cubed against `abs_ftArccot_sub_inv_le`, this is
what makes the complement errors `O(δ³)` rather than `O(δ)`. -/
theorem inv_ftArccot_arg_le {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hτa : τ ≤ a / 2)
    (hs : 0 < Real.sin θ) :
    ((a / τ - Real.cos θ) / Real.sin θ)⁻¹ ≤ 2 * τ * (a)⁻¹ := by
  have hd := chord_pos (θ := θ) ha hτ hτa
  have hrw : ((a / τ - Real.cos θ) / Real.sin θ)⁻¹
      = τ * Real.sin θ / (a - τ * Real.cos θ) := by
    rw [show (a / τ - Real.cos θ) / Real.sin θ
        = (a - τ * Real.cos θ) / (τ * Real.sin θ) by field_simp, inv_div]
  rw [hrw, div_le_iff₀ hd]
  have hge : 2 * τ * (a)⁻¹ * (a - τ * Real.cos θ) ≥ 2 * τ * (a)⁻¹ * (a / 2) :=
    mul_le_mul_of_nonneg_left (chord_mem_Icc (θ := θ) hτ hτa).1 (by positivity)
  have heq : 2 * τ * (a)⁻¹ * (a / 2) = τ := by field_simp
  have e1 : τ * Real.sin θ ≤ τ := by
    calc τ * Real.sin θ ≤ τ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hτ.le
      _ = τ := mul_one τ
  linarith

/-- **The weighted chord-reciprocal sum moves at most linearly.**  The quantity
`G(θ) = sin θ·∑(a_k - τcos θ)⁻¹` that the angle count produces differs from its
endpoint value `sin θ_0·∑a_k⁻¹` by at most `2|θ - θ_0|∑a_k⁻¹ + 2τ∑a_k^{-2}`.

Two independent movements, split before either is estimated: the sine factor
moves by `|θ - θ_0|` and the sum by `2τ∑a_k^{-2}`, the first from
`Real.abs_sin_sub_sin_le` and the second from `abs_sum_inv_chord_sub_sum_inv_le`.
Along the branch both are `O(δ)`, which is what makes the deviation of the radius
from its linear model second order rather than first. -/
theorem abs_sin_mul_sum_inv_chord_sub_le {n : ℕ} {a : Fin n → ℝ} {τ θ θ₀ : ℝ}
    (ha : ∀ k, 0 < a k) (hτ : 0 < τ) (hτa : ∀ k, τ ≤ a k / 2)
    (hs₀ : 0 ≤ Real.sin θ₀) (hs₀1 : Real.sin θ₀ ≤ 1) :
    |Real.sin θ * ∑ k, (a k - τ * Real.cos θ)⁻¹ - Real.sin θ₀ * ∑ k, (a k)⁻¹|
      ≤ |θ - θ₀| * (2 * ∑ k, (a k)⁻¹) + 2 * τ * ∑ k, ((a k)⁻¹) ^ 2 := by
  have hSigub : (∑ k, (a k - τ * Real.cos θ)⁻¹) ≤ 2 * ∑ k, (a k)⁻¹ :=
    (sum_inv_chord_mem_Icc ha hτ hτa).2
  have hSignn : (0 : ℝ) ≤ ∑ k, (a k - τ * Real.cos θ)⁻¹ :=
    Finset.sum_nonneg fun k _ => inv_nonneg.2 (chord_pos (ha k) hτ (hτa k)).le
  have hsplit : Real.sin θ * (∑ k, (a k - τ * Real.cos θ)⁻¹) - Real.sin θ₀ * ∑ k, (a k)⁻¹
      = (Real.sin θ - Real.sin θ₀) * (∑ k, (a k - τ * Real.cos θ)⁻¹)
        + Real.sin θ₀ * ((∑ k, (a k - τ * Real.cos θ)⁻¹) - ∑ k, (a k)⁻¹) := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hs₀, abs_of_nonneg hSignn]
  have b1 : |Real.sin θ - Real.sin θ₀| * (∑ k, (a k - τ * Real.cos θ)⁻¹)
      ≤ |θ - θ₀| * (2 * ∑ k, (a k)⁻¹) :=
    mul_le_mul (Real.abs_sin_sub_sin_le θ θ₀) hSigub hSignn (abs_nonneg _)
  have b2 : Real.sin θ₀ * |(∑ k, (a k - τ * Real.cos θ)⁻¹) - ∑ k, (a k)⁻¹|
      ≤ 1 * (2 * τ * ∑ k, ((a k)⁻¹) ^ 2) :=
    mul_le_mul hs₀1 (abs_sum_inv_chord_sub_sum_inv_le ha hτ hτa) (abs_nonneg _) zero_le_one
  linarith

/-- **The complement errors are cubic in the radius.**  Each angle's complement is
`Y_k⁻¹` up to `Y_k⁻³/3`, and `Y_k⁻¹ ≤ 2τ/a_k` on the window, so the whole error sum
is `O(τ³)` with the pencil-free constant `(8/3)·∑(a_k⁻¹)³`.  Uniform in `θ`: the
only place `θ` enters is through `sin θ > 0`.

This is the estimate that makes the endpoint rate second order rather than first.
A bound linear in `τ` here would be absorbed into the linear coefficient and the
`O(δ²)` conclusion would be lost. -/
theorem abs_sum_ftArccot_err_le {n : ℕ} {a : Fin n → ℝ} {τ θ : ℝ}
    (ha : ∀ k, 0 < a k) (hτ : 0 < τ) (hτa : ∀ k, τ ≤ a k / 2) (hs : 0 < Real.sin θ) :
    |∑ k, (ftArccot ((a k / τ - Real.cos θ) / Real.sin θ)
        - ((a k / τ - Real.cos θ) / Real.sin θ)⁻¹)|
      ≤ 8 / 3 * τ ^ 3 * ∑ k, ((a k)⁻¹) ^ 3 := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hY := ftArccot_arg_pos (ha k) hτ (hτa k) hs
  refine le_trans (abs_ftArccot_sub_inv_le hY) ?_
  have h2 : ((a k / τ - Real.cos θ) / Real.sin θ)⁻¹ ^ 3 ≤ (2 * τ * (a k)⁻¹) ^ 3 :=
    pow_le_pow_left₀ (inv_pos.2 hY).le (inv_ftArccot_arg_le (ha k) hτ (hτa k) hs) 3
  have e4 : (2 * τ * (a k)⁻¹) ^ 3 = 8 * τ ^ 3 * ((a k)⁻¹) ^ 3 := by ring
  linarith

/-! ### The second-order rate -/

/-- **The rearrangement that makes the rate second order.**  The angle count
delivers `τG + E = mδg₀` exactly, where `g₀` is the endpoint value of `G` and
`mg₀ = r`.  Subtracting `mδG` from both sides gives

`(τ - mδ)G = -mδ(G - g₀) - E`,

so a linear bound on `G - g₀`, a quadratic bound on `E` and a positive lower
bound on `G` together force `τ - mδ = O(δ²)`.  All of the analysis sits in the
three hypotheses; what is proved here is the algebra that combines them, and it
is what separates the deviation of the radius from the deviation of the sum. -/
theorem abs_sub_linear_le_of_perturbed_relation {τ δ m g₀ G E cG cE Glb : ℝ}
    (hδ : 0 < δ) (hm : 0 ≤ m) (hGlb : 0 < Glb) (hG : Glb ≤ G)
    (hrel : τ * G + E = m * δ * g₀)
    (hGgap : |G - g₀| ≤ cG * δ) (hE : |E| ≤ cE * δ ^ 2) :
    |τ - m * δ| ≤ (m * cG + cE) / Glb * δ ^ 2 := by
  have hGpos : 0 < G := lt_of_lt_of_le hGlb hG
  have hkey : (τ - m * δ) * G = -(m * δ * (G - g₀)) - E := by linear_combination hrel
  have habs : |τ - m * δ| * G ≤ m * δ * |G - g₀| + |E| := by
    have h1 : |(τ - m * δ) * G| = |τ - m * δ| * G := by rw [abs_mul, abs_of_pos hGpos]
    rw [← h1, hkey]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_neg, abs_mul, abs_of_nonneg (mul_nonneg hm hδ.le)]
  have hstep : |τ - m * δ| * Glb ≤ (m * cG + cE) * δ ^ 2 := by
    have hlb : |τ - m * δ| * Glb ≤ |τ - m * δ| * G :=
      mul_le_mul_of_nonneg_left hG (abs_nonneg _)
    have e1 : m * δ * |G - g₀| ≤ m * δ * (cG * δ) :=
      mul_le_mul_of_nonneg_left hGgap (mul_nonneg hm hδ.le)
    nlinarith [habs, hlb, hE]
  rw [div_mul_eq_mul_div, le_div_iff₀ hGlb]
  linarith [hstep]


/-- **The pointwise second-order rate at the upper endpoint**, the twin of
`exists_bound_ftTau_sub_linear` at the lower one.  The linear coefficient is
`r/(sin(π/r)·∑1/a_k)` and it is stated symbolically: at a pencil with
`∑1/a_k = 1` this is byte-identical in value to `r/sin(π/r)`, which is not the
general constant.

The route is the angle count with the complements resolved: `τ·G + E = rδ`
exactly, where `G = sin θ·∑(a_k - τcos θ)⁻¹` and `E` collects the arccot errors.
Since `m·g₀ = r`, that rearranges to `(τ - mδ)·G = -mδ(G - g₀) - E`, and the two
right-hand terms are `O(δ²)` and `O(δ³)` while `G` stays above `g₀/3`. -/
theorem exists_bound_ftTau_upper {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      |ftTau a r (n - 1) (π / r - δ)
        - (r : ℝ) / (Real.sin (π / r) * ∑ k, (a k)⁻¹) * δ| ≤ C * δ ^ 2 := by
  classical
  have hπ : 0 < π := pi_pos
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hupper : π / r ≤ π / 2 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hmem : π / r ∈ Ioo 0 π := ⟨div_pos hπ hr0, by linarith⟩
  have hsr : 0 < Real.sin (π / r) := Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2
  have hsr1 : Real.sin (π / r) ≤ 1 := Real.sin_le_one _
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  set S : ℝ := ∑ k, (a k)⁻¹ with hS
  set S2 : ℝ := ∑ k, ((a k)⁻¹) ^ 2 with hS2
  set S3 : ℝ := ∑ k, ((a k)⁻¹) ^ 3 with hS3
  have hSpos : 0 < S := Finset.sum_pos (fun k _ => inv_pos.2 (ha k)) hne
  have hS2pos : 0 < S2 := Finset.sum_pos (fun k _ => pow_pos (inv_pos.2 (ha k)) 2) hne
  have hS3pos : 0 < S3 := Finset.sum_pos (fun k _ => pow_pos (inv_pos.2 (ha k)) 3) hne
  set g₀ : ℝ := Real.sin (π / r) * S with hg
  have hg0 : 0 < g₀ := mul_pos hsr hSpos
  set m : ℝ := (r : ℝ) / g₀ with hmdef
  have hm0 : 0 < m := div_pos hr0 hg0
  have hmg : m * g₀ = r := by rw [hmdef]; field_simp
  set amin : ℝ := Finset.univ.inf' hne a with hamin
  have hamin_le : ∀ k, amin ≤ a k := fun k => Finset.inf'_le _ (Finset.mem_univ k)
  have hamin_pos : 0 < amin := (Finset.lt_inf'_iff _).2 fun k _ => ha k
  obtain ⟨c₂, hc2pos, hc2⟩ : ∃ c : ℝ, 0 < c ∧ c = 2 * S + 2 * S2 * (m + 1) :=
    ⟨_, by positivity, rfl⟩
  have hCpos' : (0 : ℝ) < 3 / g₀ * (m * c₂ + 8 / 3 * (m + 1) ^ 3 * S3) := by
    have h1 : 0 < m * c₂ := mul_pos hm0 hc2pos
    have h2 : (0 : ℝ) < 8 / 3 * (m + 1) ^ 3 * S3 := by positivity
    have h3 : (0 : ℝ) < 3 / g₀ := by positivity
    exact mul_pos h3 (by linarith)
  obtain ⟨C, hCpos, hC⟩ :
      ∃ c : ℝ, 0 < c ∧ c = 3 / g₀ * (m * c₂ + 8 / 3 * (m + 1) ^ 3 * S3) :=
    ⟨_, hCpos', rfl⟩
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  set T : ℝ → ℝ := fun δ => ftTau a r (n - 1) (π / r - δ) with hT
  -- transport the two endpoint limits from `θ` to `δ`
  have hmap : Tendsto (fun δ : ℝ => π / r - δ) l (𝓝[<] (π / r)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun δ : ℝ => π / r - δ) (𝓝 0) (𝓝 (π / r - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      rw [sub_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mem_Iio.2 (by linarith [mem_Ioi.1 hδ])
  have hT0 : Tendsto T l (𝓝 0) := (tendsto_ftTau_nhdsLT_upper hn2 ha hr).comp hmap
  have hTratio : Tendsto (fun δ => T δ / δ) l (𝓝 m) := by
    have h := (tendsto_ftTau_div_nhdsLT_upper hn2 ha hr).comp hmap
    refine h.congr fun δ => ?_
    simp only [Function.comp_def, hT]
    ring_nf
  -- the window
  have hwin : ∀ᶠ δ in l, 0 < δ ∧ δ ≤ 1 ∧ δ < π / r ∧ T δ ≤ (m + 1) * δ
      ∧ T δ ≤ amin / 2 ∧ Real.sin (π / r) / 2 ≤ Real.sin (π / r - δ) := by
    have h1 : ∀ᶠ δ in l, T δ / δ < m + 1 :=
      hTratio.eventually (eventually_lt_nhds (by linarith))
    have h2 : ∀ᶠ δ in l, T δ < amin / 2 :=
      hT0.eventually (eventually_lt_nhds (by linarith))
    have h3 : ∀ᶠ δ in l, Real.sin (π / r) / 2 < Real.sin (π / r - δ) := by
      have hc : Tendsto (fun δ : ℝ => Real.sin (π / r - δ)) l (𝓝 (Real.sin (π / r))) := by
        have hcont : Continuous fun δ : ℝ => Real.sin (π / r - δ) :=
          Real.continuous_sin.comp (continuous_const.sub continuous_id)
        have h0 := hcont.tendsto 0
        rw [sub_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      exact hc.eventually (eventually_gt_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < min 1 (π / r) by
      positivity), h1, h2, h3] with δ hδ hδ2 hh1 hh2 hh3
    have hδ0 : (0 : ℝ) < δ := hδ
    refine ⟨hδ0, le_of_lt (lt_of_lt_of_le hδ2.2 (min_le_left _ _)),
      lt_of_lt_of_le hδ2.2 (min_le_right _ _), ?_, hh2.le, hh3.le⟩
    rw [div_lt_iff₀ hδ0] at hh1
    linarith
  -- the estimate on that window
  have hmain : ∀ᶠ δ in l, |T δ - m * δ| ≤ C * δ ^ 2 := by
    filter_upwards [hwin] with δ ⟨hδ0, hδ1, hδr, hTub, hTa, hsl⟩
    set θ : ℝ := π / r - δ with hθdef
    have hθarc : θ ∈ Ioo 0 (π / r) := ⟨by simp only [hθdef]; linarith, by
      simp only [hθdef]; linarith⟩
    have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr1 hθarc
    have hb : FTBranchAt a r (n - 1) θ :=
      ftBranchAt_of_arc_principal hn ha hr1 (Or.inl hn2) hθarc
    set τ : ℝ := ftTau a r (n - 1) θ with hτdef
    have hτub : τ ≤ (m + 1) * δ := hTub
    have hτa : τ ≤ amin / 2 := hTa
    have hτ : 0 < τ := ftTau_pos hb
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
    have hTak : ∀ k, τ ≤ a k / 2 := fun k => le_trans hτa (by linarith [hamin_le k])
    have hdpos : ∀ k, 0 < a k - τ * Real.cos θ :=
      fun k => chord_pos (θ := θ) (ha k) hτ (hTak k)
    have hex := ftTau_mul_sum_inv_add_err hn2 ha hr1 hθarc hdpos
    set Sig : ℝ := ∑ k, (a k - τ * Real.cos θ)⁻¹ with hSig
    set G : ℝ := Real.sin θ * Sig with hG
    set E : ℝ := ∑ k, (ftArccot ((a k / τ - Real.cos θ) / Real.sin θ)
        - ((a k / τ - Real.cos θ) / Real.sin θ)⁻¹) with hE
    have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
    have hrhs : π - (r : ℝ) * θ = r * δ := by
      rw [hθdef]
      field
    rw [hrhs] at hex
    -- `Sig` between `(2/3)S` and `2S`
    have hSiglb : 2 / 3 * S ≤ Sig := by
      rw [hSig, hS]; exact (sum_inv_chord_mem_Icc ha hτ hTak).1
    have hGlb : g₀ / 3 ≤ G := by
      have h1 : Real.sin (π / r) / 2 * (2 / 3 * S) ≤ Real.sin θ * Sig :=
        mul_le_mul hsl hSiglb (by positivity) hs.le
      have h2 : Real.sin (π / r) / 2 * (2 / 3 * S) = g₀ / 3 := by rw [hg]; ring
      rw [hG, ← h2]; exact h1
    -- `G` within `c₂ δ` of `g₀`
    have hGgap : |G - g₀| ≤ c₂ * δ := by
      have hbase := abs_sin_mul_sum_inv_chord_sub_le (θ := θ) (θ₀ := π / r)
        ha hτ hTak hsr.le hsr1
      rw [← hSig, ← hG, ← hS, ← hS2, ← hg] at hbase
      have hθgap : |θ - π / r| = δ := by
        rw [hθdef, show π / r - δ - π / r = -δ by ring, abs_neg, abs_of_pos hδ0]
      rw [hθgap] at hbase
      have hτS2 : 2 * τ * S2 ≤ 2 * ((m + 1) * δ) * S2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hτub (show (0:ℝ) ≤ 2 by norm_num)) hS2pos.le
      have e : c₂ * δ = δ * (2 * S) + 2 * ((m + 1) * δ) * S2 := by rw [hc2]; ring
      rw [e]
      linarith
    -- the arccot errors
    have hEub : |E| ≤ 8 / 3 * (m + 1) ^ 3 * S3 * δ ^ 2 := by
      have hcube := abs_sum_ftArccot_err_le (θ := θ) ha hτ hTak hs
      rw [← hE] at hcube
      refine le_trans hcube ?_
      have hτd : τ ^ 3 ≤ ((m + 1) * δ) ^ 3 :=
        pow_le_pow_left₀ hτ.le hτub 3
      have hd3 : δ ^ 3 ≤ δ ^ 2 := by
        calc δ ^ 3 = δ ^ 2 * δ := by ring
          _ ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
          _ = δ ^ 2 := mul_one _
      have hnn : (0:ℝ) ≤ 8 / 3 * (m + 1) ^ 3 * S3 :=
        mul_nonneg (by positivity) hS3pos.le
      calc 8 / 3 * τ ^ 3 * S3 ≤ 8 / 3 * ((m + 1) * δ) ^ 3 * S3 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hτd (by norm_num : (0:ℝ) ≤ 8 / 3)) hS3pos.le
        _ = 8 / 3 * (m + 1) ^ 3 * S3 * δ ^ 3 := by ring
        _ ≤ 8 / 3 * (m + 1) ^ 3 * S3 * δ ^ 2 := mul_le_mul_of_nonneg_left hd3 hnn
    -- assemble
    have hrel : τ * G + E = m * δ * g₀ := by rw [hex, ← hmg]; ring
    have hbd := abs_sub_linear_le_of_perturbed_relation (Glb := g₀ / 3)
      hδ0 hm0.le (by positivity) hGlb hrel hGgap hEub
    have hCeq : (m * c₂ + 8 / 3 * (m + 1) ^ 3 * S3) / (g₀ / 3) = C := by
      rw [hC]; field_simp
    rwa [hCeq] at hbd
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hmain
  rw [mem_Ioi] at hε₀
  refine ⟨C, ε₀ / 2, hCpos, by linarith, ?_⟩
  intro δ hδ0 hδε
  exact hsub ⟨hδ0, by linarith⟩

end ForgacsTran
