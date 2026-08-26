/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchEndpoint
import ForgacsTran.FTBranchUpper
import ForgacsTran.FTGeometryBranch

/-!
# The upper-endpoint limit of the branch radius, at `r = 1`

`FTBranchEndpoint` settles `θ → 0⁺`.  At the other end of the arc the behaviour
is a **dichotomy in `r`**, and `eq:ab-def` is written around it: `b = +∞` for
`r > 1`, while for `r = 1` the upper endpoint is `b = g(t_b)` at the unique
*negative* critical point `t_b` of `g`.

`FTBranchUpper.tendsto_ftTau_nhdsLT_upper` carries the `r ≥ 2` side: the radius
collapses, `τ(θ) → 0`.  This module carries the `r = 1` side, where the arc ends
at `π`, no collapse happens, and `τ(θ)` runs to a positive limit `L` with
`t_b = -L`.  The two together are `exists_tendsto_ftTau_nhdsLT_arc_end`.

## Main statements

* `pi_sub_ftAngle_eq_arctan` — past `π/2` the angle *deficit* `π - θ_k` is
  `arctan (sin θ / (a_k/τ - cos θ))`, which is the form the endpoint is read in.
* `sum_arctan_deficit_eq` — at `r = 1` the branch equation says those `n`
  deficits sum to `π - θ`.  Every angle is within `O(π - θ)` of `π`, so the
  count is a statement about the deficits alone.
* `ftTau_le_two_mul_of_lt_pi` — the radius stays below `2 ∑_k a_k` on
  `(π - 1/2, π)`.  This is the bound `ftTau_le_div_cos` supplies at the lower
  end, and it does not: `cos θ < 0` there.
* `ftPencilIm_pi`, `ftPencilImDeriv_pi` — at `θ = π` the pencil's imaginary part
  vanishes identically in `τ`, and its `θ`-derivative is `E(-τ)`.
* `eval_ftCriticalReal_neg_eq_zero_of_mapClusterPt` — every cluster point `x` of
  the radius at `π⁻` gives `E(-x) = 0`.
* `mapClusterPt_of_mem_Ioo_nhdsLT` — the intermediate-value step at a left
  endpoint, the mirror of `mapClusterPt_of_mem_Ioo`.
* `exists_tendsto_ftTau_nhdsLT_pi` — **the `r = 1` endpoint limit**: `τ(θ)`
  converges as `θ ↑ π` to a positive `L` with `E(-L) = 0`.
* `exists_tendsto_ftTau_nhdsLT_arc_end` — the dichotomy, split on `r = 1`
  against `2 ≤ r`.
* `tendsto_ftBranchZ_atTop_arc_end`, `exists_tendsto_ftBranchZ_arc_end_pi` — the
  same limits carried over to the spectral parameter, in the `b = +∞` and the
  finite convention of `eq:ab-def` respectively.
* `ft_geometry_at_branch_unbounded_of_two_le`, `ft_geometry_at_branch_of_three_le`
  — `thm:FT-geometry` at the constructed branch with `hzb` discharged, leaving
  the minimum-modulus gap as the only hypothesis.

## Implementation notes

**The `r ≥ 2` statement is false at `r = 1` and the `r = 1` statement is false at
`r ≥ 2`**, so neither covers the arc's upper end on its own.  At `r ≥ 2` the
radius collapses and `t_b` does not exist; at `r = 1` the radius has a positive
limit and `τ(θ) → 0` fails.  `scripts/check_upper_endpoint_r_one.py` asserts both
directions at five pencils rather than one, since a single pencil sees only the
regime it is in.

The bound `ftTau_le_two_mul_of_lt_pi` is where the endpoints genuinely differ.
At `0⁺` a fixed radius is excluded because every angle would fall below `π/2`;
at `π⁻` every angle is *near* `π` whatever the radius, and both sides of the
branch equation tend to `nπ` together.  What separates them is first order in
`π - θ`: the deficits sum to `π - θ` while `n` deficits at radius `τ` sum to
about `(π - θ) ∑_k τ/(τ + a_k)`, and that sum passes `1` at a bounded radius.
The proof compares the `n` deficits against the single largest one instead of
expanding, which turns the count into `n·arctan(w) ≤ π - θ` and then into
`A/τ ≥ 65/96` by `arctan`/`tan` monotonicity alone.

Sorry-free.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `subsec:FT-geometry`,
  `eq:ab-def`, `thm:FT-geometry`.
* `Forgacs2017RationalDenominator`, Lemmas 5 and 6 and Proposition 3.

## Tags

upper endpoint, branch radius, endpoint limit, critical polynomial
-/

namespace ForgacsTran

open Real Set Filter Topology Polynomial

/-! ### The angle count in the deficit variable

Past `π/2` every branch angle sits within `O(π - θ)` of `π`, so the branch
equation is a statement about the deficits `π - θ_k` rather than about the
angles.  That is the only form in which the upper endpoint is legible. -/

/-- **The angle deficit.**  For `θ > π/2` the complement `π - θ_k` of the angle
of `Forgacs2017RationalDenominator` Lemma 2 is `arctan (sin θ / (a/τ - cos θ))`.
Both the numerator and the denominator are positive there, which is what the
form buys. -/
theorem pi_sub_ftAngle_eq_arctan {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ : θ ∈ Ioo (π / 2) π) :
    π - ftAngle a τ θ = arctan (sin θ / (a / τ - cos θ)) := by
  have hπ := pi_pos
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) hθ.2
  have hc : cos θ < 0 := cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [hθ.2])
  have hd : 0 < a / τ - cos θ := by have := div_pos ha hτ; linarith
  set y : ℝ := (a / τ - cos θ) / sin θ with hy
  have hypos : 0 < y := div_pos hd hs
  have hX : cos θ / sin θ - a / (τ * sin θ) = -y := by
    rw [hy]; field_simp; ring
  have hangle : ftAngle a τ θ = π / 2 + arctan y := by
    rw [ftAngle, ftArccot, hX, arctan_neg]; ring
  have hinv : y⁻¹ = sin θ / (a / τ - cos θ) := by
    rw [hy, inv_div]
  rw [hangle, ← hinv, arctan_inv_of_pos hypos]
  ring

/-- **The branch equation at `r = 1`, in deficits.**  The `n` deficits sum to
`π - θ`: `∑_k θ_k = θ + (n-1)π` says exactly that. -/
theorem sum_arctan_deficit_eq {n : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    {θ : ℝ} (hθ : θ ∈ Ioo (π / 2) π) (h : FTBranchAt a 1 (n - 1) θ) :
    ∑ k, arctan (sin θ / (a k / ftTau a 1 (n - 1) θ - cos θ)) = π - θ := by
  have hτ : 0 < ftTau a 1 (n - 1) θ := ftTau_pos h
  have hsum := ftAngleSum_ftTau h
  have hdef : ∑ k, arctan (sin θ / (a k / ftTau a 1 (n - 1) θ - cos θ))
      = ∑ k, (π - ftAngle (a k) (ftTau a 1 (n - 1) θ) θ) :=
    Finset.sum_congr rfl fun k _ => (pi_sub_ftAngle_eq_arctan (ha k) hτ hθ).symm
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [ftAngleSum] at hsum
  rw [hsum, hn1]
  push_cast
  ring

/-! ### The radius stays bounded

`ftTau_le_div_cos` bounds the radius by `A / cos θ`, which is vacuous past
`π/2`.  The bound here comes from the deficit count instead. -/

/-- **The comparison that bounds the radius.**  If `n ≥ 2` deficits at a common
radius sum to `s ≤ 1/2`, the radius is below `2A`.

Each deficit is at least the one built from the largest `a_k`, so
`n · arctan w ≤ s` for that one `w`; `arctan`/`tan` monotonicity turns this into
`sin s / (A/τ + cos s) ≤ tan (s/n)`, and the elementary bounds
`sin s ≥ (23/24)s`, `cos ≥ 7/8` on `[0, 1/2]` close it at `A/τ ≥ 65/96`. -/
theorem le_two_mul_of_sum_arctan_eq {n : ℕ} {a : Fin n → ℝ} {τ A s : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hA : ∀ k, a k ≤ A) (hτ : 0 < τ) (hs0 : 0 < s) (hs : s ≤ 1 / 2)
    (heq : ∑ k, arctan (sin s / (a k / τ + cos s)) = s) :
    τ ≤ 2 * A := by
  have hπ := pi_gt_three
  have hApos : 0 < A := lt_of_lt_of_le (ha ⟨0, by omega⟩) (hA ⟨0, by omega⟩)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  set m : ℝ := s / n with hm
  have hm0 : 0 < m := div_pos hs0 hn0
  have hmle : m ≤ s := by
    rw [hm, div_le_iff₀ hn0]; nlinarith
  -- the elementary bounds on `[0, 1/2]`
  have hcos_s : (7 : ℝ) / 8 ≤ cos s := by
    have := one_sub_sq_div_two_le_cos (x := s); nlinarith
  have hcos_m : (7 : ℝ) / 8 ≤ cos m := by
    have := one_sub_sq_div_two_le_cos (x := m); nlinarith
  have hsq : s ^ 2 ≤ 1 / 4 := by nlinarith
  have hsin_s : 23 / 24 * s ≤ sin s := by
    have hcube := sin_gt_sub_cube hs0
    nlinarith [mul_le_mul_of_nonneg_left hsq hs0.le]
  have hsin_m : sin m ≤ m := (sin_lt hm0).le
  have hsin_m0 : 0 < sin m := sin_pos_of_pos_of_lt_pi hm0 (by linarith)
  have hs_pos : 0 < sin s := by nlinarith
  -- every deficit dominates the one at the largest zero
  set D : ℝ := A / τ + cos s with hD
  have hDpos : 0 < D := by have := div_pos hApos hτ; linarith
  set w : ℝ := sin s / D with hw
  have hwpos : 0 < w := div_pos hs_pos hDpos
  have hstep : ∀ k, arctan w ≤ arctan (sin s / (a k / τ + cos s)) := by
    intro k
    have hk : 0 < a k / τ + cos s := by
      have := div_pos (ha k) hτ; linarith
    refine arctan_le_arctan_iff.2 ?_
    rw [hw, hD]
    refine div_le_div_of_nonneg_left hs_pos.le hk ?_
    have : a k / τ ≤ A / τ := by gcongr; exact hA k
    linarith
  have hcard : (n : ℝ) * arctan w ≤ s := by
    calc (n : ℝ) * arctan w
        = ∑ _k : Fin n, arctan w := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ k, arctan (sin s / (a k / τ + cos s)) := Finset.sum_le_sum fun k _ => hstep k
      _ = s := heq
  -- `arctan w ≤ m` becomes `w ≤ tan m`
  have harc : arctan w ≤ m := by
    rw [hm, le_div_iff₀ hn0]; linarith [hcard]
  have hwtan : w ≤ tan m := by
    have hmlt : m < π / 2 := by linarith [pi_gt_three]
    have hmgt : -(π / 2) < m := by linarith [pi_gt_three]
    refine arctan_le_arctan_iff.1 ?_
    rw [arctan_tan hmgt hmlt]
    exact harc
  -- unwind to a lower bound on `D`
  have hcos_m0 : 0 < cos m := by linarith
  have hcross : sin s * cos m ≤ D * sin m := by
    rw [hw, div_le_iff₀ hDpos, tan_eq_sin_div_cos, div_mul_eq_mul_div,
      le_div_iff₀ hcos_m0] at hwtan
    nlinarith
  have hDs : (n : ℝ) * (sin s * cos m) ≤ D * s := by
    have h1 : D * sin m ≤ D * m := by nlinarith
    have h2 : (n : ℝ) * (D * m) = D * s := by rw [hm]; field_simp
    nlinarith
  have hDlow : (161 : ℝ) / 96 ≤ D := by
    have hp : (161 : ℝ) / 192 * s ≤ sin s * cos m := by
      have h1 : 23 / 24 * s * cos m ≤ sin s * cos m :=
        mul_le_mul_of_nonneg_right hsin_s hcos_m0.le
      have h2 : 23 / 24 * s * (7 / 8) ≤ 23 / 24 * s * cos m :=
        mul_le_mul_of_nonneg_left hcos_m (by positivity)
      linarith
    have h1 : (161 : ℝ) / 96 * s ≤ (n : ℝ) * (sin s * cos m) := by
      nlinarith [mul_nonneg hs_pos.le hcos_m0.le]
    exact le_of_mul_le_mul_right (by linarith [le_trans h1 hDs]) hs0
  have hAtau : (65 : ℝ) / 96 ≤ A / τ := by
    have := cos_le_one s
    rw [hD] at hDlow
    linarith
  rw [le_div_iff₀ hτ] at hAtau
  nlinarith

/-- **The radius is bounded at the upper endpoint, at `r = 1`.**  `2 ∑_k a_k`
serves on the whole window `(π - 1/2, π)`.  The counterpart of
`ftTau_le_div_cos`, which is vacuous here because `cos θ < 0`. -/
theorem ftTau_le_two_mul_of_lt_pi {n : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    {A θ : ℝ} (hA : ∀ k, a k ≤ A) (hθ : θ ∈ Ioo (π - 1 / 2) π)
    (h : FTBranchAt a 1 (n - 1) θ) :
    ftTau a 1 (n - 1) θ ≤ 2 * A := by
  have hπ := pi_gt_three
  have hn : 0 < n := by omega
  have hθ2 : θ ∈ Ioo (π / 2) π := ⟨by linarith [hθ.1], hθ.2⟩
  set s : ℝ := π - θ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith [hθ.2]
  have hs : s ≤ 1 / 2 := by rw [hsdef]; linarith [hθ.1]
  have hsin : sin θ = sin s := by rw [hsdef, sin_pi_sub]
  have hcos : cos θ = -cos s := by rw [hsdef, cos_pi_sub]; ring
  have heq := sum_arctan_deficit_eq hn ha hθ2 h
  rw [hsin, hcos] at heq
  simp only [sub_neg_eq_add] at heq
  exact le_two_mul_of_sum_arctan_eq hn2 ha hA (ftTau_pos h) hs0 hs heq

/-! ### The endpoint identification

At `θ = π` the arc point is `-τ`, which is real, so `ftPencilIm` vanishes there
whatever the radius.  Rolle on `[θ, π]` then delivers an interior zero of the
`θ`-derivative, and that derivative at `π` is `E(-τ)`. -/

theorem eval_map_ofReal (P : Polynomial ℝ) (t : ℝ) :
    (P.map (algebraMap ℝ ℂ)).eval ((t : ℝ) : ℂ) = ((P.eval t : ℝ) : ℂ) := by
  rw [eval_map, ← aeval_def, aeval_ofReal]

@[simp] theorem ftArcPoint_pi (τ : ℝ) : ftArcPoint τ π = ((-τ : ℝ) : ℂ) := by
  have h : Complex.exp (-(π : ℂ) * Complex.I) = -1 := by
    rw [show -(π : ℂ) * Complex.I = -((π : ℂ) * Complex.I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  rw [ftArcPoint, h]
  push_cast
  ring

/-- **At `θ = π` the pencil's imaginary part vanishes identically.**  The arc
point is `-τ`, real, so `e^{iπ}P(-τ)` is real for every radius.  This is what
Rolle needs at the right end of `[θ, π]`. -/
@[simp] theorem ftPencilIm_pi (P : Polynomial ℝ) (τ : ℝ) : ftPencilIm P 1 τ π = 0 := by
  have hexp : Complex.exp (((((1 : ℕ) : ℝ) * π : ℝ)) * Complex.I) = -1 := by
    push_cast
    rw [one_mul, Complex.exp_pi_mul_I]
  rw [ftPencilIm, ftArcPoint_pi, eval_map_ofReal, hexp,
    show (-1 : ℂ) * ((P.eval (-τ) : ℝ) : ℂ) = ((-(P.eval (-τ)) : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_im _

/-- **At `θ = π` the `θ`-derivative is the critical polynomial at `-τ`.**  The
counterpart of `ftPencilImDeriv_zero`, which reads `-E(τ)` at the lower end. -/
theorem ftPencilImDeriv_pi (P : Polynomial ℝ) (τ : ℝ) :
    ftPencilImDeriv P 1 τ π = (ftCriticalReal P 1).eval (-τ) := by
  have hexp : Complex.exp (((((1 : ℕ) : ℝ) * π : ℝ)) * Complex.I) = -1 := by
    push_cast
    rw [one_mul, Complex.exp_pi_mul_I]
  rw [ftPencilImDeriv, ftCritical_map, ftArcPoint_pi, eval_map_ofReal, hexp,
    show -Complex.I * (-1 : ℂ) * (((ftCriticalReal P 1).eval (-τ) : ℝ) : ℂ)
      = Complex.I * (((ftCriticalReal P 1).eval (-τ) : ℝ) : ℂ) by ring]
  simp

/-- **The identification along any filter refining `π⁻`.**  A limit of the radius
there is a zero of `E` after reflection: `E(-L) = 0`. -/
theorem eval_ftCriticalReal_neg_eq_zero_of_tendsto {P : Polynomial ℝ} {T : ℝ → ℝ} {L : ℝ}
    {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝[<] π)
    (hzero : ∀ᶠ θ in 𝓝[<] π, ftPencilIm P 1 (T θ) θ = 0)
    (hT : Tendsto T l (𝓝 L)) :
    (ftCriticalReal P 1).eval (-L) = 0 := by
  have hrolle : ∀ θ : ℝ, ∃ η : ℝ, (θ < π ∧ ftPencilIm P 1 (T θ) θ = 0) →
      (η ∈ Ioo θ π ∧ ftPencilImDeriv P 1 (T θ) η = 0) := by
    intro θ
    by_cases hc : θ < π ∧ ftPencilIm P 1 (T θ) θ = 0
    · obtain ⟨w, hw, hw0⟩ := exists_hasDerivAt_eq_zero (f := fun s => ftPencilIm P 1 (T θ) s)
        (f' := fun s => ftPencilImDeriv P 1 (T θ) s) hc.1
        (fun s _ => ((hasDerivAt_ftPencilIm P 1 (T θ) s).continuousAt).continuousWithinAt)
        (by rw [hc.2, ftPencilIm_pi])
        (fun s _ => hasDerivAt_ftPencilIm P 1 (T θ) s)
      exact ⟨w, fun _ => ⟨hw, hw0⟩⟩
    · exact ⟨0, fun hh => absurd hh hc⟩
  choose η hη using hrolle
  have hgood : ∀ᶠ θ in l, η θ ∈ Ioo θ π ∧ ftPencilImDeriv P 1 (T θ) (η θ) = 0 := by
    filter_upwards [hl hzero, hl self_mem_nhdsWithin] with θ h0 hlt using hη θ ⟨hlt, h0⟩
  have hid : Tendsto (fun θ : ℝ => θ) l (𝓝 π) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mono_left hl
  have hηtend : Tendsto η l (𝓝 π) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun θ : ℝ => θ) (h := fun _ : ℝ => π) hid tendsto_const_nhds ?_ ?_
    · filter_upwards [hgood] with θ hθ using hθ.1.1.le
    · filter_upwards [hgood] with θ hθ using hθ.1.2.le
  have hprod : Tendsto (fun θ : ℝ => (T θ, η θ)) l (𝓝 (L, π)) := hT.prodMk_nhds hηtend
  have hcont : Tendsto ((fun p : ℝ × ℝ => ftPencilImDeriv P 1 p.1 p.2)
      ∘ (fun θ : ℝ => (T θ, η θ))) l (𝓝 (ftPencilImDeriv P 1 L π)) :=
    ((continuous_ftPencilImDeriv P 1).tendsto (L, π)).comp hprod
  simp only [Function.comp_def] at hcont
  have hzero' : Tendsto (fun θ => ftPencilImDeriv P 1 (T θ) (η θ)) l (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hgood] with θ hθ using hθ.2.symm
  have := tendsto_nhds_unique hcont hzero'
  rwa [ftPencilImDeriv_pi] at this

/-- Every cluster point of the radius at `π⁻` reflects to a zero of `E`. -/
theorem eval_ftCriticalReal_neg_eq_zero_of_mapClusterPt {P : Polynomial ℝ} {T : ℝ → ℝ} {x : ℝ}
    (hzero : ∀ᶠ θ in 𝓝[<] π, ftPencilIm P 1 (T θ) θ = 0)
    (hx : MapClusterPt x (𝓝[<] π) T) : (ftCriticalReal P 1).eval (-x) = 0 := by
  set l : Filter ℝ := 𝓝[<] π ⊓ Filter.comap T (𝓝 x) with hldef
  have hne : l.NeBot := by
    rw [hldef, Filter.inf_neBot_iff]
    intro s hs t ht
    obtain ⟨u, hu, hut⟩ := ht
    obtain ⟨θ, hθs, hθu⟩ := (Filter.frequently_iff.1 (mapClusterPt_iff_frequently.1 hx u hu)) hs
    exact ⟨θ, hθs, hut hθu⟩
  have hle : l ≤ 𝓝[<] π := inf_le_left
  have hT : Tendsto T l (𝓝 x) :=
    le_trans (Filter.map_mono inf_le_right) Filter.map_comap_le
  exact eval_ftCriticalReal_neg_eq_zero_of_tendsto (l := l) hle hzero hT

/-- **The intermediate-value step at a left endpoint.**  The mirror of
`mapClusterPt_of_mem_Ioo`: a function continuous just below `b` that clusters at
two values there clusters at every value between them. -/
theorem mapClusterPt_of_mem_Ioo_nhdsLT {T : ℝ → ℝ} {b δ : ℝ} (hδ : δ < b)
    (hcont : ContinuousOn T (Ioo δ b)) {x₁ x₂ y : ℝ}
    (h1 : MapClusterPt x₁ (𝓝[<] b) T) (h2 : MapClusterPt x₂ (𝓝[<] b) T)
    (hy : y ∈ Ioo x₁ x₂) : MapClusterPt y (𝓝[<] b) T := by
  have hfreq : ∃ᶠ θ in 𝓝[<] b, T θ = y := by
    rw [Filter.frequently_iff]
    intro s hs
    obtain ⟨δ', hδ'lt, hδ'⟩ : ∃ δ' < b, Ioo δ' b ⊆ s ∩ Ioo δ b :=
      mem_nhdsLT_iff_exists_Ioo_subset.1 (Filter.inter_mem hs (Ioo_mem_nhdsLT hδ))
    have hbasis : Ioo δ' b ∈ 𝓝[<] b := Ioo_mem_nhdsLT hδ'lt
    obtain ⟨θ₁, hθ₁mem, hθ₁⟩ :=
      (Filter.frequently_iff.1 (h1.frequently (eventually_lt_nhds hy.1))) hbasis
    obtain ⟨θ₂, hθ₂mem, hθ₂⟩ :=
      (Filter.frequently_iff.1 (h2.frequently (eventually_gt_nhds hy.2))) hbasis
    have hsub : uIcc θ₁ θ₂ ⊆ Ioo δ' b :=
      (Set.ordConnected_Ioo).uIcc_subset hθ₁mem hθ₂mem
    have hsub2 : uIcc θ₁ θ₂ ⊆ Ioo δ b := fun z hz => (hδ' (hsub hz)).2
    obtain ⟨θ₃, hθ₃mem, hθ₃⟩ := intermediate_value_uIcc (f := T) (hcont.mono hsub2)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hθ₁.le, hθ₂.le⟩)
    exact ⟨θ₃, (hδ' (hsub hθ₃mem)).1, hθ₃⟩
  rw [mapClusterPt_iff_frequently]
  intro u hu
  exact hfreq.mono fun θ hθ => hθ ▸ mem_of_mem_nhds hu

/-! ### The limit -/

/-- **The upper-endpoint limit at `r = 1`.**  As `θ ↑ π` the radius converges to
a positive `L` with `E(-L) = 0`.  The arc point `τ(θ)e^{-iθ}` therefore runs to
`-L < 0`, which is the `t_b` of `eq:ab-def` — the negative critical point of
`g` that `Forgacs2017RationalDenominator` Lemma 5 supplies and that fixes the
finite upper endpoint `b = g(t_b)` at `r = 1`.

The argument is `exists_tendsto_ftTau_nhdsGT_zero_of_two_le`'s, with
`ftTau_le_two_mul_of_lt_pi` in place of `ftTau_le_div_cos`: the radius stays in a
compact interval, every cluster point reflects to a zero of `E`, that zero set is
finite, and a continuous function cannot cluster at two values without clustering
at every value between. 
**Differs from the paper's route.**  The paper takes the upper endpoint from the
critical polynomial: `t_b` is *defined* as the negative critical point of `g`,
and `b = g(t_b)` follows.  Here the limit is produced first, from the angle count
alone, and its identification as a zero of `E` comes afterwards through the same
Rolle argument `FTBranchEndpoint` runs at `0⁺`.  Nothing is assumed about the
number or the sign of the critical points of `g`; that `E` has finitely many
zeros is all that is used, and the negativity of `t_b` is a conclusion. -/
theorem exists_tendsto_ftTau_nhdsLT_pi {n : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0 := by
  classical
  have hπ := pi_gt_three
  have hn : 0 < n := by omega
  set P : Polynomial ℝ := ftRootPolyReal c a with hPdef
  set A : ℝ := ∑ k, a k with hAdef
  have hA : ∀ k, a k ≤ A :=
    fun k => Finset.single_le_sum (f := a) (fun i _ => (ha i).le) (Finset.mem_univ k)
  have hApos : 0 < A :=
    Finset.sum_pos (fun k _ => ha k) (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  -- the arc at `r = 1` is `(0, π)`
  have harc : ∀ θ ∈ Ioo (π - 1 / 2 : ℝ) π, θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    intro θ hθ
    refine ⟨by linarith [hθ.1], ?_⟩
    push_cast
    rw [div_one]
    exact hθ.2
  have hball : ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), FTBranchAt a 1 (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha le_rfl (Or.inl hn2) hθ
  have hwin : Ioo (π - 1 / 2 : ℝ) π ∈ 𝓝[<] π := Ioo_mem_nhdsLT (by linarith)
  -- the radius stays in a compact interval
  have hmem : ∀ᶠ θ in 𝓝[<] π, ftTau a 1 (n - 1) θ ∈ Icc 0 (2 * A) := by
    filter_upwards [hwin] with θ hθ
    have hb := hball θ (harc θ hθ)
    exact ⟨(ftTau_pos hb).le, ftTau_le_two_mul_of_lt_pi hn2 ha hA hθ hb⟩
  -- the branch equation, on the whole window
  have hzero : ∀ᶠ θ in 𝓝[<] π, ftPencilIm P 1 (ftTau a 1 (n - 1) θ) θ = 0 := by
    filter_upwards [hwin] with θ hθ
    have harc' := harc θ hθ
    exact ftPencilIm_eq_zero c ha (ftArc_subset le_rfl harc') (hball θ harc')
  -- `E(0) ≠ 0`, so `E ≠ 0` and its zero set is finite
  have hE0 : (ftCriticalReal P 1).eval 0 ≠ 0 := by
    have hprod : 0 < ∏ k, (a k - (0 : ℝ)) := Finset.prod_pos fun k _ => by simpa using ha k
    have hev : (ftCriticalReal P 1).eval 0 = -(c * ∏ k, (a k - (0 : ℝ))) := by
      rw [eval_ftCriticalReal, hPdef, eval_ftRootPolyReal]
      push_cast
      ring
    rw [hev]
    exact neg_ne_zero.2 (ne_of_gt (mul_pos hc hprod))
  have hEne : ftCriticalReal P 1 ≠ 0 := fun h => hE0 (by rw [h]; simp)
  have hfin : Set.Finite {t : ℝ | (ftCriticalReal P 1).IsRoot t} :=
    Polynomial.finite_setOfPred_isRoot hEne
  -- every cluster point reflects to a zero of `E`
  have hcluster : ∀ x, MapClusterPt x (𝓝[<] π) (ftTau a 1 (n - 1)) →
      (ftCriticalReal P 1).eval (-x) = 0 := fun x hx =>
    eval_ftCriticalReal_neg_eq_zero_of_mapClusterPt hzero hx
  have hcontOn : ContinuousOn (ftTau a 1 (n - 1)) (Ioo (π - 1 / 2 : ℝ) π) := fun θ hθ =>
    (continuousAt_ftTau hn ha le_rfl (harc θ hθ) hball).continuousWithinAt
  have huniq : ∀ x₁ x₂, MapClusterPt x₁ (𝓝[<] π) (ftTau a 1 (n - 1)) →
      MapClusterPt x₂ (𝓝[<] π) (ftTau a 1 (n - 1)) → x₁ = x₂ := by
    intro x₁ x₂ h1 h2
    by_contra hne
    have hlt2 : (π - 1 / 2 : ℝ) < π := by linarith
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨y, hy, hyroot⟩ : ∃ y ∈ Ioo x₁ x₂, ¬ (ftCriticalReal P 1).IsRoot (-y) := by
        by_contra hall
        push Not at hall
        refine (Set.Ioo_infinite hlt) (Set.Finite.subset (hfin.image (fun t => -t)) ?_)
        intro y hy
        exact ⟨-y, hall y hy, by ring⟩
      exact hyroot (hcluster y (mapClusterPt_of_mem_Ioo_nhdsLT hlt2 hcontOn h1 h2 hy))
    · obtain ⟨y, hy, hyroot⟩ : ∃ y ∈ Ioo x₂ x₁, ¬ (ftCriticalReal P 1).IsRoot (-y) := by
        by_contra hall
        push Not at hall
        refine (Set.Ioo_infinite hlt) (Set.Finite.subset (hfin.image (fun t => -t)) ?_)
        intro y hy
        exact ⟨-y, hall y hy, by ring⟩
      exact hyroot (hcluster y (mapClusterPt_of_mem_Ioo_nhdsLT hlt2 hcontOn h2 h1 hy))
  -- a cluster point exists and is unique, so the radius converges
  obtain ⟨L, hLmem, hLcl⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * A)).exists_clusterPt
    (f := Filter.map (ftTau a 1 (n - 1)) (𝓝[<] π)) (Filter.le_principal_iff.2 hmem)
  have htend : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L) :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * A)).tendsto_nhds_of_unique_mapClusterPt hmem
      fun x _ hxc => huniq x L hxc hLcl
  have hLroot : (ftCriticalReal P 1).eval (-L) = 0 := hcluster L hLcl
  refine ⟨L, ?_, htend, hLroot⟩
  rcases lt_or_eq_of_le hLmem.1 with h | h
  · exact h
  · exact absurd (by rw [← h] at hLroot; simpa using hLroot) hE0

/-- **The upper-endpoint dichotomy of `eq:ab-def`.**  The radius always converges
at `θ ↑ π/r`; the limit is `0` for `r ≥ 2` and positive for `r = 1`, where it
reflects to the negative critical point `t_b` of `g`.

The split is the one the paper's endpoint convention is written around, and both
halves are needed: neither statement holds in the other regime. -/
theorem exists_tendsto_ftTau_nhdsLT_arc_end {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, Tendsto (ftTau a r (n - 1)) (𝓝[<] (π / r)) (𝓝 L) ∧
      (r = 1 → 0 < L ∧ (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) ∧
      (2 ≤ r → L = 0) := by
  rcases eq_or_lt_of_le hr with hr1 | hr2
  · obtain ⟨L, hLpos, htend, hLroot⟩ := exists_tendsto_ftTau_nhdsLT_pi hn2 ha hc
    refine ⟨L, ?_, fun _ => ⟨hLpos, hLroot⟩, fun h => absurd h (by omega)⟩
    subst hr1
    simpa using htend
  · exact ⟨0, tendsto_ftTau_nhdsLT_upper hn2 ha hr2, fun h => absurd h (by omega), fun _ => rfl⟩

/-! ### The spectral parameter at the arc's upper end

`FTGeometryBranch.ft_geometry_at_branch` and its unbounded counterpart carry two
hypotheses each.  One of them, `hzb`, is the upper-endpoint limit of `z`, and it
is a statement about the constructed branch rather than about an assumed one.
Both conventions of `eq:ab-def` are discharged here, each from the limit of `τ`
in its own regime:

* `r ≥ 2` — `FTBranchUpper.tendsto_ftTau_nhdsLT_upper` collapses the radius, and
  `tendsto_ftBranchZ_atTop_of_tendsto_ftTau_zero` turns that into `z → atTop`,
  which is `b = +∞`.
* `r = 1` — `exists_tendsto_ftTau_nhdsLT_pi` gives the positive limit `L`, and
  `tendsto_ftBranchZ_upper_pi` evaluates `z` at the limiting branch point `-L`,
  which is the finite `b = g(t_b)`.

Both restrict `𝓝[<] (π/r)` to the arc's own filter `𝓝[Ioo 0 (π/r)] (π/r)`, which
is the weaker one, so nothing is assumed by the restriction. -/

/-- **`hzb` at `r ≥ 2`, discharged.**  The spectral parameter diverges upward at
the arc's upper end — `eq:ab-def`'s `b = +∞`. -/
theorem tendsto_ftBranchZ_atTop_arc_end_of_pos {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    Filter.Tendsto (ftBranchZ a c r (n - 1)) (𝓝[Ioo 0 (π / r)] (π / r)) Filter.atTop := by
  have hr1 : 1 ≤ r := by omega
  have hr0 : (0 : ℝ) < r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    linarith
  have harc : (0 : ℝ) < π / r := div_pos pi_pos hr0
  obtain ⟨-, -, hmono, -⟩ := ft_branch_supplies (a := a) (c := c) hn ha hc hr1 (Or.inr hr)
  have hmem : ∀ᶠ θ in 𝓝[Ioo 0 (π / r)] (π / r),
      θ ∈ Ioo 0 π ∧ FTBranchAt a r (n - 1) θ := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact ⟨ftArc_subset hr1 hθ, ftBranchAt_of_arc_principal hn ha hr1 (Or.inr hr) hθ⟩
  exact tendsto_ftBranchZ_atTop_of_tendsto_ftTau_zero hr1 hc.ne' ha harc hmono hmem
    ((tendsto_ftTau_nhdsLT_upper_of_pos hn ha hr).mono_left
      (nhdsWithin_mono _ Ioo_subset_Iio_self))

/-- `tendsto_ftBranchZ_atTop_arc_end_of_pos` at `2 ≤ n`, the form consumers were
written against. -/
theorem tendsto_ftBranchZ_atTop_arc_end {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    Filter.Tendsto (ftBranchZ a c r (n - 1)) (𝓝[Ioo 0 (π / r)] (π / r)) Filter.atTop :=
  tendsto_ftBranchZ_atTop_arc_end_of_pos (by omega) ha hc hr

/-- **`hzb` at `r = 1`, discharged.**  The finite upper endpoint: `z` converges
to `-P(-L)/(-L)^r` at the limiting branch point `-L`, which is `b = g(t_b)`. -/
theorem exists_tendsto_ftBranchZ_arc_end_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ b : ℝ, Filter.Tendsto (ftBranchZ a c 1 (n - 1))
      (𝓝[Ioo 0 (π / ((1 : ℕ) : ℝ))] (π / ((1 : ℕ) : ℝ))) (𝓝 b) := by
  have hcast : π / ((1 : ℕ) : ℝ) = π := by push_cast; rw [div_one]
  obtain ⟨L, hL, hτ, -⟩ := exists_tendsto_ftTau_nhdsLT_pi hn2 ha hc
  refine ⟨-(ftRootPolyReal c a).eval (-L) / (-L) ^ 1, ?_⟩
  rw [hcast]
  refine tendsto_ftBranchZ_upper_pi ha hL ?_
    (hτ.mono_left (nhdsWithin_mono _ (fun x hx => (hcast ▸ hx.2 : x < π))))
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ' : θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) := by rw [hcast]; exact hθ
  exact ⟨ftArc_subset le_rfl hθ',
    ftBranchAt_of_arc_principal (by omega) ha le_rfl (Or.inl hn2) hθ'⟩

/-- **`thm:FT-geometry` at the constructed branch, `r ≥ 2`, with `hzb` retired.**
`ft_geometry_at_branch_unbounded`'s two hypotheses become one: only the
minimum-modulus gap of `Forgacs2017RationalDenominator` Props. 1--2 is still
assumed, and the upper-endpoint limit is supplied. -/
theorem ft_geometry_at_branch_unbounded_of_two_le {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hmin : ∀ θ ∈ Ioo 0 (π / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a r (n - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ) →
        ftTau a r (n - 1) θ < ‖w‖) :
    ∃ za : ℝ,
      ftBranchZ a c r (n - 1) '' Ioo 0 (π / r) = Ioi za
        ∧ (∀ θ ∈ Ioo 0 (π / r),
            (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a r (n - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a r (n - 1)) θ‖ = ftTau a r (n - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ)‖
                  = ftTau a r (n - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / r), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a r (n - 1) θ →
                w = ftPrincipal (ftTau a r (n - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ)) :=
  ft_geometry_at_branch_unbounded hn2 ha hc (by omega)
    (tendsto_ftBranchZ_atTop_arc_end hn2 ha hc hr) hmin

/-- **`thm:FT-geometry` at the constructed branch, `r = 1`, with `hzb` retired.**
The finite convention of `eq:ab-def`.  `n = 2` is included: the radius is
constant there — `rem:quadratic-case` — and nothing below needs it to move.
`FTGeometryBoundary.ft_geometry_at_branch_quadratic` is this at `n = 2`, with
`hmin` supplied by a degree count. -/
theorem ft_geometry_at_branch_of_two_le {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hmin : ∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a 1 (n - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ) →
        ftTau a 1 (n - 1) θ < ‖w‖) :
    ∃ za b : ℝ,
      ftBranchZ a c 1 (n - 1) '' Ioo 0 (π / ((1 : ℕ) : ℝ)) = Ioo za b
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)),
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a 1 (n - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a 1 (n - 1)) θ‖ = ftTau a 1 (n - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)‖
                  = ftTau a 1 (n - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a 1 (n - 1) θ →
                w = ftPrincipal (ftTau a 1 (n - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) := by
  obtain ⟨b, hb⟩ := exists_tendsto_ftBranchZ_arc_end_pi (by omega) ha hc
  obtain ⟨za, hza⟩ :=
    ft_geometry_at_branch (n := n) (r := 1) (by omega) ha hc le_rfl hb hmin
  exact ⟨za, b, hza⟩

/-- `ft_geometry_at_branch_of_two_le` at `3 ≤ n`, the form consumers were written
against. -/
theorem ft_geometry_at_branch_of_three_le {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hmin : ∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a 1 (n - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ) →
        ftTau a 1 (n - 1) θ < ‖w‖) :
    ∃ za b : ℝ,
      ftBranchZ a c 1 (n - 1) '' Ioo 0 (π / ((1 : ℕ) : ℝ)) = Ioo za b
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)),
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a 1 (n - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a 1 (n - 1)) θ‖ = ftTau a 1 (n - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)‖
                  = ftTau a 1 (n - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a 1 (n - 1) θ →
                w = ftPrincipal (ftTau a 1 (n - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) :=
  ft_geometry_at_branch_of_two_le (by omega) ha hc hmin

/-- **Non-vacuity at `r = 1`.**  `Q(t) = (1-t)(2-t)(3-t)`, the pencil whose
endpoint radius is `0.879385…`; the limit is positive and reflects to a zero of
`E` on the negative axis. -/
theorem exists_tendsto_ftTau_nhdsLT_pi_witness :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (ftTau (fun k : Fin 3 => (k : ℝ) + 1) 1 (3 - 1)) (𝓝[<] π) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal 1 (fun k : Fin 3 => (k : ℝ) + 1)) 1).eval (-L) = 0 :=
  exists_tendsto_ftTau_nhdsLT_pi (by norm_num) (fun k => by positivity) one_pos

/-- **Non-vacuity in the other regime.**  `Q(t) = (1-t)(2-t)` at `r = 2`, where
the same dichotomy returns `L = 0`, read out of it rather than assumed. -/
theorem tendsto_ftTau_nhdsLT_arc_end_witness :
    Tendsto (ftTau (fun k : Fin 2 => (k : ℝ) + 1) 2 (2 - 1)) (𝓝[<] (π / 2)) (𝓝 0) := by
  obtain ⟨L, htend, -, hzero⟩ :=
    exists_tendsto_ftTau_nhdsLT_arc_end (n := 2) (r := 2) (c := 1)
      (a := fun k : Fin 2 => (k : ℝ) + 1) le_rfl (fun k => by positivity) (by norm_num) one_pos
  rw [hzero le_rfl] at htend
  simpa using htend

end ForgacsTran
