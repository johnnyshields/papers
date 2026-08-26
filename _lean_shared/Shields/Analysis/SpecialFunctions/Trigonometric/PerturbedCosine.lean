/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Zeros of a perturbed cosine with a fast phase

Consider a family `Gₙ = cos Ψₙ + Eₙ` on a compact interval, where the phase `Ψₙ = nϑ + δ` turns
at a rate bounded below (`-ϑ' ≥ c > 0`), the shift has bounded derivative (`|δ'| ≤ K`), and the
perturbation is geometrically small together with its derivative (`|Eₙ|, |Eₙ'| ≤ Cqⁿ`, `q < 1`).

For all large `n` the zeros of `Gₙ` are **simple**, there is **at least one in each cell** cut out
by consecutive points of `Ψₙ⁻¹(πℤ)`, and there is **at most one** on any stretch where the cosine
stays small — so the zeros are spaced like the phase, one per half-period, at scale `O(1/n)`.

Everything rests on one estimate.  At a zero the cosine equals `-Eₙ`, hence is `O(qⁿ)`, so the
sine is bounded away from `0`; the phase derivative is at least `nc - K` in modulus; and the
perturbation's derivative is `O(qⁿ)`.  Therefore

`|Gₙ'| ≥ (nc - K)/2 - Cqⁿ`,

which is positive for all large `n`, uniformly over the interval, with a threshold depending only
on `c`, `K`, `C` and `q`.  That gives simplicity outright, and with Rolle it gives uniqueness on
any stretch where the cosine stays small.  Existence in a cell is the intermediate value theorem
against the alternation of `cos` at consecutive points of `Ψₙ⁻¹(πℤ)`, which a perturbation smaller
than `1` cannot remove.

## Main definitions

* `Shields.ClockData`: the hypotheses above, bundled.
* `Shields.ClockData.psi`, `Shields.ClockData.clockFn`, `Shields.ClockData.clockDeriv`: the phase,
  the function, and its derivative.

## Main results

* `Shields.ClockData.abs_clockDeriv_ge`: the derivative estimate, with explicit constants.
* `Shields.ClockData.eventually_zeros_simple`: **simplicity** of every zero, for large `n`.
* `Shields.ClockData.exists_zero_of_cell`: **a zero in each cell**.
* `Shields.ClockData.eventually_injOn_of_abs_cos_le`: **at most one zero** where the cosine is
  small.
* `Shields.ClockData.exists_spacing`, `Shields.ClockData.sub_le_of_psi_diff`: the spacing
  identity, and the `O(1/n)` scale.
* `Shields.pureClock`: the hypotheses are inhabited, by `cos(-nx)`.

## Implementation notes

The hypotheses are bundled into a structure rather than carried as a dozen arguments because every
result needs most of them, and because the two conclusions with an `∀ᶠ n` quantifier share the same
two thresholds (`eventually_small`, `eventually_large`), which are stated once against the bundle.

Derivatives are supplied as data (`θ'`, `δ'`, `Eₙ'`) with `HasDerivAt` hypotheses rather than taken
as `deriv`, so that no differentiability side conditions have to be discharged at each use and the
bounds can be stated directly on the supplied functions.

"Clock" is the term of art for this phenomenon — zeros advancing one per half-period of a fast
phase, as for the zeros of orthogonal polynomials on the unit circle.

Not proved here: the `O(n⁻²)` refinement of the spacing, which needs a modulus of continuity for
`ϑ'` and a cell decomposition indexing the zeros before consecutive ones can be compared.

## Tags

cosine, perturbation, zeros, simple zeros, clock behavior, spacing, Rolle
-/

open Filter Set Topology

namespace Shields

/-- The hypotheses for a perturbed cosine `cos(nϑ + δ) + Eₙ` with a fast, monotone phase. -/
structure ClockData (a b : ℝ) where
  /-- The phase. -/
  θ : ℝ → ℝ
  /-- Its derivative. -/
  θ' : ℝ → ℝ
  /-- The phase shift. -/
  δ : ℝ → ℝ
  /-- Its derivative. -/
  δ' : ℝ → ℝ
  /-- The perturbation at each order. -/
  E : ℕ → ℝ → ℝ
  /-- Its derivative. -/
  E' : ℕ → ℝ → ℝ
  /-- The lower bound for `-θ'`. -/
  c : ℝ
  /-- The bound for `|δ'|`. -/
  K : ℝ
  /-- The perturbation's constant. -/
  C : ℝ
  /-- The perturbation's ratio. -/
  q : ℝ
  hθ : ∀ x ∈ Set.Icc a b, HasDerivAt θ (θ' x) x
  hδ : ∀ x ∈ Set.Icc a b, HasDerivAt δ (δ' x) x
  hE : ∀ n, ∀ x ∈ Set.Icc a b, HasDerivAt (E n) (E' n x) x
  hc : 0 < c
  hθ'le : ∀ x ∈ Set.Icc a b, θ' x ≤ -c
  hδ'le : ∀ x ∈ Set.Icc a b, |δ' x| ≤ K
  hq : 0 ≤ q
  hq1 : q < 1
  hEle : ∀ n, ∀ x ∈ Set.Icc a b, |E n x| ≤ C * q ^ n
  hE'le : ∀ n, ∀ x ∈ Set.Icc a b, |E' n x| ≤ C * q ^ n

namespace ClockData

variable {a b : ℝ} (D : ClockData a b)

/-- The phase `Ψₙ = nϑ + δ`. -/
noncomputable def psi (n : ℕ) (x : ℝ) : ℝ := (n : ℝ) * D.θ x + D.δ x

/-- The perturbed cosine `Gₙ = cos Ψₙ + Eₙ`. -/
noncomputable def clockFn (n : ℕ) (x : ℝ) : ℝ := Real.cos (D.psi n x) + D.E n x

/-- Its derivative. -/
noncomputable def clockDeriv (n : ℕ) (x : ℝ) : ℝ :=
  -Real.sin (D.psi n x) * ((n : ℝ) * D.θ' x + D.δ' x) + D.E' n x

theorem hasDerivAt_psi (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    HasDerivAt (D.psi n) ((n : ℝ) * D.θ' x + D.δ' x) x :=
  ((D.hθ x hx).const_mul (n : ℝ)).add (D.hδ x hx)

theorem hasDerivAt_clockFn (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    HasDerivAt (D.clockFn n) (D.clockDeriv n x) x := by
  have hcos : HasDerivAt (fun y => Real.cos (D.psi n y))
      (-Real.sin (D.psi n x) * ((n : ℝ) * D.θ' x + D.δ' x)) x :=
    (Real.hasDerivAt_cos (D.psi n x)).comp x (D.hasDerivAt_psi n hx)
  exact hcos.add (D.hE n x hx)

/-! ### The estimate -/

/-- The phase derivative is at most `-(nc - K)`. -/
theorem psi_deriv_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (n : ℝ) * D.θ' x + D.δ' x ≤ -((n : ℝ) * D.c - D.K) := by
  have h1 : (n : ℝ) * D.θ' x ≤ -((n : ℝ) * D.c) := by
    have := mul_le_mul_of_nonneg_left (D.hθ'le x hx) (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have h2 : D.δ' x ≤ D.K := (abs_le.mp (D.hδ'le x hx)).2
  linarith

/-- A small cosine forces a sine bounded away from zero. -/
theorem abs_sin_ge_of_abs_cos_le {y : ℝ} (h : |Real.cos y| ≤ 1 / 2) : 1 / 2 ≤ |Real.sin y| := by
  by_contra hcon
  rw [not_le] at hcon
  have hpy := Real.sin_sq_add_cos_sq y
  nlinarith [sq_abs (Real.sin y), sq_abs (Real.cos y), abs_nonneg (Real.sin y),
    abs_nonneg (Real.cos y)]

/-- **The derivative estimate.**  Where the sine is bounded away from zero, so is the derivative —
by the phase's own growth, less the perturbation. -/
theorem abs_clockDeriv_ge (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc a b)
    (hsin : 1 / 2 ≤ |Real.sin (D.psi n x)|) (hn : D.K ≤ (n : ℝ) * D.c) :
    ((n : ℝ) * D.c - D.K) / 2 - D.C * D.q ^ n ≤ |D.clockDeriv n x| := by
  have hpsi := D.psi_deriv_le n hx
  have h0 : (0 : ℝ) ≤ (n : ℝ) * D.c - D.K := by linarith
  have hbig : (n : ℝ) * D.c - D.K ≤ |(n : ℝ) * D.θ' x + D.δ' x| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hprod : ((n : ℝ) * D.c - D.K) / 2
      ≤ |(-Real.sin (D.psi n x)) * ((n : ℝ) * D.θ' x + D.δ' x)| := by
    rw [abs_mul, abs_neg]
    nlinarith [abs_nonneg (Real.sin (D.psi n x)), abs_nonneg ((n : ℝ) * D.θ' x + D.δ' x)]
  have htri := abs_sub_abs_le_abs_sub
    ((-Real.sin (D.psi n x)) * ((n : ℝ) * D.θ' x + D.δ' x)) (-(D.E' n x))
  rw [abs_neg, sub_neg_eq_add] at htri
  have hE := D.hE'le n x hx
  rw [clockDeriv]
  linarith

/-- At a zero the cosine is the perturbation's negative, hence small. -/
theorem abs_cos_le_of_zero {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc a b) (hzero : D.clockFn n x = 0) :
    |Real.cos (D.psi n x)| ≤ D.C * D.q ^ n := by
  have hcos : Real.cos (D.psi n x) = -D.E n x := by
    have h := hzero
    rw [clockFn] at h
    linarith
  rw [hcos, abs_neg]
  exact D.hEle n x hx

/-! ### The eventual thresholds -/

private theorem eventually_small : ∀ᶠ n : ℕ in atTop, D.C * D.q ^ n ≤ 1 / 2 := by
  have hqz : Tendsto (fun n : ℕ => D.C * D.q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.hq D.hq1).const_mul D.C
  exact (Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2) hqz).mono
    fun n hn => hn.le

private theorem eventually_large : ∀ᶠ n : ℕ in atTop, D.K + 3 ≤ (n : ℝ) * D.c := by
  have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const D.hc
  exact this.eventually_ge_atTop (D.K + 3)

/-! ### Simplicity -/

/-- **Simplicity.**  For all large `n` every zero of `Gₙ` in the interval is simple, with a
threshold depending only on `c`, `K`, `C` and `q`. -/
theorem eventually_zeros_simple :
    ∀ᶠ n in atTop, ∀ x ∈ Set.Icc a b, D.clockFn n x = 0 → D.clockDeriv n x ≠ 0 := by
  filter_upwards [D.eventually_small, D.eventually_large] with n hn1 hn2 x hx hzero hd
  have hcos : |Real.cos (D.psi n x)| ≤ 1 / 2 := (D.abs_cos_le_of_zero hx hzero).trans hn1
  have hge := D.abs_clockDeriv_ge n hx (abs_sin_ge_of_abs_cos_le hcos) (by linarith)
  rw [hd, abs_zero] at hge
  linarith

/-! ### A zero in each cell -/

/-- **A zero in each cell.**  At consecutive points of `Ψₙ⁻¹(πℤ)` the cosine takes `±1` in
alternation, and a perturbation smaller than `1` cannot remove the sign change. -/
theorem exists_zero_of_cell {n : ℕ} {x₀ x₁ : ℝ} (hlt : x₀ < x₁)
    (hsub : Set.Icc x₀ x₁ ⊆ Set.Icc a b) (j : ℤ)
    (h₀ : D.psi n x₀ = j * Real.pi) (h₁ : D.psi n x₁ = (j - 1) * Real.pi)
    (hsmall : D.C * D.q ^ n < 1) :
    ∃ x ∈ Set.Ioo x₀ x₁, D.clockFn n x = 0 := by
  have hx₀ : x₀ ∈ Set.Icc a b := hsub (Set.left_mem_Icc.mpr hlt.le)
  have hx₁ : x₁ ∈ Set.Icc a b := hsub (Set.right_mem_Icc.mpr hlt.le)
  have hcont : ContinuousOn (D.clockFn n) (Set.Icc x₀ x₁) := fun x hx =>
    (D.hasDerivAt_clockFn n (hsub hx)).continuousAt.continuousWithinAt
  have hc₀ : Real.cos (D.psi n x₀) = (-1 : ℝ) ^ j := by rw [h₀, Real.cos_int_mul_pi]
  have hc₁ : Real.cos (D.psi n x₁) = -((-1 : ℝ) ^ j) := by
    have hcast : ((j : ℝ) - 1) * Real.pi = ((j - 1 : ℤ) : ℝ) * Real.pi := by push_cast; ring
    rw [h₁, hcast, Real.cos_int_mul_pi, zpow_sub₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_one,
      div_neg, div_one]
  have hb₀ := abs_le.mp ((D.hEle n x₀ hx₀).trans hsmall.le)
  have hb₁ := abs_le.mp ((D.hEle n x₁ hx₁).trans hsmall.le)
  have e₀ : D.clockFn n x₀ = (-1 : ℝ) ^ j + D.E n x₀ := by rw [clockFn, hc₀]
  have e₁ : D.clockFn n x₁ = -((-1 : ℝ) ^ j) + D.E n x₁ := by rw [clockFn, hc₁]
  have hb₀' : |D.E n x₀| < 1 := lt_of_le_of_lt (D.hEle n x₀ hx₀) hsmall
  have hb₁' : |D.E n x₁| < 1 := lt_of_le_of_lt (D.hEle n x₁ hx₁) hsmall
  have hb₀'' := abs_lt.mp hb₀'
  have hb₁'' := abs_lt.mp hb₁'
  rcases Int.even_or_odd j with hj | hj
  · have hp : ((-1 : ℝ)) ^ j = 1 := hj.neg_one_zpow
    have hpos : 0 < D.clockFn n x₀ := by rw [e₀, hp]; linarith [hb₀''.1]
    have hneg : D.clockFn n x₁ < 0 := by rw [e₁, hp]; linarith [hb₁''.2]
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' hlt.le hcont
      (Set.mem_Ioo.mpr ⟨hneg, hpos⟩)
    exact ⟨x, hx, hfx⟩
  · have hp : ((-1 : ℝ)) ^ j = -1 := hj.neg_one_zpow
    have hneg : D.clockFn n x₀ < 0 := by rw [e₀, hp]; linarith [hb₀''.2]
    have hpos : 0 < D.clockFn n x₁ := by rw [e₁, hp]; linarith [hb₁''.1]
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hlt.le hcont
      (Set.mem_Ioo.mpr ⟨hneg, hpos⟩)
    exact ⟨x, hx, hfx⟩

/-! ### At most one zero where the cosine stays small -/

/-- **Uniqueness on a stretch where the cosine is small.**  There the derivative cannot vanish, so
Rolle forbids two zeros — which is what turns "a zero in each cell" into "exactly one". -/
theorem eventually_injOn_of_abs_cos_le :
    ∀ᶠ n in atTop, ∀ u w : ℝ, Set.Icc u w ⊆ Set.Icc a b →
      (∀ x ∈ Set.Icc u w, |Real.cos (D.psi n x)| ≤ 1 / 2) →
      Set.InjOn (D.clockFn n) (Set.Icc u w) := by
  filter_upwards [D.eventually_small, D.eventually_large] with n hn1 hn2 u w hsub hcos
  have hderiv : ∀ z ∈ Set.Icc u w, D.clockDeriv n z ≠ 0 := by
    intro z hz hd
    have hge := D.abs_clockDeriv_ge n (hsub hz)
      (abs_sin_ge_of_abs_cos_le (hcos z hz)) (by linarith)
    rw [hd, abs_zero] at hge
    linarith
  have hdiff : ∀ z ∈ Set.Icc a b, HasDerivAt (D.clockFn n) (D.clockDeriv n z) z :=
    fun z hz => D.hasDerivAt_clockFn n hz
  intro x hx y hy hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hss : Set.Icc x y ⊆ Set.Icc u w := Set.Icc_subset_Icc hx.1 hy.2
    obtain ⟨ξ, hξ, h0⟩ := exists_hasDerivAt_eq_zero hlt
      (fun z hz => (hdiff z (hsub (hss hz))).continuousAt.continuousWithinAt) hxy
      (fun z hz => hdiff z (hsub (hss (Set.Ioo_subset_Icc_self hz))))
    exact hderiv ξ (hss (Set.Ioo_subset_Icc_self hξ)) h0
  · have hss : Set.Icc y x ⊆ Set.Icc u w := Set.Icc_subset_Icc hy.1 hx.2
    obtain ⟨ξ, hξ, h0⟩ := exists_hasDerivAt_eq_zero hlt
      (fun z hz => (hdiff z (hsub (hss hz))).continuousAt.continuousWithinAt) hxy.symm
      (fun z hz => hdiff z (hsub (hss (Set.Ioo_subset_Icc_self hz))))
    exact hderiv ξ (hss (Set.Ioo_subset_Icc_self hξ)) h0

/-! ### The spacing -/

/-- **The spacing identity.**  The mean value theorem turns the phase difference between two
points into their distance times the phase derivative somewhere between — the exact form the
spacing `π/(-nϑ')` is read off. -/
theorem exists_spacing (n : ℕ) {x y : ℝ} (hlt : x < y) (hsub : Set.Icc x y ⊆ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo x y,
      D.psi n y - D.psi n x = ((n : ℝ) * D.θ' ξ + D.δ' ξ) * (y - x) := by
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (D.psi n)
    (fun z => (n : ℝ) * D.θ' z + D.δ' z) hlt
    (fun z hz => (D.hasDerivAt_psi n (hsub hz)).continuousAt.continuousWithinAt)
    (fun z hz => D.hasDerivAt_psi n (hsub (Set.Ioo_subset_Icc_self hz)))
  refine ⟨ξ, hξ, ?_⟩
  rw [hd, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hlt))]

/-- **The spacing is `O(1/n)`.**  Two points whose phases differ by a bounded amount are within
`Δ/(nc - K)` of each other, so consecutive zeros — whose phases differ by `π + O(qⁿ)` — are
`O(1/n)` apart. -/
theorem sub_le_of_psi_diff (n : ℕ) {x y : ℝ} (hlt : x < y) (hsub : Set.Icc x y ⊆ Set.Icc a b)
    (hn : D.K < (n : ℝ) * D.c) :
    y - x ≤ (D.psi n x - D.psi n y) / ((n : ℝ) * D.c - D.K) := by
  obtain ⟨ξ, hξ, hid⟩ := D.exists_spacing n hlt hsub
  have hξab : ξ ∈ Set.Icc a b := hsub (Set.Ioo_subset_Icc_self hξ)
  have hpos : (0 : ℝ) < (n : ℝ) * D.c - D.K := by linarith
  have hdle := D.psi_deriv_le n hξab
  have hylt : (0 : ℝ) < y - x := sub_pos.mpr hlt
  rw [le_div_iff₀ hpos]
  nlinarith [hid]

end ClockData

/-! ### The hypotheses are inhabited -/

/-- **`ClockData` is not an empty class.**  The pure clock `Gₙ(x) = cos(-nx)` inhabits it, with
`c = 1` and no perturbation at all — so the conclusions above are statements about something. -/
noncomputable def pureClock (a b : ℝ) : ClockData a b where
  θ := fun x => -x
  θ' := fun _ => -1
  δ := fun _ => 0
  δ' := fun _ => 0
  E := fun _ _ => 0
  E' := fun _ _ => 0
  c := 1
  K := 0
  C := 0
  q := 1 / 2
  hθ := fun x _ => (hasDerivAt_id x).neg
  hδ := fun _ _ => hasDerivAt_const _ _
  hE := fun _ _ _ => hasDerivAt_const _ _
  hc := one_pos
  hθ'le := fun _ _ => le_rfl
  hδ'le := fun _ _ => by simp
  hq := by norm_num
  hq1 := by norm_num
  hEle := fun _ _ _ => by simp
  hE'le := fun _ _ _ => by simp

@[simp] theorem pureClock_clockFn (a b : ℝ) (n : ℕ) (x : ℝ) :
    (pureClock a b).clockFn n x = Real.cos ((n : ℝ) * x) := by
  simp [ClockData.clockFn, ClockData.psi, pureClock]

end Shields
