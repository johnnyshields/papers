/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.FTGeometryClosure
import ForgacsTran.FTMinModulus.Propositions

/-!
# The argument cone at `r ≥ 2`, and `thm:FT-geometry` there

`FTMinModulus.ArgumentCone` reduced `thm:FT-geometry`'s minimum-modulus clause to
`hcone` — that a zero of the pencil in the closed disk of radius `τ(θ)` has
argument strictly inside `|arg| < π/r` — and `FTMinModulus.RealCritical` closed
`hcone` at `r = 1`, where the cone is the whole plane cut along the reals.  This
module closes it at every `r ≥ 2`, so `FTGeometryClosure`'s unbounded convention
carries no analytic hypothesis either.

## The dichotomy that replaces the two figures

`Forgacs2017RationalDenominator` Prop. 1 places the inner zero in the lens
`C₁ ∩ C₂` and then splits by whether the angle at the branch point is acute,
reading each case off a figure.  Both cases become an inequality in `τ` against
`x₁\cos θ`, `x₁` the smallest zero of `Q`:

* `τ ≤ x₁\cos θ` — `abs_arg_le_of_le_mul_cos`.  The two disk inequalities alone
  give `\cos(\arg w) ≥ \cos θ`, so the whole lens lies in `|arg| ≤ θ`, and `θ`
  is already inside the cone.  Nothing about `r` is used.
* `x₁\cos θ < τ` — `ftChord_lt_mul_sin`.  Then `R\cos(θ_1 - θ) = τ - x₁\cos θ`
  is positive, so `θ_1 - θ < π/2`; the angle sum puts `θ_1` above `rθ`, hence
  `θ_1 - θ` above `(r-1)θ`; and `R = x₁\sin θ/\sin(θ_1-θ)` then falls below
  `x₁\sin(π/r)` by the monotonicity of `\sin θ/\sin((r-1)θ)`, whose derivative
  numerator is `FTMinModulus.Propositions.sin_numerator_nonneg`.  A disk about a
  positive real point of radius below `x₁\sin α` sits inside `|arg| < α`.

**Differs from the paper's route.**  Their negative-real exclusion is a separate
paragraph, closed at `r = 1` by their Lemma 5 and asserted for `r ≥ 2` from the
picture — "the only way `C₁ ∩ C₂ ∩ ℝ₋ ≠ ∅` is if `r = 1`".  Here it is not a
separate step at all: both cases of the dichotomy bound `|\arg w|` strictly below
`π/r ≤ π/2`, which excludes the negative axis outright.  The odd `r ≥ 3` negative
axis, which `RealCritical` records as out of reach through their route, therefore
never has to be reached.

Only the *positive* real exclusion is still consumed, and only to keep
`|\arg w|` away from `0`; `RealCritical.negDivPow_lt_ftBranchZ_pos` supplies it at
every `r ≥ 1` and every multiplicity.

## Containment

`cone_at_branch_of_two_le` relates `ftDen (ftRootPoly c a) r (ftBranchZ …)`, the
zero `w`, `ftTau`, and `Complex.arg w`.  Its hypotheses are `2 ≤ n`,
`∀ k, 0 < a k`, `0 < c`, `2 ≤ r`, `θ ∈ Ioo 0 (π/r)`, and the two facts about `w`
that name it — that it is a zero and that it lies in the closed disk.  None of
them mentions `Complex.arg`; the bound on it is produced by the dichotomy above,
`abs_arg_le_of_le_mul_cos` in the far case and `ftChord_lt_mul_sin` in the near
one.  The hypotheses are jointly satisfiable: `FTGeometryAssembly.ft_branch_root_and_pos`
exhibits a zero of modulus exactly `ftTau a r (n-1) θ` at every angle of the arc.

## Main statements

* `mul_abs_sin_arg_le_norm_sub`, `abs_arg_lt_of_norm_sub_le` — a closed disk
  about a positive real point, of radius below `x\sin α`, sits inside the cone
  `|arg| < α`.
* `abs_arg_le_of_le_mul_cos` — the far case of the dichotomy.
* `sin_div_sin_le`, `ftChord_lt_mul_sin` — the near case, and the trigonometric
  monotonicity it runs on.
* `mul_lt_ftAngle` — `θ_k > rθ`, from the angle sum and `ftAngle_lt_pi`.
* `ftChord_mul_cos`, `ftChord_mul_sin`, `ftChord_mul_cos_sub` — the chord to a
  zero of `Q`, resolved in the rotated frame.
* `norm_sub_min_le_of_root` — the `C₂` containment at the admissible pencil,
  through `ftRootPoly_eq_posRootPoly`.
* `cone_at_branch_of_two_le` — **`hcone` at every `r ≥ 2`**, with no hypothesis
  beyond the admissible class.
* `ft_minModulus_at_branch_two_le`, `ft_geometry_unbounded_at_branch_two_le` —
  `thm:FT-geometry` there, unconditional.

## Implementation notes

Sorry-free.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, «Forgács--Tran geometry and
  endpoint separation» — `sec:geometry`, `subsec:FT-geometry`,
  `thm:FT-geometry`, `eq:ab-def`.
* `Forgacs2017RationalDenominator`, Proposition 1.

## Tags

argument cone, minimum modulus, chord, Forgacs-Tran branch
-/

namespace ForgacsTran

open Real Set Complex

/-- The distance from a positive real point to a ray. -/
theorem mul_abs_sin_arg_le_norm_sub {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : w ≠ 0) :
    x * |Real.sin (Complex.arg w)| ≤ ‖w - (x : ℂ)‖ := by
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hsin : Real.sin (Complex.arg w) = w.im / ‖w‖ := Complex.sin_arg w
  have hsq : ‖w - (x : ℂ)‖ ^ 2 = ‖w‖ ^ 2 - 2 * x * w.re + x ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hre : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hkey : (x * |Real.sin (Complex.arg w)|) ^ 2 ≤ ‖w - (x : ℂ)‖ ^ 2 := by
    have hN : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
    rw [hsq, mul_pow, sq_abs, hsin, div_pow, ← mul_div_assoc, div_le_iff₀ hN]
    nlinarith [sq_nonneg (‖w‖ ^ 2 - x * w.re), hre]
  have h1 : (0 : ℝ) ≤ x * |Real.sin (Complex.arg w)| := by positivity
  nlinarith [norm_nonneg (w - (x : ℂ)), hkey, h1]


/-- A closed disk about a positive real point, of radius below `x sin α`, sits
inside the cone `|arg| < α`. -/
theorem abs_arg_lt_of_norm_sub_le {x R α : ℝ} (hx : 0 < x) (hα : α ∈ Ioc (0 : ℝ) (π / 2))
    (hRα : R < x * Real.sin α) {w : ℂ} (hw : ‖w - (x : ℂ)‖ ≤ R) :
    |Complex.arg w| < α := by
  have hsα : Real.sin α ≤ 1 := Real.sin_le_one α
  have hRx : R < x := lt_of_lt_of_le hRα (by nlinarith)
  have hwx : ‖w - (x : ℂ)‖ < x := lt_of_le_of_lt hw hRx
  have hre : 0 < w.re := by
    have h1 : |(w - (x : ℂ)).re| ≤ ‖w - (x : ℂ)‖ := Complex.abs_re_le_norm _
    have h2 : (w - (x : ℂ)).re = w.re - x := by simp
    rw [h2] at h1
    have := abs_le.1 h1
    linarith [this.1]
  have hw0 : w ≠ 0 := fun h => by simp [h] at hre
  have hhalf : |Complex.arg w| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
  have habs := abs_lt.1 hhalf
  have hkey : x * |Real.sin (Complex.arg w)| ≤ R :=
    le_trans (mul_abs_sin_arg_le_norm_sub hx hw0) hw
  have hlt : |Real.sin (Complex.arg w)| < Real.sin α := by nlinarith
  have hltabs := abs_lt.1 hlt
  have hmemw : Complex.arg w ∈ Icc (-(π / 2)) (π / 2) := ⟨le_of_lt habs.1, le_of_lt habs.2⟩
  have hmemα : α ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hα.1], hα.2⟩
  have hmemα' : -α ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  refine abs_lt.2 ⟨?_, ?_⟩
  · refine (Real.strictMonoOn_sin.lt_iff_lt hmemα' hmemw).1 ?_
    rw [Real.sin_neg]
    linarith [hltabs.1]
  · exact (Real.strictMonoOn_sin.lt_iff_lt hmemw hmemα).1 hltabs.2


/-- **The far case.**  When the branch radius is at most `x cos θ`, the lens
`C₁ ∩ C₂` is contained in the cone `|arg| ≤ θ`: the two disk inequalities force
`cos (arg w) ≥ cos θ` outright. -/
theorem abs_arg_le_of_le_mul_cos {x τ θ : ℝ} (hx : 0 < x) (hθ : θ ∈ Ioo 0 π)
    (hcase : τ ≤ x * Real.cos θ) {w : ℂ} (hw0 : w ≠ 0) (hnorm : ‖w‖ ≤ τ)
    (hdisk : ‖w - (x : ℂ)‖ ^ 2 ≤ τ ^ 2 - 2 * τ * x * Real.cos θ + x ^ 2) :
    |Complex.arg w| ≤ θ := by
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw0
  have hsq : ‖w - (x : ℂ)‖ ^ 2 = ‖w‖ ^ 2 - 2 * x * w.re + x ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hsq] at hdisk
  have hcos : Real.cos θ ≤ Real.cos (Complex.arg w) := by
    have hcw : Real.cos (Complex.arg w) = w.re / ‖w‖ := Complex.cos_arg hw0
    rw [hcw, le_div_iff₀ hn]
    nlinarith [mul_nonneg (sub_nonneg.2 hnorm) (sub_nonneg.2 (le_trans hnorm hcase))]
  have hmemw : |Complex.arg w| ∈ Icc (0 : ℝ) π := ⟨abs_nonneg _, Complex.abs_arg_le_pi w⟩
  have hmemθ : θ ∈ Icc (0 : ℝ) π := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hev : Real.cos |Complex.arg w| = Real.cos (Complex.arg w) := by
    rcases abs_choice (Complex.arg w) with h | h
    · rw [h]
    · rw [h, Real.cos_neg]
  by_contra hcon
  push Not at hcon
  have := Real.strictAntiOn_cos hmemθ hmemw hcon
  rw [hev] at this
  linarith


/-- The ratio `\sin θ / \sin((r-1)θ)` is bounded by `\sin(π/(2(r-1)))` on the
range where the second factor stays inside the first quarter period. -/
theorem sin_div_sin_le {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ)
    (hθc : θ ≤ π / (2 * ((r : ℝ) - 1))) :
    Real.sin θ / Real.sin (((r : ℝ) - 1) * θ) ≤ Real.sin (π / (2 * ((r : ℝ) - 1))) := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set m : ℝ := (r : ℝ) - 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by simp [hm]; linarith
  have hm0 : (0 : ℝ) < m := by linarith
  set c : ℝ := π / (2 * m) with hc
  have hc0 : 0 < c := by positivity
  have hcr : c ≤ π / r := by
    rw [hc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  set f : ℝ → ℝ := fun u => Real.sin u / Real.sin (m * u) with hf
  -- on `[θ, c]` the denominator is in the first quarter period
  have hden : ∀ u ∈ Icc θ c, 0 < Real.sin (m * u) := by
    intro u hu
    refine Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hu.1]) ?_
    have : m * u ≤ m * c := by nlinarith [hu.2]
    have hmc : m * c = π / 2 := by rw [hc]; field_simp
    rw [hmc] at this
    linarith [Real.pi_pos]
  have hd : ∀ u : ℝ, Real.sin (m * u) ≠ 0 → HasDerivAt f
      ((Real.cos u * Real.sin (m * u) - Real.sin u * (Real.cos (m * u) * m))
        / Real.sin (m * u) ^ 2) u := by
    intro u hu
    have h1 : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
    have hlin : HasDerivAt (fun v : ℝ => m * v) m u := by
      simpa using (hasDerivAt_id u).const_mul m
    have h2 : HasDerivAt (fun v : ℝ => Real.sin (m * v)) (Real.cos (m * u) * m) u := by
      simpa [Function.comp_def] using (Real.hasDerivAt_sin (m * u)).comp u hlin
    exact h1.div h2 hu
  have hmono : MonotoneOn f (Icc θ c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun u hu => ((hd u (ne_of_gt (hden u hu))).continuousAt).continuousWithinAt)
      (fun u hu => ?_) ?_
    · rw [interior_Icc] at hu
      exact ((hd u (ne_of_gt (hden u ⟨le_of_lt hu.1, le_of_lt hu.2⟩))).differentiableAt)
        |>.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have humem : u ∈ Icc θ c := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
      have hs := hden u humem
      rw [(hd u (ne_of_gt hs)).deriv]
      refine div_nonneg ?_ (sq_nonneg _)
      -- the numerator is the paper's `(r \sin((r-2)u) - (r-2)\sin(ru))/2`
      have hnum := sin_numerator_nonneg hr (θ := u)
        ⟨by linarith [hu.1, hθ0], le_trans (le_of_lt hu.2) hcr⟩
      have hexp : Real.cos u * Real.sin (m * u) - Real.sin u * (Real.cos (m * u) * m)
          = ((r : ℝ) * Real.sin (((r : ℝ) - 2) * u)
              - ((r : ℝ) - 2) * Real.sin ((r : ℝ) * u)) / 2 := by
        have e1 : m * u + u = (r : ℝ) * u := by rw [hm]; ring
        have e2 : m * u - u = ((r : ℝ) - 2) * u := by rw [hm]; ring
        have p1 : Real.cos u * Real.sin (m * u)
            = (Real.sin (m * u + u) + Real.sin (m * u - u)) / 2 := by
          rw [Real.sin_add, Real.sin_sub]; ring
        have p2 : Real.sin u * Real.cos (m * u)
            = (Real.sin (m * u + u) - Real.sin (m * u - u)) / 2 := by
          rw [Real.sin_add, Real.sin_sub]; ring
        rw [p1, e1, e2] at *
        rw [show Real.sin u * (Real.cos (m * u) * m) = (Real.sin u * Real.cos (m * u)) * m by ring,
          p2, hm]
        ring
      rw [hexp]
      linarith
  have hkey := hmono ⟨le_rfl, hθc⟩ ⟨hθc, le_rfl⟩ hθc
  have hfc : f c = Real.sin c := by
    have hmc : m * c = π / 2 := by rw [hc]; field_simp
    rw [hf]
    simp only []
    rw [hmc, Real.sin_pi_div_two, div_one]
  rw [hfc] at hkey
  exact hkey


open Polynomial in
/-- The admissible pencil in the `posRootPoly` normalization the minimum-modulus
comparisons are stated in. -/
theorem ftRootPoly_eq_posRootPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    ftRootPoly c a = posRootPoly ((-1 : ℂ) ^ n * (c : ℂ)) (Multiset.map a Finset.univ.val) := by
  classical
  rw [ftRootPoly, posRootPoly, Multiset.map_map]
  have hprod : (Multiset.map ((fun x : ℝ => X - C ((x : ℝ) : ℂ)) ∘ a) Finset.univ.val).prod
      = ∏ k : Fin n, (X - C ((a k : ℝ) : ℂ)) := rfl
  rw [hprod]
  have hneg : ∏ k : Fin n, (C ((a k : ℝ) : ℂ) - X)
      = (-1 : Polynomial ℂ) ^ n * ∏ k : Fin n, (X - C ((a k : ℝ) : ℂ)) := by
    have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
    calc ∏ k : Fin n, (C ((a k : ℝ) : ℂ) - X)
        = ∏ k : Fin n, (-1 : Polynomial ℂ) * (X - C ((a k : ℝ) : ℂ)) :=
          Finset.prod_congr rfl fun k _ => by ring
      _ = (∏ _k : Fin n, (-1 : Polynomial ℂ)) * ∏ k : Fin n, (X - C ((a k : ℝ) : ℂ)) :=
          Finset.prod_mul_distrib
      _ = (-1 : Polynomial ℂ) ^ n * ∏ k : Fin n, (X - C ((a k : ℝ) : ℂ)) := by
          rw [Finset.prod_const, hcard]
  rw [hneg, C_mul]
  simp only [map_pow, map_neg, map_one]
  ring

theorem map_norm_sub_prod {n : ℕ} (a : Fin n → ℝ) (t : ℂ) :
    ((Multiset.map a Finset.univ.val).map (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)).prod
      = ∏ k : Fin n, ‖t - ((a k : ℝ) : ℂ)‖ := by
  classical
  rw [Multiset.map_map]
  rfl


open Polynomial in
/-- **The `C₂` containment at the admissible pencil.**  A zero of the pencil no
further from the origin than another lies in the closed disk about the smallest
zero of `Q` through that other. -/
theorem norm_sub_min_le_of_root {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} {z t p : ℂ} (ht : t ≠ 0) (hp : p ≠ 0)
    (hnorm : ‖t‖ ≤ ‖p‖)
    (hrt : (ftDen (ftRootPoly c a) r z).eval t = 0)
    (hrp : (ftDen (ftRootPoly c a) r z).eval p = 0)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) :
    ‖t - ((a i : ℝ) : ℂ)‖ ≤ ‖p - ((a i : ℝ) : ℂ)‖ := by
  classical
  set xs : Multiset ℝ := Multiset.map a Finset.univ.val with hxs
  have hmem : ∀ x, x ∈ xs ↔ ∃ k : Fin n, a k = x := by
    intro x
    rw [hxs, Multiset.mem_map]
    exact ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, Finset.mem_univ k, hk⟩⟩
  have hcard : Multiset.card xs = n := by rw [hxs, Multiset.card_map]; simp
  have hne : xs ≠ 0 := by
    intro h
    rw [h] at hcard
    simp at hcard
    omega
  have hxpos : ∀ x ∈ xs, 0 < x := by
    intro x hx
    obtain ⟨k, rfl⟩ := (hmem x).1 hx
    exact ha k
  have hi : (a i : ℝ) ∈ xs := (hmem _).2 ⟨i, rfl⟩
  have hle : ∀ x ∈ xs, a i ≤ x := by
    intro x hx
    obtain ⟨k, rfl⟩ := (hmem x).1 hx
    exact hmin k
  have hbridge := ftRootPoly_eq_posRootPoly (n := n) c a
  have hc' : ((-1 : ℂ) ^ n * (c : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hc)
  rw [hbridge] at hrt hrp
  have hprod := prod_norm_sub_le_of_norm_le (xs := xs) (r := r) (z := z) hc' ht hp hnorm hrt hrp
  exact norm_sub_le_of_prod_le hne hxpos hnorm hi hle hprod


/-! ### The angle at the smallest zero -/

/-- **`θ_i > rθ`.**  The angle sum is `rθ + (n-1)π` and the other `n-1` angles are
each below `π`, so every one of them exceeds `rθ`. -/
theorem mul_lt_ftAngle {n r : ℕ} {a : Fin n → ℝ} {τ θ : ℝ} (hn2 : 2 ≤ n)
    (hsum : ftAngleSum a τ θ = r * θ + ((n - 1 : ℕ) : ℝ) * π) (i : Fin n) :
    (r : ℝ) * θ < ftAngle (a i) τ θ := by
  classical
  rw [ftAngleSum] at hsum
  have hsplit : ftAngle (a i) τ θ + ∑ k ∈ Finset.univ.erase i, ftAngle (a k) τ θ
      = ∑ k, ftAngle (a k) τ θ :=
    Finset.add_sum_erase Finset.univ (fun k => ftAngle (a k) τ θ) (Finset.mem_univ i)
  have hcard : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hnonempty : (Finset.univ.erase i).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have hlt : ∑ k ∈ Finset.univ.erase i, ftAngle (a k) τ θ
      < ∑ _k ∈ Finset.univ.erase i, π :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun k _ => ftAngle_lt_pi _ _ _
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hlt
  rw [hsum] at hsplit
  linarith

/-! ### The chord to a zero of `Q` -/

/-- `R\cos θ_k = τ\cos θ - a`, the projection of the chord onto the real axis. -/
theorem ftChord_mul_cos {a τ θ φ : ℝ} (hθ : θ ∈ Ioo 0 π) (hφ : φ ∈ Ioo θ π)
    (h : a * Real.sin φ = τ * Real.sin (φ - θ)) :
    ftChord a θ φ * Real.cos φ = τ * Real.cos θ - a := by
  have hd : Real.sin (φ - θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2, hθ.1]))
  rw [ftChord, div_mul_eq_mul_div, div_eq_iff hd, Real.sin_sub]
  rw [Real.sin_sub] at h
  linear_combination (Real.cos θ) * h

/-- `R\sin θ_k = τ\sin θ`, the imaginary part of the same. -/
theorem ftChord_mul_sin {a τ θ φ : ℝ} (hθ : θ ∈ Ioo 0 π) (hφ : φ ∈ Ioo θ π)
    (h : a * Real.sin φ = τ * Real.sin (φ - θ)) :
    ftChord a θ φ * Real.sin φ = τ * Real.sin θ := by
  have hd : Real.sin (φ - θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2, hθ.1]))
  rw [ftChord, div_mul_eq_mul_div, div_eq_iff hd]
  linear_combination (Real.sin θ) * h

/-- `R\cos(θ_k - θ) = τ - a\cos θ`: the same chord read in the rotated frame,
which is where the sign of `τ - a\cos θ` decides whether the angle at the branch
point is acute. -/
theorem ftChord_mul_cos_sub {a τ θ φ : ℝ} (hθ : θ ∈ Ioo 0 π) (hφ : φ ∈ Ioo θ π)
    (h : a * Real.sin φ = τ * Real.sin (φ - θ)) :
    ftChord a θ φ * Real.cos (φ - θ) = τ - a * Real.cos θ := by
  have hcs := ftChord_mul_cos hθ hφ h
  have hsn := ftChord_mul_sin hθ hφ h
  rw [Real.cos_sub]
  have hexp : ftChord a θ φ * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ)
      = (ftChord a θ φ * Real.cos φ) * Real.cos θ
        + (ftChord a θ φ * Real.sin φ) * Real.sin θ := by ring
  rw [hexp, hcs, hsn]
  linear_combination τ * Real.sin_sq_add_cos_sq θ


theorem sin_le_sin_of_le_pi_div_two {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) :
    Real.sin x ≤ Real.sin y := by
  have hπ := Real.pi_pos
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact le_of_lt (Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, hy⟩ h)

/-- **The near case, quantified.**  When `a\cos θ < τ` the angle at the branch
point is acute, and `θ_a > rθ` then forces the chord to the zero `a` below
`a\sin(π/r)`. -/
theorem ftChord_lt_mul_sin {r : ℕ} (hr : 2 ≤ r) {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ : θ ∈ Ioo 0 (π / r)) (hcase : a * Real.cos θ < τ)
    (hang : (r : ℝ) * θ < ftAngle a τ θ) :
    ftChord a θ (ftAngle a τ θ) < a * Real.sin (π / r) := by
  have hπ := Real.pi_pos
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset (by omega) hθ
  set φ : ℝ := ftAngle a τ θ with hφdef
  have hφ : φ ∈ Ioo θ π := ftAngle_mem_Ioo ha hτ hθπ
  have hspec : a * Real.sin φ = τ * Real.sin (φ - θ) := ftAngle_spec (ne_of_gt hτ) hθπ
  have hR : 0 < ftChord a θ φ := ftChord_pos ha hθπ hφ
  have hsub0 : 0 < φ - θ := by linarith [hφ.1]
  have hsubπ : φ - θ < π := by linarith [hφ.2, hθπ.1]
  -- the angle at the branch point is acute
  have hcossub : ftChord a θ φ * Real.cos (φ - θ) = τ - a * Real.cos θ :=
    ftChord_mul_cos_sub hθπ hφ hspec
  have hacute : φ - θ < π / 2 := by
    by_contra hcon
    push Not at hcon
    have : Real.cos (φ - θ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith)
    nlinarith
  -- `θ_a > rθ` places `φ - θ` above `(r-1)θ`
  have hrm : ((r : ℝ) - 1) * θ < φ - θ := by nlinarith [hθ.1]
  have hm0 : 0 < ((r : ℝ) - 1) * θ := by nlinarith [hθ.1]
  have hsinlt : Real.sin (((r : ℝ) - 1) * θ) < Real.sin (φ - θ) :=
    Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, le_of_lt hacute⟩ hrm
  have hsinm : 0 < Real.sin (((r : ℝ) - 1) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi hm0 (by linarith)
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  -- the chord shrinks as the angle at the branch point grows
  have hstep : ftChord a θ φ < a * Real.sin θ / Real.sin (((r : ℝ) - 1) * θ) := by
    rw [ftChord]
    exact div_lt_div_of_pos_left (by positivity) hsinm hsinlt
  have hθle : θ ≤ π / (2 * ((r : ℝ) - 1)) := by
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith
  have hratio := sin_div_sin_le hr hθπ.1 hθle
  have hlast : Real.sin (π / (2 * ((r : ℝ) - 1))) ≤ Real.sin (π / r) := by
    refine sin_le_sin_of_le_pi_div_two (le_of_lt (div_pos hπ (by nlinarith))) ?_ ?_
    · rw [div_le_div_iff₀ (by nlinarith) hr0]
      nlinarith
    · rw [div_le_div_iff₀ hr0 (by norm_num)]
      nlinarith
  have hdiv : a * Real.sin θ / Real.sin (((r : ℝ) - 1) * θ)
      = a * (Real.sin θ / Real.sin (((r : ℝ) - 1) * θ)) := by ring
  rw [hdiv] at hstep
  nlinarith


/-- The chord from a zero of `Q` to the principal point, squared. -/
theorem norm_sub_upperArc_sq (τ θ x : ℝ) :
    ‖((τ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - ((x : ℝ) : ℂ)‖ ^ 2
      = τ ^ 2 - 2 * τ * x * Real.cos θ + x ^ 2 := by
  have hre : (((τ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = τ * Real.cos θ := by
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have him : (((τ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = τ * Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  nlinarith [Real.sin_sq_add_cos_sq θ]


/-- **`hcone` at every `r ≥ 2`.**  An inner zero of the pencil has argument
strictly inside the double cone `|arg| < π/r`. -/
theorem cone_at_branch_of_two_le {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    FTArgumentCone (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) := by
  classical
  intro θ hθ w hw hnorm
  have hπ := Real.pi_pos
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr1 hθ
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr1 (Or.inl hn2) hθ
  set τ : ℝ := ftTau a r (n - 1) θ with hτdef
  have hτ : 0 < τ := ftTau_pos hb
  -- the principal point of the pair, on the upper arc
  set p : ℂ := ftPrincipal (ftTau a r (n - 1)) θ with hpdef
  have hproot : (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval p = 0 :=
    ftDen_eval_ftPrincipal_ftBranchZ c ha hθπ hb
  have hpnorm : ‖p‖ = τ := norm_ftPrincipal_eq hτ
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpnorm
    linarith
  have hw0 : w ≠ 0 := fun h => eval_ftDen_zero_ne_zero ha hc hr1 _ (h ▸ hw)
  -- the argument is nonzero: no positive real zero in the closed disk
  have hargpos : 0 < |Complex.arg w| := by
    refine abs_pos.2 fun h0 => ?_
    obtain ⟨hre, him⟩ := Complex.arg_eq_zero_iff.1 h0
    have hwre : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hs0 : 0 < w.re := lt_of_le_of_ne hre fun h => hw0 (by rw [hwre, ← h]; simp)
    have hsτ : w.re ≤ τ := by
      have : ‖w‖ = |w.re| := by rw [hwre]; simp [Complex.norm_real, Real.norm_eq_abs]
      rw [this, abs_of_pos hs0] at hnorm
      exact hnorm
    have hreal : (ftRootPolyReal c a).eval w.re
        + ftBranchZ a c r (n - 1) θ * w.re ^ r = 0 := by
      have := hw
      rw [hwre, eval_ftDen_ofReal] at this
      exact_mod_cast this
    have hval : -(ftRootPolyReal c a).eval w.re / w.re ^ r = ftBranchZ a c r (n - 1) θ := by
      field_simp
      linarith [hreal]
    exact absurd hval
      (ne_of_lt (negDivPow_lt_ftBranchZ_pos hn2 ha hc hr1 (by omega) hθ hs0 hsτ))
  refine ⟨hargpos, ?_⟩
  -- the smallest zero of `Q`, and the `C₂` containment through it
  obtain ⟨i, -, hmini⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) a
    (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  have hmin : ∀ k, a i ≤ a k := fun k => hmini k (Finset.mem_univ k)
  have hC2 : ‖w - ((a i : ℝ) : ℂ)‖ ≤ ‖p - ((a i : ℝ) : ℂ)‖ :=
    norm_sub_min_le_of_root hn ha (ne_of_gt hc) hw0 hp0 (by rw [hpnorm]; exact hnorm)
      hw hproot hmin
  have hpsq : ‖p - ((a i : ℝ) : ℂ)‖ ^ 2 = τ ^ 2 - 2 * τ * a i * Real.cos θ + a i ^ 2 :=
    norm_sub_upperArc_sq τ θ (a i)
  rcases le_or_gt τ (a i * Real.cos θ) with hcase | hcase
  · -- far case: the lens sits inside `|arg| ≤ θ`
    have hdisk : ‖w - ((a i : ℝ) : ℂ)‖ ^ 2 ≤ τ ^ 2 - 2 * τ * a i * Real.cos θ + a i ^ 2 := by
      rw [← hpsq]
      exact pow_le_pow_left₀ (norm_nonneg _) hC2 2
    exact lt_of_le_of_lt
      (abs_arg_le_of_le_mul_cos (ha i) hθπ hcase hw0 hnorm hdisk) hθ.2
  · -- near case: the chord to the smallest zero is below `a_i sin(π/r)`
    have hang : (r : ℝ) * θ < ftAngle (a i) τ θ :=
      mul_lt_ftAngle hn2 (ftAngleSum_ftTau hb) i
    have hchord := ftChord_lt_mul_sin hr (ha i) hτ hθ hcase hang
    have heq : ftChord (a i) θ (ftAngle (a i) τ θ)
        = Real.sqrt (a i ^ 2 - 2 * a i * τ * Real.cos θ + τ ^ 2) :=
      ftChord_eq_sqrt (ha i) hτ hθπ
    have hpeq : ‖p - ((a i : ℝ) : ℂ)‖ = ftChord (a i) θ (ftAngle (a i) τ θ) := by
      rw [heq, ← Real.sqrt_sq (norm_nonneg (p - ((a i : ℝ) : ℂ))), hpsq]
      congr 1
      ring
    refine abs_arg_lt_of_norm_sub_le (ha i) ⟨div_pos hπ hr0, ?_⟩ ?_ hC2
    · rw [div_le_div_iff₀ hr0 (by norm_num)]
      nlinarith
    · rw [hpeq]
      exact hchord


/-- **`thm:FT-geometry`'s `hmin` at every `r ≥ 2`, unconditional** on the
admissible class. -/
theorem ft_minModulus_at_branch_two_le {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    FTMinModulusGap (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) :=
  ft_minModulus_at_branch hn2 ha hc (by omega) (cone_at_branch_of_two_le hn2 ha hc hr)

/-- **`thm:FT-geometry` at the constructed branch, `r ≥ 2`, with no analytic
hypothesis at all.**  The unbounded convention of `eq:ab-def`, which that display
reaches exactly when `r > 1`. -/
theorem ft_geometry_unbounded_at_branch_two_le {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    ∃ za : ℝ,
      ftBranchZ a c r (n - 1) '' Ioo 0 (π / r) = Ioi za
        ∧ FTPrincipalPair (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))
        ∧ FTPrincipalDisk (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) :=
  ft_geometry_unbounded_at_branch_of_cone hn2 ha hc hr (cone_at_branch_of_two_le hn2 ha hc hr)

end ForgacsTran
