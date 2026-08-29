/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Shields.Topology.EMetricSpace.BoundedVariationAlgebra
import Shields.Topology.EMetricSpace.BoundedVariationRestrict
import ForgacsTran.ComplexPart

/-!
# Radon's viewing-angle bound

`eq:viewing-angle-bound` says that the summed variation of `arg(γ - β)` along an arc of
bounded rotation is at most `𝒦_γ + π`, whatever the vantage point `β`.  The proof here is
the folding argument: the parameter interval is cut where `sin(ϑ - φ)` vanishes, `φ` is
monotone on each piece in the direction the strip forces, and the excess of `Var φ` over
`Var ϑ` telescopes into the increment of `arccos ∘ cos ∘ (ϑ - φ)`, which lives in `[0, π]`.

The argument branches themselves are **built**, not hypothesized: for a differentiable path
avoiding `β`, `L(s) = log(γ(a) - β) + ∫_a^s γ'/(γ - β)` satisfies `e^L = γ - β`, because
`(γ - β)e^{-L}` has zero derivative.  So the continuous argument lift comes out of the
fundamental theorem of calculus rather than out of covering-space theory, which Mathlib
cannot yet supply for `exp`.  For a regular arc the tangent angle is the same lift applied to
`γ'`, and `viewing_angle_bound_regular` therefore asks only for `γ ∈ C²` on an open set
carrying the parameter interval, `γ' ≠ 0`, `γ ≠ β`, and a finite critical set for the viewing
angle — that last being the arc's real-analyticity, which the manuscript takes from
`Forgacs2017RationalDenominator` along with the rest of `thm:FT-geometry`.

## Main statements

* `phaseFold` — `arccos ∘ cos`, the triangle wave of period `2π` with values in `[0, π]`;
  `phaseFold_eq_of_mem_strip` makes it affine with slope `(-1)^k` on `[kπ, (k+1)π]`, which is
  what lets the excess telescope.
* `eVariationOn_neg`, `AntitoneOn.eVariationOn_eq` — two variation lemmas Mathlib does not
  carry, re-exported from `Shields.Topology.EMetricSpace.BoundedVariationAlgebra`; the
  second is `MonotoneOn.eVariationOn_eq` on the decreasing pieces.
* `eVariationOn_le_of_stripPartition` — the folding argument itself, over a given cut.
* `hasDerivAt_viewingAngle` — from the polar data `γ - β = ρ e^{iφ}`, `γ' = ν e^{iϑ}`:
  `φ' = (ν/ρ) sin(ϑ - φ)`.  This is what makes the sign of `φ'` a function of `ϑ - φ`.
* `sin_nonneg_of_mem_strip`, `sin_nonpos_of_mem_strip`, `monotoneOn_of_mem_strip`,
  `antitoneOn_of_mem_strip` — the strip constraint turned into monotonicity of `φ`.
* `eVariationOn_add_phaseFold_le_of_stripPartition`, `viewing_angle_bound_phaseFold`,
  `viewing_angle_bound_of_finite_phaseFold` — the sharp form: the excess of `Var φ` over
  `Var ϑ` is the *drop* of the folded phase across the interval, not merely `π`.
* `viewing_angle_bound` — `eq:viewing-angle-bound` over a given cut.
* `mem_strip_of_no_level_point`, `exists_stripPartition` — the cut, built at the critical
  points; the only remaining input is that they are finitely many.
* `viewing_angle_bound_of_finite`, `viewing_angle_bound_polar` — `lem:viewing-angle` with the
  cut discharged, the second stated in the manuscript's own polar terms.
* `logLift`, `exp_logLift` — the argument lift, by integration.
* `polarAngle`, `polarModulus`, `polar_decomposition`, `hasDerivAt_polarAngle` — the branch
  it defines, its modulus, the identity `γ - β = ρ e^{iφ}` they satisfy, and `φ' = Im(γ'/(γ - β))`.
* `hasDerivAt_viewingAngle_of_polar`, `viewing_angle_bound_arc` — `lem:viewing-angle` at a
  point off the arc, with the branch built.
* `viewing_angle_bound_regular` — the same for a regular arc, with the tangent angle built too.
* `cos_sub_of_polar`, `tendsto_phaseFold_left`, `tendsto_phaseFold_right` — the folded phase
  is `arccos` of the normalized inner product of tangent with chord, and at a parameter where
  `γ` meets `β` it runs to `π` from the left and to `0` from the right.
* `viewing_angle_bound_to_meet`, `viewing_angle_bound_from_meet`, `viewing_angle_bound_on_arc`,
  `viewing_angle_bound_on_arc_le_pi` — `eq:viewing-angle-bound` with `β` **on** the arc,
  summed over the two components of `[a,b] ∖ γ⁻¹({β})`.
* `eVariationOn_Ico_le`, `eVariationOn_Ioc_le` — the variation over a half-open interval from
  its closed subintervals, which is how a component open at the meeting parameter is reached.
* `lineViewingAngle`, `viewing_angle_bound_line` — the horizontal line viewed from the origin:
  `𝒦_γ = 0` and the viewing angle has variation `2 arctan T`, so the hypotheses are
  satisfiable and the constant `π` cannot be lowered.

## Implementation notes

`β` lying **on** the arc is covered by `viewing_angle_bound_on_arc`, at one meeting parameter
`m` — which is all an injective arc has.  The branch construction still needs `γ ≠ β`, so the
two components are reached as increasing unions of closed subintervals, and the branch on the
right one is based at `b` rather than at the component's own left endpoint, which moves.  The
summed bound there is `𝒦_γ`, below the manuscript's `𝒦_γ + π`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `lem:viewing-angle`).

## Tags

viewing angle, Radon, zero counting, convexity
-/

set_option linter.style.longFile 1700

namespace ForgacsTran

open Real Set Finset

/-! ### The folded phase -/

/-- The triangle wave of period `2π` with values in `[0, π]`, realized as
`arccos ∘ cos`. -/
noncomputable def phaseFold (x : ℝ) : ℝ := Real.arccos (Real.cos x)

theorem phaseFold_nonneg (x : ℝ) : 0 ≤ phaseFold x := Real.arccos_nonneg _

theorem phaseFold_le_pi (x : ℝ) : phaseFold x ≤ π := Real.arccos_le_pi _

/-- `(-1)^k`, as a real sign. -/
noncomputable def stripSign (k : ℤ) : ℝ := if Even k then 1 else -1

/-- The additive constant that makes `phaseFold` affine on the strip `[kπ, (k+1)π]`. -/
noncomputable def stripOffset (k : ℤ) : ℝ := if Even k then 0 else π

theorem abs_stripSign (k : ℤ) : |stripSign k| = 1 := by
  unfold stripSign; split <;> norm_num

theorem stripSign_ne_zero (k : ℤ) : stripSign k ≠ 0 := by
  unfold stripSign; split <;> norm_num

/-- On the strip `[kπ, (k+1)π]` the folded phase is affine with slope `(-1)^k`. -/
theorem phaseFold_eq_of_mem_strip {k : ℤ} {x : ℝ}
    (h1 : (k : ℝ) * π ≤ x) (h2 : x ≤ ((k : ℝ) + 1) * π) :
    phaseFold x = stripSign k * (x - k * π) + stripOffset k := by
  rcases Int.even_or_odd k with hk | hk
  · obtain ⟨m, hm⟩ := hk
    have hkm : (k : ℝ) = 2 * m := by rw [hm]; push_cast; ring
    have hy0 : 0 ≤ x - (k : ℝ) * π := by linarith
    have hyπ : x - (k : ℝ) * π ≤ π := by nlinarith [Real.pi_pos]
    have hcos : Real.cos (x - (k : ℝ) * π) = Real.cos x := by
      have := Real.cos_add_int_mul_two_pi x (-m)
      rw [show x - (k : ℝ) * π = x + ((-m : ℤ) : ℝ) * (2 * π) by rw [hkm]; push_cast; ring]
      exact this
    unfold phaseFold stripSign stripOffset
    rw [if_pos ⟨m, hm⟩, if_pos ⟨m, hm⟩, ← hcos, Real.arccos_cos hy0 hyπ]
    ring
  · have hnot : ¬ Even k := by rw [Int.not_even_iff_odd]; exact hk
    obtain ⟨m, hm⟩ := hk
    have hkm : (k : ℝ) = 2 * m + 1 := by rw [hm]; push_cast; ring
    set y := ((k : ℝ) + 1) * π - x with hy
    have hy0 : 0 ≤ y := by rw [hy]; linarith
    have hyπ : y ≤ π := by rw [hy]; nlinarith [Real.pi_pos]
    have hcos : Real.cos y = Real.cos x := by
      have := Real.cos_int_mul_two_pi_sub x (m + 1)
      rw [hy, show ((k : ℝ) + 1) * π - x = ((m + 1 : ℤ) : ℝ) * (2 * π) - x by
        rw [hkm]; push_cast; ring]
      exact this
    unfold phaseFold stripSign stripOffset
    rw [if_neg hnot, if_neg hnot, ← hcos, Real.arccos_cos hy0 hyπ, hy]
    ring

/-- The increment of the folded phase across a strip. -/
theorem phaseFold_sub_eq_of_mem_strip {k : ℤ} {x y : ℝ}
    (hx1 : (k : ℝ) * π ≤ x) (hx2 : x ≤ ((k : ℝ) + 1) * π)
    (hy1 : (k : ℝ) * π ≤ y) (hy2 : y ≤ ((k : ℝ) + 1) * π) :
    phaseFold y - phaseFold x = stripSign k * (y - x) := by
  rw [phaseFold_eq_of_mem_strip hy1 hy2, phaseFold_eq_of_mem_strip hx1 hx2]; ring

/-! ### Two variation lemmas Mathlib does not carry

`Shields.eVariationOn_neg` and `AntitoneOn.eVariationOn_eq`, the latter at the root
namespace beside Mathlib's own `MonotoneOn.eVariationOn_eq`, which it is proved from. -/

export Shields (eVariationOn_neg)


/-! ### The folding argument -/

/-- The core of Radon's bound, in its sharp form.  Let `ϑ`, `φ` be real functions on
`[u 0, u n]` and let `α = ϑ - φ`.  Suppose the interval is cut at `u 0 ≤ ⋯ ≤ u n` so that on
the `i`-th piece `α` stays inside one strip `[k π, (k+1) π]` and `φ` is monotone in the
direction `(-1)^k` that strip forces.  Then the variation of `φ` exceeds that of `ϑ` by at
most the **drop** of the folded phase `phaseFold ∘ α` across the interval.

The excess is exactly the increment of `phaseFold ∘ α`, which telescopes across the pieces
because folding is affine with slope `(-1)^k` on the `k`-th strip.  Discarding the two
endpoint values against `phaseFold ∈ [0, π]` gives `eVariationOn_le_of_stripPartition`; the
drop itself is what `viewing_angle_bound_on_arc` needs, where the folded phase runs to `π` on
one side of a parameter meeting `β` and to `0` on the other. -/
theorem eVariationOn_add_phaseFold_le_of_stripPartition
    {ϑ φ : ℝ → ℝ} {u : ℕ → ℝ} {k : ℕ → ℤ} {n : ℕ}
    (hu : Monotone u)
    (hstrip : ∀ i, i < n → ∀ s ∈ Icc (u i) (u (i + 1)),
        (k i : ℝ) * π ≤ ϑ s - φ s ∧ ϑ s - φ s ≤ ((k i : ℝ) + 1) * π)
    (hmono : ∀ i, i < n → Even (k i) → MonotoneOn φ (Icc (u i) (u (i + 1))))
    (hanti : ∀ i, i < n → ¬ Even (k i) → AntitoneOn φ (Icc (u i) (u (i + 1)))) :
    eVariationOn φ (Icc (u 0) (u n)) + ENNReal.ofReal (phaseFold (ϑ (u n) - φ (u n)))
      ≤ eVariationOn ϑ (Icc (u 0) (u n))
          + ENNReal.ofReal (phaseFold (ϑ (u 0) - φ (u 0))) := by
  have hle : ∀ i, u i ≤ u (i + 1) := fun i => hu (Nat.le_succ i)
  have hlm : ∀ i, u i ∈ Icc (u i) (u (i + 1)) := fun i => left_mem_Icc.2 (hle i)
  have hrm : ∀ i, u (i + 1) ∈ Icc (u i) (u (i + 1)) := fun i => right_mem_Icc.2 (hle i)
  -- each piece contributes `(-1)^k Δφ`, and that quantity is nonnegative
  have hpiece : ∀ i, i < n → eVariationOn φ (Icc (u i) (u (i + 1)))
      = ENNReal.ofReal (stripSign (k i) * (φ (u (i + 1)) - φ (u i))) := by
    intro i hi
    by_cases hk : Even (k i)
    · have h := (hmono i hi hk).eVariationOn_eq (hlm i) (hrm i)
      rw [Set.inter_self] at h
      rw [h]
      unfold stripSign
      rw [if_pos hk, one_mul]
    · have h := AntitoneOn.eVariationOn_eq (hanti i hi hk) (hlm i) (hrm i)
      rw [Set.inter_self] at h
      rw [h]
      unfold stripSign
      rw [if_neg hk]
      congr 1
      ring
  have hnn : ∀ i, i < n → 0 ≤ stripSign (k i) * (φ (u (i + 1)) - φ (u i)) := by
    intro i hi
    by_cases hk : Even (k i)
    · have := (hmono i hi hk) (hlm i) (hrm i) (hle i)
      unfold stripSign; rw [if_pos hk]; linarith
    · have := (hanti i hi hk) (hlm i) (hrm i) (hle i)
      unfold stripSign; rw [if_neg hk]; linarith
  have hsum : eVariationOn φ (Icc (u 0) (u n))
      = ENNReal.ofReal (∑ i ∈ range n, stripSign (k i) * (φ (u (i + 1)) - φ (u i))) := by
    rw [← eVariationOn.sum' φ hu,
      ENNReal.ofReal_sum_of_nonneg (fun i hi => hnn i (mem_range.1 hi))]
    exact Finset.sum_congr rfl fun i hi => hpiece i (mem_range.1 hi)
  -- the excess telescopes through the folded phase
  have hfold : ∀ i ∈ range n,
      stripSign (k i) * ((ϑ (u (i + 1)) - φ (u (i + 1))) - (ϑ (u i) - φ (u i)))
        = phaseFold (ϑ (u (i + 1)) - φ (u (i + 1))) - phaseFold (ϑ (u i) - φ (u i)) := by
    intro i hi
    have hi' : i < n := mem_range.1 hi
    have h1 := hstrip i hi' (u i) (hlm i)
    have h2 := hstrip i hi' (u (i + 1)) (hrm i)
    exact (phaseFold_sub_eq_of_mem_strip h1.1 h1.2 h2.1 h2.2).symm
  have htel : ∑ i ∈ range n,
      stripSign (k i) * ((ϑ (u (i + 1)) - φ (u (i + 1))) - (ϑ (u i) - φ (u i)))
        = phaseFold (ϑ (u n) - φ (u n)) - phaseFold (ϑ (u 0) - φ (u 0)) := by
    rw [Finset.sum_congr rfl hfold]
    exact Finset.sum_range_sub (fun i => phaseFold (ϑ (u i) - φ (u i))) n
  -- the real-valued inequality
  have hkey : (∑ i ∈ range n, stripSign (k i) * (φ (u (i + 1)) - φ (u i)))
        + phaseFold (ϑ (u n) - φ (u n))
      ≤ (∑ i ∈ range n, |ϑ (u (i + 1)) - ϑ (u i)|)
        + phaseFold (ϑ (u 0) - φ (u 0)) := by
    have hsplit : ∀ i ∈ range n, stripSign (k i) * (φ (u (i + 1)) - φ (u i))
        = stripSign (k i) * (ϑ (u (i + 1)) - ϑ (u i))
          - stripSign (k i) * ((ϑ (u (i + 1)) - φ (u (i + 1))) - (ϑ (u i) - φ (u i))) := by
      intro i _; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, htel]
    have h1 : ∑ i ∈ range n, stripSign (k i) * (ϑ (u (i + 1)) - ϑ (u i))
        ≤ ∑ i ∈ range n, |ϑ (u (i + 1)) - ϑ (u i)| := by
      refine Finset.sum_le_sum fun i _ => ?_
      calc stripSign (k i) * (ϑ (u (i + 1)) - ϑ (u i))
          ≤ |stripSign (k i) * (ϑ (u (i + 1)) - ϑ (u i))| := le_abs_self _
        _ = |ϑ (u (i + 1)) - ϑ (u i)| := by rw [abs_mul, abs_stripSign, one_mul]
    linarith
  -- the sampled variation of `ϑ` is below its total variation
  have hvar : ENNReal.ofReal (∑ i ∈ range n, |ϑ (u (i + 1)) - ϑ (u i)|)
      ≤ eVariationOn ϑ (Icc (u 0) (u n)) := by
    have hvmono : Monotone (fun i => u (min i n)) := fun i j hij =>
      hu (min_le_min hij le_rfl)
    have hvmem : ∀ i, (fun i => u (min i n)) i ∈ Icc (u 0) (u n) := fun i =>
      ⟨hu (Nat.zero_le _), hu (min_le_right _ _)⟩
    have hbound := eVariationOn.sum_le (f := ϑ) (s := Icc (u 0) (u n)) (n := n) hvmono hvmem
    refine le_trans (le_of_eq ?_) hbound
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n := mem_range.1 hi
    have e1 : min i n = i := min_eq_left hi'.le
    have e2 : min (i + 1) n = i + 1 := min_eq_left hi'
    simp only [e1, e2]
    rw [edist_dist, Real.dist_eq]
  have hsnn : 0 ≤ ∑ i ∈ range n, stripSign (k i) * (φ (u (i + 1)) - φ (u i)) :=
    Finset.sum_nonneg fun i hi => hnn i (mem_range.1 hi)
  calc eVariationOn φ (Icc (u 0) (u n)) + ENNReal.ofReal (phaseFold (ϑ (u n) - φ (u n)))
      = ENNReal.ofReal ((∑ i ∈ range n, stripSign (k i) * (φ (u (i + 1)) - φ (u i)))
          + phaseFold (ϑ (u n) - φ (u n))) := by
        rw [hsum, ENNReal.ofReal_add hsnn (phaseFold_nonneg _)]
    _ ≤ ENNReal.ofReal ((∑ i ∈ range n, |ϑ (u (i + 1)) - ϑ (u i)|)
          + phaseFold (ϑ (u 0) - φ (u 0))) := ENNReal.ofReal_le_ofReal hkey
    _ = ENNReal.ofReal (∑ i ∈ range n, |ϑ (u (i + 1)) - ϑ (u i)|)
          + ENNReal.ofReal (phaseFold (ϑ (u 0) - φ (u 0))) :=
        ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => abs_nonneg _) (phaseFold_nonneg _)
    _ ≤ eVariationOn ϑ (Icc (u 0) (u n))
          + ENNReal.ofReal (phaseFold (ϑ (u 0) - φ (u 0))) := by gcongr

/-- The core of Radon's bound: under a strip cut, the variation of `φ` exceeds that of `ϑ`
by at most `π`.  This is `eVariationOn_add_phaseFold_le_of_stripPartition` with the folded
phase discarded at both ends against `0 ≤ phaseFold ≤ π`. -/
theorem eVariationOn_le_of_stripPartition
    {ϑ φ : ℝ → ℝ} {u : ℕ → ℝ} {k : ℕ → ℤ} {n : ℕ}
    (hu : Monotone u)
    (hstrip : ∀ i, i < n → ∀ s ∈ Icc (u i) (u (i + 1)),
        (k i : ℝ) * π ≤ ϑ s - φ s ∧ ϑ s - φ s ≤ ((k i : ℝ) + 1) * π)
    (hmono : ∀ i, i < n → Even (k i) → MonotoneOn φ (Icc (u i) (u (i + 1))))
    (hanti : ∀ i, i < n → ¬ Even (k i) → AntitoneOn φ (Icc (u i) (u (i + 1)))) :
    eVariationOn φ (Icc (u 0) (u n))
      ≤ eVariationOn ϑ (Icc (u 0) (u n)) + ENNReal.ofReal π := by
  refine le_trans (le_trans (le_add_right le_rfl)
    (eVariationOn_add_phaseFold_le_of_stripPartition hu hstrip hmono hanti)) ?_
  gcongr
  exact phaseFold_le_pi _


/-! ### From the polar data to the strip hypotheses -/

private theorem exp_ofReal_mul_I_im (x : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := by
  rw [Complex.exp_mul_I]; simp [Complex.sin_ofReal_re]

/-- Paper `sec:geometry`: with `γ - β = ρ e^{iφ}` and `γ' = ν e^{iϑ}` in polar form and
`ρ > 0`, the viewing angle `φ` satisfies `φ' = (ν/ρ) sin (ϑ - φ)`.

This is what makes the sign of `φ'` a function of `ϑ - φ` alone, and hence what turns a
strip constraint on `ϑ - φ` into monotonicity of `φ`. -/
theorem hasDerivAt_viewingAngle
    {γ : ℝ → ℂ} {β : ℂ} {ρ ν ϑ φ : ℝ → ℝ} {s : ℝ}
    (hρs : 0 < ρ s)
    (hρ : DifferentiableAt ℝ ρ s) (hφ : DifferentiableAt ℝ φ s)
    (hpol : (fun t => γ t - β)
        =ᶠ[nhds s] fun t => (ρ t : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I))
    (hγ : HasDerivAt γ ((ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I)) s) :
    HasDerivAt φ (ν s / ρ s * Real.sin (ϑ s - φ s)) s := by
  have h1 : HasDerivAt (fun t => (ρ t : ℂ)) ((deriv ρ s : ℝ) : ℂ) s :=
    hρ.hasDerivAt.ofReal_comp
  have h2 : HasDerivAt (fun t => (φ t : ℂ) * Complex.I)
      (((deriv φ s : ℝ) : ℂ) * Complex.I) s :=
    (hφ.hasDerivAt.ofReal_comp).mul_const Complex.I
  have h4 := h1.mul h2.cexp
  have h5 := h4.congr_of_eventuallyEq hpol
  have h7 := (hγ.sub_const β).unique h5
  -- cancel the common factor `e^{iφ}`
  have hexp : Complex.exp ((φ s : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have h8 : (ν s : ℂ) * Complex.exp (((ϑ s : ℂ) - (φ s : ℂ)) * Complex.I)
      = ((deriv ρ s : ℝ) : ℂ) + ((ρ s : ℝ) : ℂ) * ((deriv φ s : ℝ) : ℂ) * Complex.I := by
    refine mul_right_cancel₀ hexp ?_
    rw [mul_assoc, ← Complex.exp_add]
    rw [show ((ϑ s : ℂ) - (φ s : ℂ)) * Complex.I + (φ s : ℂ) * Complex.I
        = (ϑ s : ℂ) * Complex.I by ring]
    rw [h7]; ring
  -- imaginary parts
  have h9 : ν s * Real.sin (ϑ s - φ s) = ρ s * deriv φ s := by
    have him : (Complex.exp (((ϑ s : ℂ) - (φ s : ℂ)) * Complex.I)).im
        = Real.sin (ϑ s - φ s) := by
      rw [show ((ϑ s : ℂ) - (φ s : ℂ)) = ((ϑ s - φ s : ℝ) : ℂ) by push_cast; ring]
      exact exp_ofReal_mul_I_im _
    have hcg := congrArg Complex.im h8
    simpa [him, Complex.add_im, Complex.mul_im] using hcg
  have h10 : deriv φ s = ν s / ρ s * Real.sin (ϑ s - φ s) := by
    field_simp at h9 ⊢
    linarith
  rw [← h10]
  exact hφ.hasDerivAt

/-! ### The sign of the sine on a strip -/

theorem sin_nonneg_of_mem_strip {k : ℤ} (hk : Even k) {x : ℝ}
    (h1 : (k : ℝ) * π ≤ x) (h2 : x ≤ ((k : ℝ) + 1) * π) : 0 ≤ Real.sin x := by
  obtain ⟨m, hm⟩ := hk
  have hkm : (k : ℝ) = 2 * m := by rw [hm]; push_cast; ring
  have e : x - (k : ℝ) * π = x + ((-m : ℤ) : ℝ) * (2 * π) := by rw [hkm]; push_cast; ring
  have hsin : Real.sin (x - (k : ℝ) * π) = Real.sin x := by
    rw [e]; exact Real.sin_add_int_mul_two_pi x (-m)
  rw [← hsin]
  refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) ?_
  nlinarith [Real.pi_pos]

theorem sin_nonpos_of_mem_strip {k : ℤ} (hk : ¬ Even k) {x : ℝ}
    (h1 : (k : ℝ) * π ≤ x) (h2 : x ≤ ((k : ℝ) + 1) * π) : Real.sin x ≤ 0 := by
  obtain ⟨m, hm⟩ := Int.not_even_iff_odd.1 hk
  have hkm : (k : ℝ) = 2 * m + 1 := by rw [hm]; push_cast; ring
  have e : x - ((k : ℝ) + 1) * π = x + ((-(m + 1) : ℤ) : ℝ) * (2 * π) := by
    rw [hkm]; push_cast; ring
  have hsin : Real.sin (x - ((k : ℝ) + 1) * π) = Real.sin x := by
    rw [e]; exact Real.sin_add_int_mul_two_pi x (-(m + 1))
  rw [← hsin]
  refine Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) ?_
  nlinarith [Real.pi_pos]

/-! ### Strip constraint gives monotonicity -/

theorem monotoneOn_of_mem_strip {ϑ φ c : ℝ → ℝ} {a b : ℝ} {k : ℤ} (hk : Even k)
    (hc : ∀ s ∈ Icc a b, 0 ≤ c s)
    (hd : ∀ s ∈ Icc a b, HasDerivAt φ (c s * Real.sin (ϑ s - φ s)) s)
    (hs : ∀ s ∈ Icc a b, (k : ℝ) * π ≤ ϑ s - φ s ∧ ϑ s - φ s ≤ ((k : ℝ) + 1) * π) :
    MonotoneOn φ (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s => c s * Real.sin (ϑ s - φ s))
    (convex_Icc a b) (fun s hs' => (hd s hs').continuousAt.continuousWithinAt)
    (fun x hx => ((hd x (interior_subset hx)).hasDerivWithinAt)) (fun x hx => ?_)
  have hx' := interior_subset hx
  exact mul_nonneg (hc x hx') (sin_nonneg_of_mem_strip hk (hs x hx').1 (hs x hx').2)

theorem antitoneOn_of_mem_strip {ϑ φ c : ℝ → ℝ} {a b : ℝ} {k : ℤ} (hk : ¬ Even k)
    (hc : ∀ s ∈ Icc a b, 0 ≤ c s)
    (hd : ∀ s ∈ Icc a b, HasDerivAt φ (c s * Real.sin (ϑ s - φ s)) s)
    (hs : ∀ s ∈ Icc a b, (k : ℝ) * π ≤ ϑ s - φ s ∧ ϑ s - φ s ≤ ((k : ℝ) + 1) * π) :
    AntitoneOn φ (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s => c s * Real.sin (ϑ s - φ s))
    (convex_Icc a b) (fun s hs' => (hd s hs').continuousAt.continuousWithinAt)
    (fun x hx => ((hd x (interior_subset hx)).hasDerivWithinAt)) (fun x hx => ?_)
  have hx' := interior_subset hx
  exact mul_nonpos_of_nonneg_of_nonpos (hc x hx')
    (sin_nonpos_of_mem_strip hk (hs x hx').1 (hs x hx').2)


/-! ### Radon's bound -/

/-- Paper `lem:viewing-angle`, `eq:viewing-angle-bound`.  For an arc in polar form
`γ - β = ρ e^{iφ}`, `γ' = ν e^{iϑ}` with `ρ, ν > 0`, whose parameter interval is cut into
finitely many pieces on each of which `ϑ - φ` stays inside one strip `[k π, (k+1) π]`, the
variation of the viewing angle `φ` exceeds the tangent-angle variation `𝒦_γ` by at most `π`.

**Differs from the paper's route.**  `lem:viewing-angle` cites Radon's theorem on the viewing
angle of an arc of bounded rotation; here the bound is proven, by cutting the parameter
interval where `sin(ϑ - φ)` vanishes and telescoping the excess through `phaseFold`.  Mathlib
carries `eVariationOn` but no theory of arcs of bounded rotation, so there is nothing to cite.

The derivative hypothesis is what `hasDerivAt_viewingAngle` supplies from the polar data;
`c = ν / ρ`. -/
theorem viewing_angle_bound
    {ϑ φ c : ℝ → ℝ} {u : ℕ → ℝ} {k : ℕ → ℤ} {n : ℕ}
    (hu : Monotone u)
    (hc : ∀ s ∈ Icc (u 0) (u n), 0 ≤ c s)
    (hd : ∀ s ∈ Icc (u 0) (u n), HasDerivAt φ (c s * Real.sin (ϑ s - φ s)) s)
    (hstrip : ∀ i, i < n → ∀ s ∈ Icc (u i) (u (i + 1)),
        (k i : ℝ) * π ≤ ϑ s - φ s ∧ ϑ s - φ s ≤ ((k i : ℝ) + 1) * π) :
    eVariationOn φ (Icc (u 0) (u n))
      ≤ eVariationOn ϑ (Icc (u 0) (u n)) + ENNReal.ofReal π := by
  have hsub : ∀ i, i < n → Icc (u i) (u (i + 1)) ⊆ Icc (u 0) (u n) := fun i hi =>
    Icc_subset_Icc (hu (Nat.zero_le i)) (hu hi)
  refine eVariationOn_le_of_stripPartition hu hstrip (fun i hi hk => ?_) (fun i hi hk => ?_)
  · exact monotoneOn_of_mem_strip hk (fun s hs => hc s (hsub i hi hs))
      (fun s hs => hd s (hsub i hi hs)) (hstrip i hi)
  · exact antitoneOn_of_mem_strip hk (fun s hs => hc s (hsub i hi hs))
      (fun s hs => hd s (hsub i hi hs)) (hstrip i hi)

/-- `viewing_angle_bound` in the sharp form of
`eVariationOn_add_phaseFold_le_of_stripPartition`: the excess of `Var φ` over `Var ϑ` is at
most the drop of the folded phase across the interval, rather than merely `π`. -/
theorem viewing_angle_bound_phaseFold
    {ϑ φ c : ℝ → ℝ} {u : ℕ → ℝ} {k : ℕ → ℤ} {n : ℕ}
    (hu : Monotone u)
    (hc : ∀ s ∈ Icc (u 0) (u n), 0 ≤ c s)
    (hd : ∀ s ∈ Icc (u 0) (u n), HasDerivAt φ (c s * Real.sin (ϑ s - φ s)) s)
    (hstrip : ∀ i, i < n → ∀ s ∈ Icc (u i) (u (i + 1)),
        (k i : ℝ) * π ≤ ϑ s - φ s ∧ ϑ s - φ s ≤ ((k i : ℝ) + 1) * π) :
    eVariationOn φ (Icc (u 0) (u n)) + ENNReal.ofReal (phaseFold (ϑ (u n) - φ (u n)))
      ≤ eVariationOn ϑ (Icc (u 0) (u n))
          + ENNReal.ofReal (phaseFold (ϑ (u 0) - φ (u 0))) := by
  have hsub : ∀ i, i < n → Icc (u i) (u (i + 1)) ⊆ Icc (u 0) (u n) := fun i hi =>
    Icc_subset_Icc (hu (Nat.zero_le i)) (hu hi)
  refine eVariationOn_add_phaseFold_le_of_stripPartition hu hstrip
    (fun i hi hk => ?_) (fun i hi hk => ?_)
  · exact monotoneOn_of_mem_strip hk (fun s hs => hc s (hsub i hi hs))
      (fun s hs => hd s (hsub i hi hs)) (hstrip i hi)
  · exact antitoneOn_of_mem_strip hk (fun s hs => hc s (hsub i hi hs))
      (fun s hs => hd s (hsub i hi hs)) (hstrip i hi)

/-! ### The strip partition from a finite critical set

`viewing_angle_bound` consumes a cut of the parameter interval on which `ϑ - φ` stays inside
one strip.  The cut is made at the points where `sin (ϑ - φ)` vanishes — the critical points
of the viewing angle, by `hasDerivAt_viewingAngle` — so the whole hypothesis reduces to the
finiteness of that set, which is what real-analyticity of the arc supplies. -/

/-- On a closed interval whose interior carries no point where `α` is an integer multiple of
`π`, `α` stays inside a single strip `[k π, (k+1) π]`. -/
theorem mem_strip_of_no_level_point {α : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (hα : ContinuousOn α (Icc c d))
    (hno : ∀ x ∈ Ioo c d, ∀ m : ℤ, α x ≠ (m : ℝ) * π) :
    ∃ k : ℤ, ∀ s ∈ Icc c d, (k : ℝ) * π ≤ α s ∧ α s ≤ ((k : ℝ) + 1) * π := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  set mid := (c + d) / 2 with hmiddef
  have hmid : mid ∈ Ioo c d := ⟨by rw [hmiddef]; linarith, by rw [hmiddef]; linarith⟩
  refine ⟨⌊α mid / π⌋, fun s hs => ?_⟩
  set k : ℤ := ⌊α mid / π⌋ with hk
  have h1 : (k:ℝ) ≤ α mid / π := Int.floor_le _
  have h2 : α mid / π < (k : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one (α mid / π)
  have hne : α mid / π ≠ (k : ℝ) := by
    intro h
    exact hno mid hmid k (by rw [div_eq_iff hπ.ne'] at h; exact h)
  have hlt1 : (k:ℝ) * π < α mid := by
    have h3 : (k:ℝ) < α mid / π := lt_of_le_of_ne h1 (Ne.symm hne)
    rw [lt_div_iff₀ hπ] at h3
    linarith
  have hlt2 : α mid < ((k:ℝ) + 1) * π := by
    rw [div_lt_iff₀ hπ] at h2
    linarith
  constructor
  · by_contra hcon
    push Not at hcon
    rcases lt_trichotomy s mid with h | h | h
    · obtain ⟨x, hx, hxv⟩ :=
        intermediate_value_Ioo h.le (hα.mono (Icc_subset_Icc hs.1 hmid.2.le))
          (⟨hcon, hlt1⟩ : (k:ℝ) * π ∈ Ioo (α s) (α mid))
      exact hno x ⟨lt_of_le_of_lt hs.1 hx.1, lt_trans hx.2 hmid.2⟩ k hxv
    · rw [h] at hcon; linarith
    · obtain ⟨x, hx, hxv⟩ :=
        intermediate_value_Ioo' h.le (hα.mono (Icc_subset_Icc hmid.1.le hs.2))
          (⟨hcon, hlt1⟩ : (k:ℝ) * π ∈ Ioo (α s) (α mid))
      exact hno x ⟨lt_trans hmid.1 hx.1, lt_of_lt_of_le hx.2 hs.2⟩ k hxv
  · by_contra hcon
    push Not at hcon
    have hcast : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rcases lt_trichotomy s mid with h | h | h
    · obtain ⟨x, hx, hxv⟩ :=
        intermediate_value_Ioo' h.le (hα.mono (Icc_subset_Icc hs.1 hmid.2.le))
          (⟨hlt2, hcon⟩ : ((k:ℝ) + 1) * π ∈ Ioo (α mid) (α s))
      exact hno x ⟨lt_of_le_of_lt hs.1 hx.1, lt_trans hx.2 hmid.2⟩ (k + 1)
        (by rw [hcast]; exact hxv)
    · rw [h] at hcon; linarith
    · obtain ⟨x, hx, hxv⟩ :=
        intermediate_value_Ioo h.le (hα.mono (Icc_subset_Icc hmid.1.le hs.2))
          (⟨hlt2, hcon⟩ : ((k:ℝ) + 1) * π ∈ Ioo (α mid) (α s))
      exact hno x ⟨lt_trans hmid.1 hx.1, lt_of_lt_of_le hx.2 hs.2⟩ (k + 1)
        (by rw [hcast]; exact hxv)


/-- The cut itself.  If every point of `(a, b)` at which `α` is an integer multiple of `π`
lies in some finite set, then `[a, b]` admits a finite cut on each piece of which `α` stays
inside one strip.  This is the hypothesis `viewing_angle_bound` consumes, so the whole of
Radon's bound rests on the finiteness of the viewing angle's critical set. -/
theorem exists_stripPartition {α : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hα : ContinuousOn α (Icc a b))
    (S : Finset ℝ) (hSsub : ∀ x ∈ S, x ∈ Icc a b)
    (hS : ∀ x ∈ Ioo a b, ∀ m : ℤ, α x = (m : ℝ) * π → x ∈ S) :
    ∃ (n : ℕ) (u : ℕ → ℝ) (k : ℕ → ℤ), Monotone u ∧ u 0 = a ∧ u n = b ∧
      ∀ i, i < n → ∀ s ∈ Icc (u i) (u (i + 1)),
        (k i : ℝ) * π ≤ α s ∧ α s ≤ ((k i : ℝ) + 1) * π := by
  classical
  rcases eq_or_lt_of_le hab with hEq | hlt
  · exact ⟨0, fun _ => a, fun _ => 0, monotone_const, rfl, hEq, fun i hi => absurd hi (by omega)⟩
  set T : Finset ℝ := insert a (insert b S) with hTdef
  have haT : a ∈ T := by simp [hTdef]
  have hbT : b ∈ T := by simp [hTdef]
  have hTsub : ∀ x ∈ T, x ∈ Icc a b := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨le_rfl, hab⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨hab, le_rfl⟩
    · exact hSsub x hx
  have hTne : T.Nonempty := ⟨a, haT⟩
  have hcard0 : 0 < T.card := Finset.card_pos.2 hTne
  set n : ℕ := T.card - 1 with hndef
  have hcard : T.card = n + 1 := by omega
  have hbnd : ∀ i : ℕ, min i n < T.card := fun i => by omega
  set e := T.orderEmbOfFin (rfl : T.card = T.card) with hedef
  set u : ℕ → ℝ := fun i => e ⟨min i n, hbnd i⟩ with hudef
  have humono : Monotone u := by
    intro i j hij
    exact e.monotone (by simp only [Fin.mk_le_mk]; omega)
  -- the endpoints
  have hmin : T.min' hTne = a :=
    le_antisymm (Finset.min'_le T a haT) (Finset.le_min' T hTne a (fun y hy => (hTsub y hy).1))
  have hmax : T.max' hTne = b :=
    le_antisymm (Finset.max'_le T hTne b (fun y hy => (hTsub y hy).2)) (Finset.le_max' T b hbT)
  have hu0 : u 0 = a := by
    have := Finset.orderEmbOfFin_zero (rfl : T.card = T.card) hcard0
    simp only [hudef, hedef, Nat.zero_min] at this ⊢
    rw [this, hmin]
  have hun : u n = b := by
    have hlast := Finset.orderEmbOfFin_last (s := T) (rfl : T.card = T.card) hcard0
    have hidx : u n = T.orderEmbOfFin (rfl : T.card = T.card)
        ⟨T.card - 1, Nat.sub_lt hcard0 (Nat.succ_pos 0)⟩ := by
      simp only [hudef, hedef]
      congr 1
      exact Fin.ext (by simp [hndef])
    rw [hidx, hlast, hmax]
  -- no element of `T` lies strictly between consecutive cut points
  have hrange : Set.range e = (T : Set ℝ) := Finset.range_orderEmbOfFin T rfl
  have hgap : ∀ i, i < n → ∀ x ∈ T, ¬ (u i < x ∧ x < u (i + 1)) := by
    rintro i hi x hxT ⟨hx1, hx2⟩
    obtain ⟨j, hj⟩ : x ∈ Set.range e := by rw [hrange]; exact Finset.mem_coe.2 hxT
    have e1 : u i = e ⟨i, by omega⟩ := by
      simp only [hudef]; congr 1; exact Fin.ext (by simp; omega)
    have e2 : u (i + 1) = e ⟨i + 1, by omega⟩ := by
      simp only [hudef]; congr 1; exact Fin.ext (by simp; omega)
    rw [e1, ← hj] at hx1
    rw [e2, ← hj] at hx2
    have j1 : i < (j : ℕ) := by
      have := e.strictMono.lt_iff_lt.1 hx1
      exact this
    have j2 : (j : ℕ) < i + 1 := by
      have := e.strictMono.lt_iff_lt.1 hx2
      exact this
    omega
  -- each piece carries no level point, hence lies in one strip
  have hex : ∀ i : ℕ, ∃ κ : ℤ, i < n → ∀ s ∈ Icc (u i) (u (i + 1)),
      (κ : ℝ) * π ≤ α s ∧ α s ≤ ((κ : ℝ) + 1) * π := by
    intro i
    by_cases hi : i < n
    · have hab' : u i < u (i + 1) := by
        have e1 : u i = e ⟨i, by omega⟩ := by
          simp only [hudef]; congr 1; exact Fin.ext (by simp; omega)
        have e2 : u (i + 1) = e ⟨i + 1, by omega⟩ := by
          simp only [hudef]; congr 1; exact Fin.ext (by simp; omega)
        rw [e1, e2]
        exact e.strictMono (by simp [Fin.mk_lt_mk])
      have hsub : Icc (u i) (u (i + 1)) ⊆ Icc a b := by
        refine Icc_subset_Icc ?_ ?_
        · rw [← hu0]; exact humono (Nat.zero_le i)
        · rw [← hun]; exact humono hi
      have hno : ∀ x ∈ Ioo (u i) (u (i + 1)), ∀ m : ℤ, α x ≠ (m : ℝ) * π := by
        intro x hx m hm
        have hxab : x ∈ Ioo a b := by
          constructor
          · exact lt_of_le_of_lt (by rw [← hu0]; exact humono (Nat.zero_le i)) hx.1
          · exact lt_of_lt_of_le hx.2 (by rw [← hun]; exact humono hi)
        exact hgap i hi x
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hS x hxab m hm))) ⟨hx.1, hx.2⟩
      obtain ⟨κ, hκ⟩ := mem_strip_of_no_level_point hab' (hα.mono hsub) hno
      exact ⟨κ, fun _ => hκ⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose k hk using hex
  exact ⟨n, u, k, humono, hu0, hun, fun i hi => hk i hi⟩


/-! ### Radon's bound with the cut discharged -/

/-- Paper `lem:viewing-angle`, `eq:viewing-angle-bound`.  The cut is gone: all that is asked
of the arc is that the viewing angle's critical set — the points of the open parameter
interval where `ϑ - φ` is an integer multiple of `π` — be contained in a finite set. -/
theorem viewing_angle_bound_of_finite
    {ϑ φ c : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hϑc : ContinuousOn ϑ (Icc a b))
    (hc : ∀ s ∈ Icc a b, 0 ≤ c s)
    (hd : ∀ s ∈ Icc a b, HasDerivAt φ (c s * Real.sin (ϑ s - φ s)) s)
    (S : Finset ℝ) (hSsub : ∀ x ∈ S, x ∈ Icc a b)
    (hS : ∀ x ∈ Ioo a b, ∀ m : ℤ, ϑ x - φ x = (m : ℝ) * π → x ∈ S) :
    eVariationOn φ (Icc a b) ≤ eVariationOn ϑ (Icc a b) + ENNReal.ofReal π := by
  obtain ⟨n, u, k, humono, hu0, hun, hstrip⟩ :=
    exists_stripPartition (α := fun s => ϑ s - φ s) hab
      (hϑc.sub (fun s hs => (hd s hs).continuousAt.continuousWithinAt)) S hSsub hS
  have hmain := viewing_angle_bound (ϑ := ϑ) (φ := φ) (c := c) (u := u) (k := k) (n := n)
    humono (by rw [hu0, hun]; exact hc) (by rw [hu0, hun]; exact hd) hstrip
  rwa [hu0, hun] at hmain

/-- `viewing_angle_bound_of_finite` in the sharp form: the excess of `Var φ` over `Var ϑ` is
at most the **drop** of `phaseFold (ϑ - φ)` from `a` to `b`.

`cos (ϑ - φ)` is the normalized inner product `Re(γ' \overline{γ - β}) / (‖γ'‖‖γ - β‖)`, so
the folded phase is a geometric quantity of the arc and the vantage point alone; it runs to
`π` as the parameter approaches a point where `γ` meets `β` from the left and to `0` from the
right, which is what makes the two components of `eq:viewing-angle-bound` cost one `π`
between them rather than one each. -/
theorem viewing_angle_bound_of_finite_phaseFold
    {ϑ φ c : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hϑc : ContinuousOn ϑ (Icc a b))
    (hc : ∀ s ∈ Icc a b, 0 ≤ c s)
    (hd : ∀ s ∈ Icc a b, HasDerivAt φ (c s * Real.sin (ϑ s - φ s)) s)
    (S : Finset ℝ) (hSsub : ∀ x ∈ S, x ∈ Icc a b)
    (hS : ∀ x ∈ Ioo a b, ∀ m : ℤ, ϑ x - φ x = (m : ℝ) * π → x ∈ S) :
    eVariationOn φ (Icc a b) + ENNReal.ofReal (phaseFold (ϑ b - φ b))
      ≤ eVariationOn ϑ (Icc a b) + ENNReal.ofReal (phaseFold (ϑ a - φ a)) := by
  obtain ⟨n, u, k, humono, hu0, hun, hstrip⟩ :=
    exists_stripPartition (α := fun s => ϑ s - φ s) hab
      (hϑc.sub (fun s hs => (hd s hs).continuousAt.continuousWithinAt)) S hSsub hS
  have hmain := viewing_angle_bound_phaseFold (ϑ := ϑ) (φ := φ) (c := c) (u := u) (k := k)
    (n := n) humono (by rw [hu0, hun]; exact hc) (by rw [hu0, hun]; exact hd) hstrip
  rwa [hu0, hun] at hmain

/-- Paper `lem:viewing-angle` in the manuscript's own terms: an arc `γ` written in polar form
about `β` as `γ - β = ρ e^{iφ}`, with tangent `γ' = ν e^{iϑ}`, obeys
`Var arg(γ - β) ≤ 𝒦_γ + π` as soon as the viewing angle has finitely many critical points on
the arc. -/
theorem viewing_angle_bound_polar
    {γ : ℝ → ℂ} {β : ℂ} {ρ ν ϑ φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hϑc : ContinuousOn ϑ (Icc a b))
    (hρpos : ∀ s ∈ Icc a b, 0 < ρ s) (hνpos : ∀ s ∈ Icc a b, 0 ≤ ν s)
    (hρ : ∀ s ∈ Icc a b, DifferentiableAt ℝ ρ s)
    (hφ : ∀ s ∈ Icc a b, DifferentiableAt ℝ φ s)
    (hpol : ∀ s ∈ Icc a b, (fun t => γ t - β)
        =ᶠ[nhds s] fun t => (ρ t : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I))
    (hγ : ∀ s ∈ Icc a b, HasDerivAt γ ((ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I)) s)
    (S : Finset ℝ) (hSsub : ∀ x ∈ S, x ∈ Icc a b)
    (hS : ∀ x ∈ Ioo a b, ∀ m : ℤ, ϑ x - φ x = (m : ℝ) * π → x ∈ S) :
    eVariationOn φ (Icc a b) ≤ eVariationOn ϑ (Icc a b) + ENNReal.ofReal π :=
  viewing_angle_bound_of_finite hab hϑc (c := fun s => ν s / ρ s)
    (fun s hs => div_nonneg (hνpos s hs) (hρpos s hs).le)
    (fun s hs => hasDerivAt_viewingAngle (hρpos s hs) (hρ s hs) (hφ s hs) (hpol s hs) (hγ s hs))
    S hSsub hS

/-! ### The constant `π` is attained in the limit

The horizontal line `γ(s) = s + i` viewed from `β = 0` has constant tangent angle, so
`𝒦_γ = 0`; the viewing angle is `φ(s) = π/2 - arctan s`, whose variation over `[-T, T]` is
`2 arctan T`.  This is a witness that the hypotheses of `viewing_angle_bound` are
satisfiable, and that its constant `π` cannot be replaced by anything smaller. -/

/-- The viewing angle of the line `γ(s) = s + i` from the origin. -/
noncomputable def lineViewingAngle (s : ℝ) : ℝ := π / 2 - Real.arctan s

theorem hasDerivAt_lineViewingAngle (s : ℝ) :
    HasDerivAt lineViewingAngle
      (1 / Real.sqrt (1 + s ^ 2) * Real.sin (0 - lineViewingAngle s)) s := by
  have hb : HasDerivAt (fun x : ℝ => π / 2 - Real.arctan x) (0 - 1 / (1 + s ^ 2)) s :=
    (hasDerivAt_const s (π / 2)).sub (Real.hasDerivAt_arctan s)
  have h : HasDerivAt lineViewingAngle (-(1 / (1 + s ^ 2))) s := by
    change HasDerivAt (fun x : ℝ => π / 2 - Real.arctan x) (-(1 / (1 + s ^ 2))) s
    simpa using hb
  have hpos : (0:ℝ) < 1 + s ^ 2 := by positivity
  have hsq : Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) = 1 + s ^ 2 :=
    Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt (1 + s ^ 2) ≠ 0 := by positivity
  refine h.congr_deriv ?_
  have : Real.sin (0 - lineViewingAngle s) = -(1 / Real.sqrt (1 + s ^ 2)) := by
    have he : (0:ℝ) - lineViewingAngle s = Real.arctan s - π / 2 := by
      unfold lineViewingAngle; ring
    rw [he, Real.sin_sub_pi_div_two, Real.cos_arctan]
  rw [this]
  field_simp
  linarith [hsq]

theorem strip_lineViewingAngle (s : ℝ) :
    ((-1 : ℤ) : ℝ) * π ≤ 0 - lineViewingAngle s
      ∧ 0 - lineViewingAngle s ≤ (((-1 : ℤ) : ℝ) + 1) * π := by
  have h1 := Real.neg_pi_div_two_lt_arctan s
  have h2 := Real.arctan_lt_pi_div_two s
  have e : (0:ℝ) - lineViewingAngle s = Real.arctan s - π / 2 := by
    unfold lineViewingAngle; ring
  rw [e]
  push_cast
  constructor <;> linarith

/-- The line witness: `𝒦_γ = 0`, and the viewing angle has variation `2 arctan T`. -/
theorem eVariationOn_lineViewingAngle {T : ℝ} (hT : 0 ≤ T) :
    eVariationOn lineViewingAngle (Icc (-T) T) = ENNReal.ofReal (2 * Real.arctan T) := by
  have hanti : AntitoneOn lineViewingAngle (Icc (-T) T) := fun x _ y _ hxy => by
    simp only [lineViewingAngle]
    have := Real.arctan_mono hxy
    linarith
  have h := AntitoneOn.eVariationOn_eq hanti (a := -T) (b := T)
    (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
  rw [Set.inter_self] at h
  rw [h]
  congr 1
  simp [lineViewingAngle, Real.arctan_neg]
  ring

/-- The line witness discharges every hypothesis of `viewing_angle_bound_of_finite` — its
critical set is empty, since `ϑ - φ` stays inside `(-π, 0)` — and the bound it returns is
`2 arctan T ≤ 0 + π`: sharp in the limit `T → ∞`.  So the whole chain, `exists_stripPartition`
included, is non-vacuous. -/
theorem viewing_angle_bound_line {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal (2 * Real.arctan T)
      ≤ eVariationOn (fun _ : ℝ => (0:ℝ)) (Icc (-T) T) + ENNReal.ofReal π := by
  have hπ := Real.pi_pos
  have hempty : ∀ x ∈ Ioo (-T) T, ∀ m : ℤ,
      (0:ℝ) - lineViewingAngle x = (m : ℝ) * π → x ∈ (∅ : Finset ℝ) := by
    intro x _ m hm
    exfalso
    have h1 := Real.neg_pi_div_two_lt_arctan x
    have h2 := Real.arctan_lt_pi_div_two x
    have he : (0:ℝ) - lineViewingAngle x = Real.arctan x - π / 2 := by
      unfold lineViewingAngle; ring
    rw [he] at hm
    have ha : (m:ℝ) * π < 0 := by rw [← hm]; linarith
    have hb : -π < (m:ℝ) * π := by rw [← hm]; linarith
    have hm0 : (m:ℝ) < 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have hm1 : (-1:ℝ) < (m:ℝ) := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have c0 : m < 0 := by exact_mod_cast hm0
    have c1 : (-1:ℤ) < m := by exact_mod_cast hm1
    omega
  have hmain := viewing_angle_bound_of_finite (ϑ := fun _ => (0:ℝ)) (φ := lineViewingAngle)
    (c := fun s => 1 / Real.sqrt (1 + s ^ 2)) (a := -T) (b := T) (by linarith)
    continuousOn_const (fun s _ => by positivity)
    (fun s _ => hasDerivAt_lineViewingAngle s)
    ∅ (fun x hx => absurd hx (Finset.notMem_empty x)) hempty
  rwa [eVariationOn_lineViewingAngle hT] at hmain

/-- The same witness with `𝒦_γ = 0` evaluated: Radon's route delivers `2 arctan T ≤ π`, and
`2 arctan T → π`, so no constant below `π` would do. -/
theorem viewing_angle_bound_line_le_pi {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal (2 * Real.arctan T) ≤ ENNReal.ofReal π := by
  have h0 : eVariationOn (fun _ : ℝ => (0:ℝ)) (Icc (-T) T) = 0 := by
    refine eVariationOn.constant_on ?_
    rintro x ⟨p, -, rfl⟩ y ⟨q, -, rfl⟩
    rfl
  simpa [h0] using viewing_angle_bound_line hT


/-! ### The argument branch, constructed

`viewing_angle_bound_polar` takes the polar decomposition `γ - β = ρ e^{iφ}` as data.  It need
not: for a differentiable nonvanishing path the branch is an integral,
`L(s) = log(γ(a) - β) + ∫_a^s γ'/(γ - β)`, and `(γ - β)e^{-L}` has zero derivative, so
`e^{L} = γ - β` throughout.  This is the continuous argument lift, built without any covering
space, and it is what removes the per-root hypothesis from `cor:linear-phase-variation`. -/

/-- The logarithmic lift of a differentiable path avoiding `β`.

**Differs from the paper's route.**  `eq:viewing-angle-bound` quantifies over a continuous
branch of the argument and does not construct one; here the branch is built, as
`log(γ(a) - β) + ∫ γ'/(γ - β)`.  Mathlib has no continuous-argument lift along a path, so a
hypothesized branch could not be produced at the point of use. -/
noncomputable def logLift (γ dγ : ℝ → ℂ) (β : ℂ) (a : ℝ) (s : ℝ) : ℂ :=
  Complex.log (γ a - β) + ∫ u in a..s, dγ u / (γ u - β)

/-- The continuous branch of `arg(γ - β)` along the path. -/
noncomputable def polarAngle (γ dγ : ℝ → ℂ) (β : ℂ) (a : ℝ) (s : ℝ) : ℝ :=
  (logLift γ dγ β a s).im

/-- The matching modulus, `‖γ - β‖` in the form `e^{Re L}`. -/
noncomputable def polarModulus (γ dγ : ℝ → ℂ) (β : ℂ) (a : ℝ) (s : ℝ) : ℝ :=
  Real.exp ((logLift γ dγ β a s).re)

theorem polarModulus_pos (γ dγ : ℝ → ℂ) (β : ℂ) (a s : ℝ) :
    0 < polarModulus γ dγ β a s := Real.exp_pos _

section Lift

variable {γ dγ : ℝ → ℂ} {β : ℂ} {U : Set ℝ} {a b : ℝ}

/-- The path avoids `β` on an open set containing the parameter interval. -/
private theorem lift_open_aux (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hne : ∀ s ∈ Icc a b, γ s ≠ β) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc a b ⊆ V ∧ V ⊆ U ∧ ∀ s ∈ V, γ s ≠ β := by
  refine ⟨U ∩ γ ⁻¹' ({β}ᶜ), ?_, ?_, Set.inter_subset_left, ?_⟩
  · exact ContinuousOn.isOpen_inter_preimage
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt) hU isOpen_compl_singleton
  · exact fun x hx => ⟨hsub hx, hne x hx⟩
  · exact fun x hx => hx.2

/-- `hasDerivAt_logLift` with the lift based anywhere in the interval rather than at its left
endpoint.  The right component of `[a,b] ∖ γ⁻¹({β})` is exhausted by intervals `[d, b]` with
`d` running down to the meeting parameter, and a branch whose base moved with `d` would not be
one branch; basing it at `b` keeps it fixed. -/
theorem hasDerivAt_logLift_base (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {c : ℝ} (hcmem : c ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivAt (logLift γ dγ β c) (dγ s / (γ s - β)) s := by
  obtain ⟨V, hVopen, hVsub, hVU, hVne⟩ := lift_open_aux hU hsub hd hne
  have hγV : ContinuousOn γ V := fun x hx =>
    (hd x (hVU hx)).continuousAt.continuousWithinAt
  have hgV : ContinuousOn (fun u => dγ u / (γ u - β)) V :=
    (hc.mono hVU).div (hγV.sub continuousOn_const) (fun x hx => sub_ne_zero.2 (hVne x hx))
  have hsV : s ∈ V := hVsub hs
  have huIcc : Set.uIcc c s ⊆ Icc a b := by
    rw [Set.uIcc_eq_union]
    exact Set.union_subset (Set.Icc_subset_Icc hcmem.1 hs.2) (Set.Icc_subset_Icc hs.1 hcmem.2)
  have hint : IntervalIntegrable (fun u => dγ u / (γ u - β)) MeasureTheory.volume c s :=
    (hgV.mono (huIcc.trans hVsub)).intervalIntegrable
  have hmeas := ContinuousOn.stronglyMeasurableAtFilter (μ := MeasureTheory.volume)
    hVopen hgV s hsV
  have hcont : ContinuousAt (fun u => dγ u / (γ u - β)) s :=
    hgV.continuousAt (hVopen.mem_nhds hsV)
  exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_add _

theorem hasDerivAt_logLift (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivAt (logLift γ dγ β a) (dγ s / (γ s - β)) s :=
  hasDerivAt_logLift_base hU hsub hd hc hne ⟨le_rfl, hs.1.trans hs.2⟩ hs

theorem exp_logLift_base (_hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {c : ℝ} (hcmem : c ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    Complex.exp (logLift γ dγ β c s) = γ s - β := by
  set F : ℝ → ℂ := fun t => (γ t - β) * Complex.exp (-(logLift γ dγ β c t)) with hF
  have hderiv : ∀ x ∈ Icc a b, HasDerivAt F 0 x := by
    intro x hx
    have hzne : γ x - β ≠ 0 := sub_ne_zero.2 (hne x hx)
    have h1 : HasDerivAt (fun t => γ t - β) (dγ x) x := (hd x (hsub hx)).sub_const β
    have h2 : HasDerivAt (fun t => -(logLift γ dγ β c t)) (-(dγ x / (γ x - β))) x :=
      (hasDerivAt_logLift_base hU hsub hd hc hne hcmem hx).neg
    have h4 := h1.mul h2.cexp
    refine h4.congr_deriv ?_
    have : (γ x - β) * (dγ x / (γ x - β)) = dγ x := by
      field_simp
    rw [show Complex.exp (-(logLift γ dγ β c x)) * (-(dγ x / (γ x - β)))
        = -(Complex.exp (-(logLift γ dγ β c x)) * (dγ x / (γ x - β))) by ring]
    rw [show (γ x - β) * -(Complex.exp (-(logLift γ dγ β c x)) * (dγ x / (γ x - β)))
        = -(Complex.exp (-(logLift γ dγ β c x)) * ((γ x - β) * (dγ x / (γ x - β)))) by ring]
    rw [this]
    ring
  have hcont : ContinuousOn F (Icc a b) := fun x hx =>
    ((hderiv x hx).continuousAt).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun x hx => (hderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
  have haF : F c = 1 := by
    have hane : γ c - β ≠ 0 := sub_ne_zero.2 (hne c hcmem)
    have hla : logLift γ dγ β c c = Complex.log (γ c - β) := by
      simp [logLift]
    rw [hF]
    simp only [hla, Complex.exp_neg, Complex.exp_log hane]
    field_simp
  have hFs : (γ s - β) * Complex.exp (-(logLift γ dγ β c s)) = 1 :=
    (hconst s hs).trans ((hconst c hcmem).symm.trans haF)
  have hexpne : Complex.exp (logLift γ dγ β c s) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.exp_neg] at hFs
  field_simp at hFs
  exact hFs.symm

theorem exp_logLift (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {s : ℝ} (hs : s ∈ Icc a b) :
    Complex.exp (logLift γ dγ β a s) = γ s - β :=
  exp_logLift_base hab hU hsub hd hc hne ⟨le_rfl, hab⟩ hs

theorem polar_decomposition_base (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {c : ℝ} (hcmem : c ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    γ s - β = (polarModulus γ dγ β c s : ℂ)
      * Complex.exp ((polarAngle γ dγ β c s : ℂ) * Complex.I) := by
  have hL := exp_logLift_base hab hU hsub hd hc hne hcmem hs
  rw [← hL, polarModulus, polarAngle, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  exact (Complex.re_add_im _).symm

theorem polar_decomposition (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {s : ℝ} (hs : s ∈ Icc a b) :
    γ s - β = (polarModulus γ dγ β a s : ℂ)
      * Complex.exp ((polarAngle γ dγ β a s : ℂ) * Complex.I) :=
  polar_decomposition_base hab hU hsub hd hc hne ⟨le_rfl, hab⟩ hs

theorem hasDerivAt_polarAngle_base (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {c : ℝ} (hcmem : c ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivAt (polarAngle γ dγ β c) ((dγ s / (γ s - β)).im) s := by
  have hL := hasDerivAt_logLift_base hU hsub hd hc hne hcmem hs
  exact hL.im

theorem hasDerivAt_polarAngle (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivAt (polarAngle γ dγ β a) ((dγ s / (γ s - β)).im) s :=
  hasDerivAt_polarAngle_base hU hsub hd hc hne ⟨le_rfl, hs.1.trans hs.2⟩ hs

end Lift


/-! ### The folded phase at a parameter where the arc meets the vantage point

`phaseFold (ϑ - φ)` is `arccos` of the normalized inner product of the tangent with the chord,
`Re(γ' \overline{γ - β}) / (‖γ'‖ ‖γ - β‖)` — a quantity of the arc and the vantage point
alone, with no branch in it.  At a parameter `m` with `γ m = β` and `γ' m ≠ 0` the chord is
`(s - m) γ'(m) + o(s - m)`, so that ratio runs to `-1` from the left and to `1` from the
right, and the folded phase runs to `π` and to `0`.  This is what makes the two components of
`eq:viewing-angle-bound` cost one `π` between them rather than one each. -/

/-- The cosine of the angle between tangent and chord, read off the two polar
decompositions. -/
theorem cos_sub_of_polar {w z : ℂ} {ρ ν φ ϑ : ℝ} (hρ : 0 < ρ) (hν : 0 < ν)
    (hz : z = (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (hw : w = (ν : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)) :
    Real.cos (ϑ - φ) = (w * (starRingEnd ℂ) z).re / (‖w‖ * ‖z‖) := by
  have hnz : ‖z‖ = ρ := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
      mul_one, abs_of_pos hρ]
  have hnw : ‖w‖ = ν := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
      mul_one, abs_of_pos hν]
  have hexp : Complex.exp ((ϑ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * -Complex.I)
      = Complex.exp (((ϑ - φ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hmul : w * (starRingEnd ℂ) z
      = ((ν * ρ : ℝ) : ℂ) * Complex.exp (((ϑ - φ : ℝ) : ℂ) * Complex.I) := by
    rw [hw, hz, map_mul]
    simp only [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show ((ν : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I))
          * ((ρ : ℂ) * Complex.exp ((φ : ℂ) * -Complex.I))
        = ((ν : ℂ) * (ρ : ℂ))
          * (Complex.exp ((ϑ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * -Complex.I)) by ring,
      hexp]
    push_cast
    ring
  have hνρ : ν * ρ ≠ 0 := by positivity
  rw [hmul, hnw, hnz, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero, mul_comm (ν * ρ) _,
    mul_div_assoc, div_self hνρ, mul_one]

/-- The chord ratio through the meeting parameter, stripped of its sign: the normalized inner
product of the tangent with the *slope*, which tends to `1` because the slope tends to the
tangent. -/
private theorem tendsto_tangent_slope_ratio {γ dγ : ℝ → ℂ} {m : ℝ}
    (hderiv : HasDerivAt γ (dγ m) m) (hdne : dγ m ≠ 0) (hdc : ContinuousAt dγ m) :
    Filter.Tendsto
        (fun s => (dγ s * (starRingEnd ℂ) (slope γ m s)).re / (‖dγ s‖ * ‖slope γ m s‖))
        (nhdsWithin m {m}ᶜ) (nhds 1) := by
  have hu : Filter.Tendsto (slope γ m) (nhdsWithin m {m}ᶜ) (nhds (dγ m)) :=
    hasDerivAt_iff_tendsto_slope.1 hderiv
  have hdd : Filter.Tendsto dγ (nhdsWithin m {m}ᶜ) (nhds (dγ m)) :=
    hdc.tendsto.mono_left nhdsWithin_le_nhds
  have hnum : Filter.Tendsto (fun s => (dγ s * (starRingEnd ℂ) (slope γ m s)).re)
      (nhdsWithin m {m}ᶜ) (nhds ((dγ m * (starRingEnd ℂ) (dγ m)).re)) :=
    (Complex.continuous_re.tendsto _).comp (hdd.mul ((Complex.continuous_conj.tendsto _).comp hu))
  have hden : Filter.Tendsto (fun s => ‖dγ s‖ * ‖slope γ m s‖)
      (nhdsWithin m {m}ᶜ) (nhds (‖dγ m‖ * ‖dγ m‖)) :=
    (hdd.norm).mul (hu.norm)
  have hdennz : ‖dγ m‖ * ‖dγ m‖ ≠ 0 := by
    simpa using (norm_ne_zero_iff.2 hdne)
  have hval : (dγ m * (starRingEnd ℂ) (dγ m)).re / (‖dγ m‖ * ‖dγ m‖) = 1 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, sq,
      div_self hdennz]
  rw [← hval]
  exact hnum.div hden hdennz

/-- The chord ratio itself, from the left: `-1`. -/
private theorem tendsto_chord_ratio_left {γ dγ : ℝ → ℂ} {β : ℂ} {m : ℝ} (hβ : γ m = β)
    (hderiv : HasDerivAt γ (dγ m) m) (hdne : dγ m ≠ 0) (hdc : ContinuousAt dγ m) :
    Filter.Tendsto (fun s => (dγ s * (starRingEnd ℂ) (γ s - β)).re / (‖dγ s‖ * ‖γ s - β‖))
        (nhdsWithin m (Set.Iio m)) (nhds (-1)) := by
  have hle : nhdsWithin m (Set.Iio m) ≤ nhdsWithin m {m}ᶜ :=
    nhdsWithin_mono _ (fun x hx => ne_of_lt hx)
  have hbase := (tendsto_tangent_slope_ratio hderiv hdne hdc).mono_left hle
  refine (hbase.neg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsm : s - m < 0 := sub_neg.2 hs
  have hsne : s - m ≠ 0 := ne_of_lt hsm
  have hchord : γ s - β = ((s - m : ℝ) : ℂ) * slope γ m s := by
    rw [← hβ, ← Complex.real_smul]
    exact (sub_smul_slope γ m s).symm
  rw [hchord, map_mul, Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show dγ s * (((s - m : ℝ) : ℂ) * (starRingEnd ℂ) (slope γ m s))
      = ((s - m : ℝ) : ℂ) * (dγ s * (starRingEnd ℂ) (slope γ m s)) by ring,
    Complex.re_ofReal_mul, abs_of_neg hsm]
  field_simp

/-- The chord ratio itself, from the right: `1`. -/
private theorem tendsto_chord_ratio_right {γ dγ : ℝ → ℂ} {β : ℂ} {m : ℝ} (hβ : γ m = β)
    (hderiv : HasDerivAt γ (dγ m) m) (hdne : dγ m ≠ 0) (hdc : ContinuousAt dγ m) :
    Filter.Tendsto (fun s => (dγ s * (starRingEnd ℂ) (γ s - β)).re / (‖dγ s‖ * ‖γ s - β‖))
        (nhdsWithin m (Set.Ioi m)) (nhds 1) := by
  have hle : nhdsWithin m (Set.Ioi m) ≤ nhdsWithin m {m}ᶜ :=
    nhdsWithin_mono _ (fun x hx => (ne_of_lt hx).symm)
  have hbase := (tendsto_tangent_slope_ratio hderiv hdne hdc).mono_left hle
  refine hbase.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsm : 0 < s - m := sub_pos.2 hs
  have hsne : s - m ≠ 0 := ne_of_gt hsm
  have hchord : γ s - β = ((s - m : ℝ) : ℂ) * slope γ m s := by
    rw [← hβ, ← Complex.real_smul]
    exact (sub_smul_slope γ m s).symm
  rw [hchord, map_mul, Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show dγ s * (((s - m : ℝ) : ℂ) * (starRingEnd ℂ) (slope γ m s))
      = ((s - m : ℝ) : ℂ) * (dγ s * (starRingEnd ℂ) (slope γ m s)) by ring,
    Complex.re_ofReal_mul, abs_of_pos hsm]
  field_simp

/-- **The folded phase runs to `π` on the left of a meeting parameter.**  `φ` is any branch
whose polar decomposition holds on a left-neighborhood of `m`; the limit does not see which
branch, because `phaseFold (ϑ - φ)` is `arccos` of the chord ratio. -/
theorem tendsto_phaseFold_left {γ dγ : ℝ → ℂ} {β : ℂ} {ϑ φ ν ρ : ℝ → ℝ} {m : ℝ} {T : Set ℝ}
    (hT : T ∈ nhdsWithin m (Set.Iio m))
    (hρ : ∀ s ∈ T, 0 < ρ s) (hν : ∀ s ∈ T, 0 < ν s)
    (hz : ∀ s ∈ T, γ s - β = (ρ s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I))
    (hw : ∀ s ∈ T, dγ s = (ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I))
    (hβ : γ m = β) (hderiv : HasDerivAt γ (dγ m) m) (hdne : dγ m ≠ 0)
    (hdc : ContinuousAt dγ m) :
    Filter.Tendsto (fun s => phaseFold (ϑ s - φ s)) (nhdsWithin m (Set.Iio m)) (nhds π) := by
  have hlim := (Real.continuous_arccos.tendsto (-1)).comp
    (tendsto_chord_ratio_left hβ hderiv hdne hdc)
  rw [Function.comp_def, Real.arccos_neg_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hT] with s hs
  rw [phaseFold, cos_sub_of_polar (hρ s hs) (hν s hs) (hz s hs) (hw s hs)]

/-- **The folded phase runs to `0` on the right of a meeting parameter.** -/
theorem tendsto_phaseFold_right {γ dγ : ℝ → ℂ} {β : ℂ} {ϑ φ ν ρ : ℝ → ℝ} {m : ℝ} {T : Set ℝ}
    (hT : T ∈ nhdsWithin m (Set.Ioi m))
    (hρ : ∀ s ∈ T, 0 < ρ s) (hν : ∀ s ∈ T, 0 < ν s)
    (hz : ∀ s ∈ T, γ s - β = (ρ s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I))
    (hw : ∀ s ∈ T, dγ s = (ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I))
    (hβ : γ m = β) (hderiv : HasDerivAt γ (dγ m) m) (hdne : dγ m ≠ 0)
    (hdc : ContinuousAt dγ m) :
    Filter.Tendsto (fun s => phaseFold (ϑ s - φ s)) (nhdsWithin m (Set.Ioi m)) (nhds 0) := by
  have hlim := (Real.continuous_arccos.tendsto 1).comp
    (tendsto_chord_ratio_right hβ hderiv hdne hdc)
  rw [Function.comp_def, Real.arccos_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hT] with s hs
  rw [phaseFold, cos_sub_of_polar (hρ s hs) (hν s hs) (hz s hs) (hw s hs)]


/-! ### Radon's bound at a point off the arc, with the branch built -/

/-- The pointwise form of `hasDerivAt_viewingAngle`.  Once the branch is the constructed one
its derivative is already `Im(γ'/(γ - β))`, so only the values at `s` are needed and no
neighborhood identity has to be carried. -/
theorem hasDerivAt_viewingAngle_of_polar
    {ρ ν ϑ φ : ℝ → ℝ} {w z : ℂ} {s : ℝ}
    (hρs : 0 < ρ s)
    (hφ : HasDerivAt φ ((w / z).im) s)
    (hz : z = (ρ s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I))
    (hw : w = (ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I)) :
    HasDerivAt φ (ν s / ρ s * Real.sin (ϑ s - φ s)) s := by
  have hρne : ((ρ s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρs.ne'
  have hkey : (w / z).im = ν s / ρ s * Real.sin (ϑ s - φ s) := by
    have hdiv : w / z = ((ν s / ρ s : ℝ) : ℂ)
        * Complex.exp (((ϑ s - φ s : ℝ) : ℂ) * Complex.I) := by
      rw [hw, hz, Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.ofReal_div]
      field_simp
    have him : (Complex.exp (((ϑ s - φ s : ℝ) : ℂ) * Complex.I)).im = Real.sin (ϑ s - φ s) :=
      exp_ofReal_mul_I_im _
    rw [hdiv, Complex.mul_im, him]
    simp
  rwa [hkey] at hφ

/-- Paper `lem:viewing-angle`, `eq:viewing-angle-bound`, at a point `β` off the arc.  Nothing
about `arg(γ - β)` is hypothesized: `polarAngle` **is** the branch, built by `logLift`.  What
is asked of the arc is regularity — differentiability on an open set carrying the parameter
interval, a continuous tangent in polar form, `γ ≠ β`, and finitely many critical points of
the viewing angle.  For the paper's principal arc that package is `thm:FT-geometry` together
with `lem:principal-endpoint-regularity`, which the manuscript itself takes from
`Forgacs2017RationalDenominator` rather than proving. -/
theorem viewing_angle_bound_arc
    {γ dγ : ℝ → ℂ} {β : ℂ} {ν ϑ : ℝ → ℝ} {U : Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β)
    (hϑc : ContinuousOn ϑ (Icc a b)) (hνpos : ∀ s ∈ Icc a b, 0 ≤ ν s)
    (htan : ∀ s ∈ Icc a b, dγ s = (ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I))
    (S : Finset ℝ) (hSsub : ∀ x ∈ S, x ∈ Icc a b)
    (hS : ∀ x ∈ Ioo a b, ∀ m : ℤ,
        ϑ x - polarAngle γ dγ β a x = (m : ℝ) * π → x ∈ S) :
    eVariationOn (polarAngle γ dγ β a) (Icc a b)
      ≤ eVariationOn ϑ (Icc a b) + ENNReal.ofReal π := by
  refine viewing_angle_bound_of_finite hab hϑc
    (c := fun s => ν s / polarModulus γ dγ β a s)
    (fun s hs => div_nonneg (hνpos s hs) (polarModulus_pos γ dγ β a s).le)
    (fun s hs => ?_) S hSsub hS
  exact hasDerivAt_viewingAngle_of_polar (ν := ν) (ϑ := ϑ)
    (polarModulus_pos γ dγ β a s)
    (hasDerivAt_polarAngle hU hsub hd hc hne hs)
    (polar_decomposition hab hU hsub hd hc hne hs)
    (htan s hs)


/-! ### `eq:viewing-angle-bound` with the vantage point **on** the arc

`lem:viewing-angle` sums the variation over the components of `[s_0,s_1] ∖ γ⁻¹({β})`.  For an
injective arc the fiber over `β` is a single parameter `m`, so there are at most two
components, `[a, m)` and `(m, b]`, and a branch of the argument is chosen on each.  The
folded phase runs to `π` at `m` from the left and to `0` from the right, so by
`viewing_angle_bound_of_finite_phaseFold` each component's variation is already below the
tangent-angle variation over it, and the two together are below `𝒦_γ`.  The manuscript's
`𝒦_γ + π` follows; the `π` is what the point-off-the-arc case needs and this case does not. -/

/-! ### Splitting the variation over subintervals

`Shields.eVariationOn_sum_le` sums ordered disjoint pieces below the whole -- the gaps are
exactly what the deleted parameters of `eq:linear-phase-variation` create -- and
`Shields.eVariationOn_Ico_le`, `Shields.eVariationOn_Ioc_le` reach a half-open interval
from the closed ones inside it. -/

export Shields (eVariationOn_Ico_le eVariationOn_Ioc_le eVariationOn_sum_le)

private theorem le_of_forall_ofReal_add {X Y : ENNReal} {t : ℝ} (ht : 0 < t)
    (h : ∀ ε : ℝ, 0 < ε → ε < t → X ≤ Y + ENNReal.ofReal ε) : X ≤ Y := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hpos : (0 : ℝ) < min (ε : ℝ) (t / 2) := lt_min (by exact_mod_cast hε) (by linarith)
  have hlt : min (ε : ℝ) (t / 2) < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine le_trans (h _ hpos hlt) ?_
  gcongr
  calc ENNReal.ofReal (min (ε : ℝ) (t / 2))
      ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal (min_le_left _ _)
    _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal

/-- Cancel a finite summand from both sides. -/
private theorem le_of_add_le_add_ofReal {X Y : ENNReal} {t : ℝ}
    (h : X + ENNReal.ofReal t ≤ Y + ENNReal.ofReal t) : X ≤ Y :=
  (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h

section OnArc

variable {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {U : Set ℝ} {a b m : ℝ}

/-- **`eq:viewing-angle-bound` on the component that ends at the meeting parameter.**  The arc
runs from `a` to `m`, meeting `β` only at `m`; the branch based at `a` is defined throughout
`[a, m)` and its variation there is already below the tangent-angle variation, with no `π`
added.  The folded phase runs to `π` at `m`, which is what pays for the excess. -/
theorem viewing_angle_bound_to_meet
    (ham : a ≤ m) (hmb : m ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hβ : γ m = β) (hne : ∀ s ∈ Icc a b, s ≠ m → γ s ≠ β)
    (S : Finset ℝ)
    (hS : ∀ x ∈ Ioo a m, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (k : ℝ) * π → x ∈ S) :
    eVariationOn (polarAngle γ dγ β a) (Set.Ico a m)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc a m) := by
  classical
  set ϑ := polarAngle dγ d2γ 0 a with hϑdef
  set φ := polarAngle γ dγ β a with hφdef
  have hab : a ≤ b := ham.trans hmb
  have hc : ContinuousOn dγ U := fun x hx => (hd2 x hx).continuousAt.continuousWithinAt
  -- the tangent angle, on the whole interval
  have htan : ∀ s ∈ Icc a b, dγ s = (polarModulus dγ d2γ 0 a s : ℂ)
      * Complex.exp ((ϑ s : ℂ) * Complex.I) := by
    intro s hs
    have := polar_decomposition hab hU hsub hd2 hc2 hreg hs
    rwa [sub_zero] at this
  -- the closed-subinterval bound, sharp
  have hpiece : ∀ c ∈ Set.Ico a m,
      eVariationOn φ (Icc a c) + ENNReal.ofReal (phaseFold (ϑ c - φ c))
        ≤ eVariationOn ϑ (Icc a m) + ENNReal.ofReal (phaseFold (ϑ a - φ a)) := by
    intro c hc'
    have hac : a ≤ c := hc'.1
    have hcb : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl (hc'.2.le.trans hmb)
    have hnec : ∀ s ∈ Icc a c, γ s ≠ β := fun s hs =>
      hne s (hcb hs) (ne_of_lt (lt_of_le_of_lt hs.2 hc'.2))
    have hmain := viewing_angle_bound_of_finite_phaseFold (ϑ := ϑ) (φ := φ)
      (c := fun s => polarModulus dγ d2γ 0 a s / polarModulus γ dγ β a s) hac
      (fun x hx =>
        ((hasDerivAt_polarAngle hU hsub hd2 hc2 hreg (hcb hx)).continuousAt).continuousWithinAt)
      (fun s _ => div_nonneg (polarModulus_pos dγ d2γ 0 a s).le
        (polarModulus_pos γ dγ β a s).le)
      (fun s hs => hasDerivAt_viewingAngle_of_polar
        (ν := fun s => polarModulus dγ d2γ 0 a s) (ϑ := ϑ)
        (polarModulus_pos γ dγ β a s)
        (hasDerivAt_polarAngle hU (hcb.trans hsub) hd hc hnec hs)
        (polar_decomposition hac hU (hcb.trans hsub) hd hc hnec hs)
        (htan s (hcb hs)))
      (S.filter (fun x => x ∈ Icc a c)) (fun x hx => (Finset.mem_filter.1 hx).2)
      (fun x hx k hk => Finset.mem_filter.2
        ⟨hS x ⟨hx.1, lt_of_lt_of_le hx.2 hc'.2.le⟩ k hk, ⟨hx.1.le, hx.2.le⟩⟩)
    exact le_trans hmain
      (by gcongr; exact eVariationOn.mono _ (Icc_subset_Icc le_rfl hc'.2.le))
  rcases eq_or_lt_of_le ham with rfl | hamlt
  · simp
  -- the folded phase runs to `π` at `m`
  have hmU : m ∈ Icc a b := ⟨ham, hmb⟩
  have hlim : Filter.Tendsto (fun s => phaseFold (ϑ s - φ s))
      (nhdsWithin m (Set.Iio m)) (nhds π) := by
    refine tendsto_phaseFold_left (T := Set.Ioo a m)
      (Ioo_mem_nhdsLT hamlt)
      (fun s _ => polarModulus_pos γ dγ β a s)
      (fun s _ => polarModulus_pos dγ d2γ 0 a s) (fun s hs => ?_) (fun s hs => ?_)
      hβ (hd m (hsub hmU)) (hreg m hmU)
      ((hd2 m (hsub hmU)).continuousAt)
    · have hsub' : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl (hs.2.le.trans hmb)
      exact polar_decomposition hs.1.le hU (hsub'.trans hsub) hd hc
        (fun x hx => hne x (hsub' hx) (ne_of_lt (lt_of_le_of_lt hx.2 hs.2)))
        ⟨hs.1.le, le_rfl⟩
    · exact htan s ⟨hs.1.le, hs.2.le.trans hmb⟩
  refine le_of_forall_ofReal_add Real.pi_pos fun ε hε hεπ => ?_
  refine eVariationOn_Ico_le fun c₀ hc₀ => ?_
  -- pick a parameter near `m` where the folded phase is within `ε` of `π`
  obtain ⟨c, hcmem, hcval⟩ : ∃ c ∈ Set.Ico c₀ m, π - ε < phaseFold (ϑ c - φ c) := by
    have hnb : (Set.Ico c₀ m ∩ {x | π - ε < phaseFold (ϑ x - φ x)}).Nonempty := by
      have h1 : {x | π - ε < phaseFold (ϑ x - φ x)} ∈ nhdsWithin m (Set.Iio m) :=
        hlim (Ioi_mem_nhds (by linarith))
      have h2 : Set.Ico c₀ m ∈ nhdsWithin m (Set.Iio m) :=
        Filter.mem_of_superset (Ioo_mem_nhdsLT hc₀.2) (fun x hx => ⟨hx.1.le, hx.2⟩)
      exact Filter.nonempty_of_mem (Filter.inter_mem h2 h1)
    obtain ⟨c, hc1, hc2⟩ := hnb
    exact ⟨c, hc1, hc2⟩
  have hcIco : c ∈ Set.Ico a m := ⟨hc₀.1.trans hcmem.1, hcmem.2⟩
  have hmono : eVariationOn φ (Icc a c₀) ≤ eVariationOn φ (Icc a c) :=
    eVariationOn.mono _ (Icc_subset_Icc le_rfl hcmem.1)
  have hstep : eVariationOn φ (Icc a c₀) + ENNReal.ofReal (π - ε)
      ≤ (eVariationOn ϑ (Icc a m) + ENNReal.ofReal ε) + ENNReal.ofReal (π - ε) := by
    calc eVariationOn φ (Icc a c₀) + ENNReal.ofReal (π - ε)
        ≤ eVariationOn φ (Icc a c) + ENNReal.ofReal (phaseFold (ϑ c - φ c)) := by
          gcongr
      _ ≤ eVariationOn ϑ (Icc a m) + ENNReal.ofReal (phaseFold (ϑ a - φ a)) := hpiece c hcIco
      _ ≤ eVariationOn ϑ (Icc a m) + ENNReal.ofReal π := by
          gcongr; exact phaseFold_le_pi _
      _ = (eVariationOn ϑ (Icc a m) + ENNReal.ofReal ε) + ENNReal.ofReal (π - ε) := by
          rw [add_assoc, ← ENNReal.ofReal_add hε.le (by linarith)]
          congr 2
          ring
  exact le_of_add_le_add_ofReal hstep

/-- **`eq:viewing-angle-bound` on the component that starts at the meeting parameter.**  The
mirror of `viewing_angle_bound_to_meet`: the branch is based at `b`, and the folded phase runs
to `0` at `m` from the right, so this component costs nothing above the tangent-angle
variation either. -/
theorem viewing_angle_bound_from_meet
    (ham : a ≤ m) (hmb : m ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hβ : γ m = β) (hne : ∀ s ∈ Icc a b, s ≠ m → γ s ≠ β)
    (S : Finset ℝ)
    (hS : ∀ x ∈ Ioo m b, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (k : ℝ) * π → x ∈ S) :
    eVariationOn (polarAngle γ dγ β b) (Set.Ioc m b)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc m b) := by
  classical
  set ϑ := polarAngle dγ d2γ 0 a with hϑdef
  set φ := polarAngle γ dγ β b with hφdef
  have hab : a ≤ b := ham.trans hmb
  have hc : ContinuousOn dγ U := fun x hx => (hd2 x hx).continuousAt.continuousWithinAt
  have htan : ∀ s ∈ Icc a b, dγ s = (polarModulus dγ d2γ 0 a s : ℂ)
      * Complex.exp ((ϑ s : ℂ) * Complex.I) := by
    intro s hs
    have := polar_decomposition hab hU hsub hd2 hc2 hreg hs
    rwa [sub_zero] at this
  have hsubd : ∀ d, m < d → Icc d b ⊆ Icc a b := fun d hdm =>
    Icc_subset_Icc (ham.trans hdm.le) le_rfl
  have hned : ∀ d, m < d → ∀ s ∈ Icc d b, γ s ≠ β := fun d hdm s hs =>
    hne s (hsubd d hdm hs) (ne_of_gt (lt_of_lt_of_le hdm hs.1))
  have hpolar : ∀ d, m < d → ∀ s ∈ Icc d b, γ s - β
      = (polarModulus γ dγ β b s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I) := by
    intro d hdm s hs
    exact polar_decomposition_base (hs.1.trans hs.2) hU ((hsubd d hdm).trans hsub) hd hc
      (hned d hdm) ⟨hs.1.trans hs.2, le_rfl⟩ hs
  have hpiece : ∀ d ∈ Set.Ioc m b, eVariationOn φ (Icc d b)
      ≤ eVariationOn ϑ (Icc m b) + ENNReal.ofReal (phaseFold (ϑ d - φ d)) := by
    intro d hd'
    have hdb : d ≤ b := hd'.2
    have hsd := hsubd d hd'.1
    have hmain := viewing_angle_bound_of_finite_phaseFold (ϑ := ϑ) (φ := φ)
      (c := fun s => polarModulus dγ d2γ 0 a s / polarModulus γ dγ β b s) hdb
      (fun x hx =>
        ((hasDerivAt_polarAngle hU hsub hd2 hc2 hreg (hsd hx)).continuousAt).continuousWithinAt)
      (fun s _ => div_nonneg (polarModulus_pos dγ d2γ 0 a s).le
        (polarModulus_pos γ dγ β b s).le)
      (fun s hs => hasDerivAt_viewingAngle_of_polar
        (ν := fun s => polarModulus dγ d2γ 0 a s) (ϑ := ϑ)
        (polarModulus_pos γ dγ β b s)
        (hasDerivAt_polarAngle_base hU (hsd.trans hsub) hd hc (hned d hd'.1)
          ⟨hdb, le_rfl⟩ hs)
        (hpolar d hd'.1 s hs) (htan s (hsd hs)))
      (S.filter (fun x => x ∈ Icc d b)) (fun x hx => (Finset.mem_filter.1 hx).2)
      (fun x hx k hk => Finset.mem_filter.2
        ⟨hS x ⟨lt_of_lt_of_le hd'.1 hx.1.le, hx.2⟩ k hk, ⟨hx.1.le, hx.2.le⟩⟩)
    refine le_trans (le_trans (le_add_right le_rfl) hmain) ?_
    gcongr
    exact eVariationOn.mono _ (Icc_subset_Icc hd'.1.le le_rfl)
  rcases eq_or_lt_of_le hmb with rfl | hmblt
  · simp
  have hmU : m ∈ Icc a b := ⟨ham, hmb⟩
  have hlim : Filter.Tendsto (fun s => phaseFold (ϑ s - φ s))
      (nhdsWithin m (Set.Ioi m)) (nhds 0) :=
    tendsto_phaseFold_right (T := Set.Ioo m b) (Ioo_mem_nhdsGT hmblt)
      (fun s _ => polarModulus_pos γ dγ β b s)
      (fun s _ => polarModulus_pos dγ d2γ 0 a s)
      (fun s hs => hpolar s hs.1 s ⟨le_rfl, hs.2.le⟩)
      (fun s hs => htan s ⟨ham.trans hs.1.le, hs.2.le⟩)
      hβ (hd m (hsub hmU)) (hreg m hmU) ((hd2 m (hsub hmU)).continuousAt)
  refine le_of_forall_ofReal_add Real.pi_pos fun ε hε _ => ?_
  refine eVariationOn_Ioc_le fun d₀ hd₀ => ?_
  obtain ⟨d, hdmem, hdval⟩ : ∃ d ∈ Set.Ioc m d₀, phaseFold (ϑ d - φ d) < ε := by
    have h1 : {x | phaseFold (ϑ x - φ x) < ε} ∈ nhdsWithin m (Set.Ioi m) :=
      hlim (Iio_mem_nhds hε)
    have h2 : Set.Ioc m d₀ ∈ nhdsWithin m (Set.Ioi m) :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT hd₀.1) (fun x hx => ⟨hx.1, hx.2.le⟩)
    obtain ⟨d, hd1, hd2'⟩ := Filter.nonempty_of_mem (Filter.inter_mem h2 h1)
    exact ⟨d, hd1, hd2'⟩
  calc eVariationOn φ (Icc d₀ b)
      ≤ eVariationOn φ (Icc d b) := eVariationOn.mono _ (Icc_subset_Icc hdmem.2 le_rfl)
    _ ≤ eVariationOn ϑ (Icc m b) + ENNReal.ofReal (phaseFold (ϑ d - φ d)) :=
        hpiece d ⟨hdmem.1, hdmem.2.trans hd₀.2⟩
    _ ≤ eVariationOn ϑ (Icc m b) + ENNReal.ofReal ε := by gcongr

/-- **`lem:viewing-angle`, `eq:viewing-angle-bound`, with `β` on the arc.**  For an injective
arc the fiber over `β` is one parameter `m`, so `[a,b] ∖ γ⁻¹({β})` has the two components
`[a, m)` and `(m, b]`; a continuous branch is used on each, and the summed variation is at
most `𝒦_γ`.

The manuscript's `𝒦_γ + π` is `viewing_angle_bound_on_arc_le_pi`.  The `π` is what the
point-off-the-arc case genuinely needs — `viewing_angle_bound_line` shows it cannot be lowered
there — and this case does not need it: the jump of `π` that the off-arc branch traverses
continuously has become the gap between the two components, which the sum does not see.

**Containment.**  No hypothesis mentions `eVariationOn` at all: what is asked is the arc's
regularity, that `γ` meets `β` at `m` and nowhere else, and that each viewing angle has
finitely many critical points.  `hS₁` and `hS₂` do name the very `polarAngle` functions the
conclusion takes the variation of, but only to locate the parameters where two of them differ
by a multiple of `π`.  Both sides of the conclusion are produced here, by
`viewing_angle_bound_to_meet` and `viewing_angle_bound_from_meet` over the split at `m`. -/
theorem viewing_angle_bound_on_arc
    (ham : a ≤ m) (hmb : m ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hβ : γ m = β) (hne : ∀ s ∈ Icc a b, s ≠ m → γ s ≠ β)
    (S₁ S₂ : Finset ℝ)
    (hS₁ : ∀ x ∈ Ioo a m, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (k : ℝ) * π → x ∈ S₁)
    (hS₂ : ∀ x ∈ Ioo m b, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (k : ℝ) * π → x ∈ S₂) :
    eVariationOn (polarAngle γ dγ β a) (Set.Ico a m)
        + eVariationOn (polarAngle γ dγ β b) (Set.Ioc m b)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) := by
  have hsplit := eVariationOn.Icc_add_Icc (polarAngle dγ d2γ 0 a) (s := Set.univ)
    ham hmb (Set.mem_univ m)
  simp only [Set.univ_inter] at hsplit
  rw [← hsplit]
  exact add_le_add
    (viewing_angle_bound_to_meet ham hmb hU hsub hd hd2 hc2 hreg hβ hne S₁ hS₁)
    (viewing_angle_bound_from_meet ham hmb hU hsub hd hd2 hc2 hreg hβ hne S₂ hS₂)

/-- `eq:viewing-angle-bound` as the manuscript states it, with `β` on the arc: the summed
variation over the components of `[a,b] ∖ γ⁻¹({β})` is at most `𝒦_γ + π`. -/
theorem viewing_angle_bound_on_arc_le_pi
    (ham : a ≤ m) (hmb : m ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hβ : γ m = β) (hne : ∀ s ∈ Icc a b, s ≠ m → γ s ≠ β)
    (S₁ S₂ : Finset ℝ)
    (hS₁ : ∀ x ∈ Ioo a m, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (k : ℝ) * π → x ∈ S₁)
    (hS₂ : ∀ x ∈ Ioo m b, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (k : ℝ) * π → x ∈ S₂) :
    eVariationOn (polarAngle γ dγ β a) (Set.Ico a m)
        + eVariationOn (polarAngle γ dγ β b) (Set.Ioc m b)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) + ENNReal.ofReal π :=
  le_trans (viewing_angle_bound_on_arc ham hmb hU hsub hd hd2 hc2 hreg hβ hne S₁ S₂ hS₁ hS₂)
    (le_add_right le_rfl)

/-! ### `eq:viewing-angle-bound` summed over the components of a finer partition

`cor:linear-phase-variation` deletes the parameters where *any* zero of `B` is met, so for a
fixed zero `β` the pieces it sums over refine the components of `[a,b] ∖ γ⁻¹({β})`.  With
`eVariationOn_sum_le` that refinement costs nothing: each piece sits inside one component, the
pieces are ordered, and their variations add up below the component's. -/

/-- **The summed bound at a `β` the arc meets.**  Each piece lies on one side of the meeting
parameter and carries that side's branch; the pieces left of `m` sum below the variation over
`[a, m)` and those right of it below the variation over `(m, b]`, so the whole family stays at
`𝒦_γ` — and a fortiori at the manuscript's `𝒦_γ + π`. -/
theorem viewing_angle_bound_components_of_meet
    (ham : a ≤ m) (hmb : m ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hβ : γ m = β) (hne : ∀ s ∈ Icc a b, s ≠ m → γ s ≠ β)
    (S₁ S₂ : Finset ℝ)
    (hS₁ : ∀ x ∈ Ioo a m, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (k : ℝ) * π → x ∈ S₁)
    (hS₂ : ∀ x ∈ Ioo m b, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (k : ℝ) * π → x ∈ S₂)
    {J : ℕ → Set ℝ} {ψ : ℕ → ℝ → ℝ} (t : Finset ℕ)
    (hside : ∀ i ∈ t, (J i ⊆ Set.Ico a m ∧ ψ i = polarAngle γ dγ β a)
      ∨ (J i ⊆ Set.Ioc m b ∧ ψ i = polarAngle γ dγ β b))
    (hord : ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x ≤ y) :
    ∑ i ∈ t, eVariationOn (ψ i) (J i)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) := by
  classical
  set P : ℕ → Prop := fun i => J i ⊆ Set.Ico a m ∧ ψ i = polarAngle γ dγ β a with hP
  set L : Finset ℕ := t.filter P with hL
  set R : Finset ℕ := t.filter (fun i => ¬ P i) with hR
  have hleft : ∑ i ∈ L, eVariationOn (ψ i) (J i)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc a m) := by
    have heq : ∑ i ∈ L, eVariationOn (ψ i) (J i)
        = ∑ i ∈ L, eVariationOn (polarAngle γ dγ β a) (J i) :=
      Finset.sum_congr rfl fun i hi => by rw [((Finset.mem_filter.1 hi).2).2]
    rw [heq]
    refine le_trans (eVariationOn_sum_le L (Set.Ico a m)
      (fun i hi => ((Finset.mem_filter.1 hi).2).1)
      (fun i hi j hj hij => hord i (Finset.mem_filter.1 hi).1 j
        (Finset.mem_filter.1 hj).1 hij)) ?_
    exact viewing_angle_bound_to_meet ham hmb hU hsub hd hd2 hc2 hreg hβ hne S₁ hS₁
  have hright : ∑ i ∈ R, eVariationOn (ψ i) (J i)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc m b) := by
    have hRside : ∀ i ∈ R, J i ⊆ Set.Ioc m b ∧ ψ i = polarAngle γ dγ β b := by
      intro i hi
      rcases hside i (Finset.mem_filter.1 hi).1 with h | h
      · exact absurd h (Finset.mem_filter.1 hi).2
      · exact h
    have heq : ∑ i ∈ R, eVariationOn (ψ i) (J i)
        = ∑ i ∈ R, eVariationOn (polarAngle γ dγ β b) (J i) :=
      Finset.sum_congr rfl fun i hi => by rw [(hRside i hi).2]
    rw [heq]
    refine le_trans (eVariationOn_sum_le R (Set.Ioc m b) (fun i hi => (hRside i hi).1)
      (fun i hi j hj hij => hord i (Finset.mem_filter.1 hi).1 j
        (Finset.mem_filter.1 hj).1 hij)) ?_
    exact viewing_angle_bound_from_meet ham hmb hU hsub hd hd2 hc2 hreg hβ hne S₂ hS₂
  have hsplit := eVariationOn.Icc_add_Icc (polarAngle dγ d2γ 0 a) (s := Set.univ)
    ham hmb (Set.mem_univ m)
  simp only [Set.univ_inter] at hsplit
  rw [← hsplit, ← Finset.sum_filter_add_sum_filter_not t P]
  exact add_le_add hleft hright

end OnArc


/-! ### `lem:viewing-angle` for a regular arc

The tangent angle is the same lift applied to `γ'`, so a regular arc needs no polar data at
all: `ϑ = polarAngle γ' γ'' 0 a` and `ν = polarModulus γ' γ'' 0 a` are built, and what is left
is `γ ∈ C²` on an open set carrying the interval, `γ' ≠ 0`, `γ ≠ β`, and the finite critical
set.  The manuscript's arc is real-analytic, which is stronger than `C²`. -/

/-- Paper `lem:viewing-angle`, `eq:viewing-angle-bound`, for a regular arc: neither the
viewing angle nor the tangent angle is hypothesized — both are branches built by `logLift`. -/
theorem viewing_angle_bound_regular
    {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {U : Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β)
    (S : Finset ℝ) (hSsub : ∀ x ∈ S, x ∈ Icc a b)
    (hS : ∀ x ∈ Ioo a b, ∀ m : ℤ,
        polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (m : ℝ) * π → x ∈ S) :
    eVariationOn (polarAngle γ dγ β a) (Icc a b)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) + ENNReal.ofReal π := by
  have hc : ContinuousOn dγ U := fun x hx => (hd2 x hx).continuousAt.continuousWithinAt
  have hreg' : ∀ s ∈ Icc a b, dγ s ≠ (0 : ℂ) := hreg
  refine viewing_angle_bound_arc hab hU hsub hd hc hne
    (fun x hx => (hasDerivAt_polarAngle hU hsub hd2 hc2 hreg' hx).continuousAt.continuousWithinAt)
    (fun s _ => (polarModulus_pos dγ d2γ 0 a s).le)
    (fun s hs => ?_) S hSsub hS
  have := polar_decomposition hab hU hsub hd2 hc2 hreg' hs
  rwa [sub_zero] at this


section ComponentsOffArc

variable {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {U : Set ℝ} {a b : ℝ}

/-- The summed bound at a `β` the arc misses: whatever ordered family of subintervals is
summed over, the total stays at `𝒦_γ + π`. -/
theorem viewing_angle_bound_components_off_arc
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β)
    (S : Finset ℝ) (hSsub : ∀ x ∈ S, x ∈ Icc a b)
    (hS : ∀ x ∈ Ioo a b, ∀ k : ℤ,
      polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (k : ℝ) * π → x ∈ S)
    {J : ℕ → Set ℝ} (t : Finset ℕ) (hJ : ∀ i ∈ t, J i ⊆ Icc a b)
    (hord : ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x ≤ y) :
    ∑ i ∈ t, eVariationOn (polarAngle γ dγ β a) (J i)
      ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) + ENNReal.ofReal π :=
  le_trans (eVariationOn_sum_le t _ hJ hord)
    (viewing_angle_bound_regular hab hU hsub hd hd2 hc2 hreg hne S hSsub hS)

end ComponentsOffArc

end ForgacsTran
