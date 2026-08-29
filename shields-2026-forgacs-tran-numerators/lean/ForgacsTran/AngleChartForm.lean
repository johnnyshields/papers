/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.BranchCurvature
import ForgacsTran.FTBranchProp1

/-!
# The angle partials over the chord

`FTBranchTauDeriv` and `BranchCurvature` write the six partials of `θ_k` the way
the differentiation produced them: a numerator in `\sin θ_k` and `\cos θ_k` over
a power of `\sin θ`.  Every one of those forms is `0/0` at `θ = 0`, which is what
stops a limit at the lower endpoint being read off the formula — and the reading
is not merely inconvenient, since `∂θ_k/∂τ` genuinely diverges there for a zero
the branch runs into.

The partials themselves are not all singular.  Writing

  `D = a^2 - 2aτ\cos θ + τ^2`

for the squared chord from `a` to the branch point — `chordSq_nonneg`'s
expression — each of the six is a polynomial in `(a, τ, \sin θ, \cos θ)` over a
power of `D`, and `D` vanishes only where the branch point meets `a`.  So at a
zero the branch circle does not reach, all six extend continuously to `θ = 0`,
and the singular behaviour is confined to the zeros it does reach.

The cancellation is not an accident of the algebra.  `\sin θ_k` and `\cos θ_k`
are `τ\sin θ/\sqrt D` and `(τ\cos θ - a)/\sqrt D`, and every partial has **even**
total degree in that pair, so each `\sqrt D` meets another.  That is what
`exists_ftAngle_chart` packages: one witness `g` with `g^2 = D`, in which each of
the six identities clears its denominators and then closes on the two relations
in play — `g^2 = D`, and the Pythagorean identity in `θ`.

## Main statements

* `ftChordSq`, `ftChordSq_pos` — the squared chord, off zero away from the zero.
* `exists_ftAngle_chart` — `\sin θ_k` and `\cos θ_k` over a square root of `D`.
* `ftAngleDerivTau_chart`, `ftAngleDerivAngle_chart` — the two first partials,
  `-a\sin θ/D` and `τ(τ - a\cos θ)/D`.
* `ftAngleDeriv2Tau_chart`, `ftAngleDeriv2AngleTau_chart`,
  `ftAngleDeriv2TauAngle_chart`, `ftAngleDeriv2Angle_chart` — the four second
  partials.  The two mixed ones have the **same** chart form, which is
  `EndpointCofactorBound.ftAngleDeriv2AngleTau_eq_ftAngleDeriv2TauAngle` read off
  the chart rather than proved.

## Implementation notes

Sorry-free.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `sec:dominance`.
* `../../scripts/check_endpoint_tau2_limit.py`, block `X1`.

## Tags

branch angle, partial derivative, chord, endpoint regularity
-/

namespace ForgacsTran

open Real Set

/-- The squared chord from the zero `a` to the branch point `τe^{iψ}`.  The same
expression `chordSq_nonneg` and `ftChord_eq_sqrt` carry, named because the chart
forms below all have a power of it as their denominator. -/
noncomputable def ftChordSq (a τ ψ : ℝ) : ℝ := a ^ 2 - 2 * a * τ * Real.cos ψ + τ ^ 2

/-- The chord is off zero away from the zero itself: on `(0, π)` the angular
displacement alone keeps it positive, whatever `τ` does. -/
theorem ftChordSq_pos {a τ ψ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hψ : ψ ∈ Ioo 0 π) :
    0 < ftChordSq a τ ψ := by
  have hs : 0 < Real.sin ψ := sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hpy := Real.sin_sq_add_cos_sq ψ
  have hlt : Real.cos ψ < 1 := by nlinarith [sq_nonneg (Real.cos ψ - 1)]
  have := mul_pos ha hτ
  rw [ftChordSq]
  nlinarith [sq_nonneg (a - τ)]

/-- **The branch angle's sine and cosine over the chord.**  `\sin θ_k = τ\sin
θ/\sqrt D` and `\cos θ_k = (τ\cos θ - a)/\sqrt D` — the imaginary and real parts
of the chord `τe^{iθ} - a`, normalized.  The witness is handed out rather than
the square root itself, so that the identities below are rational in one atom. -/
theorem exists_ftAngle_chart {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    ∃ g : ℝ, 0 < g ∧ g ^ 2 = ftChordSq a τ s
      ∧ Real.sin (ftAngle a τ s) = τ * Real.sin s / g
      ∧ Real.cos (ftAngle a τ s) = (τ * Real.cos s - a) / g := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hD : 0 < ftChordSq a τ s := ftChordSq_pos ha hτ hs
  set g : ℝ := Real.sqrt (ftChordSq a τ s) with hgdef
  have hg0 : 0 < g := Real.sqrt_pos.2 hD
  have hg2 : g ^ 2 = ftChordSq a τ s := Real.sq_sqrt hD.le
  have hmem := ftAngle_mem_Ioo ha hτ hs
  have hq : 0 < Real.sin (ftAngle a τ s - s) :=
    sin_pos_of_pos_of_lt_pi (by linarith [hmem.1]) (by linarith [hmem.2, hs.1])
  -- `a\sin θ_k = τ\sin(θ_k - θ)`, the defining relation
  have h1 : a * Real.sin (ftAngle a τ s) = τ * Real.sin (ftAngle a τ s - s) :=
    ftAngle_spec hτ.ne' hs
  -- `a\sin θ = \sqrt D\,\sin(θ_k - θ)`, the chord in the same triangle
  have h2 : a * Real.sin s = g * Real.sin (ftAngle a τ s - s) := by
    have hc := ftChord_eq_sqrt ha hτ hs
    simp only [ftChord] at hc
    rw [div_eq_iff hq.ne'] at hc
    simpa [hgdef, ftChordSq] using hc
  have hsinθk : Real.sin (ftAngle a τ s) = τ * Real.sin s / g := by
    rw [eq_div_iff hg0.ne']
    refine mul_left_cancel₀ ha.ne' ?_
    calc a * (Real.sin (ftAngle a τ s) * g)
        = (a * Real.sin (ftAngle a τ s)) * g := by ring
      _ = (τ * Real.sin (ftAngle a τ s - s)) * g := by rw [h1]
      _ = τ * (g * Real.sin (ftAngle a τ s - s)) := by ring
      _ = τ * (a * Real.sin s) := by rw [← h2]
      _ = a * (τ * Real.sin s) := by ring
  refine ⟨g, hg0, hg2, hsinθk, ?_⟩
  have hcc : Real.cos (ftAngle a τ s)
      = (Real.cos s / Real.sin s - a / (τ * Real.sin s)) * Real.sin (ftAngle a τ s) :=
    cos_ftArccot _
  rw [hcc, hsinθk]
  field_simp

/-! ### The six partials -/

/-- `∂θ_k/∂τ = -a\sin θ/D`.  Divergent as `θ ↓ 0` exactly when `D` does not
survive — that is, at a zero the branch point runs into. -/
theorem ftAngleDerivTau_chart {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    -(Real.sin (ftAngle a τ s) ^ 2 * a / (τ ^ 2 * Real.sin s))
      = -(a * Real.sin s) / ftChordSq a τ s := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  obtain ⟨g, hg0, hg2, hS, hC⟩ := exists_ftAngle_chart ha hτ hs
  rw [← hg2, hS]
  field_simp

/-- `∂θ_k/∂θ = τ(τ - a\cos θ)/D`. -/
theorem ftAngleDerivAngle_chart {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s - s) / Real.sin s
      = τ * (τ - a * Real.cos s) / ftChordSq a τ s := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  obtain ⟨g, hg0, hg2, hS, hC⟩ := exists_ftAngle_chart ha hτ hs
  rw [Real.cos_sub, ← hg2, hS, hC]
  field_simp
  linear_combination τ * Real.sin_sq_add_cos_sq s

/-- `∂²θ_k/∂τ² = 2a\sin θ(τ - a\cos θ)/D²`. -/
theorem ftAngleDeriv2Tau_chart {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    ftAngleDeriv2Tau a τ s
      = 2 * a * Real.sin s * (τ - a * Real.cos s) / ftChordSq a τ s ^ 2 := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  obtain ⟨g, hg0, hg2, hS, hC⟩ := exists_ftAngle_chart ha hτ hs
  have hg2' : g ^ 2 = a ^ 2 - 2 * a * τ * Real.cos s + τ ^ 2 := by simpa [ftChordSq] using hg2
  rw [ftAngleDeriv2Tau, ← hg2, hS, hC]
  field_simp
  linear_combination hg2'

/-- `∂²θ_k/∂τ∂θ = -a(\cos θ·D - 2aτ\sin²θ)/D²`. -/
theorem ftAngleDeriv2AngleTau_chart {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hs : s ∈ Ioo 0 π) :
    ftAngleDeriv2AngleTau a τ s
      = -(a * (Real.cos s * ftChordSq a τ s - 2 * a * τ * Real.sin s ^ 2))
        / ftChordSq a τ s ^ 2 := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  obtain ⟨g, hg0, hg2, hS, hC⟩ := exists_ftAngle_chart ha hτ hs
  have hg2' : g ^ 2 = a ^ 2 - 2 * a * τ * Real.cos s + τ ^ 2 := by simpa [ftChordSq] using hg2
  rw [ftAngleDeriv2AngleTau,
    show (2 : ℝ) * ftAngle a τ s - s = ftAngle a τ s + (ftAngle a τ s - s) by ring,
    Real.cos_add, Real.cos_sub, Real.sin_sub, ← hg2, hS, hC]
  field_simp
  linear_combination (-(Real.cos s * τ ^ 2)) * Real.sin_sq_add_cos_sq s + Real.cos s * hg2'

/-- `∂²θ_k/∂θ∂τ`, the mixed partial the other way, has the **same** chart form. -/
theorem ftAngleDeriv2TauAngle_chart {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hs : s ∈ Ioo 0 π) :
    ftAngleDeriv2TauAngle a τ s
      = -(a * (Real.cos s * ftChordSq a τ s - 2 * a * τ * Real.sin s ^ 2))
        / ftChordSq a τ s ^ 2 := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  obtain ⟨g, hg0, hg2, hS, hC⟩ := exists_ftAngle_chart ha hτ hs
  have hg2' : g ^ 2 = a ^ 2 - 2 * a * τ * Real.cos s + τ ^ 2 := by simpa [ftChordSq] using hg2
  rw [ftAngleDeriv2TauAngle, Real.cos_sub, ← hg2, hS, hC]
  field_simp
  linear_combination (-(2 * Real.cos s * τ ^ 2)) * Real.sin_sq_add_cos_sq s
    + (2 * Real.cos s) * hg2'

/-- `∂²θ_k/∂θ² = aτ\sin θ(D - 2τ(τ - a\cos θ))/D²`. -/
theorem ftAngleDeriv2Angle_chart {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hs : s ∈ Ioo 0 π) :
    ftAngleDeriv2Angle a τ s
      = a * τ * Real.sin s * (ftChordSq a τ s - 2 * τ * (τ - a * Real.cos s))
        / ftChordSq a τ s ^ 2 := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  obtain ⟨g, hg0, hg2, hS, hC⟩ := exists_ftAngle_chart ha hτ hs
  have hg2' : g ^ 2 = a ^ 2 - 2 * a * τ * Real.cos s + τ ^ 2 := by simpa [ftChordSq] using hg2
  rw [ftAngleDeriv2Angle, Real.cos_sub, Real.sin_sub, ← hg2, hS, hC]
  field_simp
  linear_combination
    (τ * a ^ 2 * Real.cos s - 3 * a * τ ^ 2 * Real.cos s ^ 2
      - 2 * a * τ ^ 2 * Real.sin s ^ 2 + τ ^ 3 * Real.cos s ^ 3 - τ * Real.cos s * g ^ 2
      + τ ^ 3 * Real.cos s * Real.sin s ^ 2 + τ ^ 3 * Real.cos s)
      * Real.sin_sq_add_cos_sq s
    + (Real.cos s * (a * Real.cos s - τ)) * hg2'

end ForgacsTran
