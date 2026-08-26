/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Vieta separation at the panel-B cancellation point

At `z_* = -Q(t_*)/t_*` the denominator `-8(Q(t) + z_* t)` is the monic cubic
`t^3 - 7t^2 + (14 - 8z_*)t - 8`, whose remaining two zeros satisfy
`u + v = 7 - t_*` and `uv = 8/t_*`.  `vieta_separation` is the corollary's own
contradiction: were `‖u‖ ≤ 3/2` then `‖v‖ > 32/3`, hence `‖u + v‖ > 55/6`, while
`‖7 - t_*‖ < 15/2 < 55/6`.  So both remaining zeros have modulus greater than
`3/2`, `t_*` is the unique minimum-modulus zero, and the local spectral ratio
`eq:local-spectral-ratio` is below `(1/2)/(3/2) = 1/3`.

## Implementation notes

Everything here is stated for an arbitrary zero of modulus below `1/2`, so
nothing depends on locating `t_*`.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`, `cor:panel-B-attractor`,
`eq:local-spectral-ratio`).

## Tags

Vieta formulas, root separation, zero attractor
-/

namespace ForgacsTran

open Complex

/-- Paper `cor:panel-B-attractor` — the denominator `D(t,z) = Q(t) + zt` of the
panel-B data, `Q(t) = (1-t)(1-t/2)(1-t/4)`. -/
noncomputable def panelDen (z t : ℂ) : ℂ :=
  1 - (7 / 4) * t + (7 / 8) * t ^ 2 - (1 / 8) * t ^ 3 + z * t

/-- Paper `cor:panel-B-attractor` — the monic form `-8(Q(t) + zt)`. -/
def panelCubic (z t : ℂ) : ℂ := t ^ 3 - 7 * t ^ 2 + (14 - 8 * z) * t - 8

theorem panelCubic_eq (z t : ℂ) : panelCubic z t = -8 * panelDen z t := by
  simp only [panelCubic, panelDen]; ring

theorem panelDen_eq_zero_iff (z t : ℂ) : panelDen z t = 0 ↔ panelCubic z t = 0 := by
  rw [panelCubic_eq]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have : (-8 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h).resolve_left this

/-- Paper `cor:panel-B-attractor` — `z_* = -Q(t_*)/t_*`. -/
noncomputable def panelZstar (t : ℂ) : ℂ :=
  -(1 - (7 / 4) * t + (7 / 8) * t ^ 2 - (1 / 8) * t ^ 3) / t

theorem panelDen_panelZstar {t : ℂ} (ht : t ≠ 0) : panelDen (panelZstar t) t = 0 := by
  simp only [panelDen, panelZstar]
  field

/-! ### The other two denominator zeros -/

/-- Paper `cor:panel-B-attractor` — dividing the cubic by `(t - t₀)` displays the
other two zeros, with `u + v = 7 - t₀` and `uv = 8/t₀`, which is Vieta for the
monic cubic with constant term `-8`. -/
theorem panelCubic_other_roots {z t₀ : ℂ} (ht0 : t₀ ≠ 0) (hroot : panelCubic z t₀ = 0) :
    ∃ u v : ℂ, (∀ t, panelCubic z t = (t - t₀) * (t - u) * (t - v)) ∧
      u + v = 7 - t₀ ∧ u * v = 8 / t₀ := by
  have ht0c : t₀ * (t₀ ^ 2 - 7 * t₀ + 14 - 8 * z) = 8 := by
    simp only [panelCubic] at hroot
    linear_combination hroot
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = (t₀ - 7) ^ 2 - 4 * (t₀ ^ 2 - 7 * t₀ + 14 - 8 * z) :=
    IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
  refine ⟨(7 - t₀ + s) / 2, (7 - t₀ - s) / 2, ?_, by ring, ?_⟩
  · intro t
    simp only [panelCubic]
    linear_combination ((t - t₀) / 4) * hs + ht0c
  · rw [eq_div_iff ht0]
    linear_combination ht0c - (t₀ / 4) * hs

/-! ### The separation

`vieta_separation` is the contradiction `cor:panel-B-attractor` runs: a remaining
zero of modulus at most `3/2` forces its partner past `32/3`, and then their sum
past `55/6`, which `7 - t_*` cannot reach.
-/

/-- **Paper `cor:panel-B-attractor` — Vieta separation.**  If `u + v = 7 - t` and
`uv = 8/t` with `0 < ‖t‖ < 1/2`, then `‖u‖ > 3/2`. -/
theorem vieta_separation {t u v : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < 1 / 2)
    (hsum : u + v = 7 - t) (hprod : u * v = 8 / t) : 3 / 2 < ‖u‖ := by
  by_contra hcon
  push Not at hcon
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have hun : u ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact div_ne_zero (by norm_num : (8 : ℂ) ≠ 0) ht0 hprod.symm
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hun
  have hnp : ‖u‖ * ‖v‖ * ‖t‖ = 8 := by
    have h := congrArg norm hprod
    rw [norm_mul, norm_div] at h
    have h8 : ‖(8 : ℂ)‖ = 8 := by norm_num
    rw [h8] at h
    field_simp at h
    linarith [h]
  have hv0 : 0 < ‖v‖ := by
    by_contra h
    push Not at h
    have hz : ‖v‖ = 0 := le_antisymm h (norm_nonneg v)
    rw [hz] at hnp
    simp at hnp
  have step1 : ‖u‖ * ‖v‖ * ‖t‖ < ‖u‖ * ‖v‖ * (1 / 2) :=
    mul_lt_mul_of_pos_left ht (mul_pos hu0 hv0)
  have step2 : ‖u‖ * ‖v‖ ≤ 3 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hcon hv0.le
  have hv : 32 / 3 ≤ ‖v‖ := by linarith
  have h1 : ‖v‖ - ‖u‖ ≤ ‖u + v‖ := by
    have h := norm_sub_norm_le v (-u)
    simpa [sub_neg_eq_add, add_comm] using h
  have h2 : ‖u + v‖ ≤ 7 + ‖t‖ := by
    rw [hsum]
    refine (norm_sub_le _ _).trans ?_
    have : ‖(7 : ℂ)‖ = 7 := by norm_num
    rw [this]
  linarith

/-- Paper `eq:local-spectral-ratio` — the local spectral ratio at a zero of
modulus below `1/2` whose competitors all exceed `3/2` is below `1/3`. -/
theorem spectral_ratio_lt_third {t u : ℂ} (ht : ‖t‖ < 1 / 2) (hu : 3 / 2 < ‖u‖) :
    ‖t‖ / ‖u‖ < 1 / 3 := by
  have hu0 : (0 : ℝ) < ‖u‖ := lt_trans (by norm_num) hu
  rw [div_lt_iff₀ hu0]
  nlinarith [norm_nonneg t]

end ForgacsTran
