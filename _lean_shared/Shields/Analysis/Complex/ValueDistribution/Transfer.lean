/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Removing an exceptional set of finite measure

The Second Main Theorem of Nevanlinna theory, and the Lemma on the Logarithmic Derivative it
rests on, hold for all large radii outside a set of finite Lebesgue measure, that is, along the
filter `volume.cofinite ⊓ atTop`.  For a monotone function the exceptional set can be removed:
an interval longer than the measure of the exceptional set must meet its complement, and
monotonicity carries the estimate from the good radius back.

## Main results

* `Shields.exists_good_radius` — a property holding along `volume.cofinite ⊓ atTop` holds at some
  point of every sufficiently late interval of a fixed length.
* `Shields.isBigO_rpow_of_monotoneOn` — a monotone function bounded by `C * r ^ p` along
  `volume.cofinite ⊓ atTop` is `O(r ^ p)` along `atTop`.

## Tags

Nevanlinna theory, exceptional set, Borel growth lemma
-/

open Filter MeasureTheory Set

namespace Shields

/--
A property that holds for all large radii outside a set of finite Lebesgue measure holds at some
radius in every interval `[r, r + M]` with `r` large, for one fixed length `M`.
-/
theorem exists_good_radius {P : ℝ → Prop} (h : ∀ᶠ r in volume.cofinite ⊓ atTop, P r) :
    ∃ M R₀ : ℝ, 0 ≤ M ∧ ∀ r, R₀ ≤ r → ∃ r', r ≤ r' ∧ r' ≤ r + M ∧ P r' := by
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_inf_iff.1 h
  obtain ⟨R₀, hR₀⟩ := Filter.mem_atTop_sets.1 ht
  have hfin : volume sᶜ ≠ ⊤ := (Measure.mem_cofinite.1 hs).ne
  refine ⟨(volume sᶜ).toReal + 1, R₀, by positivity, fun r hr ↦ ?_⟩
  rcases (Set.Icc r (r + ((volume sᶜ).toReal + 1)) ∩ s).eq_empty_or_nonempty with hempty | hne
  · exfalso
    have h₃ : Set.Icc r (r + ((volume sᶜ).toReal + 1)) ⊆ sᶜ := fun x hx hxs ↦
      Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hx, hxs⟩
    have h₄ := measure_mono (μ := volume) h₃
    rw [Real.volume_Icc, show r + ((volume sᶜ).toReal + 1) - r = (volume sᶜ).toReal + 1 by ring,
      ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_one] at h₄
    exact absurd h₄ (not_le.2 (ENNReal.lt_add_right hfin one_ne_zero))
  · obtain ⟨r', ⟨hr'₁, hr'₂⟩, hr's⟩ := hne
    refine ⟨r', hr'₁, hr'₂, ?_⟩
    have h₉ : r' ∈ s ∩ t := ⟨hr's, hR₀ r' (hr.trans hr'₁)⟩
    rw [← hst] at h₉
    exact h₉

/--
A nonnegative function that is monotone on `[x₀, ∞)` and bounded by `C * r ^ p` for all large
radii outside a set of finite Lebesgue measure is `O(r ^ p)` along `atTop`.
-/
theorem isBigO_rpow_of_monotoneOn {u : ℝ → ℝ} {x₀ C p : ℝ} (hp : 0 ≤ p)
    (h₀ : ∀ᶠ r in atTop, 0 ≤ u r) (h₁ : MonotoneOn u (Set.Ici x₀))
    (h₂ : ∀ᶠ r in volume.cofinite ⊓ atTop, u r ≤ C * r ^ p) :
    u =O[atTop] fun r ↦ r ^ p := by
  obtain ⟨M, R₀, hM, hgood⟩ := exists_good_radius h₂
  rw [Asymptotics.isBigO_iff]
  refine ⟨max C 0 * (M + 1) ^ p, ?_⟩
  filter_upwards [h₀, eventually_ge_atTop x₀, eventually_ge_atTop R₀, eventually_ge_atTop (1 : ℝ)]
    with r hur hrx₀ hrR₀ hr₁
  obtain ⟨r', hrr', hr'M, hr'good⟩ := hgood r hrR₀
  have hr'₀ : (0 : ℝ) ≤ r' := le_trans (by linarith) hrr'
  -- Monotonicity carries the bound from the good radius `r'` back to `r`.
  have h₃ : u r ≤ u r' := h₁ (Set.mem_Ici.2 hrx₀) (Set.mem_Ici.2 (hrx₀.trans hrr')) hrr'
  have h₄ : u r' ≤ max C 0 * r' ^ p :=
    hr'good.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hr'₀ p))
  -- The good radius is at most `(M + 1) * r`, so its `p`-th power is controlled.
  have h₅ : r' ^ p ≤ ((M + 1) * r) ^ p := by
    refine Real.rpow_le_rpow hr'₀ ?_ hp
    nlinarith
  have h₆ : ((M + 1) * r) ^ p = (M + 1) ^ p * r ^ p :=
    Real.mul_rpow (by linarith) (by linarith)
  rw [Real.norm_of_nonneg hur, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) p)]
  calc u r ≤ max C 0 * r' ^ p := h₃.trans h₄
    _ ≤ max C 0 * ((M + 1) ^ p * r ^ p) := by
        exact mul_le_mul_of_nonneg_left (by rw [← h₆]; exact h₅) (le_max_right C 0)
    _ = max C 0 * (M + 1) ^ p * r ^ p := by ring

end Shields
