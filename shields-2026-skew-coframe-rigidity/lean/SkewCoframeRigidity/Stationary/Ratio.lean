/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.TopData
import SkewCoframeRigidity.Stationary.ComponentRemainderThm
import SkewCoframeRigidity.Stationary.Transcendence

/-!
# The pole ratio of a component

Formalizes the ratio `[H^p g]_L / k` of `shields-2026-skew-coframe-rigidity.tex`,
`sc:component-ratio`, in its three shapes: `ϑ^{p-1}` for a true unit, `p ϑ^{p-1}` for a cell, and
`p ϑ^{p-1} + α/k` with a genuine pole in `H_L` for a component of span `L ≥ 2`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial

/-- The component data of `top_data`, with the ratio read off. -/
structure CompData (p : ℕ) where
  L : ℕ
  g : CohField[X]
  k : CohField
  hk : k ≠ 0
  g0 : g.coeff 0 = 1
  hkdef : PowerSeries.coeff L (PowerSeries.mk cohLetters * (g : PowerSeries CohField)) = k
  shape : (L = 0 ∧ g = 1 ∧ k = cohLetters 0) ∨
    (1 ≤ L ∧ ∃ (n' : ℕ) (E : BetaDiagram (n' + 1)), E.Connected ∧ span E = L ∧
      coframe E = g ∧ topQuotient E = k)

variable {p : ℕ}

/-- The ratio. -/
noncomputable def CompData.ratio (c : CompData p) : CohField :=
  PowerSeries.coeff c.L (letterSeries ^ p * (c.g : PowerSeries CohField)) / c.k

theorem ratio_unit (c : CompData p) (hL : c.L = 0) (hp : 1 ≤ p) :
    c.ratio = cohLetters 0 ^ (p - 1) := by
  rcases c.shape with ⟨_, hg, hk⟩ | ⟨h1, _⟩
  · unfold CompData.ratio
    rw [hL, hg, hk]
    simp only [Polynomial.coe_one, mul_one]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    have : PowerSeries.constantCoeff letterSeries = cohLetters 0 := by
      simp [letterSeries, seriesOf, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [this]
    have h0 : cohLetters 0 ≠ 0 := cohLetters_zero_ne_zero
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    field_simp
    simp only [Nat.add_sub_cancel]; ring
  · omega


theorem span_one_eq {n' : ℕ} (E : BetaDiagram (n' + 1)) (h : span E = 1) :
    n' = 0 := by
  by_contra hn
  have hn' : 0 < n' := Nat.pos_of_ne_zero hn
  have := colPos_pos E ⟨0, hn'⟩
  have := colPos_lt_span E ⟨0, hn'⟩
  omega

theorem coeff_one_pow {R : Type*} [CommRing R] (φ : PowerSeries R) (q : ℕ) :
    PowerSeries.coeff 1 (φ ^ q) =
      q * PowerSeries.constantCoeff φ ^ (q - 1) * PowerSeries.coeff 1 φ := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons,
      Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_singleton]
    simp only [Function.Embedding.coe_prodMap, Prod.map_apply, Function.Embedding.coeFn_mk,
      Nat.succ_eq_add_one, zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    rw [ih]
    rcases q with _ | q
    · simp
    · simp only [Nat.add_sub_cancel, id_eq]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; push_cast
      have e : PowerSeries.coeff (id 0) φ = PowerSeries.coeff 0 φ := rfl
      rw [e]; ring

theorem ratio_cell (c : CompData p) (hL : c.L = 1) (hp : 1 ≤ p) :
    c.ratio = p * cohLetters 0 ^ (p - 1) := by
  rcases c.shape with ⟨h0, _⟩ | ⟨_, n', E, hE, hs, hg, hk⟩
  · omega
  · have hn : n' = 0 := span_one_eq E (hs.trans hL)
    subst hn
    have hg1 : c.g = 1 := by
      rw [← hg]; simp [coframe, coframeOf]
    have hk1 : c.k = cohLetters 1 := by
      have := c.hkdef
      rw [hL, hg1] at this
      simpa [PowerSeries.coeff_mk] using this.symm
    unfold CompData.ratio
    rw [hL, hg1, hk1]
    simp only [Polynomial.coe_one, mul_one]
    rw [coeff_one_pow]
    have : PowerSeries.constantCoeff letterSeries = cohLetters 0 := by
      simp [letterSeries, seriesOf, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h1 : PowerSeries.coeff 1 letterSeries = cohLetters 1 := by simp [letterSeries, seriesOf]
    have hne : cohLetters 1 ≠ 0 := by
      unfold cohLetters
      rw [map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)]
      exact MvPolynomial.X_ne_zero 1
    rw [this, h1]
    field_simp

theorem ratio_big (c : CompData p) (hL : 2 ≤ c.L) (hp : 2 ≤ p) :
    ∃ k₀ α : CohField, k₀ ∈ lowerField c.L ∧ α ∈ lowerField c.L ∧ α ≠ 0 ∧
      c.k = cohLetters c.L + k₀ ∧ c.ratio = p * cohLetters 0 ^ (p - 1) + α / c.k := by
  rcases c.shape with ⟨h0, _⟩ | ⟨_, n', E, hE, hs, hg, hk⟩
  · omega
  · obtain ⟨k₀, α, hk₀, hα, hα0, hq, hc⟩ := component_remainder hE (hs ▸ hL) hp
    rw [hs] at hk₀ hα hq hc
    refine ⟨k₀, α, hk₀, hα, hα0, by rw [← hk, hq], ?_⟩
    unfold CompData.ratio
    have : PowerSeries.coeff c.L (letterSeries ^ p * (c.g : PowerSeries CohField)) =
        p * cohLetters 0 ^ (p - 1) * c.k + α := by
      rw [← hg, ← hk]; exact hc
    rw [this]
    field_simp [c.hk]

theorem ratio_mem_lower (c : CompData p) (hp : 2 ≤ p) : c.ratio ∈ lowerField (c.L + 1) := by
  have hθ : ∀ L', 0 < L' → cohLetters 0 ∈ lowerField L' := fun L' h => letter_mem_lowerField h
  have hnat : ∀ (q : ℕ), (q : CohField) ∈ lowerField (c.L + 1) := fun q =>
    (lowerField (c.L + 1)).natCast_mem q
  have hθ' : cohLetters 0 ∈ lowerField (c.L + 1) := hθ _ (by omega)
  rcases Nat.lt_or_ge c.L 2 with hl | hl
  · have hcases : c.L = 0 ∨ c.L = 1 := by omega
    rcases hcases with hL | hL
    · rw [ratio_unit c hL (by omega)]
      exact pow_mem hθ' _
    · rw [ratio_cell c hL (by omega)]
      exact (lowerField _).mul_mem (hnat _) (pow_mem hθ' _)
  · obtain ⟨k₀, α, hk₀, hα, hα0, hk, hr⟩ := ratio_big c hl hp
    have hmono := lowerField_mono (show c.L ≤ c.L + 1 by omega)
    have hxL : cohLetters c.L ∈ lowerField (c.L + 1) := letter_mem_lowerField (by omega)
    rw [hr]
    refine (lowerField _).add_mem ((lowerField _).mul_mem (hnat _)
      (pow_mem hθ' _)) ((lowerField _).div_mem (hmono hα) ?_)
    rw [hk]; exact (lowerField _).add_mem hxL (hmono hk₀)

theorem unit_gk (c : CompData p) (hL : c.L = 0) : c.g = 1 ∧ c.k = cohLetters 0 := by
  rcases c.shape with ⟨_, hg, hk⟩ | ⟨h1, _⟩
  · exact ⟨hg, hk⟩
  · omega

theorem cell_gk (c : CompData p) (hL : c.L = 1) : c.g = 1 ∧ c.k = cohLetters 1 := by
  rcases c.shape with ⟨h0, _⟩ | ⟨_, n', E, hE, hs, hg, hk⟩
  · omega
  · have hn : n' = 0 := span_one_eq E (hs.trans hL)
    subst hn
    have hg1 : c.g = 1 := by
      rw [← hg]; simp [coframe, coframeOf]
    refine ⟨hg1, ?_⟩
    have := c.hkdef
    rw [hL, hg1] at this
    simpa [PowerSeries.coeff_mk] using this.symm

theorem not_ratio_eq_of_lt (c d : CompData p) (hp : 2 ≤ p) (hlt : d.L < c.L) :
    c.ratio ≠ d.ratio := by
  intro h
  have hθ : cohLetters 0 ≠ 0 := cohLetters_zero_ne_zero
  rcases Nat.lt_or_ge c.L 2 with hl | hl
  · have hc1 : c.L = 1 := by omega
    have hd0 : d.L = 0 := by omega
    rw [ratio_cell c hc1 (by omega), ratio_unit d hd0 (by omega)] at h
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    simp only [show q + 2 - 1 = q + 1 by omega, pow_succ] at h
    have : ((q + 1 : ℕ) : CohField) * (cohLetters 0 ^ q * cohLetters 0) = 0 := by
      push_cast at h ⊢; linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (by exact_mod_cast h1 : (q + 1 : ℕ) = 0) (by omega)
    · exact mul_ne_zero (pow_ne_zero _ hθ) hθ h1
  · obtain ⟨k₀, α, hk₀, hα, hα0, hk, hr⟩ := ratio_big c hl hp
    have hmem := ratio_mem_lower d hp
    have hmono := lowerField_mono (show d.L + 1 ≤ c.L by omega)
    have hF : (cohLetters 0) ∈ lowerField c.L := letter_mem_lowerField (by omega)
    have hnat : ((p : ℕ) : CohField) ∈ lowerField c.L := (lowerField c.L).natCast_mem p
    have hr' : α / c.k ∈ lowerField c.L := by
      have : α / c.k = d.ratio - p * cohLetters 0 ^ (p - 1) := by linear_combination (-1 : CohField) * hr + h
      rw [this]
      exact (lowerField _).sub_mem (hmono hmem) ((lowerField _).mul_mem hnat (pow_mem hF _))
    have hkne := c.hk
    have h2 : (α / c.k) * cohLetters c.L + (α / c.k * k₀ - α) = 0 := by
      have e : α = α / c.k * c.k := by field_simp
      linear_combination (-1 : CohField) * e + (-(α / c.k)) * hk
    have := eq_zero_of_mul_add_eq_zero (F := (lowerField c.L).toSubfield) (letter_notMem_lowerField c.L)
      hr' ((lowerField _).sub_mem ((lowerField _).mul_mem hr' hk₀) hα) h2
    rcases this with ⟨h3, h4⟩
    have : α = 0 := by
      have e : α = α / c.k * c.k := by field_simp
      rw [e, h3, zero_mul]
    exact hα0 this

theorem ratio_compare (c d : CompData p) (hp : 2 ≤ p) (h : c.ratio = d.ratio) :
    c.L = d.L ∧ c.k = d.k := by
  have hLeq : c.L = d.L := by
    rcases lt_trichotomy c.L d.L with hlt | heq | hgt
    · exact absurd h.symm (not_ratio_eq_of_lt d c hp hlt)
    · exact heq
    · exact absurd h (not_ratio_eq_of_lt c d hp hgt)
  refine ⟨hLeq, ?_⟩
  rcases Nat.lt_or_ge c.L 2 with hl | hl
  · have : c.L = 0 ∨ c.L = 1 := by omega
    rcases this with h0 | h1
    · rw [(unit_gk c h0).2, (unit_gk d (hLeq ▸ h0)).2]
    · rw [(cell_gk c h1).2, (cell_gk d (hLeq ▸ h1)).2]
  · obtain ⟨k₀, α, hk₀, hα, hα0, hk, hr⟩ := ratio_big c hl hp
    obtain ⟨k₀', α', hk₀', hα', hα0', hk', hr'⟩ := ratio_big d (hLeq ▸ hl) hp
    rw [← hLeq] at hk₀' hα' hk'
    rw [hr, hr'] at h
    have hh : α / c.k = α' / d.k := add_left_cancel h
    have hkc := c.hk; have hkd := d.hk
    have e1 : α * d.k = α' * c.k := by field_simp at hh; linear_combination hh
    rw [hk, hk'] at e1
    have e2 : (α - α') * cohLetters c.L + (α * k₀' - α' * k₀) = 0 := by linear_combination e1
    have F := (lowerField c.L).toSubfield
    obtain ⟨h5, h6⟩ := eq_zero_of_mul_add_eq_zero (F := (lowerField c.L).toSubfield)
      (letter_notMem_lowerField c.L) ((lowerField _).sub_mem hα hα')
      ((lowerField _).sub_mem ((lowerField _).mul_mem hα hk₀') ((lowerField _).mul_mem hα' hk₀)) e2
    have hαα : α = α' := sub_eq_zero.1 h5
    rw [← hαα] at h6
    have : k₀' = k₀ := by
      have : α * (k₀' - k₀) = 0 := by linear_combination h6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hα0
      · exact sub_eq_zero.1 h
    rw [hk, hk', this]

end SkewCoframeRigidity.Coframe
