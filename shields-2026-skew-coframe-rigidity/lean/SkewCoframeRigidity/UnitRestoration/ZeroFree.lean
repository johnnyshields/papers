/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.Coprimality

/-!
# Finite injectivity at a zero-free diagram

Formalizes the zero-free half of `sc:finite-injectivity` in
`shields-2026-skew-coframe-rigidity.tex`: with `U = H - ϑ` (so `U₀ = 0`) and
`P⁺ = [Ug]_{<M}`, a polynomial `δ` with `δ₀ = 0` and `[Uδ]_i = 0` at every original proper row
is determined by `𝒯_{g,δ}(z^a U)`, `0 ≤ a ≤ M - 2`.  The free numerator coordinates stay
independent over the remaining atlas coordinates after the substitution `P ↦ P - ϑ g`, so
every available coefficient of `P⁺` is nonzero and `g` is coprime to `z^a P⁺_{<M-a}`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence SkewCoframeRigidity Polynomial PowerSeries

variable {n : ℕ}

/-- The letter series with the coherent unit removed: `U = H - ϑ`. -/
noncomputable def unitFreeSeries : PowerSeries CohField :=
  PowerSeries.mk fun k => if k = 0 then 0 else cohLetters k

theorem letterSeries_eq_add : letterSeries = unitFreeSeries + PowerSeries.C (cohLetters 0) := by
  ext k
  simp only [letterSeries, seriesOf, unitFreeSeries, map_add, PowerSeries.coeff_mk,
    PowerSeries.coeff_C]
  by_cases hk : k = 0 <;> simp [hk]

theorem coeff_unitFree_mul (D : BetaDiagram (n + 1)) (k : ℕ) :
    PowerSeries.coeff k (unitFreeSeries * (coframe D : PowerSeries CohField)) =
      PowerSeries.coeff k (letterSeries * (coframe D : PowerSeries CohField)) -
        cohLetters 0 * (coframe D).coeff k := by
  rw [letterSeries_eq_add, add_mul, map_add, PowerSeries.coeff_C_mul, Polynomial.coeff_coe]
  ring

/-- The atlas setup around a free numerator coordinate: a subfield `L` containing every
coframe coefficient, `ϑ`, and every other numerator coefficient, over which the free
coordinate is transcendental. -/
theorem free_setup {D : BetaDiagram (n + 1)} (hD : D.Connected) {i : ℕ} (h0 : 0 < i)
    (hi : i < span D) (hr : i ∉ rowSet D) :
    ∃ L : IntermediateField ℚ CohField, (∀ k, (coframe D).coeff k ∈ L) ∧ cohLetters 0 ∈ L ∧
      (∀ k, k ≠ i → k < span D → (numerator D).coeff k ∈ L) ∧
      ¬ IsAlgebraic L ((numerator D).coeff i) := by
  classical
  let o1 : AtlasIdx D := some (Sum.inr ⟨i, h0, hi, hr⟩)
  set T := atlasCoords D '' {o | o ≠ o1} with hT
  refine ⟨IntermediateField.adjoin ℚ T, ?_, ?_, ?_, ?_⟩
  · intro k
    unfold coframe coframeOf
    rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
    refine add_mem (by rw [Polynomial.coeff_one]; split_ifs <;> simp) (sum_mem fun j _ => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs
    · rw [mul_one]
      exact IntermediateField.subset_adjoin ℚ T ⟨some (Sum.inl j),
        by intro h; exact absurd (Option.some.inj h) Sum.inl_ne_inr, rfl⟩
    · simp
  · exact IntermediateField.subset_adjoin ℚ T ⟨none,
      by intro h; exact absurd h.symm (by simp only [o1]; exact Option.some_ne_none _), rfl⟩
  · intro k hk hkM
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [numerator_coeff_zero]
      exact IntermediateField.subset_adjoin ℚ T ⟨none,
        by intro h; exact absurd h.symm (by simp only [o1]; exact Option.some_ne_none _), rfl⟩
    · by_cases hkr : k ∈ rowSet D
      · rw [(numerator_coeff_eq_zero_iff hD hk0 hkM).mpr hkr]; exact zero_mem _
      · exact IntermediateField.subset_adjoin ℚ T ⟨some (Sum.inr ⟨k, hk0, hkM, hkr⟩), by
          intro h
          exact hk (congrArg Subtype.val (Sum.inr.inj (Option.some.inj h))), rfl⟩
  · intro halg
    have hind := atlasCoords_algebraicIndependent hD
    have htr := hind.transcendental_adjoin (s := {o | o ≠ o1}) (i := o1) (by simp)
    exact htr ((IntermediateField.isAlgebraic_adjoin_iff (F := ℚ) (E := CohField) (s := T)
      (S := CohField) (x := (numerator D).coeff i)).mp halg)

/-- Every available coefficient of `P⁺` is nonzero. -/
theorem coeff_unitFree_ne_zero {D : BetaDiagram (n + 1)} (hD : D.Connected) {i : ℕ}
    (h0 : 0 < i) (hi : i < span D) (hr : i ∉ rowSet D) :
    PowerSeries.coeff i (unitFreeSeries * (coframe D : PowerSeries CohField)) ≠ 0 := by
  obtain ⟨L, hg, hϑ, -, hx⟩ := free_setup hD h0 hi hr
  rw [coeff_unitFree_mul, ← numerator_coeff_eq_series D hi]
  intro h
  apply hx
  have hmem : (numerator D).coeff i ∈ L := by
    have : (numerator D).coeff i = cohLetters 0 * (coframe D).coeff i := sub_eq_zero.mp h
    rw [this]; exact mul_mem hϑ (hg i)
  exact ⟨Polynomial.X - Polynomial.C (⟨_, hmem⟩ : L), Polynomial.X_sub_C_ne_zero _, by
    simp⟩

theorem rowPos_cast_aux (D : BetaDiagram (n + 1)) (i : Fin n) :
    (rowPos D i : ℤ) = D.row i.succ - D.col (Fin.last n) := by
  have h1 := D.col_strictAnti.antitone (Fin.le_last i.succ)
  have h2 := D.row_nonempty i.succ
  unfold rowPos
  omega

/-- A zero-free connected diagram has no proper row at one. -/
theorem one_not_mem_rowSet {D : BetaDiagram (n + 1)} (hD : D.Connected)
    (hzf : ∀ i j, D.row i ≠ D.col j) : 1 ∉ rowSet D := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
  have hi' : (rowPos D i : ℤ) = 1 := by exact_mod_cast hi
  have h1 : D.row i.succ = D.col (Fin.last n) + 1 := by
    have := rowPos_cast_aux D i
    omega
  have hlt := D.col_strictAnti (show i.castSucc < Fin.last n from Fin.castSucc_lt_last i)
  have hle := hD.2 i.castSucc (by simp)
  refine hzf i.succ i.castSucc ?_
  have : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = i.succ := rfl
  simp only [Fin.val_castSucc] at hle
  rw [this] at hle
  omega

/-- Coprimality of the coframe with `z^a P⁺_{<M-a}`. -/
theorem coframe_isCoprime_unitFree {D : BetaDiagram (n + 1)} (hD : D.Connected)
    (hzf : ∀ i j, D.row i ≠ D.col j) (a : ℕ) (ha : a + 2 ≤ span D) :
    IsCoprime (coframe D)
      (trunc (span D - a) (unitFreeSeries * (coframe D : PowerSeries CohField))) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : coframe D = 1 := by simp [coframe, coframeOf]
    rw [this]; exact isCoprime_one_left
  refine (Irreducible.coprime_iff_not_dvd (coframe_irreducible hD hn)).mpr fun hdvd => ?_
  set Q := trunc (span D - a) (unitFreeSeries * (coframe D : PowerSeries CohField)) with hQ
  have hdeg := coframe_natDegree_pos hD hn
  have h1r := one_not_mem_rowSet hD hzf
  obtain ⟨L, hg, hϑ, hP, hx⟩ := free_setup hD (Nat.one_pos) (show 1 < span D by omega) h1r
  set x := (numerator D).coeff 1 with hx'
  have hQL : ∀ k, (Q - Polynomial.C x * Polynomial.X ^ 1).coeff k ∈ L := by
    intro k
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
    by_cases hk : k < span D - a
    · have hQk : Q.coeff k = (numerator D).coeff k - cohLetters 0 * (coframe D).coeff k := by
        rw [hQ, coeff_trunc, if_pos hk, coeff_unitFree_mul,
          ← numerator_coeff_eq_series D (by omega)]
      rw [hQk]
      by_cases hk1 : k = 1
      · subst hk1; simp only [if_true]
        have : (numerator D).coeff 1 - cohLetters 0 * (coframe D).coeff 1 - x =
            -(cohLetters 0 * (coframe D).coeff 1) := by rw [hx']; ring
        rw [this]; exact neg_mem (mul_mem hϑ (hg 1))
      · rw [if_neg hk1, sub_zero]
        exact sub_mem (hP k hk1 (by omega)) (mul_mem hϑ (hg k))
    · rw [show Q.coeff k = 0 by rw [hQ, coeff_trunc, if_neg hk]]
      by_cases hk1 : k = 1
      · subst hk1; omega
      · simp [hk1]
  exact hx (isAlgebraic_of_dvd_add L (coframe D) (Q - Polynomial.C x * Polynomial.X ^ 1) x 1
    (coframe_coeff_zero D) hdeg hg hQL (by rwa [sub_add_cancel]))

/-- **Finite injectivity at a zero-free diagram** (`sc:finite-injectivity`, second statement). -/
theorem finite_injectivity_unitFree {D : BetaDiagram (n + 1)} (hD : D.Connected)
    (hzf : ∀ i j, D.row i ≠ D.col j) (a : ℕ) (ha : a + 2 ≤ span D) (δ : CohField[X])
    (hδ0 : δ.coeff 0 = 0)
    (hrows : ∀ i ∈ rowSet D,
      PowerSeries.coeff i (unitFreeSeries * (δ : PowerSeries CohField)) = 0)
    (hT : clippedOp (span D) (coframe D) δ (PowerSeries.X ^ a * unitFreeSeries) = 0) : δ = 0 := by
  refine eq_zero_of_clippedOp_eq_zero (span D) a (coframe D) δ unitFreeSeries
    (coframe_coeff_zero D) hδ0 ?_ ⟨1, by omega, ?_⟩ ?_ hT
  · rw [trunc_shift_eq _ _ (by omega)]
    refine IsCoprime.mul_right ?_ (coframe_isCoprime_unitFree hD hzf a ha)
    refine IsCoprime.pow_right ?_
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := coframe D)
    rw [coframe_coeff_zero D, map_one] at hq
    exact ⟨1, -q, by linear_combination hq⟩
  · exact coeff_unitFree_ne_zero hD Nat.one_pos (by omega) (one_not_mem_rowSet hD hzf)
  · intro i hi hia hP
    refine hrows i ?_
    by_contra hir
    exact coeff_unitFree_ne_zero hD hi (by omega) hir hP

end SkewCoframeRigidity.Coframe
