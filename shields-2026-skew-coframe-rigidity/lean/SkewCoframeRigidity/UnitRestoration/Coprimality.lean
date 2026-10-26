/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.FiniteInjectivity
import SkewCoframeRigidity.UnitRestoration.Algebraicity

/-!
# Coprimality of the coframe with a clipped numerator

Formalizes the coprimality step of `sc:finite-injectivity` in
`shields-2026-skew-coframe-rigidity.tex`: for a connected diagram of span `M` and `0 ≤ a < M`
the coframe `g` is coprime to `[Hg]_{<M-a}`.  If the clipped numerator has an available
coefficient of positive index, that coordinate would be algebraic over the remaining atlas
coordinates, contradicting their independence; otherwise it is the unit `ϑ`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence SkewCoframeRigidity Polynomial PowerSeries

variable {n : ℕ}

theorem numerator_coeff_eq_series (D : BetaDiagram (n + 1)) {i : ℕ} (hi : i < span D) :
    (numerator D).coeff i = PowerSeries.coeff i (letterSeries * (coframe D : PowerSeries CohField)) := by
  unfold numerator numeratorOf
  rw [coeff_trunc]; simp only [hi, ite_true]; rfl

theorem coframe_natDegree_pos {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n) :
    0 < (coframe D).natDegree := by
  have hj := colPos_pos_aux D ⟨0, hn⟩
  have : (coframe D).coeff (colPos D ⟨0, hn⟩) ≠ 0 :=
    (coframe_coeff_ne_zero_iff hD hj).mpr (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  exact lt_of_lt_of_le hj (Polynomial.le_natDegree_of_ne_zero this)

theorem coframe_isCoprime_shifted {D : BetaDiagram (n + 1)} (hD : D.Connected) (a : ℕ)
    (ha : a < span D) :
    IsCoprime (coframe D)
      (trunc (span D - a) (letterSeries * (coframe D : PowerSeries CohField))) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : coframe D = 1 := by simp [coframe, coframeOf]
    rw [this]; exact isCoprime_one_left
  refine (Irreducible.coprime_iff_not_dvd (coframe_irreducible hD hn)).mpr fun hdvd => ?_
  set Q := trunc (span D - a) (letterSeries * (coframe D : PowerSeries CohField)) with hQ
  have hdeg := coframe_natDegree_pos hD hn
  have hQc : ∀ k, Q.coeff k = if k < span D - a then (numerator D).coeff k else 0 := by
    intro k
    by_cases hk : k < span D - a
    · simp only [hQ, coeff_trunc, hk, ite_true]
      rw [numerator_coeff_eq_series D (by omega)]
    · simp [hQ, coeff_trunc, hk]
  by_cases hfree : ∃ i, 0 < i ∧ i < span D - a ∧ i ∉ rowSet D
  · obtain ⟨i1, hi0, hi1, hi1r⟩ := hfree
    have hi1M : i1 < span D := by omega
    let o1 : AtlasIdx D := some (Sum.inr ⟨i1, hi0, hi1M, hi1r⟩)
    set x := atlasCoords D o1 with hx
    have hxc : x = (numerator D).coeff i1 := rfl
    set T := atlasCoords D '' {o | o ≠ o1} with hT
    set L := IntermediateField.adjoin ℚ T with hL
    have hcoord : ∀ o, o ≠ o1 → atlasCoords D o ∈ L := fun o ho =>
      IntermediateField.subset_adjoin ℚ T ⟨o, ho, rfl⟩
    have hgL : ∀ k, (coframe D).coeff k ∈ L := by
      intro k
      unfold coframe coframeOf
      rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
      refine add_mem (by rw [Polynomial.coeff_one]; split_ifs <;> simp) (sum_mem fun j _ => ?_)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      split_ifs
      · rw [mul_one]; exact hcoord (some (Sum.inl j)) (by intro h; exact absurd (Option.some.inj h) Sum.inl_ne_inr)
      · simp
    have hQL : ∀ k, (Q - Polynomial.C x * Polynomial.X ^ i1).coeff k ∈ L := by
      intro k
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, hQc]
      by_cases hk1 : k = i1
      · subst hk1; simp [hi1, hxc]
      · rw [if_neg hk1, sub_zero]
        by_cases hk : k < span D - a
        · rw [if_pos hk]
          rcases Nat.eq_zero_or_pos k with rfl | hk0
          · rw [numerator_coeff_zero]
            exact hcoord none (by intro h; exact absurd h.symm (by simp only [o1]; exact Option.some_ne_none _))
          · by_cases hkr : k ∈ rowSet D
            · rw [(numerator_coeff_eq_zero_iff hD hk0 (by omega)).mpr hkr]; exact zero_mem _
            · have := hcoord (some (Sum.inr ⟨k, hk0, by omega, hkr⟩)) (by
                intro h
                exact hk1 (congrArg Subtype.val (Sum.inr.inj (Option.some.inj h))))
              exact this
        · rw [if_neg hk]; exact zero_mem _
    have halg : IsAlgebraic L x := by
      refine isAlgebraic_of_dvd_add L (coframe D) (Q - Polynomial.C x * Polynomial.X ^ i1) x i1
        (coframe_coeff_zero D) hdeg hgL hQL ?_
      rwa [sub_add_cancel]
    have hind := atlasCoords_algebraicIndependent hD
    have htr := hind.transcendental_adjoin (s := {o | o ≠ o1}) (i := o1) (by simp)
    have := (IntermediateField.isAlgebraic_adjoin_iff (F := ℚ) (E := CohField) (s := T)
      (S := CohField) (x := x)).mp halg
    exact htr this
  · push Not at hfree
    have hQC : Q = Polynomial.C (cohLetters 0) := by
      ext k
      rw [hQc, Polynomial.coeff_C]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [ite_true]
        rw [if_pos (by omega), numerator_coeff_zero]
      · rw [if_neg hk0.ne']
        by_cases hk : k < span D - a
        · rw [if_pos hk]
          exact (numerator_coeff_eq_zero_iff hD hk0 (by omega)).mpr (hfree k hk0 hk)
        · rw [if_neg hk]
    rw [hQC] at hdvd
    have hu : IsUnit (Polynomial.C (cohLetters 0) : CohField[X]) :=
      Polynomial.isUnit_C.mpr (Ne.isUnit cohLetters_zero_ne)
    have := Polynomial.natDegree_eq_zero_of_isUnit (isUnit_of_dvd_unit hdvd hu)
    omega

/-- **Finite injectivity** (`sc:finite-injectivity`, first statement), with no coprimality
hypothesis. -/
theorem finite_injectivity {D : BetaDiagram (n + 1)} (hD : D.Connected) (a : ℕ)
    (ha : a < span D) (δ : CohField[X]) (hδ0 : δ.coeff 0 = 0)
    (hrows : ∀ i ∈ rowSet D,
      PowerSeries.coeff i (letterSeries * (δ : PowerSeries CohField)) = 0)
    (hT : clippedOp (span D) (coframe D) δ (PowerSeries.X ^ a * letterSeries) = 0) : δ = 0 :=
  eq_zero_of_clippedOp_letterSeries hD a ha δ hδ0 hrows (coframe_isCoprime_shifted hD a ha) hT

end SkewCoframeRigidity.Coframe
