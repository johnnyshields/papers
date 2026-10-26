/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Separation

/-!
# Agreement of the coframes through half the span

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner): if the complete coframes of a board and its
rotation agree through index `⌊M/2⌋`, they agree through the numerators as well, so the low
native supports agree and, by the half-turn, so do the high ones; the board is its own rotation.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem eq_of_coframe_low {V W : BetaDiagram (n + 1)} {c0 : ℤ}
    (hr : ∀ i, W.row i = c0 - V.col i.rev) (hc : ∀ i, W.col i = c0 - V.row i.rev)
    (hV : V.Connected) (hW : W.Connected) (hVn : V.col (Fin.last n) = 0)
    (hWn : W.col (Fin.last n) = 0) (t : ℕ) (ht : span V ≤ 2 * t + 1)
    (hlow : ∀ i ≤ t, (coframe V).coeff i = (coframe W).coeff i) : V = W := by
  have hs : span W = span V := span_rot hr hc hWn
  set M := span V with hM
  have keyC : ∀ {k : ℕ} (F : BetaDiagram (k + 1)), F.Connected → ∀ s,
      s ∈ colSet F ↔ 0 < s ∧ (coframe F).coeff s ≠ 0 := by
    intro k F hF s
    constructor
    · intro hs'
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hs'
      exact ⟨colPos_pos F j, (coframe_coeff_ne_zero_iff hF (colPos_pos F j)).2 hs'⟩
    · rintro ⟨h1, h2⟩
      exact (coframe_coeff_ne_zero_iff hF h1).1 h2
  have keyR : ∀ {k : ℕ} (F : BetaDiagram (k + 1)), F.Connected → ∀ i,
      i ∈ rowSet F ↔ 0 < i ∧ i < span F ∧ (numerator F).coeff i = 0 := by
    intro k F hF i
    constructor
    · intro hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨rowPos_pos F j, rowPos_lt_span F j,
        (numerator_coeff_eq_zero_iff hF (rowPos_pos F j) (rowPos_lt_span F j)).2 hi⟩
    · rintro ⟨h1, h2, h3⟩
      exact (numerator_coeff_eq_zero_iff hF h1 h2).1 h3
  have hnum : ∀ i ≤ t, i < M → (numerator V).coeff i = (numerator W).coeff i := by
    intro i hi hiM
    unfold numerator numeratorOf
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, hs, ite_eq_left hiM, ite_eq_left hiM]
    change PowerSeries.coeff i (letterSeries * (coframe V : PowerSeries CohField)) =
      PowerSeries.coeff i (letterSeries * (coframe W : PowerSeries CohField))
    rw [mul_comm letterSeries, mul_comm letterSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe, hlow x.1 (by omega)]
  have colW : ∀ s, 0 < s → s < M → (s ∈ colSet W ↔ M - s ∈ rowSet V) := by
    intro s hs0 hsM
    constructor
    · intro hsW
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsW
      have := colPos_rot hc hWn j
      have h2 := rowPos_lt_span V j.rev
      have h3 := rowPos_pos V j.rev
      have : M - colPos W j = rowPos V j.rev := by omega
      rw [this]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · intro hs'
      obtain ⟨i0, -, hi0⟩ := Finset.mem_image.mp hs'
      refine Finset.mem_image.mpr ⟨i0.rev, Finset.mem_univ _, ?_⟩
      have := colPos_rot hc hWn i0.rev
      rw [Fin.rev_rev] at this
      omega
  have rowW : ∀ i, 0 < i → i < M → (i ∈ rowSet W ↔ M - i ∈ colSet V) := by
    intro i hi0 hiM
    constructor
    · intro hiW
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hiW
      have := rowPos_rot hr hc hWn j
      have h2 := colPos_lt_span V j.rev
      have h3 := colPos_pos V j.rev
      have : M - rowPos W j = colPos V j.rev := by omega
      rw [this]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · intro hi'
      obtain ⟨j0, -, hj0⟩ := Finset.mem_image.mp hi'
      refine Finset.mem_image.mpr ⟨j0.rev, Finset.mem_univ _, ?_⟩
      have := rowPos_rot hr hc hWn j0.rev
      rw [Fin.rev_rev] at this
      omega
  have colAgree : ∀ s, 0 < s → s ≤ t → (s ∈ colSet V ↔ s ∈ colSet W) := by
    intro s hs0 hst
    rw [keyC V hV, keyC W hW, hlow s hst]
  have rowAgree : ∀ i, 0 < i → i ≤ t → i < M → (i ∈ rowSet V ↔ i ∈ rowSet W) := by
    intro i hi0 hit hiM
    rw [keyR V hV, keyR W hW, hnum i hit hiM, hs]
  have hcol : colSet V = colSet W := by
    ext s
    by_cases hb : 0 < s ∧ s < M
    · obtain ⟨hs0, hsM⟩ := hb
      by_cases hst : s ≤ t
      · exact colAgree s hs0 hst
      · rw [colW s hs0 hsM]
        have h1 := rowAgree (M - s) (by omega) (by omega) (by omega)
        have h2 := rowW (M - s) (by omega) (by omega)
        rw [show M - (M - s) = s by omega] at h2
        rw [h1, h2]
    · constructor
      · intro hsV
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsV
        exact absurd ⟨colPos_pos V j, colPos_lt_span V j⟩ hb
      · intro hsW
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsW
        have := colPos_lt_span W j
        rw [hs] at this
        exact absurd ⟨colPos_pos W j, this⟩ hb
  have hrow : rowSet V = rowSet W := by
    ext i
    by_cases hb : 0 < i ∧ i < M
    · obtain ⟨hi0, hiM⟩ := hb
      by_cases hit : i ≤ t
      · exact rowAgree i hi0 hit hiM
      · rw [rowW i hi0 hiM]
        have h1 := colAgree (M - i) (by omega) (by omega)
        have h2 := colW (M - i) (by omega) (by omega)
        rw [show M - (M - i) = i by omega] at h2
        rw [← h2, ← h1]
    · constructor
      · intro hiV
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hiV
        exact absurd ⟨rowPos_pos V j, rowPos_lt_span V j⟩ hb
      · intro hiW
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hiW
        have := rowPos_lt_span W j
        rw [hs] at this
        exact absurd ⟨rowPos_pos W j, this⟩ hb
  have hr' : V.row = W.row := by
    apply strictAnti_eq_of_range_eq V.row_strictAnti W.row_strictAnti
    ext z
    rw [mem_range_row V hVn, mem_range_row W hWn, hs, hrow]
  have hc' : V.col = W.col := by
    apply strictAnti_eq_of_range_eq V.col_strictAnti W.col_strictAnti
    ext z
    rw [mem_range_col V hVn, mem_range_col W hWn, hcol]
  obtain ⟨r1, c1, _, _, _⟩ := V
  obtain ⟨r2, c2, _, _, _⟩ := W
  simp only at hr' hc'
  subst hr' hc'
  rfl

end SkewCoframeRigidity.Unshifted
