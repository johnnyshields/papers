/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.WeightedJacobiTrudi

/-!
# The weighted Murnaghan–Nakayama rule for skew Young diagrams

«The algebra map and the weighted operator» of `shields-2026-skew-marked-factor.tex`.
For a skew Young diagram `λ / μ` whose row-move terms in `wDeriv_jtDet` vanish,
`V_r s_{λ/μ} = - Σ_R (-1)^{ht R} y(R) s_{λ/μ \ R}` over the northwest-removable ribbons `R` with
`r` cells, where `y(R)` is the least content of `R`, the content `μ_j - j` of its southwest cell.
Without the weight the same bijection gives the ordinary rule `pDeriv_cellSchur_left_young`.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.MN MvPolynomial

/-- The sum of the row-move terms of `wDeriv_jtDet` for the skew diagram `λ / μ`. -/
def rowMoveSum (lam mu : YoungDiagram) (r : ℕ) : Lambda :=
  let M := lam.colLen 0
  let a : Fin M → ℤ := fun i => (lam.rowLen i : ℤ) - i
  let b : Fin M → ℤ := fun i => (mu.rowLen i : ℤ) - i
  ∑ i : Fin M, ((a i - r : ℤ) : Lambda) * jtDet (Function.update a i (a i - r)) b

/-- The least content of a ribbon removed by a row move is the beta number it raises. -/
theorem minContent_rowMove {mu nu : YoungDiagram} {j i1 m : ℕ} (hm : 0 < m)
    (h : RowMove mu nu j i1 m) : minContent (skewDiagram nu mu) = (mu.rowLen j : ℤ) - j := by
  have hc := h.contents_eq hm
  have hne : (contents (skewDiagram nu mu)).Nonempty := by
    rw [hc]; exact ⟨_, Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩⟩
  have hmem : ∀ k, k ∈ contents (skewDiagram nu mu) ↔
      (mu.rowLen j : ℤ) - j ≤ k ∧ k < (mu.rowLen j : ℤ) - j + m := fun k => by
    rw [hc, Finset.mem_Ico]
  unfold minContent
  simp only [hne, dite_true]
  apply le_antisymm
  · exact Finset.min'_le _ _ ((hmem _).mpr ⟨le_refl _, by omega⟩)
  · exact ((hmem _).mp (Finset.min'_mem _ hne)).1

/-- **Column-move sum as a ribbon sum.**  For every weight `g` of the beta number, the
`g`-weighted sum of the column-move determinants of `λ / μ` is the sum over the
northwest-removable ribbons `R` of `(-1)^{ht R} g(y(R)) s_{λ/μ \ R}`. -/
theorem sum_column_moves_weighted {lam mu : YoungDiagram} (hmu : mu ≤ lam) {m : ℕ}
    (hm : 0 < m) (g : ℤ → Lambda) :
    (let M := lam.colLen 0
     let a : Fin M → ℤ := fun i => (lam.rowLen i : ℤ) - i
     let b : Fin M → ℤ := fun i => (mu.rowLen i : ℤ) - i
     ∑ j : Fin M, g (b j) * jtDet a (Function.update b j (b j + m))) =
      ∑ Y ∈ leftRibbons (skewDiagram lam mu) m,
        (ribbonSign Y : Lambda) * g (minContent Y) * cellSchur (skewDiagram lam mu \ Y) := by
  classical
  set M := lam.colLen 0 with hMdef
  have hM : ∀ i, M ≤ i → lam.rowLen i = 0 := rowLen_eq_zero_of_colLen_le lam
  have hMmu : ∀ i, M ≤ i → mu.rowLen i = 0 := fun i hi => by
    have := rowLen_le_of_le hmu i
    have := hM i hi
    omega
  set a : Fin M → ℤ := fun i => (lam.rowLen i : ℤ) - i with ha
  set b : Fin M → ℤ := fun i => (mu.rowLen i : ℤ) - i with hb
  have haanti : Antitone a := fun i i' h => by
    have := lam.rowLen_anti i i' h
    have : (i : ℕ) ≤ i' := h
    simp only [ha]
    omega
  change ∑ j : Fin M, g (b j) * jtDet a (Function.update b j (b j + m)) = _
  have hmain : ∀ (j : ℕ) (hj : j < M) (nu : YoungDiagram) (i1 : ℕ), RowMove mu nu j i1 m →
      nu ≤ lam → jtDet a (Function.update b ⟨j, hj⟩ (b ⟨j, hj⟩ + m)) =
          (ribbonSign (skewDiagram nu mu) : Lambda) *
          cellSchur (skewDiagram lam mu \ skewDiagram nu mu) := by
    intro j hj nu i1 hRM hl
    have h1 := jtDet_update_eq hj hRM a
    rw [skewDiagram_sdiff (hRM.le hm), cellSchur_skewDiagram_eq_jtDet hl hM]
    unfold ribbonSign ribbonHeight
    rw [hRM.numRows_eq hm]
    simp only [Nat.add_sub_cancel, Int.cast_pow, Int.cast_neg, Int.cast_one]
    exact h1
  have hex : ∀ j : Fin M, jtDet a (Function.update b j (b j + m)) ≠ 0 →
      ∃ nu i1, RowMove mu nu j.val i1 m ∧ nu ≤ lam := by
    intro j hne
    have hinj : ∀ k, k < M → k ≠ j.val →
        (mu.rowLen k : ℤ) - k ≠ mu.rowLen j - j + m := by
      intro k hk hkj heq
      apply hne
      refine jtDet_eq_zero_of_eq a _ (p := ⟨k, hk⟩) (q := j)
        (fun h => hkj (by simpa using congrArg Fin.val h)) ?_
      rw [Function.update_of_ne (fun h => hkj (by simpa using congrArg Fin.val h)),
        Function.update_self]
      simpa [hb] using heq
    obtain ⟨nu, i1, hRM⟩ := exists_rowMove_of_injective hMmu j.isLt hm hinj
    refine ⟨nu, i1, hRM, ?_⟩
    by_contra hnle
    have hk : ∃ k, lam.rowLen k < nu.rowLen k := by
      by_contra hc
      push Not at hc
      exact hnle (le_of_rowLen_le hc)
    obtain ⟨k, hk⟩ := hk
    have hkM : k < M := by
      by_contra h'
      have h1 := hRM.outside k (Or.inr (by have := j.isLt; omega))
      have h2 := hM k (by omega)
      have h3 := hMmu k (by omega)
      omega
    apply hne
    have h1 := jtDet_update_eq j.isLt hRM a
    have h2 : jtDet a (fun i : Fin M => (nu.rowLen i : ℤ) - i) = 0 := by
      refine jtDet_eq_zero_of_lt a _ haanti ?_ ⟨k, hkM⟩ ?_
      · intro i i' h
        have := nu.rowLen_anti i i' h
        have : (i : ℕ) ≤ i' := h
        change (nu.rowLen i' : ℤ) - i' ≤ (nu.rowLen i : ℤ) - i
        omega
      · simp only [ha]
        omega
    rw [h2, mul_zero] at h1
    exact h1
  refine Finset.sum_bij_ne_zero
    (fun j _ hne => skewDiagram (hex j (right_ne_zero_of_mul hne)).choose mu) ?_ ?_ ?_ ?_
  · intro j _ hne
    have hne' := right_ne_zero_of_mul hne
    obtain ⟨i1, hRM, hl⟩ := (hex j hne').choose_spec
    exact mem_leftRibbons_of_rowMove hm hRM hl
  · intro j1 _ h1 j2 _ h2 heq
    have h1' : jtDet a (Function.update b j1 (b j1 + m)) ≠ 0 := fun h => h1 (by rw [h, mul_zero])
    have h2' : jtDet a (Function.update b j2 (b j2 + m)) ≠ 0 := fun h => h2 (by rw [h, mul_zero])
    obtain ⟨i1, hRM1, -⟩ := (hex j1 h1').choose_spec
    obtain ⟨i2, hRM2, -⟩ := (hex j2 h2').choose_spec
    have hnu := skewDiagram_injective (hRM1.le hm) (hRM2.le hm) heq
    rw [← hnu] at hRM2
    exact Fin.ext (hRM1.unique_j hm hRM2)
  · intro Y hY hgY
    obtain ⟨hYX, hcard, hrib, hdown⟩ := mem_leftRibbons.mp hY
    obtain ⟨nu, hmunu, hnul, rfl⟩ := exists_young_of_isDownsetIn hmu hdown
    obtain ⟨j, i1, hRM⟩ := RowMove.of_isRibbon hmunu hrib
    rw [hcard] at hRM
    have hjM : j < M := by
      by_contra h'
      have h1 := hRM.row_lt hm hRM.i1_le (le_refl j)
      have h2 := rowLen_le_of_le hnul j
      have h3 := hM j (by omega)
      omega
    have hfg := hmain j hjM nu i1 hRM hnul
    have hne : g (b ⟨j, hjM⟩) * jtDet a (Function.update b ⟨j, hjM⟩ (b ⟨j, hjM⟩ + m)) ≠ 0 := by
      have hg : g (b ⟨j, hjM⟩) = g (minContent (skewDiagram nu mu)) := by
        rw [minContent_rowMove hm hRM]
      rw [hfg, hg]
      intro h
      apply hgY
      linear_combination h
    refine ⟨⟨j, hjM⟩, Finset.mem_univ _, hne, ?_⟩
    have hne' := right_ne_zero_of_mul hne
    obtain ⟨i1', hRM', -⟩ := (hex ⟨j, hjM⟩ hne').choose_spec
    rw [hRM.unique_nu hm hRM']
  · intro j _ hne
    have hne' := right_ne_zero_of_mul hne
    obtain ⟨i1, hRM, hl⟩ := (hex j hne').choose_spec
    generalize (hex j hne').choose = nu at hRM hl ⊢
    rw [hmain j.val j.isLt nu i1 hRM hl]
    have hb' : g (b j) = g (minContent (skewDiagram nu mu)) := by
      rw [minContent_rowMove hm hRM]
    rw [hb']
    ring

/-- **The weighted Murnaghan–Nakayama rule for a skew Young diagram with vanishing row moves**:
if the row-move terms of `V_r s_{λ/μ}` sum to zero, then
`V_r s_{λ/μ} = - Σ_R (-1)^{ht R} y(R) s_{λ/μ \ R}` over the `r`-cell northwest-removable
ribbons `R`, `y(R)` the least content of `R`. -/
theorem wDeriv_cellSchur_of_rowMoveSum_eq_zero {lam mu : YoungDiagram} (hmu : mu ≤ lam) {r : ℕ}
    (hr : 0 < r) (hrow : rowMoveSum lam mu r = 0) :
    wDeriv r (cellSchur (skewDiagram lam mu)) =
      -∑ Y ∈ leftRibbons (skewDiagram lam mu) r,
        (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
          cellSchur (skewDiagram lam mu \ Y) := by
  have hM : ∀ i, lam.colLen 0 ≤ i → lam.rowLen i = 0 := rowLen_eq_zero_of_colLen_le lam
  rw [cellSchur_skewDiagram_eq_jtDet hmu hM, wDeriv_jtDet]
  have h := sum_column_moves_weighted hmu hr (fun y => ((y : ℤ) : Lambda))
  simp only at h
  unfold rowMoveSum at hrow
  simp only at hrow
  rw [hrow, h]
  ring

/-- The row-move hypothesis holds when every row-move term vanishes. -/
theorem rowMoveSum_eq_zero_of_terms {lam mu : YoungDiagram} {r : ℕ}
    (h : ∀ i : Fin (lam.colLen 0),
      jtDet (Function.update (fun i : Fin (lam.colLen 0) => (lam.rowLen i : ℤ) - i) i
        ((lam.rowLen i : ℤ) - i - r)) (fun i : Fin (lam.colLen 0) => (mu.rowLen i : ℤ) - i) = 0) :
    rowMoveSum lam mu r = 0 := by
  unfold rowMoveSum
  simp only
  exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]

/-- **Consistency with the ordinary rule**: the unweighted ribbon sum is the derivative
`∂_r s_{λ/μ}`. -/
theorem sum_column_moves_unweighted {lam mu : YoungDiagram} (hmu : mu ≤ lam) {m : ℕ}
    (hm : 0 < m) :
    pDeriv m (cellSchur (skewDiagram lam mu)) =
      ∑ Y ∈ leftRibbons (skewDiagram lam mu) m,
        (ribbonSign Y : Lambda) * cellSchur (skewDiagram lam mu \ Y) := by
  have hM : ∀ i, lam.colLen 0 ≤ i → lam.rowLen i = 0 := rowLen_eq_zero_of_colLen_le lam
  rw [cellSchur_skewDiagram_eq_jtDet hmu hM, pDeriv_jtDet hm]
  have h := sum_column_moves_weighted hmu hm (fun _ => 1)
  simp only [one_mul, mul_one] at h
  exact h

end SkewMarkedFactor
