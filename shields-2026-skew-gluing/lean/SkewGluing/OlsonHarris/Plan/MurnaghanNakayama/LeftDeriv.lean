import SkewGluing.OlsonHarris.Plan.MurnaghanNakayama.Young

/-!
# The derivation form of the Murnaghan–Nakayama rule, for skew shapes of Young diagrams

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis Cor. 5.1.15 (`OlsonHarris2024HopfApplications`),
the left derivation form for `X = λ / μ`.

`pDeriv_cellSchur_left_young`: `∂_m s_{λ/μ} = Σ_Y (-1)^{ht Y} s_{λ/μ \ Y}`.  The derivative of the
Jacobi–Trudi determinant `det (h_{λ_i - i - (μ_j - j)})` is the sum over `j` of the determinants
with `μ_j - j` raised by `m`.  A raised list with a repeated entry gives zero; otherwise sorting
it is a row move (`Raise`) whose sign is the height of the ribbon; and a determinant with some
`ν_k > λ_k` is zero (`RowMoveDet`).  The ribbons that are downsets of `λ / μ` correspond to the
nonzero terms (`RowMove`, `Young`).

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace MN

open MvPolynomial

theorem rowLen_eq_zero_of_colLen_le (lam : YoungDiagram) :
    ∀ i, lam.colLen 0 ≤ i → lam.rowLen i = 0 := by
  intro i hi
  by_contra h
  have : (i, 0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
  rw [YoungDiagram.mem_iff_lt_colLen] at this
  omega

theorem mem_leftRibbons_of_rowMove {lam mu nu : YoungDiagram} {j i1 m : ℕ} (hm : 0 < m)
    (hRM : RowMove mu nu j i1 m) (hl : nu ≤ lam) :
    skewDiagram nu mu ∈ leftRibbons (skewDiagram lam mu) m :=
  mem_leftRibbons.mpr ⟨skewDiagram_subset hl, hRM.card_eq hm, hRM.isRibbon hm,
    isDownsetIn_skewDiagram hl⟩

theorem pDeriv_cellSchur_left_young {lam mu : YoungDiagram} (hmu : mu ≤ lam) {m : ℕ}
    (hm : 0 < m) :
    pDeriv m (cellSchur (skewDiagram lam mu)) =
      ribbonSumLeft cellSchur (skewDiagram lam mu) m := by
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
  rw [cellSchur_skewDiagram_eq_jtDet hmu hM, pDeriv_jtDet hm]
  unfold ribbonSumLeft
  -- the value of a term attached to a row move
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
  -- nonzero terms come from row moves
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
  refine Finset.sum_bij_ne_zero (fun j _ hne => skewDiagram (hex j hne).choose mu) ?_ ?_ ?_ ?_
  · intro j _ hne
    obtain ⟨i1, hRM, hl⟩ := (hex j hne).choose_spec
    exact mem_leftRibbons_of_rowMove hm hRM hl
  · intro j1 _ h1 j2 _ h2 heq
    obtain ⟨i1, hRM1, -⟩ := (hex j1 h1).choose_spec
    obtain ⟨i2, hRM2, -⟩ := (hex j2 h2).choose_spec
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
    have hne : jtDet a (Function.update b ⟨j, hjM⟩ (b ⟨j, hjM⟩ + m)) ≠ 0 := by
      rw [hfg]
      exact hgY
    refine ⟨⟨j, hjM⟩, Finset.mem_univ _, hne, ?_⟩
    obtain ⟨i1', hRM', -⟩ := (hex ⟨j, hjM⟩ hne).choose_spec
    rw [hRM.unique_nu hm hRM']
  · intro j _ hne
    obtain ⟨i1, hRM, hl⟩ := (hex j hne).choose_spec
    exact hmain j.val j.isLt _ i1 hRM hl

end MN

end Plan

end SkewGluing
