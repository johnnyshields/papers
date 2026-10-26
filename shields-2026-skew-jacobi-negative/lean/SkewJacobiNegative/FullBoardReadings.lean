/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.RestorationComponents
import SkewJacobiNegative.RepresentationBridges

/-!
# Minimum ordinary degree and unit-count recovery

The remaining assertion of `lem:readings` and the zero-free mate consequence
in `sec:boundary-tools` of `shields-2026-skew-jacobi-negative.tex`.  Common
beta entries are counted on the full lists, before any cancellation.
-/

namespace SkewJacobiNegative.BetaDiagram
variable {n m : ℕ}

@[simp]
theorem castOrder_commonPositions {a b : ℕ} (D : BetaDiagram a) (h : a = b) :
    (D.castOrder h).commonPositions = D.commonPositions := by
  cases h
  rfl

/-- The exact minimum degree is identified by vanishing below and nonvanishing at it. -/
theorem minimum_ordinary_degree (D : BetaDiagram n) (hD : D.Connected) :
    (∀ d < n - D.commonPositions.card, ordinaryComponent D.schur d = 0) ∧
      ordinaryComponent D.schur (n - D.commonPositions.card) ≠ 0 := by
  classical
  obtain ⟨a, C, hC, hZero, Z, hZ, horder, hreal⟩ := D.exists_restoration hD
  let R := C.restore hC hZero Z hZ
  have hpoly : D.schur = R.schur := by
    rw [← hreal, castOrder_schur]
  have hcommon : D.commonPositions = Z := by
    rw [← hreal, castOrder_commonPositions, C.restore_commonPositions]
  have hdegree : a + 1 = n - D.commonPositions.card := by
    rw [hcommon]
    omega
  have hr := C.available_disjoint_rows Z hZ
  have hc := C.available_disjoint_cols Z hZ
  have er : R.rowSet = C.rowSet ∪ Z := C.restore_rowSet hC hZero Z hZ
  have ec : R.colSet = C.colSet ∪ Z := C.restore_colSet hC hZero Z hZ
  constructor
  · intro d hd
    rw [hpoly]
    exact C.restoration_coeff_below hZero Z hr hc R er ec d (by omega)
  · rw [hpoly, ← hdegree]
    exact C.restoration_lowest_nonzero hZero Z hr hc R er ec

/-- Full Schur equality determines the number of common beta entries. -/
theorem commonPositions_card_eq_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    D.commonPositions.card = E.commonPositions.card := by
  have hn := D.row_count_of_schur_eq E he
  have hd := D.minimum_ordinary_degree hD
  have hh := E.minimum_ordinary_degree hE
  have hmin : n - D.commonPositions.card = m - E.commonPositions.card := by
    apply le_antisymm
    · by_contra h
      have hlt : m - E.commonPositions.card < n - D.commonPositions.card := by omega
      have hz := hd.1 _ hlt
      rw [he] at hz
      exact hh.2 hz
    · by_contra h
      have hlt : n - D.commonPositions.card < m - E.commonPositions.card := by omega
      have hz := hh.1 _ hlt
      rw [← he] at hz
      exact hd.2 hz
  have hdc := D.residualOrder_add_common
  have hec := E.residualOrder_add_common
  omega

/-- Zero-freeness means precisely that the full lists have no common entries. -/
theorem zeroFree_iff_commonPositions_card_eq_zero (D : BetaDiagram n) :
    D.ZeroFree ↔ D.commonPositions.card = 0 := by
  classical
  constructor
  · intro h
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    obtain ⟨hr, hc⟩ := Finset.mem_inter.mp hz
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hr
    obtain ⟨j, hj, hf⟩ := Finset.mem_image.mp hc
    exact h i j (he.trans hf.symm)
  · intro h i j he
    have hempty := Finset.card_eq_zero.mp h
    have hm : D.row i ∈ D.commonPositions := by
      apply Finset.mem_inter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he.symm⟩
    rw [hempty] at hm
    exact Finset.notMem_empty _ hm

/-- No common beta entries can appear in a connected mate of a zero-free source. -/
theorem zeroFree_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (hE : E.Connected) (hz : D.ZeroFree) (he : D.schur = E.schur) :
    E.ZeroFree := by
  rw [E.zeroFree_iff_commonPositions_card_eq_zero,
    ← D.commonPositions_card_eq_of_schur_eq E hD hE he]
  exact D.zeroFree_iff_commonPositions_card_eq_zero.mp hz

end SkewJacobiNegative.BetaDiagram
