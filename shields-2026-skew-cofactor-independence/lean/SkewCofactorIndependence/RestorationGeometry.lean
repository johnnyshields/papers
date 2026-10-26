/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.BetaEndpointCounts

/-!
# Cancellation and restoration of actual beta lists

The geometric producers in `sec:restoration` of
`shields-2026-skew-cofactor-independence.tex`.
-/

namespace SkewCofactorIndependence
namespace BetaDiagram

open BetaEndpointCounts

variable {n : ℕ}

/-- The finite set of row betas. -/
noncomputable def rowSet (D : BetaDiagram n) : Finset ℤ := Finset.univ.image D.row
/-- The finite set of column betas. -/
noncomputable def colSet (D : BetaDiagram n) : Finset ℤ := Finset.univ.image D.col
/-- The beta positions shared by the row and column sets. -/
noncomputable def commonPositions (D : BetaDiagram n) : Finset ℤ := D.rowSet ∩ D.colSet

@[simp] theorem rowSet_card (D : BetaDiagram n) : D.rowSet.card = n := by
  classical
  simp [rowSet, Finset.card_image_of_injective _ D.row_strictAnti.injective]

@[simp] theorem colSet_card (D : BetaDiagram n) : D.colSet.card = n := by
  classical
  simp [colSet, Finset.card_image_of_injective _ D.col_strictAnti.injective]

/-- The positive endpoint span determined by a connected beta diagram. -/
noncomputable def connectedSpan (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    SpanPair D.rowSet D.colSet where
  bottom := D.col (Fin.last n)
  top := D.row 0
  bottom_mem := by
    classical
    simp [colSet]
  top_mem := by
    classical
    simp [rowSet]
  lower x hx := by
    classical
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hc := D.col_strictAnti.antitone (show i ≤ Fin.last n from Fin.le_last i)
      exact hc.trans (D.row_nonempty i).le
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact D.col_strictAnti.antitone (Fin.le_last i)
  upper x hx := by
    classical
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact D.row_strictAnti.antitone (Fin.zero_le i)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact (D.row_nonempty i).le.trans (D.row_strictAnti.antitone (Fin.zero_le i))
  strict_span := by
    exact lt_of_le_of_lt (D.col_strictAnti.antitone (Fin.zero_le (Fin.last n)))
      (D.row_nonempty 0)
  positive x hbottom htop := by
    classical
    let q := above D.rowSet x
    have hqpos : 0 < q := above_lt_at D.row D.row_strictAnti 0 htop
    have hqle : q ≤ n + 1 := by
      exact (Finset.card_filter_le _ _).trans D.rowSet_card.le
    let i : Fin (n + 1) := ⟨q - 1, by omega⟩
    have hi : D.col i ≤ x := by
      by_cases hq : q = n + 1
      · have he : i = Fin.last n := Fin.ext (by dsimp [i]; omega)
        simpa [he] using hbottom
      · have hj : q < n + 1 := by omega
        let j : Fin (n + 1) := ⟨q, hj⟩
        have hr : D.row j ≤ x :=
          (above_le_iff D.row D.row_strictAnti j x).mp (by dsimp [rowSet, j, q]; rfl)
        have hov := hD.2 i (show i.val + 1 < n + 1 by dsimp [i]; omega)
        have he : (⟨i.val + 1, by dsimp [i]; omega⟩ : Fin (n + 1)) = j :=
          Fin.ext (by dsimp [i, j]; omega)
        rw [he] at hov
        exact hov.trans hr
    have hc := above_le_at D.col D.col_strictAnti i hi
    change above D.colSet x < q
    change above D.colSet x ≤ q - 1 at hc
    omega
  equal_card := by simp

theorem mem_availablePositions_sets_iff (C : BetaDiagram (n + 1)) (z : ℤ) :
    z ∈ C.availablePositions ↔
      C.col (Fin.last n) < z ∧ z < C.row 0 ∧ z ∉ C.rowSet ∧ z ∉ C.colSet := by
  classical
  simp [availablePositions, rowSet, colSet, and_assoc]

theorem available_disjoint_rows (C : BetaDiagram (n + 1)) (Z : Finset ℤ)
    (hZ : Z ⊆ C.availablePositions) : Disjoint C.rowSet Z := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hr hz
  exact ((C.mem_availablePositions_sets_iff z).mp (hZ hz)).2.2.1 hr

theorem available_disjoint_cols (C : BetaDiagram (n + 1)) (Z : Finset ℤ)
    (hZ : Z ⊆ C.availablePositions) : Disjoint C.colSet Z := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hc hz
  exact ((C.mem_availablePositions_sets_iff z).mp (hZ hz)).2.2.2 hc

/-- Restoring common beta entries uses the sorted literal unions. -/
noncomputable def restore (C : BetaDiagram (n + 1)) (hC : C.Connected)
    (_hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    BetaDiagram (n + 1 + Z.card) :=
  ((C.connectedSpan hC).restore Z (C.available_disjoint_rows Z hZ)
    (C.available_disjoint_cols Z hZ)
    (fun z hz => by
      have h := (C.mem_availablePositions_sets_iff z).mp (hZ hz)
      exact ⟨h.1, h.2.1⟩)).diagram (by
        rw [Finset.card_union_of_disjoint (C.available_disjoint_rows Z hZ), C.rowSet_card])

theorem restore_connected (C : BetaDiagram (n + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    (C.restore hC hZero Z hZ).Connected :=
  SpanPair.diagram_connected _ _

@[simp] theorem restore_rowSet (C : BetaDiagram (n + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    (C.restore hC hZero Z hZ).rowSet = C.rowSet ∪ Z := image_descending _ _

@[simp] theorem restore_colSet (C : BetaDiagram (n + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    (C.restore hC hZero Z hZ).colSet = C.colSet ∪ Z := image_descending _ _

theorem ext_sets (D E : BetaDiagram n) (hr : D.rowSet = E.rowSet)
    (hc : D.colSet = E.colSet) : D = E := by
  have er := strictAnti_eq_of_image D.row E.row D.row_strictAnti E.row_strictAnti hr
  have ec := strictAnti_eq_of_image D.col E.col D.col_strictAnti E.col_strictAnti hc
  cases D
  cases E
  simp_all

theorem restore_eq_of_sets (C : BetaDiagram (n + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions)
    (D : BetaDiagram (n + 1 + Z.card))
    (hr : D.rowSet = C.rowSet ∪ Z) (hc : D.colSet = C.colSet ∪ Z) :
    D = C.restore hC hZero Z hZ := by
  apply ext_sets D _
  · rw [restore_rowSet]
    exact hr
  · rw [restore_colSet]
    exact hc

theorem restore_commonPositions (C : BetaDiagram (n + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    (C.restore hC hZero Z hZ).commonPositions = Z := by
  classical
  have hd : Disjoint C.rowSet C.colSet := by
    apply Finset.disjoint_left.mpr
    intro z hz hc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
    exact hZero i j (hi.trans hj.symm)
  ext z
  simp only [commonPositions, restore_rowSet, restore_colSet,
    Finset.mem_inter, Finset.mem_union]
  have hn : z ∈ C.rowSet → z ∉ C.colSet :=
    fun hr hc => Finset.disjoint_left.mp hd hr hc
  tauto

/-- The residual order is computed from the actual uncanceled row endpoints. -/
noncomputable def residualOrder (D : BetaDiagram n) : ℕ := (D.rowSet \ D.colSet).card

theorem residualOrder_pos (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    0 < D.residualOrder := (D.connectedSpan hD).cancel.card_pos

/-- The actual nonempty connected residual core after common-beta cancellation. -/
noncomputable def residualCore (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    BetaDiagram (D.residualOrder - 1 + 1) :=
  (D.connectedSpan hD).cancel.diagram (by
    change D.residualOrder = D.residualOrder - 1 + 1
    have := D.residualOrder_pos hD
    omega)

theorem residualCore_connected (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.residualCore hD).Connected := SpanPair.diagram_connected _ _

@[simp] theorem residualCore_rowSet (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.residualCore hD).rowSet = D.rowSet \ D.colSet := image_descending _ _

@[simp] theorem residualCore_colSet (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.residualCore hD).colSet = D.colSet \ D.rowSet := image_descending _ _

theorem residualCore_zeroFree (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.residualCore hD).ZeroFree := by
  classical
  intro i j he
  have hr : (D.residualCore hD).row i ∈ D.rowSet \ D.colSet := by
    rw [← residualCore_rowSet D hD]
    simp [rowSet]
  have hc : (D.residualCore hD).col j ∈ D.colSet \ D.rowSet := by
    rw [← residualCore_colSet D hD]
    simp [colSet]
  exact (Finset.mem_sdiff.mp hr).2 (he ▸ (Finset.mem_sdiff.mp hc).1)

theorem residualCore_top (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.residualCore hD).row 0 = D.row 0 := by
  have hm := (D.connectedSpan hD).cancel.top_mem
  obtain ⟨i, hi⟩ := descending_surjective _ _ hm
  have hupper := (D.connectedSpan hD).cancel.upper
    ((D.residualCore hD).row 0)
    (Finset.mem_union_left _ (descending_mem _ _ 0))
  have hanti := (D.residualCore hD).row_strictAnti.antitone (Fin.zero_le i)
  change (D.residualCore hD).row i = D.row 0 at hi
  rw [hi] at hanti
  exact le_antisymm hupper hanti

theorem residualCore_bottom (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.residualCore hD).col (Fin.last (D.residualOrder - 1)) = D.col (Fin.last n) := by
  have hm := (D.connectedSpan hD).cancel.bottom_mem
  obtain ⟨i, hi⟩ := descending_surjective _ _ hm
  have hlower := (D.connectedSpan hD).cancel.lower
    ((D.residualCore hD).col (Fin.last (D.residualOrder - 1)))
    (Finset.mem_union_right _ (descending_mem _ _ _))
  have hanti := (D.residualCore hD).col_strictAnti.antitone (Fin.le_last i)
  change (D.residualCore hD).col i = D.col (Fin.last n) at hi
  rw [hi] at hanti
  exact le_antisymm hanti hlower

theorem commonPositions_available (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    D.commonPositions ⊆ (D.residualCore hD).availablePositions := by
  classical
  intro z hz
  obtain ⟨hr, hc⟩ := Finset.mem_inter.mp hz
  rw [mem_availablePositions_sets_iff, residualCore_top, residualCore_bottom,
    residualCore_rowSet, residualCore_colSet]
  have hl := (D.connectedSpan hD).lower z (Finset.mem_union_left _ hr)
  have hu := (D.connectedSpan hD).upper z (Finset.mem_union_right _ hc)
  change D.col (Fin.last n) ≤ z at hl
  change z ≤ D.row 0 at hu
  have hnebottom : z ≠ D.col (Fin.last n) := by
    intro he
    apply (D.connectedSpan hD).bottom_not_row
    change D.col (Fin.last n) ∈ D.rowSet
    simpa only [he] using hr
  have hnetop : z ≠ D.row 0 := by
    intro he
    apply (D.connectedSpan hD).top_not_col
    change D.row 0 ∈ D.colSet
    simpa only [he] using hc
  exact ⟨lt_of_le_of_ne hl hnebottom.symm, lt_of_le_of_ne hu hnetop,
    by simp [hc], by simp [hr]⟩

theorem residualOrder_add_common (D : BetaDiagram n) :
    D.residualOrder + D.commonPositions.card = n := by
  classical
  change (D.rowSet \ D.colSet).card + (D.rowSet ∩ D.colSet).card = n
  rw [Finset.card_sdiff_add_card_inter, D.rowSet_card]

theorem reconstruct_sets (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    D.rowSet = (D.residualCore hD).rowSet ∪ D.commonPositions ∧
      D.colSet = (D.residualCore hD).colSet ∪ D.commonPositions := by
  classical
  simp only [residualCore_rowSet, residualCore_colSet, commonPositions]
  constructor <;> ext z <;> simp <;> tauto

/-- Changes only the finite order index, never the beta coordinates. -/
def castOrder {a b : ℕ} (D : BetaDiagram a) (h : a = b) : BetaDiagram b := h ▸ D

@[simp] theorem castOrder_schur {a b : ℕ} (D : BetaDiagram a) (h : a = b) :
    (D.castOrder h).schur = D.schur := by cases h; rfl

@[simp] theorem castOrder_rowSet {a b : ℕ} (D : BetaDiagram a) (h : a = b) :
    (D.castOrder h).rowSet = D.rowSet := by cases h; rfl

@[simp] theorem castOrder_colSet {a b : ℕ} (D : BetaDiagram a) (h : a = b) :
    (D.castOrder h).colSet = D.colSet := by cases h; rfl

/-- Every connected diagram is literally a restoration of its actual residual core. -/
theorem exists_restoration {m : ℕ} (D : BetaDiagram m) (hD : D.Connected) :
    ∃ (a : ℕ) (C : BetaDiagram (a + 1)) (hC : C.Connected) (hZero : C.ZeroFree)
      (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions)
      (h : a + 1 + Z.card = m), (C.restore hC hZero Z hZ).castOrder h = D := by
  cases m with
  | zero => exact False.elim (by simpa [Connected] using hD.1)
  | succ m =>
    let C := D.residualCore hD
    let Z := D.commonPositions
    let hC := D.residualCore_connected hD
    let hZero := D.residualCore_zeroFree hD
    let hZ := D.commonPositions_available hD
    have h : D.residualOrder - 1 + 1 + Z.card = m + 1 := by
      have hn := D.residualOrder_pos hD
      have hc := D.residualOrder_add_common
      dsimp [Z]
      omega
    refine ⟨D.residualOrder - 1, C, hC, hZero, Z, hZ, h, ?_⟩
    apply ext_sets
    · rw [castOrder_rowSet, restore_rowSet]
      exact (D.reconstruct_sets hD).1.symm
    · rw [castOrder_colSet, restore_colSet]
      exact (D.reconstruct_sets hD).2.symm

end BetaDiagram
end SkewCofactorIndependence
