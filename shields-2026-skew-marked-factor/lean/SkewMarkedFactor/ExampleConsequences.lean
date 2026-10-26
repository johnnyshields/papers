/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.ReadoutExamples
import SkewMarkedFactor.FactorRecovery
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.OrdinaryAssemble

/-!
# Concrete differential readouts

The literal diagrams of «Explicit formulas and examples» (`sec:examples`),
including `eq:example-tail`, `eq:example-outer`, and the empty-edge gauge.
The Jacobi--Trudi calculations are bridged to the actual finite cell sets.
-/

set_option maxRecDepth 4096

namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The two-row profile of the nine-cell inner. -/
def exampleInnerProfile : Profile 1 where
  r := ![4, 5]
  g := ![1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The profile of the seven-cell outer. -/
def exampleOuterProfile : Profile 2 where
  r := ![3, 2, 2]
  g := ![1, 1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The first displayed parent profile. -/
def exampleParentProfile : Profile 7 where
  r := ![4, 7, 7, 8, 7, 8, 7, 5]
  g := ![1, 1, 4, 5, 4, 5, 1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The second displayed parent profile. -/
def exampleRotatedParentProfile : Profile 7 where
  r := ![4, 7, 8, 7, 8, 7, 7, 5]
  g := ![1, 4, 5, 4, 5, 1, 1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

set_option maxHeartbeats 0 in
-- Kernel evaluation expands the explicit finite inner diagram and its translated profile.
theorem exampleInner_profile_cells :
    exampleInner = translate (0, -1) exampleInnerProfile.cells := by decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation expands the explicit finite outer diagram and its translated profile.
theorem exampleOuter_profile_cells :
    exampleOuter = translate (0, -2) exampleOuterProfile.cells := by decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation expands the 53-cell composition and the translated parent profile.
theorem exampleParent_profile_cells :
    exampleParent = translate (-2, -15) exampleParentProfile.cells := by decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation expands the rotated 53-cell composition and its translated profile.
theorem exampleRotatedParent_profile_cells :
    exampleRotatedParent = translate (-4, -17) exampleRotatedParentProfile.cells := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Expanding the finite Jacobi--Trudi determinant requires a larger elaboration budget.
/-- The genuine two-by-two Jacobi--Trudi determinant. -/
theorem exampleInner_schur :
    cellSchur exampleInner = X 4 * X 5 - X 1 * X 8 := by
  rw [exampleInner_profile_cells, cellSchur_translate, cellSchur_cells,
    Profile.schur, Matrix.det_fin_two]
  norm_num [Profile.xi, Profile.zeta, exampleInnerProfile, Fin.sum_univ_succ, hh, hPos]
  ring

set_option maxHeartbeats 0 in
-- Expanding the three-row Jacobi--Trudi determinant requires a larger elaboration budget.
/-- The six terms of the genuine three-by-three determinant. -/
theorem exampleOuter_schur :
    cellSchur exampleOuter =
      X 3 * X 2 ^ 2 - X 3 ^ 2 * X 1 - X 4 * X 2 * X 1 + X 4 * X 3 +
        X 5 * X 1 ^ 2 - X 5 * X 2 := by
  rw [exampleOuter_profile_cells, cellSchur_translate, cellSchur_cells,
    Profile.schur, Matrix.det_fin_three]
  norm_num [Profile.xi, Profile.zeta, exampleOuterProfile, Fin.sum_univ_succ, hh, hPos]
  ring

/-- A row profile used to evaluate the actual southwest mark. -/
def exampleRowTwoProfile : Profile 0 where
  r := ![2]
  g := Fin.elim0
  r_pos := by decide
  g_lt_castSucc := by intro j; exact Fin.elim0 j
  g_lt_succ := by intro j; exact Fin.elim0 j

theorem exampleRowTwoProfile_schur : exampleRowTwoProfile.schur = X 2 := by
  rw [Profile.schur, Matrix.det_succ_row_zero]
  norm_num [Profile.xi, Profile.zeta, exampleRowTwoProfile, Fin.sum_univ_succ, hh, hPos]

theorem exampleMark_W_cells :
    exampleMark.W = translate (1, 0) exampleRowTwoProfile.cells := by decide

set_option maxHeartbeats 0 in
-- Kernel evaluation expands the finite reduced mark.
theorem exampleMark_hatMark_cells : hatMarkFin exampleMark = ∅ := by decide +kernel

theorem exampleMark_hatMiddle_cells : hatMiddleFin exampleMark = {(0, 3)} := by decide

theorem exampleMark_normalizerRow : normalizerRow exampleMark = X 2 := by
  rw [normalizerRow, exampleMark_W_cells, cellSchur_translate, cellSchur_cells,
    exampleRowTwoProfile_schur]

theorem exampleMark_normalizerColumn : normalizerColumn exampleMark = 1 := by
  rw [normalizerColumn, exampleMark_hatMark_cells, cellSchur_empty]

theorem exampleMark_normalizerDiagonal : normalizerDiagonal exampleMark = X 1 := by
  rw [normalizerDiagonal, exampleMark_hatMiddle_cells, cellSchur_singleton]

theorem exampleMark_edgeSign : edgeSign exampleMark 1 = -1 := by decide

/-- Each interface with the middle consists of one cell, hence lies in a single row. -/
theorem exampleMark_middle_interfaces :
    exampleMark.middle.filter (fun x => ∃ y ∈ exampleMark.W, CellAdj x y) = {(1, 2)} ∧
      exampleMark.middle.filter (fun x => ∃ y ∈ exampleMark.upper, CellAdj x y) =
        {(0, 4)} := by decide

theorem exampleOuter_dimensions :
    numRows exampleOuter = 3 ∧ numCols exampleOuter = 3 ∧ span exampleOuter = 5 := by decide

set_option maxHeartbeats 0 in
-- Kernel evaluation computes the row, column, and content sets of the 53-cell parent.
theorem exampleParent_dimensions :
    numRows exampleParent = 8 ∧ numCols exampleParent = 25 ∧ span exampleParent = 32 := by
  decide +kernel

/-- Forward composition comes from the ordinary composition theorem, not factor recovery. -/
theorem example_parents_schur_eq : cellSchur exampleParent = cellSchur exampleRotatedParent := by
  exact cellSchur_compose_eq_of_ordinary_plan exampleMark_legal (Or.inl rfl)
    exampleOuter_connected (isConnectedSkew_rotate exampleOuter_connected)
    (cellSchur_rotate exampleOuter).symm

set_option maxHeartbeats 0 in
-- The final kernel decision compares explicit 53-cell diagrams after translation.
/-- Even rotation followed by an arbitrary translation cannot identify the two parents. -/
theorem example_parents_not_rotated_translates :
    ¬ ∃ t : ℤ × ℤ, exampleParent = translate t (rotate exampleRotatedParent) := by
  rintro ⟨t, ht⟩
  have hsw := congrArg sw ht
  have hn : (rotate exampleRotatedParent).Nonempty := by decide
  rw [sw_translate hn] at hsw
  have hs1 : sw exampleParent = (5, -8) := by decide
  have hs2 : sw (rotate exampleRotatedParent) = (4, -14) := by decide
  rw [hs1, hs2] at hsw
  have htval : t = (1, 6) := by
    apply Prod.ext <;> have := congrArg Prod.fst hsw <;> have := congrArg Prod.snd hsw <;>
      simp only [Prod.fst_add, Prod.snd_add] at * <;> omega
  subst t
  exact (by decide +kernel :
    exampleParent ≠ translate (1, 6) (rotate exampleRotatedParent)) ht

/-- A finite witness predicate for an actual two-by-two block. -/
def containsTwoByTwo (D : Diagram) : Prop :=
  ∃ z ∈ D, z + (0, 1) ∈ D ∧ z + (1, 0) ∈ D ∧ z + (1, 1) ∈ D

theorem exampleOuter_contains_block : containsTwoByTwo exampleOuter := by
  unfold containsTwoByTwo
  decide

set_option maxHeartbeats 0 in
-- Kernel evaluation searches the explicit 53-cell parent for a two-by-two block.
theorem exampleParent_contains_block : containsTwoByTwo exampleParent := by
  unfold containsTwoByTwo
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation searches the explicit rotated parent for a two-by-two block.
theorem exampleRotatedParent_contains_block : containsTwoByTwo exampleRotatedParent := by
  unfold containsTwoByTwo
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating the factor-recovery specialization expands the explicit composition.
/-- The terminal order is the actual seven-cell outer area. -/
theorem example_terminal_order : terminalOrder (cellSchur exampleParent) 6 = 7 := by
  have h := factor_recovery_order (χ := ⟨exampleOuter, exampleMark⟩) exampleChart_proper
  change terminalOrder (cellSchur exampleParent) exampleMark.period.toNat = exampleOuter.card at h
  have hp : exampleMark.period.toNat = 6 := rfl
  simpa only [hp, exampleOuter_card] using h

set_option maxHeartbeats 0 in
-- Normalizing the specialized factor-recovery identity expands the explicit parent.
/-- The terminal polynomial in `eq:example-tail`. -/
theorem example_terminal_tail :
    terminalDerivative (cellSchur exampleParent) 6 = -21 * X 1 ^ 5 * X 2 ^ 3 := by
  have h := ordinary_last_display exampleChart_proper
  change terminalDerivative (cellSchur exampleParent) 6 = _ at h
  rw [exampleOuter_card, exampleOuter_tableau_count, exampleMark_edgeSign,
    exampleMark_normalizerRow, exampleMark_normalizerColumn, exampleMark_normalizerDiagonal,
    exampleOuter_dimensions.1, exampleOuter_dimensions.2.1, exampleOuter_dimensions.2.2] at h
  norm_num at h
  simp only [map_ofNat] at h
  rw [h]
  ring

set_option maxHeartbeats 0 in
-- Normalizing the specialized factor-recovery identity expands the explicit parent.
/-- The penultimate polynomial in `eq:example-tail`. -/
theorem example_penultimate_tail :
    penultimateDerivative (cellSchur exampleParent) 6 =
      21 * X 1 ^ 4 * X 2 ^ 2 * (X 4 * X 5 - X 1 * X 8) := by
  have h := ordinary_penultimate_display exampleChart_proper
  change penultimateDerivative (cellSchur exampleParent) 6 = _ at h
  have hE : exampleMark.E = exampleInner := rfl
  simp only [hE] at h
  rw [exampleOuter_card, exampleOuter_tableau_count, exampleMark_edgeSign,
    exampleMark_normalizerRow, exampleMark_normalizerColumn, exampleMark_normalizerDiagonal,
    exampleOuter_dimensions.1, exampleOuter_dimensions.2.1, exampleOuter_dimensions.2.2,
    exampleInner_schur] at h
  norm_num at h
  simp only [map_ofNat] at h
  rw [h]
  ring

set_option maxHeartbeats 0 in
-- The repeated-derivative specialization expands the explicit composition.
/-- The same tails written as the actual repeated derivatives of orders seven and six. -/
theorem example_derivative_tails :
    deltaAt 6 7 (cellSchur exampleParent) = -21 * X 1 ^ 5 * X 2 ^ 3 ∧
      deltaAt 6 6 (cellSchur exampleParent) =
        21 * X 1 ^ 4 * X 2 ^ 2 * (X 4 * X 5 - X 1 * X 8) := by
  constructor
  · simpa only [terminalDerivative, example_terminal_order] using example_terminal_tail
  · simpa only [penultimateDerivative, example_terminal_order, Nat.reduceSub] using
      example_penultimate_tail

set_option maxHeartbeats 0 in
-- The reduced-numerator specialization expands the explicit composition.
/-- The reduced numerator recovers the actual inner polynomial. -/
theorem example_inner_readout :
    innerReadout (cellSchur exampleParent) 6 = X 4 * X 5 - X 1 * X 8 := by
  have h := factor_recovery_inner exampleChart_proper
  change innerReadout (cellSchur exampleParent) 6 = cellSchur exampleInner at h
  exact h.trans exampleInner_schur

set_option maxHeartbeats 0 in
-- Specializing the canonical character readout expands the explicit composition.
/-- The complete normalized outer readout in `eq:example-outer`. -/
theorem example_outer_readout :
    outerReadout (cellSchur exampleParent) 6 =
      (21 : ℚ)⁻¹ • (X 3 * X 2 ^ 2 - X 3 ^ 2 * X 1 - X 4 * X 2 * X 1 +
        X 4 * X 3 + X 5 * X 1 ^ 2 - X 5 * X 2) := by
  have h := factor_recovery_outer exampleChart_proper
  change outerReadout (cellSchur exampleParent) 6 =
    (standardTableauCount exampleOuter : ℚ)⁻¹ • adjustedOuter ⟨exampleOuter, exampleMark⟩ at h
  simpa [exampleOuter_tableau_count, adjustedOuter, exampleMark, exampleOuter_schur] using h

set_option maxHeartbeats 0 in
-- Specializing primitive recovery expands the explicit composition.
/-- Primitive normalization recovers the unscaled six-term outer. -/
theorem example_outer_primitive :
    primitive (outerReadout (cellSchur exampleParent) 6) = cellSchur exampleOuter := by
  have h := factor_recovery_outer_primitive exampleChart_proper
  change primitive (outerReadout (cellSchur exampleParent) 6) =
    adjustedOuter ⟨exampleOuter, exampleMark⟩ at h
  simpa [adjustedOuter, exampleMark] using h

/-- The hook inner of the empty-overlap example. -/
def gaugeExampleInner : Diagram := skewOf [2, 1] []

/-- The horizontal two-cell outer; its antitranspose is the vertical outer. -/
def gaugeExampleRow : Diagram := skewOf [2] []

/-- The vertical two-cell outer, obtained by antitransposing the horizontal outer. -/
def gaugeExampleColumn : Diagram := antitranspose gaugeExampleRow

/-- The parent composed from the hook inner with a horizontal empty-edge mark. -/
def gaugeExampleParent : Diagram := (emptyMarkH gaugeExampleInner).compose gaugeExampleRow

theorem gaugeExample_inner_connected : IsConnectedSkew gaugeExampleInner := by decide

theorem gaugeExample_row_connected : IsConnectedSkew gaugeExampleRow := by decide

theorem gaugeExample_column_connected : IsConnectedSkew gaugeExampleColumn :=
  isConnectedSkew_antitranspose gaugeExample_row_connected

theorem gaugeExample_displacements :
    (emptyMarkH gaugeExampleInner).v = (-1, 2) ∧
      (emptyMarkV gaugeExampleInner).v = (-2, 1) := by decide

theorem gaugeExample_periods :
    (emptyMarkH gaugeExampleInner).period = 3 ∧
      (emptyMarkV gaugeExampleInner).period = 3 := by decide

theorem gaugeExample_horizontal_proper :
    (⟨gaugeExampleRow, emptyMarkH gaugeExampleInner⟩ : Chart).IsProperOrdinary :=
  empty_horizontal_proper gaugeExample_row_connected gaugeExample_inner_connected
    (by decide) (by decide)

theorem gaugeExample_vertical_proper :
    (⟨gaugeExampleColumn, emptyMarkV gaugeExampleInner⟩ : Chart).IsProperOrdinary :=
  empty_vertical_proper gaugeExample_column_connected gaugeExample_inner_connected
    (by decide) (by decide)

/-- The two empty-edge compositions are equal as actual finite cell sets. -/
theorem gaugeExample_parent_eq :
    gaugeExampleParent = (emptyMarkV gaugeExampleInner).compose gaugeExampleColumn := by
  exact ordinary_mark_gauge
    (MarkedInner.emptyMarkH_readoutLegal gaugeExample_inner_connected)
    (MarkedInner.emptyMarkV_readoutLegal gaugeExample_inner_connected)
    rfl (MarkAtlas.empty_period_eq gaugeExampleInner) rfl rfl
    gaugeExample_row_connected.2.1

theorem gaugeExample_row_schur : cellSchur gaugeExampleRow = X 2 := by
  have hc : gaugeExampleRow = exampleRowTwoProfile.cells := by decide
  rw [hc, cellSchur_cells, exampleRowTwoProfile_schur]

theorem gaugeExample_column_schur : cellSchur gaugeExampleColumn = elem 2 := by
  rw [gaugeExampleColumn, cellSchur_antitranspose, gaugeExample_row_schur,
    schurInvolution_X]
  rfl

theorem gaugeExample_row_tableau_count : standardTableauCount gaugeExampleRow = 1 := by decide

theorem gaugeExample_column_tableau_count : standardTableauCount gaugeExampleColumn = 1 := by
  decide

theorem gaugeExample_inner_schur :
    cellSchur gaugeExampleInner = X 1 * X 2 - X 3 := cellSchur_hook

set_option maxHeartbeats 0 in
-- Specializing the canonical readout expands the empty-edge composition.
/-- Horizontal empty-edge recovery reads the row. -/
theorem gaugeExample_horizontal_readout :
    outerReadout (cellSchur gaugeExampleParent) 3 = X 2 := by
  have h := factor_recovery_outer gaugeExample_horizontal_proper
  change outerReadout (cellSchur gaugeExampleParent) 3 =
    (standardTableauCount gaugeExampleRow : ℚ)⁻¹ •
      adjustedOuter ⟨gaugeExampleRow, emptyMarkH gaugeExampleInner⟩ at h
  simpa [adjustedOuter, emptyMarkH, gaugeExample_row_tableau_count,
    gaugeExample_row_schur] using h

set_option maxHeartbeats 0 in
-- Specializing both recovery maps expands the empty-edge composition.
/-- Vertical recovery involutes the column and leaves the inner untouched. -/
theorem gaugeExample_vertical_readout :
    innerReadout (cellSchur gaugeExampleParent) 3 = cellSchur gaugeExampleInner ∧
      outerReadout (cellSchur gaugeExampleParent) 3 = X 2 := by
  have h := factor_recovery_empty_vertical gaugeExample_column_connected
    gaugeExample_inner_connected (by decide) (by decide)
  rw [← gaugeExample_parent_eq] at h
  have hp : (emptyMarkV gaugeExampleInner).period.toNat = 3 := by decide
  rw [hp, gaugeExample_column_tableau_count] at h
  have he : schurInvolution (cellSchur gaugeExampleColumn) = X 2 := by
    rw [gaugeExampleColumn, cellSchur_antitranspose, schurInvolution_involutive,
      gaugeExample_row_schur]
  simpa only [he, Nat.cast_one, inv_one, one_smul] using h

set_option maxHeartbeats 0 in
-- Comparing the canonical readout with the column requires its explicit specialization.
/-- The uninvoluted column polynomial is not the common readout. -/
theorem gaugeExample_readout_ne_column :
    outerReadout (cellSchur gaugeExampleParent) 3 ≠ cellSchur gaugeExampleColumn := by
  rw [gaugeExample_horizontal_readout, gaugeExample_column_schur]
  intro h
  have he := congrArg (MvPolynomial.eval fun k : ℕ+ => if k = 2 then (1 : ℚ) else 0) h
  norm_num [elem_two, map_sub, map_pow, eval_X] at he

set_option maxHeartbeats 0 in
-- Transporting all four readouts expands the explicit rotated composition.
/-- Equal parent functions give literally equal supplied-period readouts. -/
theorem example_rotated_readouts :
    terminalDerivative (cellSchur exampleRotatedParent) 6 =
        -21 * X 1 ^ 5 * X 2 ^ 3 ∧
      penultimateDerivative (cellSchur exampleRotatedParent) 6 =
        21 * X 1 ^ 4 * X 2 ^ 2 * (X 4 * X 5 - X 1 * X 8) ∧
      innerReadout (cellSchur exampleRotatedParent) 6 = X 4 * X 5 - X 1 * X 8 ∧
      outerReadout (cellSchur exampleRotatedParent) 6 =
        (21 : ℚ)⁻¹ • (X 3 * X 2 ^ 2 - X 3 ^ 2 * X 1 - X 4 * X 2 * X 1 +
          X 4 * X 3 + X 5 * X 1 ^ 2 - X 5 * X 2) := by
  rw [← example_parents_schur_eq]
  exact ⟨example_terminal_tail, example_penultimate_tail, example_inner_readout,
    example_outer_readout⟩

end SkewMarkedFactor
