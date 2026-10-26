/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.DilationRay
import SkewCofactorIndependence.RestorationComponents
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Exact unequal restorations and the symmetric dilation limitation

The literal parents in `ex:unequal-restorations`, the coefficient of
`eq:restoration-separator`, and the symmetric dense counterexample in the
concluding remarks of `shields-2026-skew-cofactor-independence.tex`.
The specialization kills only the other generators and preserves the
specified coefficient exactly.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The first literal seven-row restoration parent. -/
def restorationZ : BetaDiagram 7 where
  row := ![20, 16, 11, 10, 6, 2, 1]
  col := ![16, 11, 6, 5, 2, 1, 0]
  row_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  col_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  row_nonempty := by intro i; fin_cases i <;> norm_num

/-- The second literal seven-row restoration parent. -/
def restorationW : BetaDiagram 7 where
  row := ![20, 19, 14, 10, 9, 4, 2]
  col := ![19, 14, 9, 5, 4, 2, 0]
  row_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  col_strictAnti := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  row_nonempty := by intro i; fin_cases i <;> norm_num

/-- The actual parents are connected, not just valid beta presentations. -/
theorem restorationZ_connected : restorationZ.Connected := by
  refine ⟨by omega, ?_⟩
  intro i
  fin_cases i <;> intro hi <;> norm_num [restorationZ] at hi <;> norm_num [restorationZ]

theorem restorationW_connected : restorationW.Connected := by
  refine ⟨by omega, ?_⟩
  intro i
  fin_cases i <;> intro hi <;> norm_num [restorationW] at hi <;> norm_num [restorationW]

/-- The common betas in the two parents, without multiplicity or ordering artifacts. -/
def restorationZBetas : Finset ℤ := {1, 2, 6, 11, 16}
/-- The common beta positions of the second restoration parent. -/
def restorationWBetas : Finset ℤ := {2, 4, 9, 14, 19}

/-- The genuine fivefold core shared by both parents. -/
def restorationCore : BetaDiagram 2 := dilationRayCore.dilate 5

/-- Every proposed common beta is genuinely available in the core. -/
theorem restorationZBetas_available : restorationZBetas ⊆ restorationCore.availablePositions := by
  intro z hz
  simp only [restorationZBetas, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;>
    rw [BetaDiagram.mem_availablePositions] <;>
    refine ⟨by norm_num [restorationCore, BetaDiagram.dilate, dilationRayCore],
      by norm_num [restorationCore, BetaDiagram.dilate, dilationRayCore], ?_, ?_⟩ <;>
    intro i <;> fin_cases i <;>
    norm_num [restorationCore, BetaDiagram.dilate, dilationRayCore]

theorem restorationWBetas_available : restorationWBetas ⊆ restorationCore.availablePositions := by
  intro z hz
  simp only [restorationWBetas, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;>
    rw [BetaDiagram.mem_availablePositions] <;>
    refine ⟨by norm_num [restorationCore, BetaDiagram.dilate, dilationRayCore],
      by norm_num [restorationCore, BetaDiagram.dilate, dilationRayCore], ?_, ?_⟩ <;>
    intro i <;> fin_cases i <;>
    norm_num [restorationCore, BetaDiagram.dilate, dilationRayCore]

/-- Both parent row sets are the literal unions used in restoration. -/
theorem restorationZ_rowSet :
    restorationZ.rowSet = restorationCore.rowSet ∪ restorationZBetas := by decide

theorem restorationZ_colSet :
    restorationZ.colSet = restorationCore.colSet ∪ restorationZBetas := by decide

theorem restorationW_rowSet :
    restorationW.rowSet = restorationCore.rowSet ∪ restorationWBetas := by decide

theorem restorationW_colSet :
    restorationW.colSet = restorationCore.colSet ∪ restorationWBetas := by decide

theorem restorationZ_commonPositions : restorationZ.commonPositions = restorationZBetas := by
  decide

theorem restorationW_commonPositions : restorationW.commonPositions = restorationWBetas := by
  decide

theorem restorationCore_dense : restorationCore.Dense := dilationRayCore_dense.dilate 5
theorem restorationCore_connected : restorationCore.Connected :=
  restorationCore_dense.connected (by omega)

/-- Set equality identifies the full determinant even when the index types are
presented differently. -/
theorem beta_schur_eq_of_sets {n m : ℕ} (D : BetaDiagram n) (E : BetaDiagram m)
    (hr : D.rowSet = E.rowSet) (hc : D.colSet = E.colSet) : D.schur = E.schur := by
  have hn : n = m := by
    simpa only [BetaDiagram.rowSet_card] using congrArg Finset.card hr
  cases hn
  exact congrArg BetaDiagram.schur (BetaDiagram.ext_sets D E hr hc)

/-- The first parent is the actual sorted restoration, at the level of its full determinant. -/
theorem restorationZ_is_restoration :
    restorationZ.schur =
      (restorationCore.restore restorationCore_connected restorationCore_dense.zeroFree
        restorationZBetas restorationZBetas_available).schur := by
  apply beta_schur_eq_of_sets
  · simpa only [BetaDiagram.restore_rowSet] using restorationZ_rowSet
  · simpa only [BetaDiagram.restore_colSet] using restorationZ_colSet

theorem restorationW_is_restoration :
    restorationW.schur =
      (restorationCore.restore restorationCore_connected restorationCore_dense.zeroFree
        restorationWBetas restorationWBetas_available).schur := by
  apply beta_schur_eq_of_sets
  · simpa only [BetaDiagram.restore_rowSet] using restorationW_rowSet
  · simpa only [BetaDiagram.restore_colSet] using restorationW_colSet

/-- Cancellation leaves the actual fivefold core, not merely a core of the same rank. -/
theorem restorationZ_residual_schur :
    (restorationZ.residualCore restorationZ_connected).schur = restorationCore.schur := by
  apply beta_schur_eq_of_sets
  · rw [BetaDiagram.residualCore_rowSet]
    decide
  · rw [BetaDiagram.residualCore_colSet]
    decide

theorem restorationW_residual_schur :
    (restorationW.residualCore restorationW_connected).schur = restorationCore.schur := by
  apply beta_schur_eq_of_sets
  · rw [BetaDiagram.residualCore_rowSet]
    decide
  · rw [BetaDiagram.residualCore_colSet]
    decide

/-- The sorted common-beta lists used by the exact deletion-sign producer. -/
theorem restorationZ_descending :
    BetaEndpointCounts.descending restorationZBetas rfl = ![16, 11, 6, 2, 1] := by
  apply BetaEndpointCounts.strictAnti_eq_of_image
  · exact BetaEndpointCounts.descending_strictAnti _ _
  · exact (by decide : StrictAnti (![16, 11, 6, 2, 1] : Fin 5 → ℤ))
  · rw [BetaEndpointCounts.image_descending]
    decide

theorem restorationW_descending :
    BetaEndpointCounts.descending restorationWBetas rfl = ![19, 14, 9, 4, 2] := by
  apply BetaEndpointCounts.strictAnti_eq_of_image
  · exact BetaEndpointCounts.descending_strictAnti _ _
  · exact (by decide : StrictAnti (![19, 14, 9, 4, 2] : Fin 5 → ℤ))
  · rw [BetaEndpointCounts.image_descending]
    decide

theorem restorationZ_rows_disjoint : Disjoint restorationCore.rowSet restorationZBetas :=
  restorationCore.available_disjoint_rows _ restorationZBetas_available

theorem restorationZ_cols_disjoint : Disjoint restorationCore.colSet restorationZBetas :=
  restorationCore.available_disjoint_cols _ restorationZBetas_available

theorem restorationW_rows_disjoint : Disjoint restorationCore.rowSet restorationWBetas :=
  restorationCore.available_disjoint_rows _ restorationWBetas_available

theorem restorationW_cols_disjoint : Disjoint restorationCore.colSet restorationWBetas :=
  restorationCore.available_disjoint_cols _ restorationWBetas_available

/-- The same row and column permutations regroup both literal parents. -/
def restorationRowPermutation : Equiv.Perm (Fin 7) :=
  Equiv.swap 1 2 * Equiv.swap 1 3

/-- The column permutation regrouping both restoration parents into core and common betas. -/
def restorationColPermutation : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 2 * Equiv.swap 0 4 * Equiv.swap 0 5 *
    Equiv.swap 0 6 * Equiv.swap 0 1 * Equiv.swap 0 3

theorem restorationRowPermutation_apply (i : Fin 7) :
    restorationRowPermutation i = ![0, 3, 1, 2, 4, 5, 6] i := by
  fin_cases i <;> decide

theorem restorationColPermutation_apply (i : Fin 7) :
    restorationColPermutation i = ![3, 6, 0, 1, 2, 4, 5] i := by
  fin_cases i <;> decide

theorem restorationZ_row_regroup :
    BetaDiagram.regroup restorationCore.row restorationCore.row_strictAnti.injective
      restorationZBetas restorationZ_rows_disjoint restorationZ.row
      restorationZ.row_strictAnti.injective restorationZ_rowSet =
        finSumFinEquiv.trans restorationRowPermutation := by
  apply Equiv.ext
  intro u
  apply restorationZ.row_strictAnti.injective
  rw [BetaDiagram.regroup_apply restorationCore.row restorationCore.row_strictAnti.injective
    restorationZBetas restorationZ_rows_disjoint restorationZ.row
    restorationZ.row_strictAnti.injective restorationZ_rowSet u]
  cases u with
  | inl i => fin_cases i <;> decide
  | inr j =>
    rw [restorationZ_descending]
    fin_cases j <;> decide

theorem restorationZ_col_regroup :
    BetaDiagram.regroup restorationCore.col restorationCore.col_strictAnti.injective
      restorationZBetas restorationZ_cols_disjoint restorationZ.col
      restorationZ.col_strictAnti.injective restorationZ_colSet =
        finSumFinEquiv.trans restorationColPermutation := by
  apply Equiv.ext
  intro u
  apply restorationZ.col_strictAnti.injective
  rw [BetaDiagram.regroup_apply restorationCore.col restorationCore.col_strictAnti.injective
    restorationZBetas restorationZ_cols_disjoint restorationZ.col
    restorationZ.col_strictAnti.injective restorationZ_colSet u]
  cases u with
  | inl i => fin_cases i <;> decide
  | inr j =>
    rw [restorationZ_descending]
    fin_cases j <;> decide

theorem restorationW_row_regroup :
    BetaDiagram.regroup restorationCore.row restorationCore.row_strictAnti.injective
      restorationWBetas restorationW_rows_disjoint restorationW.row
      restorationW.row_strictAnti.injective restorationW_rowSet =
        finSumFinEquiv.trans restorationRowPermutation := by
  apply Equiv.ext
  intro u
  apply restorationW.row_strictAnti.injective
  rw [BetaDiagram.regroup_apply restorationCore.row restorationCore.row_strictAnti.injective
    restorationWBetas restorationW_rows_disjoint restorationW.row
    restorationW.row_strictAnti.injective restorationW_rowSet u]
  cases u with
  | inl i => fin_cases i <;> decide
  | inr j =>
    rw [restorationW_descending]
    fin_cases j <;> decide

theorem restorationW_col_regroup :
    BetaDiagram.regroup restorationCore.col restorationCore.col_strictAnti.injective
      restorationWBetas restorationW_cols_disjoint restorationW.col
      restorationW.col_strictAnti.injective restorationW_colSet =
        finSumFinEquiv.trans restorationColPermutation := by
  apply Equiv.ext
  intro u
  apply restorationW.col_strictAnti.injective
  rw [BetaDiagram.regroup_apply restorationCore.col restorationCore.col_strictAnti.injective
    restorationWBetas restorationW_cols_disjoint restorationW.col
    restorationW.col_strictAnti.injective restorationW_colSet u]
  cases u with
  | inl i => fin_cases i <;> decide
  | inr j =>
    rw [restorationW_descending]
    fin_cases j <;> decide

/-- Regrouping back along the same enumeration gives the literal permutation. -/
theorem regroup_permutation_cancel {α β : Type*} (e : α ≃ β) (p : Equiv.Perm β) :
    e.symm.trans (e.trans p) = p := by
  apply Equiv.ext
  intro i
  change p (e (e.symm i)) = p i
  rw [e.apply_symm_apply]

/-- The signs agree; in fact each is positive. -/
theorem restorationZ_deletionSign :
    restorationCore.deletionSign restorationZBetas restorationZ_rows_disjoint
      restorationZ_cols_disjoint restorationZ restorationZ_rowSet restorationZ_colSet = 1 := by
  unfold BetaDiagram.deletionSign
  rw [restorationZ_row_regroup, restorationZ_col_regroup]
  rw [regroup_permutation_cancel, regroup_permutation_cancel]
  simp [restorationRowPermutation, restorationColPermutation, Equiv.Perm.sign_mul]

theorem restorationW_deletionSign :
    restorationCore.deletionSign restorationWBetas restorationW_rows_disjoint
      restorationW_cols_disjoint restorationW restorationW_rowSet restorationW_colSet = 1 := by
  unfold BetaDiagram.deletionSign
  rw [restorationW_row_regroup, restorationW_col_regroup]
  rw [regroup_permutation_cancel, regroup_permutation_cancel]
  simp [restorationRowPermutation, restorationColPermutation, Equiv.Perm.sign_mul]

/-- The literal common-set difference in the actual available-coordinate space. -/
def restorationRelation : restorationCore.Available → ℚ :=
  fun z => (if z.val ∈ restorationZBetas then 1 else 0) -
    (if z.val ∈ restorationWBetas then 1 else 0)

/-- The exact odd residue function exchanging residues one and four modulo five. -/
def restorationResidueFunction :
    ZMod (5 * dilationRayCore.endpointModulus) → ℚ :=
  fun r => (if r.val = 1 then 1 else 0) - (if r.val = 4 then 1 else 0)

theorem restorationResidueFunction_offGrid :
    restorationResidueFunction ∈
      offGridResidueSpace 5 dilationRayCore.endpointModulus dilationRayCore.span := by
  change (fun r : ZMod 5 =>
    (if r.val = 1 then (1 : ℚ) else 0) - (if r.val = 4 then 1 else 0)) ∈
      offGridResidueSpace 5 1 4
  constructor
  · intro r
    change ((if r.val = 1 then (1 : ℚ) else 0) - (if r.val = 4 then 1 else 0)) +
      ((if ((20 : ZMod 5) - r).val = 1 then 1 else 0) -
        (if ((20 : ZMod 5) - r).val = 4 then 1 else 0)) = 0
    fin_cases r <;> norm_num [ZMod.val]
  · intro r hr
    have hv := ZMod.val_lt r
    have hz : r.val = 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hv] using hr
    simp [hz]

theorem restorationRelation_eq_residue :
    restorationRelation =
      restorationCore.residueRestriction (5 * dilationRayCore.endpointModulus)
        restorationResidueFunction := by
  funext z
  have hb := (restorationCore.mem_availablePositions z.val).mp z.property
  have h₀ : 0 < z.val := by
    simpa [restorationCore, BetaDiagram.dilate, dilationRayCore] using hb.1
  have h₂₀ : z.val < 20 := by
    simpa [restorationCore, BetaDiagram.dilate, dilationRayCore] using hb.2.1
  change ((if z.val ∈ restorationZBetas then 1 else 0) -
    (if z.val ∈ restorationWBetas then 1 else 0)) =
      restorationResidueFunction (z.val : ZMod (5 * dilationRayCore.endpointModulus))
  change ((if z.val ∈ restorationZBetas then (1 : ℚ) else 0) -
    (if z.val ∈ restorationWBetas then 1 else 0)) =
      (if (z.val : ZMod 5).val = 1 then 1 else 0) -
        (if (z.val : ZMod 5).val = 4 then 1 else 0)
  have hmod := ZMod.val_intCast (n := 5) z.val
  have hone :
      (z.val : ZMod 5).val = 1 ↔ z.val = 1 ∨ z.val = 6 ∨ z.val = 11 ∨ z.val = 16 := by
    omega
  have hfour :
      (z.val : ZMod 5).val = 4 ↔ z.val = 4 ∨ z.val = 9 ∨ z.val = 14 ∨ z.val = 19 := by
    omega
  simp only [hone, hfour]
  simp only [restorationZBetas, restorationWBetas, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> norm_num <;> omega

/-- The set difference is a genuine arithmetic kernel relation, not a numerical near-relation. -/
theorem restorationRelation_arithmetic :
    restorationRelation ∈ dilationRayCore.arithmeticOffGrid 5 := by
  exact ⟨restorationResidueFunction, restorationResidueFunction_offGrid,
    restorationRelation_eq_residue.symm⟩

theorem restorationRelation_kernel : restorationRelation ∈ restorationCore.unitKernel :=
  dilationRayCore.arithmeticOffGrid_le_kernel 5 dilationRayCore_normalized
    dilationRayCore_dense.zeroFree restorationRelation_arithmetic

/-- The relation has exactly the two finite sums of units as its polynomial image. -/
theorem restorationRelation_image :
    restorationCore.unitRelationMap restorationRelation =
      (∑ z ∈ restorationZBetas, restorationCore.unitVariation z) -
        ∑ z ∈ restorationWBetas, restorationCore.unitVariation z := by
  classical
  have sum_indicator (S : Finset ℤ) (hS : S ⊆ restorationCore.availablePositions) :
      (∑ z : restorationCore.Available,
        (if z.val ∈ S then (1 : ℚ) else 0) • restorationCore.unitVariation z.val) =
        ∑ z ∈ S, restorationCore.unitVariation z := by
    calc
      _ = ∑ z ∈ restorationCore.availablePositions,
          (if z ∈ S then (1 : ℚ) else 0) • restorationCore.unitVariation z :=
        Finset.sum_coe_sort restorationCore.availablePositions
          (fun z : ℤ => (if z ∈ S then (1 : ℚ) else 0) • restorationCore.unitVariation z)
      _ = ∑ z ∈ S, restorationCore.unitVariation z := by
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_mem]
        rw [Finset.inter_eq_right.mpr hS]
  change (∑ z : restorationCore.Available,
    restorationRelation z • restorationCore.unitVariation z.val) = _
  simp only [restorationRelation, sub_smul, Finset.sum_sub_distrib]
  rw [sum_indicator _ restorationZBetas_available, sum_indicator _ restorationWBetas_available]

theorem restoration_units_sum_eq :
    (∑ z ∈ restorationZBetas, restorationCore.unitVariation z) =
      ∑ z ∈ restorationWBetas, restorationCore.unitVariation z := by
  apply sub_eq_zero.mp
  rw [← restorationRelation_image]
  exact restorationRelation_kernel

/-- The two lowest ordinary components agree although the full functions do not. -/
theorem restoration_components_eq :
    ordinaryComponent restorationZ.schur 2 = ordinaryComponent restorationW.schur 2 ∧
      ordinaryComponent restorationZ.schur 3 = ordinaryComponent restorationW.schur 3 := by
  have hZ := restorationCore.restoration_first_coefficients restorationCore_dense.zeroFree
    restorationZBetas restorationZ_rows_disjoint restorationZ_cols_disjoint restorationZ
    restorationZ_rowSet restorationZ_colSet
  have hW := restorationCore.restoration_first_coefficients restorationCore_dense.zeroFree
    restorationWBetas restorationW_rows_disjoint restorationW_cols_disjoint restorationW
    restorationW_rowSet restorationW_colSet
  rw [restorationZ_deletionSign] at hZ
  rw [restorationW_deletionSign] at hW
  constructor
  · exact hZ.1.trans hW.1.symm
  · change ordinaryComponent restorationZ.schur (1 + 2) =
      ordinaryComponent restorationW.schur (1 + 2)
    rw [hZ.2, hW.2, restoration_units_sum_eq]

/-- Degree two is genuinely the lowest ordinary degree in both parents. -/
theorem restoration_components_below_two (d : ℕ) (hd : d < 2) :
    ordinaryComponent restorationZ.schur d = 0 ∧
      ordinaryComponent restorationW.schur d = 0 := by
  exact ⟨restorationCore.restoration_coeff_below restorationCore_dense.zeroFree
    restorationZBetas restorationZ_rows_disjoint restorationZ_cols_disjoint restorationZ
    restorationZ_rowSet restorationZ_colSet d hd,
    restorationCore.restoration_coeff_below restorationCore_dense.zeroFree
    restorationWBetas restorationW_rows_disjoint restorationW_cols_disjoint restorationW
    restorationW_rowSet restorationW_colSet d hd⟩

theorem restoration_component_two_ne_zero :
    ordinaryComponent restorationZ.schur 2 ≠ 0 ∧
      ordinaryComponent restorationW.schur 2 ≠ 0 := by
  exact ⟨restorationCore.restoration_lowest_nonzero restorationCore_dense.zeroFree
    restorationZBetas restorationZ_rows_disjoint restorationZ_cols_disjoint restorationZ
    restorationZ_rowSet restorationZ_colSet,
    restorationCore.restoration_lowest_nonzero restorationCore_dense.zeroFree
    restorationWBetas restorationW_rows_disjoint restorationW_cols_disjoint restorationW
    restorationW_rowSet restorationW_colSet⟩

/-- Exactly the generators retained in the separator specialization. -/
def SeparatorGenerator := {k : ℕ+ // k = 2 ∨ k = 5 ∨ k = 9}

/-- The retained generator with index two. -/
def separatorTwo : SeparatorGenerator := ⟨2, by simp⟩
/-- The retained generator with index five. -/
def separatorFive : SeparatorGenerator := ⟨5, by simp⟩
/-- The retained generator with index nine. -/
def separatorNine : SeparatorGenerator := ⟨9, by simp⟩

/-- Rational polynomials in the three retained separator generators. -/
abbrev SeparatorRing := MvPolynomial SeparatorGenerator ℚ

/-- The canonical kill-complement map, retaining the variables themselves. -/
def separatorSpecialization : CompleteRing →ₐ[ℚ] SeparatorRing :=
  MvPolynomial.killCompl (f := fun k : SeparatorGenerator => k.val) Subtype.val_injective

/-- This map preserves every coefficient supported on the three retained generators. -/
theorem separatorSpecialization_coeff (p : CompleteRing) (e : SeparatorGenerator →₀ ℕ) :
    (separatorSpecialization p).coeff e =
      p.coeff (e.mapDomain (fun k : SeparatorGenerator => k.val)) :=
  MvPolynomial.coeff_killCompl Subtype.val_injective

/-- A retained variable is not identified with any other retained variable. -/
theorem separatorSpecialization_X (k : SeparatorGenerator) :
    separatorSpecialization (MvPolynomial.X k.val) = MvPolynomial.X k := by
  simpa only [separatorSpecialization, MvPolynomial.rename_X] using
    MvPolynomial.killCompl_rename_app
      (f := fun k : SeparatorGenerator => k.val) Subtype.val_injective
      (MvPolynomial.X k : SeparatorRing)

/-- Exact specialization of all signed indices, including the genuine zero-index unit. -/
theorem separatorSpecialization_complete (k : ℤ) :
    separatorSpecialization (complete k) =
      if k = 0 then 1 else
      if k = 2 then MvPolynomial.X separatorTwo else
      if k = 5 then MvPolynomial.X separatorFive else
      if k = 9 then MvPolynomial.X separatorNine else 0 := by
  by_cases h₀ : k = 0
  · subst k; simp
  by_cases h₂ : k = 2
  · subst k
    simpa [separatorTwo, complete_of_pos (by norm_num : (0 : ℤ) < 2)]
      using separatorSpecialization_X separatorTwo
  by_cases h₅ : k = 5
  · subst k
    simpa [separatorFive, complete_of_pos (by norm_num : (0 : ℤ) < 5)]
      using separatorSpecialization_X separatorFive
  by_cases h₉ : k = 9
  · subst k
    simpa [separatorNine, complete_of_pos (by norm_num : (0 : ℤ) < 9)]
      using separatorSpecialization_X separatorNine
  simp only [ite_eq_right h₀, ite_eq_right h₂, ite_eq_right h₅, ite_eq_right h₉]
  by_cases hk : k < 0
  · rw [complete_of_neg hk, map_zero]
  · have hp : 0 < k := by omega
    let p : ℕ+ := ⟨k.toNat, by omega⟩
    rw [complete_of_pos hp]
    change separatorSpecialization (MvPolynomial.X p) = 0
    have hn : p ∉ Set.range (fun a : SeparatorGenerator => a.val) := by
      rintro ⟨a, ha⟩
      rcases a.property with h | h | h
      all_goals
        have hpk := ha.symm.trans h
        have hv := congrArg PNat.val hpk
        dsimp [p] at hv
        omega
    change (MvPolynomial.monomial (Finsupp.single p 1) (1 : ℚ)).killCompl
      (f := fun a : SeparatorGenerator => a.val) Subtype.val_injective = 0
    exact MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range
      Subtype.val_injective (1 : ℚ) (by simp) hn

/-- The three disjoint transpositions realizing the manuscript's column word. -/
def restorationAssignment : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 2 4 * Equiv.swap 5 6

/-- Zero-based spelling of the one-based column word `(2,1,5,4,3,7,6)`. -/
theorem restorationAssignment_apply (i : Fin 7) :
    restorationAssignment i = ![1, 0, 4, 3, 2, 6, 5] i := by
  fin_cases i <;> decide

/-- The assignment consists of three swaps and has negative sign. -/
theorem restorationAssignment_sign : Equiv.Perm.sign restorationAssignment = -1 := by
  simp [restorationAssignment, Equiv.Perm.sign_mul]

/-- The surviving assignment's actual complete labels, including all three units. -/
theorem restorationAssignment_labels (i : Fin 7) :
    restorationZ.row i - restorationZ.col (restorationAssignment i) =
      ![9, 0, 9, 5, 0, 2, 0] i := by
  rw [restorationAssignment_apply]
  fin_cases i <;> norm_num [restorationZ]

/-- An assignment survives precisely when every label is zero or one of the
three retained positive indices. -/
def separatorSurvives (D : BetaDiagram 7) (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ i, D.row i - D.col (σ i) = 0 ∨ D.row i - D.col (σ i) = 2 ∨
    D.row i - D.col (σ i) = 5 ∨ D.row i - D.col (σ i) = 9

/-- Forced rows and injectivity give a unique surviving assignment.
No permutation enumeration or determinant-rank certificate is used. -/
theorem restorationZ_unique_surviving_assignment (σ : Equiv.Perm (Fin 7))
    (hσ : separatorSurvives restorationZ σ) : σ = restorationAssignment := by
  have h₀ := hσ 0
  have h₆ := hσ 6
  have e₀ : σ 0 = 1 := by
    generalize he : σ 0 = a at h₀ ⊢
    fin_cases a <;> norm_num [restorationZ] at h₀; norm_num
  have e₆ : σ 6 = 5 := by
    generalize he : σ 6 = a at h₆ ⊢
    fin_cases a <;> norm_num [restorationZ] at h₆; norm_num
  have e₁ : σ 1 = 0 := by
    have h₁ := hσ 1
    have hn := σ.injective.ne (by decide : (1 : Fin 7) ≠ 0)
    rw [e₀] at hn
    generalize he : σ 1 = a at h₁ hn ⊢
    fin_cases a <;> norm_num [restorationZ] at h₁ <;> norm_num at hn; norm_num
  have e₃ : σ 3 = 3 := by
    have h₃ := hσ 3
    have hn := σ.injective.ne (by decide : (3 : Fin 7) ≠ 6)
    rw [e₆] at hn
    generalize he : σ 3 = a at h₃ hn ⊢
    fin_cases a <;> norm_num [restorationZ] at h₃ <;> norm_num at hn; norm_num
  have e₄ : σ 4 = 2 := by
    have h₄ := hσ 4
    have hn := σ.injective.ne (by decide : (4 : Fin 7) ≠ 6)
    rw [e₆] at hn
    generalize he : σ 4 = a at h₄ hn ⊢
    fin_cases a <;> norm_num [restorationZ] at h₄ <;> norm_num at hn; norm_num
  have e₂ : σ 2 = 4 := by
    have h₂ := hσ 2
    have hn₀ := σ.injective.ne (by decide : (2 : Fin 7) ≠ 0)
    have hn₄ := σ.injective.ne (by decide : (2 : Fin 7) ≠ 4)
    rw [e₀] at hn₀
    rw [e₄] at hn₄
    generalize he : σ 2 = a at h₂ hn₀ hn₄ ⊢
    fin_cases a <;> norm_num [restorationZ] at h₂ <;>
      norm_num at hn₀ <;> norm_num at hn₄; norm_num
  have e₅ : σ 5 = 6 := by
    have h₅ := hσ 5
    have hn := σ.injective.ne (by decide : (5 : Fin 7) ≠ 2)
    rw [e₂] at hn
    generalize he : σ 5 = a at h₅ hn ⊢
    fin_cases a <;> norm_num [restorationZ] at h₅ <;> norm_num at hn; norm_num
  apply Equiv.ext
  intro i
  rw [restorationAssignment_apply]
  fin_cases i
  · simpa using e₀
  · simpa using e₁
  · simpa using e₂
  · simpa using e₃
  · simpa using e₄
  · simpa using e₅
  · simpa using e₆

/-- A non-surviving assignment contributes zero to the specialized determinant. -/
theorem separatorSpecialization_assignment_zero (D : BetaDiagram 7)
    (σ : Equiv.Perm (Fin 7)) (hσ : ¬ separatorSurvives D σ) :
    ∏ i, separatorSpecialization (D.matrix i (σ i)) = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hσ
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change separatorSpecialization (complete (D.row i - D.col (σ i))) = 0
  rw [separatorSpecialization_complete]
  have h₀ : D.row i - D.col (σ i) ≠ 0 := fun h => hi (Or.inl h)
  have h₂ : D.row i - D.col (σ i) ≠ 2 := fun h => hi (Or.inr (Or.inl h))
  have h₅ : D.row i - D.col (σ i) ≠ 5 := fun h => hi (Or.inr (Or.inr (Or.inl h)))
  have h₉ : D.row i - D.col (σ i) ≠ 9 := fun h => hi (Or.inr (Or.inr (Or.inr h)))
  simp only [ite_eq_right h₀, ite_eq_right h₂, ite_eq_right h₅, ite_eq_right h₉]

/-- The exact exponent of the separator in the retained-variable ring. -/
def separatorExponent : SeparatorGenerator →₀ ℕ :=
  Finsupp.single separatorTwo 1 + Finsupp.single separatorFive 1 +
    Finsupp.single separatorNine 2

/-- The exponent in the original free algebra: `h₂ h₅ h₉²`. -/
def restorationSeparator : ℕ+ →₀ ℕ :=
  Finsupp.single 2 1 + Finsupp.single 5 1 + Finsupp.single 9 2

/-- The coefficient map transports the very same exponent, not a different test monomial. -/
theorem separatorExponent_mapDomain :
    separatorExponent.mapDomain (fun k : SeparatorGenerator => k.val) = restorationSeparator := by
  unfold separatorExponent restorationSeparator
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  rfl

/-- The product of the surviving labels is exactly the separator monomial. -/
theorem restorationAssignment_product :
    (∏ i, separatorSpecialization (restorationZ.matrix i (restorationAssignment i))) =
      MvPolynomial.monomial separatorExponent (1 : ℚ) := by
  simp only [BetaDiagram.matrix, Matrix.of_apply, restorationAssignment_labels]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, separatorSpecialization_complete]
  norm_num
  calc
    _ = MvPolynomial.X separatorTwo * MvPolynomial.X separatorFive *
        MvPolynomial.X separatorNine ^ 2 := by ring
    _ = MvPolynomial.monomial separatorExponent (1 : ℚ) := by
      rw [MvPolynomial.X_pow_eq_monomial]
      change MvPolynomial.monomial (Finsupp.single separatorTwo 1) (1 : ℚ) *
        MvPolynomial.monomial (Finsupp.single separatorFive 1) (1 : ℚ) *
          MvPolynomial.monomial (Finsupp.single separatorNine 2) (1 : ℚ) = _
      rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
      simp only [separatorExponent, mul_one]

/-- The entire specialized determinant, not just its degree-four component. -/
theorem restorationZ_specialized_schur :
    separatorSpecialization restorationZ.schur =
      -MvPolynomial.monomial separatorExponent (1 : ℚ) := by
  classical
  change separatorSpecialization.toRingHom restorationZ.matrix.det = _
  rw [separatorSpecialization.toRingHom.map_det]
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  rw [Finset.sum_eq_single restorationAssignment]
  · change Equiv.Perm.sign restorationAssignment •
      (∏ i, separatorSpecialization (restorationZ.matrix i (restorationAssignment i))) = _
    rw [restorationAssignment_sign, restorationAssignment_product]
    simp
  · intro σ hσ hne
    have hn : ¬ separatorSurvives restorationZ σ :=
      fun h => hne (restorationZ_unique_surviving_assignment σ h)
    change Equiv.Perm.sign σ •
      (∏ i, separatorSpecialization (restorationZ.matrix i (σ i))) = 0
    rw [separatorSpecialization_assignment_zero restorationZ σ hn]
    simp
  · simp

/-- The second parent's specialized first row is literally zero. -/
theorem restorationW_specialized_first_row (j : Fin 7) :
    separatorSpecialization (restorationW.matrix 0 j) = 0 := by
  change separatorSpecialization (complete (restorationW.row 0 - restorationW.col j)) = 0
  rw [separatorSpecialization_complete]
  fin_cases j <;> norm_num [restorationW]

/-- Vanishing of a full row kills the actual specialized determinant. -/
theorem restorationW_specialized_schur : separatorSpecialization restorationW.schur = 0 := by
  change separatorSpecialization.toRingHom restorationW.matrix.det = 0
  rw [separatorSpecialization.toRingHom.map_det]
  exact Matrix.det_eq_zero_of_row_eq_zero 0 restorationW_specialized_first_row

/-- The first exact coefficient asserted in `eq:restoration-separator`. -/
theorem restorationZ_separator_coefficient :
    restorationZ.schur.coeff restorationSeparator = -1 := by
  classical
  rw [← separatorExponent_mapDomain, ← separatorSpecialization_coeff,
    restorationZ_specialized_schur]
  rw [MvPolynomial.coeff_neg]
  apply congrArg (fun q : ℚ => -q)
  exact (MvPolynomial.coeff_monomial separatorExponent separatorExponent (1 : ℚ)).trans
    (ite_eq_left rfl)

/-- The second exact coefficient asserted in `eq:restoration-separator`. -/
theorem restorationW_separator_coefficient : restorationW.schur.coeff restorationSeparator = 0 := by
  rw [← separatorExponent_mapDomain, ← separatorSpecialization_coeff,
    restorationW_specialized_schur]
  simp

/-- The connected parents have unequal actual full skew Schur functions. -/
theorem restoration_full_schur_ne : restorationZ.schur ≠ restorationW.schur := by
  intro h
  have hc := congrArg (fun p : CompleteRing => p.coeff restorationSeparator) h
  rw [restorationZ_separator_coefficient, restorationW_separator_coefficient] at hc
  norm_num at hc

/-- The doubled actual symmetric dense core in the concluding limitation. -/
def symmetricDouble : BetaDiagram 2 := symmetricDenseCore.dilate 2

theorem symmetricDouble_dense : symmetricDouble.Dense :=
  symmetricDenseCore_dense.dilate 2

theorem symmetricDouble_normalized : symmetricDouble.Normalized := by
  intro hn
  norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore]

theorem symmetricDouble_symmetric : symmetricDouble.Symmetric := by
  refine ⟨8, ?_, ?_⟩ <;> intro i <;>
    fin_cases i <;> norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore]

/-- Its four cofactors are the actual complementary determinants. -/
theorem symmetricDouble_cofactor (i j : Fin 2) :
    symmetricDouble.cofactor i j =
      ![![complete 6, -complete 4], ![-complete 8, complete 6]] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [BetaDiagram.cofactor, BetaDiagram.matrix, symmetricDouble,
      BetaDiagram.dilate, symmetricDenseCore, Fin.succAbove]

/-- The two off-grid units are equal to the stated nonzero polynomial. -/
theorem symmetricDouble_unit_one :
    symmetricDouble.unitVariation 1 =
      complete 1 * (complete 5 * complete 6 - complete 4 * complete 7) := by
  unfold BetaDiagram.unitVariation
  rw [Fin.sum_univ_two]
  simp_rw [symmetricDouble_cofactor]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore,
    StrictTriangularPaths.positiveGap]
  ring

theorem symmetricDouble_unit_seven :
    symmetricDouble.unitVariation 7 =
      complete 1 * (complete 5 * complete 6 - complete 4 * complete 7) := by
  unfold BetaDiagram.unitVariation
  rw [Fin.sum_univ_two]
  simp_rw [symmetricDouble_cofactor]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore,
    StrictTriangularPaths.positiveGap]
  ring

/-- A rational evaluation separates the two products, proving nonvanishing exactly. -/
theorem symmetricDouble_unit_one_ne_zero : symmetricDouble.unitVariation 1 ≠ 0 := by
  intro h
  let e : CompleteRing →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ)
    (fun k => if k = 4 then 0 else 1)
  have he := congrArg e h
  rw [symmetricDouble_unit_one] at he
  norm_num [e, complete_of_pos (by norm_num : (0 : ℤ) < 1),
    complete_of_pos (by norm_num : (0 : ℤ) < 4),
    complete_of_pos (by norm_num : (0 : ℤ) < 5),
    complete_of_pos (by norm_num : (0 : ℤ) < 6),
    complete_of_pos (by norm_num : (0 : ℤ) < 7)] at he

theorem symmetricDouble_unit_seven_ne_zero : symmetricDouble.unitVariation 7 ≠ 0 := by
  rw [symmetricDouble_unit_seven, ← symmetricDouble_unit_one]
  exact symmetricDouble_unit_one_ne_zero

/-- The base endpoint modulus in the symmetric example is also one. -/
theorem symmetricDenseCore_endpointModulus : symmetricDenseCore.endpointModulus = 1 := by
  apply Nat.dvd_one.mp
  simpa [BetaDiagram.endpointPeriod, symmetricDenseCore] using
    symmetricDenseCore.endpointModulus_dvd (Sum.inr (0 : Fin 2))

theorem symmetricDenseCore_span : symmetricDenseCore.span = 4 := by
  norm_num [BetaDiagram.span, symmetricDenseCore]

/-- The arithmetic residue space of the double is zero: both residues are fixed. -/
theorem symmetricDouble_offGridResidueSpace :
    offGridResidueSpace 2 symmetricDenseCore.endpointModulus symmetricDenseCore.span = ⊥ := by
  rw [symmetricDenseCore_endpointModulus, symmetricDenseCore_span]
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  funext r
  have hr : (-r : ZMod 2) = r := by fin_cases r <;> rfl
  have he := hf.1 r
  change f r + f ((8 : ZMod 2) - r) = 0 at he
  have hh : (8 : ZMod 2) - r = r := by
    exact hr
  rw [hh] at he
  change f r = 0
  linarith

/-- The actual available-coordinate image of that arithmetic space is zero. -/
theorem symmetricDouble_arithmeticOffGrid :
    symmetricDenseCore.arithmeticOffGrid 2 = ⊥ := by
  simp [BetaDiagram.arithmeticOffGrid, symmetricDouble_offGridResidueSpace]

/-- Both reflected off-grid positions are actually available. -/
def symmetricDoublePositionOne : symmetricDouble.Available :=
  ⟨1, by
    rw [BetaDiagram.mem_availablePositions]
    refine ⟨by norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore],
      by norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore], ?_, ?_⟩ <;>
      intro i <;> fin_cases i <;>
      norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore]⟩

/-- The available position seven in the symmetric double. -/
def symmetricDoublePositionSeven : symmetricDouble.Available :=
  ⟨7, by
    rw [BetaDiagram.mem_availablePositions]
    refine ⟨by norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore],
      by norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore], ?_, ?_⟩ <;>
      intro i <;> fin_cases i <;>
      norm_num [symmetricDouble, BetaDiagram.dilate, symmetricDenseCore]⟩

/-- The literal relation between the two nonzero unit polynomials. -/
def symmetricDoubleRelation : symmetricDouble.Available → ℚ :=
  Pi.single symmetricDoublePositionOne 1 - Pi.single symmetricDoublePositionSeven 1

/-- Evaluation of a genuine finite coordinate singleton in the actual unit relation map. -/
theorem BetaDiagram.unitRelationMap_single {n : ℕ} (D : BetaDiagram (n + 1))
    (z : D.Available) :
    D.unitRelationMap (Pi.single z (1 : ℚ)) = D.unitVariation z.val := by
  classical
  change (∑ w : D.Available, ((Pi.single z 1 : D.Available → ℚ) w) •
    D.unitVariation w.val) = _
  rw [Finset.sum_eq_single z]
  · simp
  · intro w hw hne
    simp [hne]
  · simp

theorem symmetricDouble_relation_kernel :
    symmetricDoubleRelation ∈ symmetricDouble.unitKernel := by
  change symmetricDouble.unitRelationMap symmetricDoubleRelation = 0
  change symmetricDouble.unitRelationMap
    (Pi.single symmetricDoublePositionOne 1 - Pi.single symmetricDoublePositionSeven 1) = 0
  rw [map_sub]
  rw [BetaDiagram.unitRelationMap_single, BetaDiagram.unitRelationMap_single]
  change symmetricDouble.unitVariation 1 - symmetricDouble.unitVariation 7 = 0
  rw [symmetricDouble_unit_one, symmetricDouble_unit_seven, sub_self]

theorem symmetricDouble_relation_at_one :
    symmetricDoubleRelation symmetricDoublePositionOne = 1 := by
  have hn : symmetricDoublePositionOne ≠ symmetricDoublePositionSeven := by
    intro h
    have hh := congrArg Subtype.val h
    norm_num [symmetricDoublePositionOne, symmetricDoublePositionSeven] at hh
  simp [symmetricDoubleRelation, hn]

theorem symmetricDouble_relation_ne_zero : symmetricDoubleRelation ≠ 0 := by
  intro h
  have hh := congrFun h symmetricDoublePositionOne
  rw [symmetricDouble_relation_at_one] at hh
  norm_num at hh

/-- The relation is not inherited: inherited coordinates vanish at every odd position. -/
theorem symmetricDouble_relation_not_inherited :
    symmetricDoubleRelation ∉ symmetricDenseCore.inheritedKernel 2 := by
  rintro ⟨c, hc, he⟩
  have hzero := symmetricDenseCore.gridLift_offGrid 2 c
    symmetricDoublePositionOne (by norm_num [symmetricDoublePositionOne])
  have hh := congrFun he symmetricDoublePositionOne
  rw [hzero, symmetricDouble_relation_at_one] at hh
  norm_num at hh

/-- Nor is it supplied by the arithmetic summand, which is zero. -/
theorem symmetricDouble_relation_not_arithmetic :
    symmetricDoubleRelation ∉ symmetricDenseCore.arithmeticOffGrid 2 := by
  rw [symmetricDouble_arithmeticOffGrid]
  change symmetricDoubleRelation ≠ 0
  exact symmetricDouble_relation_ne_zero

/-- Even the sum of the two purported sources misses this genuine kernel relation. -/
theorem symmetricDouble_relation_not_inherited_sup_arithmetic :
    symmetricDoubleRelation ∉
      symmetricDenseCore.inheritedKernel 2 ⊔ symmetricDenseCore.arithmeticOffGrid 2 := by
  rw [symmetricDouble_arithmeticOffGrid, sup_bot_eq]
  exact symmetricDouble_relation_not_inherited

/-- The unconditional containment in `thm:dilation` is strict on this actual double. -/
theorem symmetricDouble_dilation_containment_strict :
    symmetricDenseCore.inheritedKernel 2 ⊔ symmetricDenseCore.arithmeticOffGrid 2 <
      symmetricDouble.unitKernel := by
  apply lt_of_le_of_ne
  · have hnorm : symmetricDenseCore.Normalized := by
      intro hn; norm_num [symmetricDenseCore]
    exact (symmetricDenseCore.dilation_kernel_containment 2 (by omega)
      hnorm symmetricDenseCore_dense.zeroFree).1
  · intro h
    apply symmetricDouble_relation_not_inherited_sup_arithmetic
    rw [h]
    exact symmetricDouble_relation_kernel

end SkewCofactorIndependence
