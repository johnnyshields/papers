/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/CofactorActions.lean

import SkewSchurReconstruction.CappedDiagrams
import SkewSchurReconstruction.ScalarRecovery
import SkewSchurReconstruction.MongeMinors

/-!
# Initial cofactors and normalized actions

Formalizes "Strict-Monge geometry of cofactor actions" (`sec:geometry`):
`prop:cofactor-initial`, `prop:action-recurrence`, and `prop:initial-energy`.
The actions are least weights of actual signed maximal determinants, not assigned
matching costs.  Strict-Monge initial forms identify those weights with the
increasing matching.  No ordinary-degree bridge is asserted here.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

private theorem succAbove_strictMono (j : Fin (n + 1)) : StrictMono j.succAbove := by
  intro a b hab
  simp only [Fin.succAbove]
  split_ifs <;>
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega

private theorem castSucc_le_succAbove (j : Fin (n + 1)) (i : Fin n) :
    i.castSucc ≤ j.succAbove i := by
  by_cases hi : i.castSucc < j
  · simp [Fin.succAbove_of_castSucc_lt _ _ hi]
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hi)]
    change i.val ≤ i.val + 1
    omega

/-- Connectedness supplies feasibility for every increasing maximal-minor matching. -/
theorem peelIndex_nonneg (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) (i : Fin n) : 0 ≤ X.peelIndex j i := by
  have hdiag := X.diagonal_feasible hX i
  have hcap := X.capShift_strictMono.monotone (castSucc_le_succAbove j i)
  unfold peelIndex
  omega

/-- The ordered maximal minor is exactly a staircase matrix, with no row permutation. -/
theorem capMatrix_minor_eq_staircase (X : Diagram n) (j : Fin (n + 1)) :
    X.capMatrix.submatrix id j.succAbove =
      staircaseMatrix X.rowParam (fun i => X.capShift (j.succAbove i)) := by
  ext i k
  rfl

private theorem minor_nonzero (w : ConvexWeight) (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) : (X.capMatrix.submatrix id j.succAbove).det ≠ 0 := by
  rw [capMatrix_minor_eq_staircase]
  apply monge_minor_ne_zero w X.rowParam_strictMono
    (X.capShift_strictMono.comp (succAbove_strictMono j))
  intro i
  have h := X.peelIndex_nonneg hX j i
  unfold peelIndex at h
  change 0 ≤ (X.capShift ∘ j.succAbove) i - X.rowParam i at h
  omega

/-- Every signed maximal cofactor is nonzero for a connected diagram. -/
theorem cofactor_ne_zero (w : ConvexWeight) (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) : X.cofactor j ≠ 0 := by
  unfold cofactor signedMaximalCofactor
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (minor_nonzero w X hX j)

private theorem sign_homogeneous (w : ConvexWeight) (j : Fin (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous w.generatorWeight
      ((-1 : CompleteRing) ^ j.val) 0 := by
  have h := MvPolynomial.isWeightedHomogeneous_C w.generatorWeight ((-1 : ℤ) ^ j.val)
  simpa using h

/-- Initial form of the actual signed maximal cofactor `prop:cofactor-initial`. -/
theorem cofactor_initialForm (w : ConvexWeight) (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) :
    initialForm w.generatorWeight (X.cofactor j) =
      (-1 : CompleteRing) ^ j.val * ∏ i, complete (X.peelIndex j i) := by
  have hminor := minor_nonzero w X hX j
  have hsign : (-1 : CompleteRing) ^ j.val ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  unfold cofactor signedMaximalCofactor
  rw [initialForm_mul hsign hminor,
    initialForm_eq_of_homogeneous hsign (sign_homogeneous w j)]
  rw [capMatrix_minor_eq_staircase]
  have hf : ∀ i, X.rowParam i ≤ X.capShift (j.succAbove i) := by
    intro i
    have h := X.peelIndex_nonneg hX j i
    unfold peelIndex at h
    omega
  exact congrArg (fun p => (-1 : CompleteRing) ^ j.val * p)
    (monge_minor_initialForm w X.rowParam_strictMono
      (X.capShift_strictMono.comp (succAbove_strictMono j)) hf)

/-- Exact least weight of the signed determinant, including zero-index factors. -/
theorem cofactor_leastWeight (w : ConvexWeight) (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) :
    leastWeight w.generatorWeight (X.cofactor j) =
      ∑ i, w.weight (X.peelIndex j i).toNat := by
  have hp := X.cofactor_ne_zero w hX j
  have hprod := complete_prod_convex_homogeneous Finset.univ
    (fun i => X.peelIndex j i) w (fun i _ => X.peelIndex_nonneg hX j i)
  have hi : MvPolynomial.IsWeightedHomogeneous w.generatorWeight
      (initialForm w.generatorWeight (X.cofactor j))
      (∑ i, w.weight (X.peelIndex j i).toNat) := by
    rw [cofactor_initialForm w X hX j]
    simpa using (sign_homogeneous w j).mul hprod
  have hleast : MvPolynomial.IsWeightedHomogeneous w.generatorWeight
      (initialForm w.generatorWeight (X.cofactor j))
      (leastWeight w.generatorWeight (X.cofactor j)) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
  exact MvPolynomial.IsWeightedHomogeneous.inj_right (initialForm_ne_zero hp) hleast hi

/-- Finite valuation of the actual signed cofactor. -/
theorem cofactor_monomialValuation (w : ConvexWeight) (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) :
    monomialValuation w.generatorWeight (X.cofactor j) =
      ((∑ i, w.weight (X.peelIndex j i).toNat) : WithTop ℝ) := by
  rw [monomialValuation_eq_coe (X.cofactor_ne_zero w hX j), cofactor_leastWeight w X hX j]
  rw [WithTop.coe_sum]

/-- The normalized action `eq:sigma-def` of the actual cofactor. -/
noncomputable def parentAction (w : ConvexWeight) (X : Diagram n) (j : Fin (n + 1)) : ℝ :=
  leastWeight w.generatorWeight (X.cofactor j) + w.weight (X.capShift j).toNat

/-- Adjacent matching costs change only in the exchanged row. -/
theorem matching_weight_exchange (w : ConvexWeight) (X : Diagram n) (j : Fin n) :
    (∑ i, w.weight (X.peelIndex j.succ i).toNat) -
      (∑ i, w.weight (X.peelIndex j.castSucc i).toNat) =
        w.weight (X.exchangeZero j).toNat - w.weight (X.exchangeRow j).toNat := by
  classical
  rw [← Finset.sum_sub_distrib]
  have he : ∀ i : Fin n,
      w.weight (X.peelIndex j.succ i).toNat - w.weight (X.peelIndex j.castSucc i).toNat =
        if i = j then w.weight (X.exchangeZero j).toNat -
          w.weight (X.exchangeRow j).toNat else 0 := by
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi, X.peelIndex_adjacent_eq j i hi]
  simp_rw [he]
  simp

/-- The exact adjacent normalized-action recurrence `prop:action-recurrence`. -/
theorem parentAction_recurrence (w : ConvexWeight) (X : Diagram n) (hX : X.Connected)
    (j : Fin n) :
    parentAction w X j.succ - parentAction w X j.castSucc =
      w.weight (X.capShift j.castSucc - X.rowParam j).toNat -
        w.weight (X.capShift j.succ - X.rowParam j).toNat +
          w.weight (X.capShift j.succ).toNat - w.weight (X.capShift j.castSucc).toNat := by
  unfold parentAction
  rw [cofactor_leastWeight w X hX, cofactor_leastWeight w X hX]
  have he := matching_weight_exchange w X j
  unfold exchangeZero exchangeRow at he
  linarith

/-- Initial action is the sum of the row energies `prop:initial-energy`. -/
theorem parentAction_zero (w : ConvexWeight) (X : Diagram n) (hX : X.Connected) :
    parentAction w X 0 = ∑ i, w.weight (X.rowLength i) := by
  unfold parentAction
  rw [cofactor_leastWeight w X hX]
  simp only [capShift_zero, Int.toNat_zero, w.zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have h : X.peelIndex 0 i = (X.rowLength i : ℤ) := by
    simpa [peelIndex] using (X.rowLength_eq_coordinates i).symm
  rw [h]
  simp

private theorem cast_toNat_real (a : ℤ) (ha : 0 ≤ a) : (a.toNat : ℝ) = (a : ℝ) := by
  have h : (a.toNat : ℤ) = a := by omega
  exact_mod_cast h

/-- The square-weight action increment is the discrete geometric action formula. -/
theorem parentAction_square_recurrence (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    parentAction squareWeight X j.succ - parentAction squareWeight X j.castSucc =
      2 * (X.rowParam j : ℝ) * ((X.capShift j.succ : ℝ) - (X.capShift j.castSucc : ℝ)) := by
  rw [parentAction_recurrence squareWeight X hX]
  have hz : 0 ≤ X.capShift j.castSucc - X.rowParam j :=
    sub_nonneg.mpr (X.diagonal_feasible hX j)
  have hr : 0 ≤ X.capShift j.succ - X.rowParam j := by
    have h := X.row_nonempty j
    rw [← X.rowLength_eq_coordinates j]
    positivity
  change ((X.capShift j.castSucc - X.rowParam j).toNat : ℝ) ^ 2 -
    ((X.capShift j.succ - X.rowParam j).toNat : ℝ) ^ 2 +
      ((X.capShift j.succ).toNat : ℝ) ^ 2 - ((X.capShift j.castSucc).toNat : ℝ) ^ 2 = _
  rw [cast_toNat_real _ hz, cast_toNat_real _ hr,
    cast_toNat_real _ (X.capShift_nonneg j.succ),
    cast_toNat_real _ (X.capShift_nonneg j.castSucc)]
  push_cast
  ring

end Diagram
end SkewSchurReconstruction
