/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.AlternantRatioBridge
import SkewJacobiNegative.ConnectedIrreducibility
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The lower part of the dense four-row endpoint difference

The true three-variable specialization kills each dense four-row endpoint
function but not its fixed geometric leader.  The equal-margin case retains
the actual maximal child's endpoint difference.
-/

namespace SkewJacobiNegative

open scoped BigOperators

/-- A true three-variable complete homogeneous polynomial is nonzero at every degree. -/
theorem hsymm_three_ne_zero (k : ℕ) : MvPolynomial.hsymm (Fin 3) ℚ k ≠ 0 := by
  classical
  let ev : MvPolynomial (Fin 3) ℚ →+* ℚ := MvPolynomial.eval (fun _ => 1)
  have he : ev (MvPolynomial.hsymm (Fin 3) ℚ k) =
      (Fintype.card (Sym (Fin 3) k) : ℚ) := by
    simp [ev, MvPolynomial.hsymm, ← Multiset.prod_hom']
  intro hz
  have h := congrArg ev hz
  rw [he, map_zero] at h
  exact (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
    Fintype.card (Sym (Fin 3) k) ≠ 0)) h

/-- The signed-index specialization retains all nonnegative complete functions. -/
theorem threeVariable_complete_ne_zero (k : ℤ) (hk : 0 ≤ k) :
    threeVariableSpecialization (complete k) ≠ 0 := by
  have he : (k.toNat : ℤ) = k := by omega
  rw [← he, finiteSpecialization_complete_nat]
  exact hsymm_three_ne_zero k.toNat

namespace BetaDiagram

/-- Both endpoint determinants vanish in the actual three-variable alphabet. -/
theorem dense_four_endpoint_specialization_zero (D : BetaDiagram 4) (hD : D.Dense)
    (t : ℤ) (ht : 0 < t) :
    threeVariableSpecialization (D.endpointDifference t ht) = 0 := by
  unfold endpointDifference
  rw [map_sub,
    (D.extendTop t ht).finiteSpecialization_schur_eq_zero_dense
      (by omega) (D.extendTop_dense hD t ht) 3 (by omega),
    (D.extendBottom t ht).finiteSpecialization_schur_eq_zero_dense
      (by omega) (D.extendBottom_dense hD t ht) 3 (by omega), sub_self]

/-- In a strict-margin case the fixed coefficient is an actual three-row Schur function. -/
theorem dense_four_coefficient_specialization_ne_zero_untied (D : BetaDiagram 4)
    (hD : D.Dense) (hne : D.topMargin ≠ D.bottomMargin) :
    threeVariableSpecialization D.endpointCoefficient ≠ 0 := by
  let hP := D.positiveCorner_of_nonnegative hD.nonnegative
  rw [D.endpointCoefficient_eq_sites]
  rcases lt_or_gt_of_ne hne with h | h
  · have he₁ : D.row 0 - D.col (Fin.last 2).castSucc ≠ D.endpointKappa := by
      rw [D.endpointKappa_eq_row_offset h.le]
      change D.row 0 - D.col 2 ≠ D.row 1 - D.col 3
      change D.row 0 - D.row 1 < D.col 2 - D.col 3 at h
      omega
    have he₂ : D.row (0 : Fin 3).succ - D.col (Fin.last 3) =
        D.endpointKappa := (D.endpointKappa_eq_row_offset h.le).symm
    rw [if_neg he₁, if_pos he₂, zero_sub, map_neg]
    apply neg_ne_zero.mpr
    rw [D.cofactor_eq_signed_unsignedMinor, D.endpoint_bottom_minor hP, map_mul]
    apply mul_ne_zero
    · simp
    · exact threeVariable_schur_ne_zero
        ((D.cornerDiagram hP).extendTop D.topMargin D.topMargin_pos)
  · have he₁ : D.row 0 - D.col (Fin.last 2).castSucc = D.endpointKappa :=
      (D.endpointKappa_eq_col_offset h.le).symm
    have he₂ : D.row (0 : Fin 3).succ - D.col (Fin.last 3) ≠ D.endpointKappa := by
      rw [D.endpointKappa_eq_col_offset h.le]
      change D.row 1 - D.col 3 ≠ D.row 0 - D.col 2
      change D.col 2 - D.col 3 < D.row 0 - D.row 1 at h
      omega
    rw [if_pos he₁, if_neg he₂, sub_zero,
      D.cofactor_eq_signed_unsignedMinor, D.endpoint_top_minor hP, map_mul]
    apply mul_ne_zero
    · simp
    · exact threeVariable_schur_ne_zero
        ((D.cornerDiagram hP).extendBottom D.bottomMargin D.bottomMargin_pos)

/-- Nonsymmetry produces a nonzero specialized coefficient also at the tied top level. -/
theorem dense_four_coefficient_specialization_ne_zero (D : BetaDiagram 4)
    (hD : D.Dense) (hS : ¬ D.Symmetric) :
    threeVariableSpecialization D.endpointCoefficient ≠ 0 := by
  by_cases htie : D.topMargin = D.bottomMargin
  · let hP := D.positiveCorner_of_nonnegative hD.nonnegative
    rw [D.endpointCoefficient_tied hP htie, map_mul]
    apply mul_ne_zero
    · simp
    · apply (D.cornerDiagram hP).threeVariable_endpointDifference_ne_zero
      · intro i j
        exact hD i.succ j.castSucc
      · exact fun hs => hS (D.symmetric_of_tied_corner hP htie hs)
  · exact D.dense_four_coefficient_specialization_ne_zero_untied hD htie

/-- The specialized true leader survives every positive shift. -/
theorem dense_four_leading_term_specialization_ne_zero (D : BetaDiagram 4)
    (hD : D.Dense) (hS : ¬ D.Symmetric) (t : ℤ) (ht : 0 < t) :
    threeVariableSpecialization
      (complete (D.endpointKappa + t) * D.endpointCoefficient) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero
    (threeVariable_complete_ne_zero _ (by have := D.endpointKappa_pos; omega))
    (D.dense_four_coefficient_specialization_ne_zero hD hS)

/-- `eq:dense-four-remainder`: the actual endpoint difference is not its leading term. -/
theorem dense_four_lower_part (D : BetaDiagram 4) (hD : D.Dense)
    (hS : ¬ D.Symmetric) (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht ≠ complete (D.endpointKappa + t) * D.endpointCoefficient := by
  intro he
  have hs := congrArg threeVariableSpecialization he
  rw [D.dense_four_endpoint_specialization_zero hD t ht] at hs
  exact D.dense_four_leading_term_specialization_ne_zero hD hS t ht hs.symm

/-- The full fixed geometric top and the genuinely nonzero lower part are simultaneous. -/
theorem dense_four_top_and_remainder (D : BetaDiagram 4) (hD : D.Dense)
    (hS : ¬ D.Symmetric) :
    D.EndpointTop ∧ ∀ (t : ℤ) (ht : 0 < t),
      D.endpointDifference t ht ≠ complete (D.endpointKappa + t) * D.endpointCoefficient :=
  ⟨D.endpoint_top_dense hD hS, D.dense_four_lower_part hD hS⟩

/-- Differentiation at an independent label uses the true signed-index convention. -/
theorem pderiv_complete_label (w : ℕ+) (j : ℤ) :
    MvPolynomial.pderiv w (complete j) = if j = (w.val : ℤ) then 1 else 0 := by
  by_cases hj : j = (w.val : ℤ)
  · rw [hj, if_pos rfl, complete_nat, MvPolynomial.pderiv_X_self]
  · rw [if_neg hj]
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    rw [mem_vars_complete_iff]
    exact Ne.symm hj

/-- Every derivative above the largest source index vanishes. -/
theorem pderiv_schur_above {n : ℕ} (D : BetaDiagram (n + 1)) (w : ℕ+)
    (hw : D.largestLabel < (w.val : ℤ)) : MvPolynomial.pderiv w D.schur = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hv
  have := D.vars_le_largestLabel w hv
  omega

/-- The derivative at the largest source label is the actual signed maximal cofactor. -/
theorem pderiv_schur_at {n : ℕ} (D : BetaDiagram (n + 1)) (w : ℕ+)
    (hw : (w.val : ℤ) = D.largestLabel) :
    MvPolynomial.pderiv w D.schur = D.cornerCoefficient := by
  have he : w = (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) := by
    apply PNat.eq
    change w.val = D.largestLabel.toNat
    have := D.largestLabel_pos
    omega
  exact (congrArg (fun v : ℕ+ => MvPolynomial.pderiv v D.schur) he).trans
    D.pderiv_schur_largest

/-- A top extension changes no entry of its maximal cofactor. -/
theorem extendTop_cornerCoefficient {n : ℕ} (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).cornerCoefficient = D.cornerCoefficient := by
  unfold cornerCoefficient cornerPolynomial cornerBoard
  congr 2

/-- All indices in an endpoint difference are bounded by the prescribed shifted level. -/
theorem endpointDifference_vars_le {n : ℕ} (D : BetaDiagram (n + 2))
    (t : ℤ) (ht : 0 < t) (w : ℕ+)
    (hw : w ∈ (D.endpointDifference t ht).vars) :
    (w.val : ℤ) ≤ D.endpointKappa + t := by
  rw [D.endpointDifference_split t ht] at hw
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hw) with hm | hr
  · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hm) with hg | hc
    · have := (mem_vars_complete_iff _ w).mp hg
      omega
    · exact (D.endpointCoefficient_labels t ht w hc).le
  · exact (D.endpointRemainder_labels t ht w hr).le

theorem pderiv_endpointDifference_above {n : ℕ} (D : BetaDiagram (n + 2))
    (t : ℤ) (ht : 0 < t) (w : ℕ+)
    (hw : D.endpointKappa + t < (w.val : ℤ)) :
    MvPolynomial.pderiv w (D.endpointDifference t ht) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hv
  have := D.endpointDifference_vars_le t ht w hv
  omega

theorem pderiv_endpointDifference_at {n : ℕ} (D : BetaDiagram (n + 2))
    (t : ℤ) (ht : 0 < t) (w : ℕ+)
    (hw : (w.val : ℤ) = D.endpointKappa + t) :
    MvPolynomial.pderiv w (D.endpointDifference t ht) = D.endpointCoefficient := by
  have he : w = D.endpointGenerator t ht := by
    apply PNat.eq
    change w.val = (D.endpointKappa + t).toNat
    have := D.endpointKappa_pos
    omega
  rw [he, D.endpointDifference_pderiv]

/-- The actual dense three-row maximal cofactor has no coordinate divisor. -/
theorem dense_four_corner_erased_ne_zero (D : BetaDiagram 4) (hD : D.Dense)
    (w : ℕ+) : eraseGenerator w D.cornerCoefficient ≠ 0 := by
  let hP := D.positiveCorner_of_nonnegative hD.nonnegative
  have hC : (D.cornerDiagram hP).Connected :=
    D.cornerDiagram_connected hD.nonnegative hP (by omega)
  rw [cornerCoefficient, ← D.cornerDiagram_schur hP, map_mul]
  exact mul_ne_zero (by simp) ((D.cornerDiagram hP).connected_erased_ne_zero hC w)

/-- Every diagonal index lies strictly below the dense four-row endpoint offset. -/
theorem dense_four_diagonal_below_kappa (D : BetaDiagram 4) (i : Fin 4) :
    D.rowLength i < D.endpointKappa := by
  have hrow13 := D.row_strictAnti (show (1 : Fin 4) < 3 by decide)
  have hrow12 := D.row_strictAnti (show (1 : Fin 4) < 2 by decide)
  have hcol02 := D.col_strictAnti (show (0 : Fin 4) < 2 by decide)
  have hcol13 := D.col_strictAnti (show (1 : Fin 4) < 3 by decide)
  have hcol23 := D.col_strictAnti (show (2 : Fin 4) < 3 by decide)
  have hm₁ : D.row 1 - D.col 3 ≤ D.endpointKappa := le_max_left _ _
  have hm₂ : D.row 0 - D.col 2 ≤ D.endpointKappa := le_max_right _ _
  fin_cases i <;> norm_num [rowLength] <;> omega

/-- No label at or above the endpoint offset occurs in the diagonal coefficient-one monomial. -/
theorem dense_four_diagonalExponent_zero (D : BetaDiagram 4) (w : ℕ+)
    (hw : D.endpointKappa ≤ (w.val : ℤ)) : D.diagonalExponent w = 0 := by
  rw [D.diagonalExponent_eq_rowLengths, Base.exponentVector_apply_count]
  apply Multiset.count_eq_zero.mpr
  intro hm
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  have hp := D.rowLength_pos i
  have hb := D.dense_four_diagonal_below_kappa i
  omega

/-- A high coordinate multiple cannot contribute to the diagonal monomial. -/
theorem dense_four_diagonal_coefficient_high_multiple (D : BetaDiagram 4)
    (j : ℤ) (hj : D.endpointKappa ≤ j) (p : CompleteRing) :
    (complete j * p).coeff D.diagonalExponent = 0 := by
  have hp : 0 < j := by have := D.endpointKappa_pos; omega
  let w : ℕ+ := ⟨j.toNat, by omega⟩
  have hw : (w.val : ℤ) = j := by dsimp [w]; omega
  have hd := D.dense_four_diagonalExponent_zero w (by omega)
  rw [complete_of_pos hp]
  change (MvPolynomial.X w * p).coeff D.diagonalExponent = 0
  rw [MvPolynomial.coeff_X_mul']
  simp [Finsupp.mem_support_iff, hd]

/-- The actual source highest-generator coefficient for the first cross resonance. -/
theorem dense_cross_resonance_coefficient (D : BetaDiagram 4)
    (ℓ x u : ℤ) (hℓ : 0 < ℓ) (hx : ℓ < x) (hu : 0 < u)
    (w : ℕ+) (hA : D.largestLabel + x ≤ (w.val : ℤ))
    (hB : ℓ + (x + u) ≤ (w.val : ℤ))
    (hC : D.endpointKappa + (x + u) ≤ (w.val : ℤ)) :
    MvPolynomial.pderiv w
      (complete (ℓ + u) * (D.extendTop x (by omega)).schur -
        complete (ℓ + (x + u)) * D.schur -
        complete ℓ * D.endpointDifference (x + u) (by omega)) =
      (if (w.val : ℤ) = D.largestLabel + x then
        complete (ℓ + u) * D.cornerCoefficient else 0) -
      (if (w.val : ℤ) = ℓ + (x + u) then D.schur else 0) -
      (if (w.val : ℤ) = D.endpointKappa + (x + u) then
        complete ℓ * D.endpointCoefficient else 0) := by
  have hκ := D.endpointKappa_pos
  have ht : (D.extendTop x (by omega)).largestLabel = D.largestLabel + x := by
    simp [largestLabel, extendTop]
    ring
  have hfx : MvPolynomial.pderiv w (D.extendTop x (by omega)).schur =
      if (w.val : ℤ) = D.largestLabel + x then D.cornerCoefficient else 0 := by
    split_ifs with he
    · rw [(D.extendTop x (by omega)).pderiv_schur_at w (by omega),
        D.extendTop_cornerCoefficient]
    · exact (D.extendTop x (by omega)).pderiv_schur_above w (by omega)
  have hfv : MvPolynomial.pderiv w (D.endpointDifference (x + u) (by omega)) =
      if (w.val : ℤ) = D.endpointKappa + (x + u) then D.endpointCoefficient else 0 := by
    split_ifs with he
    · exact D.pderiv_endpointDifference_at _ _ w he
    · exact D.pderiv_endpointDifference_above _ _ w (by omega)
  have hf := D.pderiv_schur_above w (by omega)
  rw [map_sub, map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_mul, pderiv_complete_label, pderiv_complete_label,
    pderiv_complete_label, hfx, hf, hfv]
  rw [if_neg (show ℓ + u ≠ (w.val : ℤ) by omega),
    if_neg (show ℓ ≠ (w.val : ℤ) by omega)]
  split_ifs <;> first | omega | ring

/-- `eq:cross-resonance-one`, uniformly in all positive shifts. -/
theorem dense_cross_resonance_one (D : BetaDiagram 4) (hD : D.Dense)
    (ℓ x u : ℤ) (hℓ : 0 < ℓ) (hx : ℓ < x) (hu : 0 < u) :
    complete (ℓ + u) * (D.extendTop x (by omega)).schur -
      complete (ℓ + (x + u)) * D.schur -
      complete ℓ * D.endpointDifference (x + u) (by omega) ≠ 0 := by
  classical
  by_cases hS : D.Symmetric
  · rw [D.endpointDifference_eq_zero_of_symmetric hS, mul_zero, sub_zero]
    let z : ℕ+ := ⟨(ℓ + u).toNat, by omega⟩
    have hzv : (z.val : ℤ) = ℓ + u := by dsimp [z]; omega
    intro he
    have hh := congrArg (eraseGenerator z) he
    rw [map_sub, map_mul, map_mul, eraseGenerator_complete,
      eraseGenerator_complete, if_pos hzv.symm, if_neg (by omega),
      zero_mul, zero_sub, map_zero] at hh
    exact (neg_ne_zero.mpr
      (mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega))
        (D.connected_erased_ne_zero (hD.connected (by omega)) z))) hh
  have hcoeff := D.endpointCoefficient_ne_zero_dense hD hS
  let k := max (D.largestLabel + x)
    (max (ℓ + (x + u)) (D.endpointKappa + (x + u)))
  have hκ := D.endpointKappa_pos
  have hk : 0 < k := by
    have hmax := le_max_left (D.largestLabel + x)
      (max (ℓ + (x + u)) (D.endpointKappa + (x + u)))
    have hSpos := D.largestLabel_pos
    dsimp [k]
    omega
  let w : ℕ+ := ⟨k.toNat, by omega⟩
  have hw : (w.val : ℤ) = k := by dsimp [w]; omega
  have hA : D.largestLabel + x ≤ (w.val : ℤ) := by rw [hw]; exact le_max_left _ _
  have hB : ℓ + (x + u) ≤ (w.val : ℤ) := by
    rw [hw]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC : D.endpointKappa + (x + u) ≤ (w.val : ℤ) := by
    rw [hw]; exact (le_max_right _ _).trans (le_max_right _ _)
  intro hz
  have hd := congrArg (MvPolynomial.pderiv w) hz
  rw [D.dense_cross_resonance_coefficient ℓ x u hℓ hx hu w hA hB hC, map_zero] at hd
  let z : ℕ+ := ⟨ℓ.toNat, by omega⟩
  have hzv : (z.val : ℤ) = ℓ := by dsimp [z]; omega
  have hf := D.connected_erased_ne_zero (hD.connected (by omega)) z
  have hb := D.dense_four_corner_erased_ne_zero hD z
  by_cases hPA : (w.val : ℤ) = D.largestLabel + x
  · by_cases hPB : (w.val : ℤ) = ℓ + (x + u)
    · by_cases hPC : (w.val : ℤ) = D.endpointKappa + (x + u)
      · have heS : ℓ + u = D.largestLabel := by omega
        have heκ : ℓ = D.endpointKappa := by omega
        simp only [if_pos hPA, if_pos hPB, if_pos hPC] at hd
        have hc := congrArg (fun p : CompleteRing => p.coeff D.diagonalExponent) hd
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_zero,
          D.diagonal_coefficient_one, heS, heκ,
          D.dense_four_diagonal_coefficient_high_multiple _ D.endpointKappa_lt_largestLabel.le,
          D.dense_four_diagonal_coefficient_high_multiple _ le_rfl] at hc
        norm_num at hc
      · have heS : ℓ + u = D.largestLabel := by omega
        simp only [if_pos hPA, if_pos hPB, if_neg hPC, sub_zero] at hd
        let s : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
        have hs : (s.val : ℤ) = D.largestLabel := by dsimp [s]; omega
        have he := congrArg (eraseGenerator s) hd
        rw [map_sub, map_mul, eraseGenerator_complete, heS, if_pos hs.symm,
          map_zero, zero_mul, zero_sub] at he
        exact (neg_ne_zero.mpr
          (D.connected_erased_ne_zero (hD.connected (by omega)) s)) he
    · by_cases hPC : (w.val : ℤ) = D.endpointKappa + (x + u)
      · simp only [if_pos hPA, if_neg hPB, if_pos hPC, sub_zero] at hd
        have he := congrArg (eraseGenerator z) hd
        rw [map_sub, map_mul, map_mul, eraseGenerator_complete,
          eraseGenerator_complete, if_neg (by omega), if_pos hzv.symm,
          zero_mul, sub_zero, map_zero] at he
        exact mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega)) hb he
      · simp only [if_pos hPA, if_neg hPB, if_neg hPC, sub_zero] at hd
        have hbc : D.cornerCoefficient ≠ 0 := by
          intro he
          exact hb (by rw [he, map_zero])
        exact mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega)) hbc hd
  · by_cases hPB : (w.val : ℤ) = ℓ + (x + u)
    · by_cases hPC : (w.val : ℤ) = D.endpointKappa + (x + u)
      · simp only [if_neg hPA, if_pos hPB, if_pos hPC, zero_sub] at hd
        have he := congrArg (eraseGenerator z) hd
        rw [map_sub, map_neg, map_mul, eraseGenerator_complete, if_pos hzv.symm,
          zero_mul, sub_zero, map_zero] at he
        exact (neg_ne_zero.mpr hf) he
      · simp only [if_neg hPA, if_pos hPB, if_neg hPC, zero_sub, sub_zero] at hd
        exact (neg_ne_zero.mpr D.schur_ne_zero) hd
    · by_cases hPC : (w.val : ℤ) = D.endpointKappa + (x + u)
      · simp only [if_neg hPA, if_neg hPB, if_pos hPC, sub_self, zero_sub] at hd
        exact (neg_ne_zero.mpr
          (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hcoeff)) hd
      · have hmax : k = D.largestLabel + x ∨ k = ℓ + (x + u) ∨
            k = D.endpointKappa + (x + u) := by
          dsimp [k]
          rcases le_total (max (ℓ + (x + u)) (D.endpointKappa + (x + u)))
              (D.largestLabel + x) with h | h
          · exact Or.inl (max_eq_left h)
          · rw [max_eq_right h]
            rcases le_total (D.endpointKappa + (x + u)) (ℓ + (x + u)) with h | h
            · exact Or.inr (Or.inl (max_eq_left h))
            · exact Or.inr (Or.inr (max_eq_right h))
        rcases hmax with h | h | h <;> omega

/-- The largest source cofactor is independent of its own moving corner label. -/
theorem pderiv_cornerCoefficient_at {n : ℕ} (D : BetaDiagram (n + 1))
    (w : ℕ+) (hw : (w.val : ℤ) = D.largestLabel) :
    MvPolynomial.pderiv w D.cornerCoefficient = 0 := by
  have he : w = (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) := by
    apply PNat.eq
    change w.val = D.largestLabel.toNat
    have := D.largestLabel_pos
    omega
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hs | hc
  · have hs' := MvPolynomial.vars_pow (-1 : CompleteRing) n hs
    simp only [MvPolynomial.vars_neg, MvPolynomial.vars_one, Finset.notMem_empty] at hs'
  · exact D.largest_not_mem_corner (he ▸ hc)

/-- Highest-generator extraction for a coordinate factor times the source Schur function. -/
theorem source_coordinate_product_coefficient (D : BetaDiagram 4) (r : ℤ)
    (w : ℕ+) (hr : r ≤ (w.val : ℤ)) (hS : D.largestLabel ≤ (w.val : ℤ)) :
    MvPolynomial.pderiv w (complete r * D.schur) =
      (if (w.val : ℤ) = r then D.schur else 0) +
      complete r * (if (w.val : ℤ) = D.largestLabel then D.cornerCoefficient else 0) := by
  have hf : MvPolynomial.pderiv w D.schur =
      if (w.val : ℤ) = D.largestLabel then D.cornerCoefficient else 0 := by
    split_ifs with he
    · exact D.pderiv_schur_at w he
    · exact D.pderiv_schur_above w (by omega)
  rw [MvPolynomial.pderiv_mul, pderiv_complete_label, hf]
  split_ifs <;> first | omega | ring

/-- A square of the top source coordinate has a nonzero second derivative. -/
theorem source_coordinate_product_second_derivative (D : BetaDiagram 4)
    (w : ℕ+) (hw : (w.val : ℤ) = D.largestLabel) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv w
      (complete D.largestLabel * D.schur)) = 2 * D.cornerCoefficient := by
  rw [D.source_coordinate_product_coefficient _ w (by omega) (by omega),
    if_pos hw, if_pos hw, map_add, MvPolynomial.pderiv_mul,
    D.pderiv_schur_at w hw, pderiv_complete_label,
    if_pos hw.symm, D.pderiv_cornerCoefficient_at w hw]
  ring

/-- The left side of the second resonance has its full fixed leading coefficient. -/
theorem dense_cross_resonance_two_coefficient (D : BetaDiagram 4)
    (ℓ x u : ℤ) (hℓ : 0 < ℓ) (hx : ℓ < x) (hu : 0 < u)
    (w : ℕ+) (hM : D.endpointKappa + (x + u) ≤ (w.val : ℤ)) :
    MvPolynomial.pderiv w
      (complete (ℓ + u) * D.endpointDifference x (by omega) -
        complete ℓ * D.endpointDifference (x + u) (by omega)) =
      if (w.val : ℤ) = D.endpointKappa + (x + u) then
        -(complete ℓ * D.endpointCoefficient) else 0 := by
  have hκ := D.endpointKappa_pos
  have hd := D.pderiv_endpointDifference_above x (by omega) w (by omega)
  have hv : MvPolynomial.pderiv w (D.endpointDifference (x + u) (by omega)) =
      if (w.val : ℤ) = D.endpointKappa + (x + u) then D.endpointCoefficient else 0 := by
    split_ifs with he
    · exact D.pderiv_endpointDifference_at _ _ w he
    · exact D.pderiv_endpointDifference_above _ _ w (by omega)
  rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
    pderiv_complete_label, pderiv_complete_label,
    if_neg (by omega), if_neg (by omega), hd, hv]
  split_ifs <;> ring

/-- The left side is genuinely linear in its top coordinate. -/
theorem dense_cross_resonance_two_second_derivative (D : BetaDiagram 4)
    (ℓ x u : ℤ) (hℓ : 0 < ℓ) (hx : ℓ < x) (hu : 0 < u)
    (w : ℕ+) (hw : (w.val : ℤ) = D.endpointKappa + (x + u)) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv w
      (complete (ℓ + u) * D.endpointDifference x (by omega) -
        complete ℓ * D.endpointDifference (x + u) (by omega))) = 0 := by
  have hκ := D.endpointKappa_pos
  have hc : MvPolynomial.pderiv w D.endpointCoefficient = 0 :=
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      ((D.endpointCoefficient_labels (x + u) (by omega)).not_mem w hw)
  rw [D.dense_cross_resonance_two_coefficient ℓ x u hℓ hx hu w hw.ge,
    if_pos hw, map_neg, MvPolynomial.pderiv_mul,
    pderiv_complete_label, if_neg (by omega), hc]
  ring

/-- The second resonance cannot equal a nonzero scalar multiple of its proposed coordinate product. -/
theorem dense_cross_resonance_two_scalar (D : BetaDiagram 4) (hD : D.Dense)
    (ℓ x u : ℤ) (hℓ : 0 < ℓ) (hx : ℓ < x) (hu : 0 < u)
    (η : ℚ) (hη : η ≠ 0) :
    complete (ℓ + u) * D.endpointDifference x (by omega) -
      complete ℓ * D.endpointDifference (x + u) (by omega) ≠
        MvPolynomial.C η * (complete (ℓ + (x + u)) * D.schur) := by
  classical
  by_cases hSym : D.Symmetric
  · rw [D.endpointDifference_eq_zero_of_symmetric hSym,
      D.endpointDifference_eq_zero_of_symmetric hSym, mul_zero, mul_zero, sub_self]
    exact Ne.symm (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hη)
      (mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega)) D.schur_ne_zero))
  have hκ := D.endpointKappa_pos
  have hc := D.endpointCoefficient_ne_zero_dense hD hSym
  have hb : D.cornerCoefficient ≠ 0 := by
    intro hz
    exact D.dense_four_corner_erased_ne_zero hD 1 (by rw [hz, map_zero])
  have hηC : (MvPolynomial.C η : CompleteRing) ≠ 0 := MvPolynomial.C_ne_zero.mpr hη
  let M := D.endpointKappa + (x + u)
  let r := ℓ + (x + u)
  let q := max r D.largestLabel
  have hq : 0 < q := by
    have := D.largestLabel_pos
    dsimp [q]
    have := le_max_right r D.largestLabel
    omega
  let w : ℕ+ := ⟨q.toNat, by omega⟩
  have hw : (w.val : ℤ) = q := by dsimp [w]; omega
  have hqr : r ≤ (w.val : ℤ) := by rw [hw]; exact le_max_left _ _
  have hqS : D.largestLabel ≤ (w.val : ℤ) := by rw [hw]; exact le_max_right _ _
  intro he
  by_cases hqM : M < q
  · have hd := congrArg (MvPolynomial.pderiv w) he
    rw [D.dense_cross_resonance_two_coefficient ℓ x u hℓ hx hu w (by omega),
      if_neg (by omega), MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
      zero_mul, zero_add, D.source_coordinate_product_coefficient _ w hqr hqS] at hd
    by_cases hwr : (w.val : ℤ) = r
    · by_cases hwS : (w.val : ℤ) = D.largestLabel
      · have hrS : r = D.largestLabel := by omega
        have hd2 := congrArg (MvPolynomial.pderiv w ∘ MvPolynomial.pderiv w) he
        have hL0 := D.dense_cross_resonance_two_coefficient ℓ x u hℓ hx hu w (by omega)
        rw [if_neg (by omega)] at hL0
        simp only [Function.comp_apply] at hd2
        rw [hL0, map_zero] at hd2
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add,
          show ℓ + (x + u) = D.largestLabel by change r = D.largestLabel; exact hrS,
          D.source_coordinate_product_second_derivative w hwS] at hd2
        exact (mul_ne_zero hηC (mul_ne_zero (by norm_num) hb)) hd2.symm
      · simp only [if_pos hwr, if_neg hwS, mul_zero, add_zero] at hd
        exact (mul_ne_zero hηC D.schur_ne_zero) hd.symm
    · have hwS : (w.val : ℤ) = D.largestLabel := by
        dsimp [q] at hw
        by_cases hrS : r ≤ D.largestLabel
        · rw [max_eq_right hrS] at hw
          exact hw
        · rw [max_eq_left (by omega)] at hw
          exact False.elim (hwr hw)
      simp only [if_neg hwr, if_pos hwS, zero_add] at hd
      exact (mul_ne_zero hηC
        (mul_ne_zero ((complete_ne_zero_iff _).mpr (by dsimp [r]; omega)) hb)) hd.symm
  · have hMq : q ≤ M := by omega
    let z : ℕ+ := ⟨M.toNat, by dsimp [M]; omega⟩
    have hz : (z.val : ℤ) = M := by dsimp [z]; dsimp [M]; omega
    have hd := congrArg (MvPolynomial.pderiv z) he
    rw [D.dense_cross_resonance_two_coefficient ℓ x u hℓ hx hu z (by omega),
      if_pos hz, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
      zero_mul, zero_add,
      D.source_coordinate_product_coefficient r z (by omega) (by omega)] at hd
    by_cases hrM : r = M
    · by_cases hSM : D.largestLabel = M
      · have hd2 := congrArg (MvPolynomial.pderiv z ∘ MvPolynomial.pderiv z) he
        simp only [Function.comp_apply] at hd2
        rw [D.dense_cross_resonance_two_second_derivative ℓ x u hℓ hx hu z hz] at hd2
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add,
          show ℓ + (x + u) = D.largestLabel by change r = D.largestLabel; omega,
          D.source_coordinate_product_second_derivative z (by omega)] at hd2
        exact (mul_ne_zero hηC (mul_ne_zero (by norm_num) hb)) hd2.symm
      · simp only [if_pos (show (z.val : ℤ) = r by omega),
          if_neg (show (z.val : ℤ) ≠ D.largestLabel by omega), mul_zero, add_zero] at hd
        let e : ℕ+ := ⟨ℓ.toNat, by omega⟩
        have heℓ : (e.val : ℤ) = ℓ := by dsimp [e]; omega
        have hde := congrArg (eraseGenerator e) hd
        rw [map_neg, map_mul, map_mul, eraseGenerator_complete, if_pos heℓ.symm,
          zero_mul, neg_zero] at hde
        have hCfix : eraseGenerator e (MvPolynomial.C η : CompleteRing) = MvPolynomial.C η := by
          simp [eraseGenerator]
        rw [hCfix] at hde
        exact (mul_ne_zero hηC
          (D.connected_erased_ne_zero (hD.connected (by omega)) e)) hde.symm
    · by_cases hSM : D.largestLabel = M
      · simp only [if_neg (show (z.val : ℤ) ≠ r by omega),
          if_pos (show (z.val : ℤ) = D.largestLabel by omega), zero_add] at hd
        let e : ℕ+ := ⟨ℓ.toNat, by omega⟩
        have heℓ : (e.val : ℤ) = ℓ := by dsimp [e]; omega
        have hde := congrArg (eraseGenerator e) hd
        rw [map_neg, map_mul, map_mul, map_mul, eraseGenerator_complete,
          eraseGenerator_complete, if_pos heℓ.symm, if_neg (by dsimp [r]; omega),
          zero_mul, neg_zero] at hde
        have hCfix : eraseGenerator e (MvPolynomial.C η : CompleteRing) = MvPolynomial.C η := by
          simp [eraseGenerator]
        rw [hCfix] at hde
        exact (mul_ne_zero hηC
          (mul_ne_zero ((complete_ne_zero_iff _).mpr (by dsimp [r]; omega))
            (D.dense_four_corner_erased_ne_zero hD e))) hde.symm
      · simp only [if_neg (show (z.val : ℤ) ≠ r by omega),
          if_neg (show (z.val : ℤ) ≠ D.largestLabel by omega),
          mul_zero, add_zero] at hd
        exact (neg_ne_zero.mpr (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hc)) hd

/-- `eq:cross-resonance-two`, with both signs excluded uniformly. -/
theorem dense_cross_resonance_two (D : BetaDiagram 4) (hD : D.Dense)
    (ℓ x u : ℤ) (hℓ : 0 < ℓ) (hx : ℓ < x) (hu : 0 < u) :
    (complete (ℓ + u) * D.endpointDifference x (by omega) -
      complete ℓ * D.endpointDifference (x + u) (by omega) ≠
        complete (ℓ + (x + u)) * D.schur) ∧
    (complete (ℓ + u) * D.endpointDifference x (by omega) -
      complete ℓ * D.endpointDifference (x + u) (by omega) ≠
        -(complete (ℓ + (x + u)) * D.schur)) := by
  constructor
  · simpa using D.dense_cross_resonance_two_scalar hD ℓ x u hℓ hx hu 1 one_ne_zero
  · simpa using D.dense_cross_resonance_two_scalar hD ℓ x u hℓ hx hu (-1)
      (neg_ne_zero.mpr one_ne_zero)

end BetaDiagram
end SkewJacobiNegative
