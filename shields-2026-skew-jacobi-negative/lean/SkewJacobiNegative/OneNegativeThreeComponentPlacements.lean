/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.DenseThreeComponentPlacements
import SkewJacobiNegative.LowNegativeRigidity
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Cast

/-!
# One-negative four-row placement inputs

Actual finite-alphabet responses and the minimum-square lower-term obstruction
in `lem:one-negative-four-lower` of `shields-2026-skew-jacobi-negative.tex`.
The generic placement diagrams are the same actual diagrams used for dense cores.
-/

namespace SkewJacobiNegative
open scoped BigOperators

/-- Evaluate the genuine finite alphabet at all ones, after the symmetric specialization. -/
noncomputable def finiteOnes (b : ℕ) : CompleteRing →+* ℚ :=
  (MvPolynomial.eval (fun _ : Fin b => (1 : ℚ))).comp (finiteSpecialization b).toRingHom

/-- Evaluation counts the actual complete-homogeneous monomials. -/
theorem finiteOnes_complete_nat (b k : ℕ) :
    finiteOnes b (complete (k : ℤ)) = (Fintype.card (Sym (Fin b) k) : ℚ) := by
  simp [finiteOnes, finiteSpecialization_complete_nat, MvPolynomial.hsymm,
    ← Multiset.prod_hom']

/-- The rank-two alphabet response is exactly `j+1` at every nonnegative index. -/
theorem finiteOnes_two_complete (j : ℤ) (hj : 0 ≤ j) :
    finiteOnes 2 (complete j) = (j : ℚ) + 1 := by
  have he : (j.toNat : ℤ) = j := by omega
  rw [← he, finiteOnes_complete_nat]
  simp only [Sym.card_sym_eq_multichoose, Fintype.card_fin, Nat.multichoose_two,
    Nat.cast_add, Nat.cast_one]
  push_cast
  rfl

/-- The rank-three response is the virtual quadratic at every nonnegative index. -/
theorem finiteOnes_three_complete (j : ℤ) (hj : 0 ≤ j) :
    finiteOnes 3 (complete j) = ((j : ℚ) + 1) * ((j : ℚ) + 2) / 2 := by
  have he : (j.toNat : ℤ) = j := by omega
  rw [← he, finiteOnes_complete_nat, Sym.card_sym_eq_choose]
  have hn : Fintype.card (Fin 3) + j.toNat - 1 = j.toNat + 2 := by simp; omega
  rw [hn, Nat.choose_symm_add, Nat.cast_choose_two]
  push_cast
  ring

/-- The virtual rank-three response is also correct at the two negative indices `-1,-2`. -/
theorem finiteOnes_three_complete_ge_neg_two (j : ℤ) (hj : -2 ≤ j) :
    finiteOnes 3 (complete j) = ((j : ℚ) + 1) * ((j : ℚ) + 2) / 2 := by
  by_cases h : 0 ≤ j
  · exact finiteOnes_three_complete j h
  · have he : j = -1 ∨ j = -2 := by omega
    rcases he with rfl | rfl <;> norm_num [complete_of_neg, finiteOnes]

/-- A corrected affine index matrix still has determinant zero in four rows. -/
theorem corrected_affine_four_det_zero (a b : Fin 4 → ℚ) :
    (Matrix.of fun i j : Fin 4 => if i = 3 ∧ j = 0 then 0 else a i - b j + 1).det = 0 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Matrix.of_apply]
  norm_num [Fin.succAbove, Fin.lt_def]
  ring

/-- The virtual quadratic index matrix has rank at most three, without a determinant oracle. -/
theorem quadratic_four_det_zero (a b : Fin 4 → ℚ) :
    (Matrix.of fun i j : Fin 4 =>
      (a i - b j + 1) * (a i - b j + 2) / 2).det = 0 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Matrix.of_apply]
  norm_num [Fin.succAbove, Fin.lt_def]
  ring

/-- The actual three-row one-negative rank-two response, including its sign. -/
theorem corrected_affine_three_det (a b c d e f : ℚ) :
    (Matrix.of ![![a-d+1,a-e+1,a-f+1],
      ![b-d+1,b-e+1,b-f+1], ![0,c-e+1,c-f+1]]).det =
      (d-c-1) * (a-b) * (e-f) := by
  simp [Matrix.det_fin_three]
  ring

/-- The exact virtual rank-three determinant, with both Vandermonde products retained. -/
theorem quadratic_three_det (a b : Fin 3 → ℚ) :
    (Matrix.of fun i j : Fin 3 =>
      (a i - b j + 1) * (a i - b j + 2) / 2).det =
      (a 0-a 1) * (a 0-a 2) * (a 1-a 2) *
        (b 0-b 1) * (b 0-b 2) * (b 1-b 2) / 4 := by
  simp [Matrix.det_fin_three]
  ring

namespace BetaDiagram
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

/-- The one-negative source has its only negative entry at the actual southwest site. -/
theorem one_negative_site_iff (Q : BetaDiagram (n + 1)) (hN : negativeCount Q = 1)
    (i j : Fin (n + 1)) : Q.row i < Q.col j ↔ i = Fin.last n ∧ j = 0 := by
  constructor
  · intro h
    by_contra hn
    have hoff : i ≠ Fin.last n ∨ j ≠ 0 := by tauto
    exact not_lt_of_ge (Q.nonnegative_off_southwest_of_one_negative hN.le i j hoff) h
  · rintro ⟨rfl, rfl⟩
    exact Q.southwest_negative_of_one_negative hN

/-- Correcting the unique southwest entry gives the actual two-variable matrix. -/
theorem one_negative_four_twoVariable_zero (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) : finiteOnes 2 Q.schur = 0 := by
  have hm : (finiteOnes 2).mapMatrix Q.matrix =
      Matrix.of (fun i j : Fin 4 => if i = 3 ∧ j = 0 then 0 else
        (Q.row i : ℚ) - (Q.col j : ℚ) + 1) := by
    apply Matrix.ext
    intro i j
    by_cases h : i = 3 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩
      have hn : Q.row 3 - Q.col 0 < 0 :=
        sub_neg.mpr (Q.southwest_negative_of_one_negative hN)
      simp [matrix, complete_of_neg hn]
    · have hoff : i ≠ Fin.last 3 ∨ j ≠ 0 := by simpa using (not_and_or.mp h)
      have hp := Q.nonnegative_off_southwest_of_one_negative hN.le i j hoff
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, matrix, Matrix.of_apply,
        finiteOnes_two_complete _ (sub_nonneg.mpr hp), if_neg h]
      push_cast
      rfl
  rw [schur, RingHom.map_det, hm]
  exact corrected_affine_four_det_zero _ _

/-- The true rank-two response kills both endpoint functions, at every positive shift. -/
theorem one_negative_four_endpoint_twoVariable_zero (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (t : ℤ) (ht : 0 < t) :
    finiteOnes 2 (Q.endpointDifference t ht) = 0 := by
  unfold endpointDifference
  rw [map_sub,
    (Q.extendTop t ht).one_negative_four_twoVariable_zero
      (by rw [extendTop_negativeCount]; exact hN),
    (Q.extendBottom t ht).one_negative_four_twoVariable_zero
      (by rw [extendBottom_negativeCount]; exact hN), sub_self]

/-- At southwest gap one or two, the uncorrected quadratic matrix is already exact. -/
theorem one_negative_four_threeVariable_zero (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (hgap : Q.col 0 - Q.row 3 ≤ 2) :
    finiteOnes 3 Q.schur = 0 := by
  have hm : (finiteOnes 3).mapMatrix Q.matrix =
      Matrix.of (fun i j : Fin 4 =>
        ((Q.row i : ℚ) - (Q.col j : ℚ) + 1) *
          ((Q.row i : ℚ) - (Q.col j : ℚ) + 2) / 2) := by
    apply Matrix.ext
    intro i j
    have hp : -2 ≤ Q.row i - Q.col j := by
      by_cases h : i = 3 ∧ j = 0
      · rcases h with ⟨rfl, rfl⟩; omega
      · have hoff : i ≠ Fin.last 3 ∨ j ≠ 0 := by simpa using (not_and_or.mp h)
        have hh := Q.nonnegative_off_southwest_of_one_negative hN.le i j hoff
        omega
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, matrix, Matrix.of_apply,
      finiteOnes_three_complete_ge_neg_two _ hp]
    push_cast
    rfl
  rw [schur, RingHom.map_det, hm]
  exact quadratic_four_det_zero _ _

/-- The rank-three endpoint response uses the same unchanged southwest gap. -/
theorem one_negative_four_endpoint_threeVariable_zero (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (hgap : Q.col 0 - Q.row 3 ≤ 2)
    (t : ℤ) (ht : 0 < t) : finiteOnes 3 (Q.endpointDifference t ht) = 0 := by
  unfold endpointDifference
  rw [map_sub,
    (Q.extendTop t ht).one_negative_four_threeVariable_zero
      (by rw [extendTop_negativeCount]; exact hN)
      (by simpa [extendTop] using hgap),
    (Q.extendBottom t ht).one_negative_four_threeVariable_zero
      (by rw [extendBottom_negativeCount]; exact hN)
      (by simpa [extendBottom] using hgap), sub_self]

/-- The original coefficient-one diagonal monomial has coefficient one in the full polynomial. -/
theorem schur_diagonal_coefficient (Q : BetaDiagram n) :
    Q.schur.coeff Q.diagonalExponent = 1 := by
  have h := Q.square_initial_coefficient
  rw [Base.initialForm, MvPolynomial.coeff_weightedHomogeneousComponent] at h
  split_ifs at h with hw
  · exact h
  · exact (zero_ne_one h).elim

/-- Its monomial weight is exactly the least source weight. -/
theorem leastWeight_eq_diagonal (Q : BetaDiagram n) :
    Base.leastWeight Base.squareWeight.generatorWeight Q.schur =
      Finsupp.weight Base.squareWeight.generatorWeight Q.diagonalExponent := by
  have h := Q.square_initial_coefficient
  rw [Base.initialForm, MvPolynomial.coeff_weightedHomogeneousComponent] at h
  split_ifs at h with hw
  · exact hw.symm
  · exact (zero_ne_one h).elim

/-- A smaller diagonal weight cannot occur in another Schur polynomial. -/
theorem schur_diagonal_coefficient_zero_of_smaller_weight
    (Q : BetaDiagram n) (R : BetaDiagram k)
    (h : Base.leastWeight Base.squareWeight.generatorWeight Q.schur <
      Base.leastWeight Base.squareWeight.generatorWeight R.schur) :
    R.schur.coeff Q.diagonalExponent = 0 := by
  by_contra hn
  have hb := Base.leastWeight_lowerBound Base.squareWeight.generatorWeight R.schur
    Q.diagonalExponent hn
  rw [← Q.leastWeight_eq_diagonal] at hb
  linarith

/-- Diagonal square weights are the sum of the actual row-length squares. -/
theorem diagonal_square_weight (Q : BetaDiagram n) :
    Finsupp.weight Base.squareWeight.generatorWeight Q.diagonalExponent =
      ∑ i : Fin n, ((Q.rowLength i : ℤ) : ℝ) ^ 2 := by
  have hexp : ∀ l : List ℕ,
      Finsupp.weight Base.squareWeight.generatorWeight (Base.exponentVector l) =
        (l.map (fun k : ℕ => (k : ℝ) ^ 2)).sum := by
    intro l
    induction l with
    | nil => simp [Base.exponentVector]
    | cons a l ih =>
      simp only [Base.exponentVector, List.map_cons, List.sum_cons, map_add]
      change Finsupp.weight Base.squareWeight.generatorWeight (Base.completeIndexExponent a) +
        Finsupp.weight Base.squareWeight.generatorWeight (Base.exponentVector l) = _
      rw [ih]
      congr 1
      by_cases ha : 0 < a
      · simp [Base.completeIndexExponent, ha, Finsupp.weight_single,
          Base.ConvexWeight.generatorWeight, Base.squareWeight]
      · have hz : a = 0 := by omega
        simp [hz, Base.completeIndexExponent]
  rw [diagonalExponent_eq_rowLengths,hexp,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hp := Q.rowLength_pos i
  have hc : ((Q.rowLength i).toNat : ℝ) = ((Q.rowLength i : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hp.le)
  dsimp only [Function.comp_apply]
  rw [hc]

/-- The two endpoint initial weights differ by the end-row asymmetry, exactly. -/
theorem endpoint_square_weight_difference (Q : BetaDiagram 4) (t : ℤ) (ht : 0 < t) :
    Base.leastWeight Base.squareWeight.generatorWeight (Q.extendTop t ht).schur -
      Base.leastWeight Base.squareWeight.generatorWeight (Q.extendBottom t ht).schur =
      2 * (t : ℝ) * (((Q.rowLength 0 : ℤ) : ℝ) - ((Q.rowLength 3 : ℤ) : ℝ)) := by
  rw [leastWeight_eq_diagonal, leastWeight_eq_diagonal,
    diagonal_square_weight, diagonal_square_weight]
  simp [Fin.sum_univ_succ, rowLength, extendTop, extendBottom]
  push_cast
  ring

/-- Unequal end-row lengths force a genuinely lower monomial without any density hypothesis. -/
theorem four_lower_part_of_unequal_end_rows (Q : BetaDiagram 4)
    (hend : Q.rowLength 0 ≠ Q.rowLength 3) (t : ℤ) (ht : 0 < t) :
    Q.endpointDifference t ht ≠ complete (Q.endpointKappa + t) * Q.endpointCoefficient := by
  have hw : Base.leastWeight Base.squareWeight.generatorWeight (Q.extendTop t ht).schur ≠
      Base.leastWeight Base.squareWeight.generatorWeight (Q.extendBottom t ht).schur := by
    intro h
    have hd := Q.endpoint_square_weight_difference t ht
    rw [h, sub_self] at hd
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    have hendR : (((Q.rowLength 0 : ℤ) : ℝ) - ((Q.rowLength 3 : ℤ) : ℝ)) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hend)
    exact (mul_ne_zero (mul_ne_zero (by norm_num) htR) hendR) hd.symm
  have htop : (Q.extendTop t ht).endpointKappa ≤ Q.endpointKappa + t := by
    have h₁ := le_max_left (Q.row 1-Q.col 3) (Q.row 0-Q.col 2)
    have h₂ := le_max_right (Q.row 1-Q.col 3) (Q.row 0-Q.col 2)
    simp only [endpointKappa, extendTop, Fin.succ_ne_zero, if_false, ite_true]
    omega
  have hbot : (Q.extendBottom t ht).endpointKappa ≤ Q.endpointKappa + t := by
    have h₁ := le_max_left (Q.row 1-Q.col 3) (Q.row 0-Q.col 2)
    have h₂ := le_max_right (Q.row 1-Q.col 3) (Q.row 0-Q.col 2)
    simp only [endpointKappa, extendBottom, ite_true, Fin.castSucc_ne_last, if_false]
    omega
  intro he
  rcases lt_or_gt_of_ne hw with h | h
  · have hzero := (Q.extendTop t ht).schur_diagonal_coefficient_zero_of_smaller_weight
      (Q.extendBottom t ht) h
    have hc := congrArg (fun p : CompleteRing =>
      p.coeff (Q.extendTop t ht).diagonalExponent) he
    rw [endpointDifference, MvPolynomial.coeff_sub, schur_diagonal_coefficient, hzero,
      (Q.extendTop t ht).dense_four_diagonal_coefficient_high_multiple _ htop] at hc
    norm_num at hc
  · have hzero := (Q.extendBottom t ht).schur_diagonal_coefficient_zero_of_smaller_weight
      (Q.extendTop t ht) h
    have hc := congrArg (fun p : CompleteRing =>
      p.coeff (Q.extendBottom t ht).diagonalExponent) he
    rw [endpointDifference, MvPolynomial.coeff_sub, schur_diagonal_coefficient, hzero,
      (Q.extendBottom t ht).dense_four_diagonal_coefficient_high_multiple _ hbot] at hc
    norm_num at hc

/-- Every arbitrary mate's true connected factors are identified geometrically,
without a hypothesis about its negative partition or its singleton order. -/
theorem one_negative_three_context_mate_component_motions (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (P : ThreeComponentParameters) (middle : Bool)
    {k : ℕ} (E : BetaDiagram k) (hE : E.Connected)
    (he : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur = E.schur) :
    ∃ hrow : k = 7,
      let F := E.castOrder hrow
      ∃ hP : F.PositiveCorner, F.ZeroFree ∧
        ∀ K : ComponentDecomposition (F.cornerDiagram hP),
          K.components.length = 3 ∧
          Multiset.Rel (fun X Y : Σ a : ℕ, BetaDiagram a => X.2.MotionEquivalent Y.2)
            (([⟨1, singletonDiagram P.ell P.ell_pos⟩,
              ⟨1, singletonDiagram P.m P.m_pos⟩, ⟨4, Q⟩] :
                List (Σ a : ℕ, BetaDiagram a)) : Multiset _)
            (K.components : Multiset _) := by
  obtain ⟨hrow, hP, hZF, hK⟩ := Q.three_context_mate_components hC hZ P middle E hE he
  refine ⟨hrow, hP, hZF, ?_⟩
  intro K
  have hrel := hK K
  have hcard := Multiset.card_eq_card_of_rel hrel
  refine ⟨by simpa using hcard.symm, ?_⟩
  apply hrel.mono
  intro X hX Y hY hXY
  have hXC : X.2.RotationRigid := by
    have hm : X ∈ [⟨1, singletonDiagram P.ell P.ell_pos⟩,
        ⟨1, singletonDiagram P.m P.m_pos⟩, ⟨4, Q⟩] := by simpa using hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact singletonDiagram_rigid P.ell P.ell_pos
    · exact singletonDiagram_rigid P.m P.m_pos
    · exact Q.one_negative_rigidity hC hN.le
  exact hXC Y.1 Y.2 (K.components_connected Y (by simpa using hY)) hXY.symm

/-- The three reflection equations used at the tied endpoint level imply actual symmetry. -/
theorem four_symmetric_of_reflection_gaps (Q : BetaDiagram 4)
    (ht : Q.topMargin = Q.bottomMargin)
    (hend : Q.rowLength 0 = Q.rowLength 3)
    (hinner : Q.row 1 - Q.row 2 = Q.col 1 - Q.col 2) : Q.Symmetric := by
  have htop : Q.row 0 - Q.row 1 = Q.col 2 - Q.col 3 := ht
  have he : Q.row 0 - Q.col 0 = Q.row 3 - Q.col 3 := hend
  have hr : ∀ i : Fin 4, Q.row i = Q.row 0 + Q.col 3 - Q.col i.rev := by
    intro i
    fin_cases i <;> simp <;> omega
  refine ⟨Q.row 0 + Q.col 3, hr, ?_⟩
  intro i
  have h := hr i.rev
  simp only [Fin.rev_rev] at h
  omega

/-- Nonsymmetry retains a nonzero inner-gap difference at equal end rows and tied margins. -/
theorem four_inner_gap_ne_of_nonsymmetric (Q : BetaDiagram 4)
    (ht : Q.topMargin = Q.bottomMargin)
    (hend : Q.rowLength 0 = Q.rowLength 3) (hS : ¬ Q.Symmetric) :
    (Q.row 1 - Q.row 2 : ℤ) ≠ Q.col 1 - Q.col 2 :=
  fun h => hS (Q.four_symmetric_of_reflection_gaps ht hend h)

/-- The exact affine response at every site, including its single corrected entry. -/
theorem one_negative_two_entry (Q : BetaDiagram 4) (hN : negativeCount Q = 1)
    (i j : Fin 4) :
    finiteOnes 2 (complete (Q.row i - Q.col j)) =
      if i = 3 ∧ j = 0 then 0 else (Q.row i : ℚ) - (Q.col j : ℚ) + 1 := by
  by_cases h : i = 3 ∧ j = 0
  · rcases h with ⟨rfl, rfl⟩
    have hn : Q.row 3 - Q.col 0 < 0 :=
      sub_neg.mpr (Q.southwest_negative_of_one_negative hN)
    simp [complete_of_neg hn]
  · have hoff : i ≠ Fin.last 3 ∨ j ≠ 0 := by simpa using (not_and_or.mp h)
    have hp := Q.nonnegative_off_southwest_of_one_negative hN.le i j hoff
    rw [finiteOnes_two_complete _ (sub_nonneg.mpr hp), if_neg h]
    push_cast
    rfl

/-- The exact quadratic response at every site when the southwest gap is one or two. -/
theorem one_negative_three_entry (Q : BetaDiagram 4) (hN : negativeCount Q = 1)
    (hg : Q.col 0 - Q.row 3 ≤ 2) (i j : Fin 4) :
    finiteOnes 3 (complete (Q.row i - Q.col j)) =
      ((Q.row i : ℚ) - (Q.col j : ℚ) + 1) *
        ((Q.row i : ℚ) - (Q.col j : ℚ) + 2) / 2 := by
  have hp : -2 ≤ Q.row i - Q.col j := by
    by_cases h : i = 3 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩; omega
    · have hoff : i ≠ Fin.last 3 ∨ j ≠ 0 := by simpa using (not_and_or.mp h)
      have hh := Q.nonnegative_off_southwest_of_one_negative hN.le i j hoff
      omega
  rw [finiteOnes_three_complete_ge_neg_two _ hp]
  push_cast
  rfl

/-- The top endpoint cofactor's true rank-two response. -/
theorem one_negative_two_top_cofactor (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) :
    finiteOnes 2 (Q.cofactor 0 2) =
      ((Q.col 0 : ℚ)-(Q.row 3 : ℚ)-1) *
        ((Q.row 1 : ℚ)-(Q.row 2 : ℚ)) *
        ((Q.col 1 : ℚ)-(Q.col 3 : ℚ)) := by
  rw [cofactor, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  simp only [Matrix.det_fin_three, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    matrix, Matrix.of_apply]
  simp only [Q.one_negative_two_entry hN]
  norm_num [Fin.succAbove, Fin.lt_def]
  ring

/-- The bottom endpoint cofactor's true rank-two response. -/
theorem one_negative_two_bottom_cofactor (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) :
    finiteOnes 2 (Q.cofactor 1 3) =
      ((Q.col 0 : ℚ)-(Q.row 3 : ℚ)-1) *
        ((Q.row 0 : ℚ)-(Q.row 2 : ℚ)) *
        ((Q.col 1 : ℚ)-(Q.col 2 : ℚ)) := by
  rw [cofactor, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  simp only [Matrix.det_fin_three, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    matrix, Matrix.of_apply]
  simp only [Q.one_negative_two_entry hN]
  norm_num [Fin.succAbove, Fin.lt_def]
  ring

/-- The top cofactor retains both Vandermonde factors under rank-three evaluation. -/
theorem one_negative_three_top_cofactor (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (hg : Q.col 0 - Q.row 3 ≤ 2) :
    finiteOnes 3 (Q.cofactor 0 2) =
      ((Q.row 1 : ℚ)-(Q.row 2 : ℚ)) *
        ((Q.row 1 : ℚ)-(Q.row 3 : ℚ)) *
        ((Q.row 2 : ℚ)-(Q.row 3 : ℚ)) *
        ((Q.col 0 : ℚ)-(Q.col 1 : ℚ)) *
        ((Q.col 0 : ℚ)-(Q.col 3 : ℚ)) *
        ((Q.col 1 : ℚ)-(Q.col 3 : ℚ)) / 4 := by
  rw [cofactor, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  simp only [Matrix.det_fin_three, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    matrix, Matrix.of_apply]
  simp only [Q.one_negative_three_entry hN hg]
  norm_num [Fin.succAbove, Fin.lt_def]
  ring

theorem one_negative_three_bottom_cofactor (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (hg : Q.col 0 - Q.row 3 ≤ 2) :
    finiteOnes 3 (Q.cofactor 1 3) =
      ((Q.row 0 : ℚ)-(Q.row 2 : ℚ)) *
        ((Q.row 0 : ℚ)-(Q.row 3 : ℚ)) *
        ((Q.row 2 : ℚ)-(Q.row 3 : ℚ)) *
        ((Q.col 0 : ℚ)-(Q.col 1 : ℚ)) *
        ((Q.col 0 : ℚ)-(Q.col 2 : ℚ)) *
        ((Q.col 1 : ℚ)-(Q.col 2 : ℚ)) / 4 := by
  rw [cofactor, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  simp only [Matrix.det_fin_three, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    matrix, Matrix.of_apply]
  simp only [Q.one_negative_three_entry hN hg]
  norm_num [Fin.succAbove, Fin.lt_def]
  ring

theorem four_endpointCoefficient_eq_sites (Q : BetaDiagram 4) :
    Q.endpointCoefficient =
      (if Q.row 0-Q.col 2 = Q.endpointKappa then Q.cofactor 0 2 else 0) -
      (if Q.row 1-Q.col 3 = Q.endpointKappa then Q.cofactor 1 3 else 0) := by
  simpa only [show (Fin.last 2).castSucc = (2 : Fin 4) by decide,
    show (0 : Fin 3).succ = (1 : Fin 4) by decide,
    show Fin.last 3 = (3 : Fin 4) by decide] using Q.endpointCoefficient_eq_sites

/-- At a tied endpoint level the rank-two response is the exact inner-gap obstruction. -/
theorem one_negative_two_tied_coefficient (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (ht : Q.topMargin = Q.bottomMargin) :
    finiteOnes 2 Q.endpointCoefficient =
      ((Q.col 0 : ℚ)-(Q.row 3 : ℚ)-1) *
        ((Q.col 2 : ℚ)-(Q.col 3 : ℚ)) *
        (((Q.row 1 : ℚ)-(Q.row 2 : ℚ))-((Q.col 1 : ℚ)-(Q.col 2 : ℚ))) := by
  have he₁ : Q.row 0-Q.col 2 = Q.endpointKappa :=
    (Q.endpointKappa_eq_col_offset ht.ge).symm
  have he₂ : Q.row 1-Q.col 3 = Q.endpointKappa :=
    (Q.endpointKappa_eq_row_offset ht.le).symm
  rw [four_endpointCoefficient_eq_sites, if_pos he₁, if_pos he₂, map_sub,
    one_negative_two_top_cofactor Q hN, one_negative_two_bottom_cofactor Q hN]
  have he : (Q.row 0 : ℚ) = (Q.row 1 : ℚ)+(Q.col 2 : ℚ)-(Q.col 3 : ℚ) := by
    have hh : Q.row 0-Q.row 1 = Q.col 2-Q.col 3 := ht
    exact_mod_cast (show Q.row 0 = Q.row 1+Q.col 2-Q.col 3 by omega)
  rw [he]
  ring

/-- The exceptional southwest gap one has a nonzero rank-three tied response. -/
theorem one_negative_three_tied_coefficient (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (ht : Q.topMargin = Q.bottomMargin)
    (hend : Q.rowLength 0 = Q.rowLength 3) (hg : Q.col 0-Q.row 3 = 1) :
    finiteOnes 3 Q.endpointCoefficient =
      ((Q.row 2 : ℚ)-(Q.row 3 : ℚ)) *
        ((Q.col 0 : ℚ)-(Q.col 1 : ℚ)) *
        ((Q.row 1 : ℚ)-(Q.row 3 : ℚ)) *
        ((Q.row 0 : ℚ)-(Q.row 3 : ℚ)) *
        ((Q.col 2 : ℚ)-(Q.col 3 : ℚ)) *
        (((Q.row 1 : ℚ)-(Q.row 2 : ℚ))-((Q.col 1 : ℚ)-(Q.col 2 : ℚ))) / 4 := by
  have he₁ : Q.row 0-Q.col 2 = Q.endpointKappa :=
    (Q.endpointKappa_eq_col_offset ht.ge).symm
  have he₂ : Q.row 1-Q.col 3 = Q.endpointKappa :=
    (Q.endpointKappa_eq_row_offset ht.le).symm
  rw [four_endpointCoefficient_eq_sites, if_pos he₁, if_pos he₂, map_sub,
    one_negative_three_top_cofactor _ hN (by omega),
    one_negative_three_bottom_cofactor _ hN (by omega)]
  have htop : Q.row 0-Q.row 1 = Q.col 2-Q.col 3 := ht
  have hend' : Q.row 0-Q.col 0 = Q.row 3-Q.col 3 := hend
  have e₀ : (Q.col 0 : ℚ) = (Q.row 3 : ℚ)+1 := by
    exact_mod_cast (show Q.col 0 = Q.row 3+1 by omega)
  have e₁ : (Q.row 0 : ℚ) = 2*(Q.row 3 : ℚ)+1-(Q.col 3 : ℚ) := by
    exact_mod_cast (show Q.row 0 = 2*Q.row 3+1-Q.col 3 by omega)
  have e₂ : (Q.row 1 : ℚ) =
      2*(Q.row 3 : ℚ)+1-(Q.col 2 : ℚ) := by
    exact_mod_cast (show Q.row 1 = 2*Q.row 3+1-Q.col 2 by omega)
  rw [e₀, e₁, e₂]
  ring

/-- Beta gaps remain strictly positive after rational casting. -/
private theorem row_gap_rat_pos (Q : BetaDiagram 4) (i j : Fin 4) (h : i < j) :
    0 < (Q.row i : ℚ)-(Q.row j : ℚ) := by
  exact sub_pos.mpr (by exact_mod_cast Q.row_strictAnti h)

private theorem col_gap_rat_pos (Q : BetaDiagram 4) (i j : Fin 4) (h : i < j) :
    0 < (Q.col i : ℚ)-(Q.col j : ℚ) := by
  exact sub_pos.mpr (by exact_mod_cast Q.col_strictAnti h)

/-- Rank-two evaluation sees the fixed leader whenever the southwest gap is not one. -/
theorem one_negative_two_coefficient_ne_zero (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (hS : ¬ Q.Symmetric)
    (hend : Q.rowLength 0 = Q.rowLength 3)
    (hg : Q.col 0-Q.row 3 ≠ 1) : finiteOnes 2 Q.endpointCoefficient ≠ 0 := by
  have hgap : (Q.col 0 : ℚ)-(Q.row 3 : ℚ)-1 ≠ 0 := by
    intro h
    apply hg
    exact_mod_cast (show (Q.col 0 : ℚ)-(Q.row 3 : ℚ) = 1 by linarith)
  have ht₁ : finiteOnes 2 (Q.cofactor 0 2) ≠ 0 := by
    rw [one_negative_two_top_cofactor _ hN]
    exact mul_ne_zero (mul_ne_zero hgap
      (Q.row_gap_rat_pos 1 2 (by decide)).ne')
      (Q.col_gap_rat_pos 1 3 (by decide)).ne'
  have ht₂ : finiteOnes 2 (Q.cofactor 1 3) ≠ 0 := by
    rw [one_negative_two_bottom_cofactor _ hN]
    exact mul_ne_zero (mul_ne_zero hgap
      (Q.row_gap_rat_pos 0 2 (by decide)).ne')
      (Q.col_gap_rat_pos 1 2 (by decide)).ne'
  by_cases ht : Q.topMargin = Q.bottomMargin
  · rw [Q.one_negative_two_tied_coefficient hN ht]
    have hc : ((Q.row 1 : ℚ)-(Q.row 2 : ℚ))-
        ((Q.col 1 : ℚ)-(Q.col 2 : ℚ)) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast Q.four_inner_gap_ne_of_nonsymmetric ht hend hS)
    exact mul_ne_zero (mul_ne_zero hgap
      (Q.col_gap_rat_pos 2 3 (by decide)).ne') hc
  · rw [four_endpointCoefficient_eq_sites, map_sub]
    rcases lt_or_gt_of_ne ht with ht | ht
    · have he₁ : Q.row 0-Q.col 2 ≠ Q.endpointKappa := by
        rw [endpointKappa_eq_row_offset _ ht.le]
        change Q.row 0-Q.col 2 ≠ Q.row 1-Q.col 3
        have hh : Q.row 0-Q.row 1 < Q.col 2-Q.col 3 := ht
        omega
      have he₂ : Q.row 1-Q.col 3 = Q.endpointKappa :=
        (Q.endpointKappa_eq_row_offset ht.le).symm
      simpa [he₁, he₂] using neg_ne_zero.mpr ht₂
    · have he₁ : Q.row 0-Q.col 2 = Q.endpointKappa :=
        (Q.endpointKappa_eq_col_offset ht.le).symm
      have he₂ : Q.row 1-Q.col 3 ≠ Q.endpointKappa := by
        rw [endpointKappa_eq_col_offset _ ht.le]
        change Q.row 1-Q.col 3 ≠ Q.row 0-Q.col 2
        have hh : Q.col 2-Q.col 3 < Q.row 0-Q.row 1 := ht
        omega
      simpa [he₁, he₂] using ht₁

/-- Rank-three evaluation sees the fixed leader in the southwest-gap-one case. -/
theorem one_negative_three_coefficient_ne_zero (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (hS : ¬ Q.Symmetric)
    (hend : Q.rowLength 0 = Q.rowLength 3) (hg : Q.col 0-Q.row 3 = 1) :
    finiteOnes 3 Q.endpointCoefficient ≠ 0 := by
  have ht₁ : finiteOnes 3 (Q.cofactor 0 2) ≠ 0 := by
    rw [one_negative_three_top_cofactor _ hN (by omega)]
    apply div_ne_zero _ (by norm_num)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (Q.row_gap_rat_pos 1 2 (by decide)).ne'
        (Q.row_gap_rat_pos 1 3 (by decide)).ne')
      (Q.row_gap_rat_pos 2 3 (by decide)).ne')
      (Q.col_gap_rat_pos 0 1 (by decide)).ne')
      (Q.col_gap_rat_pos 0 3 (by decide)).ne')
      (Q.col_gap_rat_pos 1 3 (by decide)).ne'
  have ht₂ : finiteOnes 3 (Q.cofactor 1 3) ≠ 0 := by
    rw [one_negative_three_bottom_cofactor _ hN (by omega)]
    apply div_ne_zero _ (by norm_num)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (Q.row_gap_rat_pos 0 2 (by decide)).ne'
        (Q.row_gap_rat_pos 0 3 (by decide)).ne')
      (Q.row_gap_rat_pos 2 3 (by decide)).ne')
      (Q.col_gap_rat_pos 0 1 (by decide)).ne')
      (Q.col_gap_rat_pos 0 2 (by decide)).ne')
      (Q.col_gap_rat_pos 1 2 (by decide)).ne'
  by_cases ht : Q.topMargin = Q.bottomMargin
  · rw [Q.one_negative_three_tied_coefficient hN ht hend hg]
    have hc : ((Q.row 1 : ℚ)-(Q.row 2 : ℚ))-
        ((Q.col 1 : ℚ)-(Q.col 2 : ℚ)) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast Q.four_inner_gap_ne_of_nonsymmetric ht hend hS)
    apply div_ne_zero _ (by norm_num)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (Q.row_gap_rat_pos 2 3 (by decide)).ne'
        (Q.col_gap_rat_pos 0 1 (by decide)).ne')
      (Q.row_gap_rat_pos 1 3 (by decide)).ne')
      (Q.row_gap_rat_pos 0 3 (by decide)).ne')
      (Q.col_gap_rat_pos 2 3 (by decide)).ne') hc
  · rw [four_endpointCoefficient_eq_sites, map_sub]
    rcases lt_or_gt_of_ne ht with ht | ht
    · have he₁ : Q.row 0-Q.col 2 ≠ Q.endpointKappa := by
        rw [endpointKappa_eq_row_offset _ ht.le]
        change Q.row 0-Q.col 2 ≠ Q.row 1-Q.col 3
        have hh : Q.row 0-Q.row 1 < Q.col 2-Q.col 3 := ht
        omega
      have he₂ : Q.row 1-Q.col 3 = Q.endpointKappa :=
        (Q.endpointKappa_eq_row_offset ht.le).symm
      simpa [he₁, he₂] using neg_ne_zero.mpr ht₂
    · have he₁ : Q.row 0-Q.col 2 = Q.endpointKappa :=
        (Q.endpointKappa_eq_col_offset ht.le).symm
      have he₂ : Q.row 1-Q.col 3 ≠ Q.endpointKappa := by
        rw [endpointKappa_eq_col_offset _ ht.le]
        change Q.row 1-Q.col 3 ≠ Q.row 0-Q.col 2
        have hh : Q.col 2-Q.col 3 < Q.row 0-Q.row 1 := ht
        omega
      simpa [he₁, he₂] using ht₁

/-- `eq:one-negative-four-remainder`, uniformly in the actual source parameters. -/
theorem one_negative_four_lower_part (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1) (hS : ¬ Q.Symmetric) (t : ℤ) (ht : 0 < t) :
    Q.endpointDifference t ht ≠ complete (Q.endpointKappa+t) * Q.endpointCoefficient := by
  by_cases hend : Q.rowLength 0 = Q.rowLength 3
  · by_cases hg : Q.col 0-Q.row 3 = 1
    · intro he
      have h := congrArg (finiteOnes 3) he
      rw [Q.one_negative_four_endpoint_threeVariable_zero hN (by omega) t ht,
        map_mul, finiteOnes_three_complete _ (by have := Q.endpointKappa_pos; omega)] at h
      have hp : ((Q.endpointKappa+t : ℤ) : ℚ)+1 > 0 := by
        have hk := Q.endpointKappa_pos
        exact_mod_cast (show 0 < Q.endpointKappa+t+1 by omega)
      have hq : ((Q.endpointKappa+t : ℤ) : ℚ)+2 > 0 := by
        have hk := Q.endpointKappa_pos
        exact_mod_cast (show 0 < Q.endpointKappa+t+2 by omega)
      exact mul_ne_zero (div_ne_zero (mul_ne_zero hp.ne' hq.ne') (by norm_num))
        (Q.one_negative_three_coefficient_ne_zero hN hS hend hg) h.symm
    · intro he
      have h := congrArg (finiteOnes 2) he
      rw [Q.one_negative_four_endpoint_twoVariable_zero hN t ht,
        map_mul, finiteOnes_two_complete _ (by have := Q.endpointKappa_pos; omega)] at h
      have hp : ((Q.endpointKappa+t : ℤ) : ℚ)+1 > 0 := by
        have hk := Q.endpointKappa_pos
        exact_mod_cast (show 0 < Q.endpointKappa+t+1 by omega)
      exact mul_ne_zero hp.ne'
        (Q.one_negative_two_coefficient_ne_zero hN hS hend hg) h.symm
  · exact Q.four_lower_part_of_unequal_end_rows hend t ht

/-- The true three-row maximal child has no coordinate divisor. -/
theorem one_negative_four_corner_erased_ne_zero (D : BetaDiagram 4)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1)
    (w : ℕ+) : eraseGenerator w D.cornerCoefficient ≠ 0 := by
  let hP := D.positiveCorner_of_connected_zeroFree hC hZ
  have hK := D.corner_connected_of_one_negative hN.le hP
  rw [cornerCoefficient, ← D.cornerDiagram_schur hP, map_mul]
  exact mul_ne_zero (by simp) ((D.cornerDiagram hP).connected_erased_ne_zero hK w)

/-- `eq:cross-resonance-one` for the actual one-negative core, including symmetric cores. -/
theorem one_negative_cross_resonance_one (D : BetaDiagram 4)
    (hDC : D.Connected) (hDZ : D.ZeroFree) (hDN : negativeCount D = 1)
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
        (D.connected_erased_ne_zero hDC z))) hh
  have hcoeff := D.endpointCoefficient_ne_zero_one_negative hDC hDZ hDN hS
  let k := max (D.largestLabel + x)
    (max (ℓ + (x + u)) (D.endpointKappa + (x + u)))
  have hκ := D.endpointKappa_pos
  have hk : 0 < k := by
    dsimp [k]
    have := le_max_left (D.largestLabel + x)
      (max (ℓ + (x + u)) (D.endpointKappa + (x + u)))
    have := D.largestLabel_pos
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
  have hf := D.connected_erased_ne_zero hDC z
  have hb := D.one_negative_four_corner_erased_ne_zero hDC hDZ hDN z
  by_cases hPA : (w.val : ℤ) = D.largestLabel + x
  · by_cases hPB : (w.val : ℤ) = ℓ + (x + u)
    · by_cases hPC : (w.val : ℤ) = D.endpointKappa + (x + u)
      · have heS : ℓ + u = D.largestLabel := by omega
        have heκ : ℓ = D.endpointKappa := by omega
        simp only [if_pos hPA, if_pos hPB, if_pos hPC] at hd
        have hc := congrArg (fun p : CompleteRing => p.coeff D.diagonalExponent) hd
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_zero,
          D.schur_diagonal_coefficient, heS, heκ,
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
        exact (neg_ne_zero.mpr (D.connected_erased_ne_zero hDC s)) he
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

/-- The second cross resonance excludes every nonzero scalar response for a one-negative core. -/
theorem one_negative_cross_resonance_two_scalar (D : BetaDiagram 4)
    (hDC : D.Connected) (hDZ : D.ZeroFree) (hDN : negativeCount D = 1)
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
  have hc := D.endpointCoefficient_ne_zero_one_negative hDC hDZ hDN hSym
  have hb : D.cornerCoefficient ≠ 0 := by
    intro hz
    exact D.one_negative_four_corner_erased_ne_zero hDC hDZ hDN 1 (by rw [hz, map_zero])
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
        change MvPolynomial.pderiv w (MvPolynomial.pderiv w _) =
          MvPolynomial.pderiv w (MvPolynomial.pderiv w _) at hd2
        rw [hL0, map_zero] at hd2
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add, show ℓ+(x+u) = D.largestLabel by dsimp [r] at hrS; exact hrS,
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
      D.source_coordinate_product_coefficient _ z (by omega) (by omega)] at hd
    by_cases hrM : r = M
    · by_cases hSM : D.largestLabel = M
      · have hd2 := congrArg (MvPolynomial.pderiv z ∘ MvPolynomial.pderiv z) he
        change MvPolynomial.pderiv z (MvPolynomial.pderiv z _) =
          MvPolynomial.pderiv z (MvPolynomial.pderiv z _) at hd2
        rw [D.dense_cross_resonance_two_second_derivative ℓ x u hℓ hx hu z hz] at hd2
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
          zero_mul, zero_add, show ℓ+(x+u) = D.largestLabel by dsimp [r] at *; omega,
          D.source_coordinate_product_second_derivative z (by omega)] at hd2
        exact (mul_ne_zero hηC (mul_ne_zero (by norm_num) hb)) hd2.symm
      · simp only [if_pos (show (z.val : ℤ) = ℓ+(x+u) by dsimp [r,M] at *; omega),
          if_neg (show (z.val : ℤ) ≠ D.largestLabel by omega), mul_zero, add_zero] at hd
        let e : ℕ+ := ⟨ℓ.toNat, by omega⟩
        have heℓ : (e.val : ℤ) = ℓ := by dsimp [e]; omega
        have hde := congrArg (eraseGenerator e) hd
        rw [map_neg, map_mul, map_mul, eraseGenerator_complete, if_pos heℓ.symm,
          zero_mul, neg_zero] at hde
        have hCfix : eraseGenerator e (MvPolynomial.C η : CompleteRing) = MvPolynomial.C η := by
          simp [eraseGenerator]
        rw [hCfix] at hde
        exact (mul_ne_zero hηC (D.connected_erased_ne_zero hDC e)) hde.symm
    · by_cases hSM : D.largestLabel = M
      · simp only [if_neg (show (z.val : ℤ) ≠ ℓ+(x+u) by dsimp [r,M] at *; omega),
          if_pos (show (z.val : ℤ) = D.largestLabel by omega), zero_add] at hd
        let e : ℕ+ := ⟨ℓ.toNat, by omega⟩
        have heℓ : (e.val : ℤ) = ℓ := by dsimp [e]; omega
        have hde := congrArg (eraseGenerator e) hd
        simp only [map_neg, map_mul, eraseGenerator_complete,
          if_pos heℓ.symm, if_neg (show ℓ+(x+u) ≠ (e.val : ℤ) by dsimp [r]; omega),
          zero_mul, neg_zero] at hde
        have hCfix : eraseGenerator e (MvPolynomial.C η : CompleteRing) = MvPolynomial.C η := by
          simp [eraseGenerator]
        rw [hCfix] at hde
        exact (mul_ne_zero hηC
          (mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega))
            (D.one_negative_four_corner_erased_ne_zero hDC hDZ hDN e))) hde.symm
      · simp only [if_neg (show (z.val : ℤ) ≠ ℓ+(x+u) by dsimp [r,M] at *; omega),
          if_neg (show (z.val : ℤ) ≠ D.largestLabel by omega),
          mul_zero, add_zero] at hd
        exact (neg_ne_zero.mpr (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hc)) hd

/-- Both signs in `eq:cross-resonance-two` are excluded uniformly. -/
theorem one_negative_cross_resonance_two (D : BetaDiagram 4)
    (hDC : D.Connected) (hDZ : D.ZeroFree) (hDN : negativeCount D = 1)
    (ℓ x u : ℤ) (hℓ : 0 < ℓ) (hx : ℓ < x) (hu : 0 < u) :
    (complete (ℓ + u) * D.endpointDifference x (by omega) -
      complete ℓ * D.endpointDifference (x + u) (by omega) ≠
        complete (ℓ + (x + u)) * D.schur) ∧
    (complete (ℓ + u) * D.endpointDifference x (by omega) -
      complete ℓ * D.endpointDifference (x + u) (by omega) ≠
        -(complete (ℓ + (x + u)) * D.schur)) := by
  constructor
  · simpa using D.one_negative_cross_resonance_two_scalar hDC hDZ hDN
      ℓ x u hℓ hx hu 1 one_ne_zero
  · simpa using D.one_negative_cross_resonance_two_scalar hDC hDZ hDN
      ℓ x u hℓ hx hu (-1) (neg_ne_zero.mpr one_ne_zero)

/-- The one-negative core adds exactly one inherited negative site to U's first-column strip. -/
theorem one_negative_threeComponentU_negative_iff (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u)
    (i j : Fin 5) :
    (Q.threeComponentU ell x u hℓ hx hu).row i <
        (Q.threeComponentU ell x u hℓ hx hu).col j ↔
      (2 ≤ i.val ∧ j = 0) ∨ (i = 4 ∧ j = 1) := by
  cases j using Fin.cases with
  | zero =>
    cases i using Fin.cases with
    | zero => simp [threeComponentU]; omega
    | succ i =>
      cases i using Fin.cases with
      | zero => simp [threeComponentU, extendTop]; omega
      | succ i =>
        have hr := Q.row_strictAnti.antitone (Fin.zero_le i.succ)
        simp only [threeComponentU, Fin.cons_succ, Fin.cons_zero, extendTop,
          Fin.succ_ne_zero, if_false, Fin.val_succ]
        simp
        omega
  | succ j =>
    cases i using Fin.cases with
    | zero =>
      have hc := Q.col_strictAnti.antitone (Fin.zero_le j)
      have hd := Q.row_nonempty 0
      simp only [threeComponentU, Fin.cons_zero, Fin.cons_succ]
      simp
      omega
    | succ i =>
      rw [Q.threeComponentU_negative_core_iff ell x u hℓ hx hu i j,
        Q.one_negative_site_iff hN i j]
      fin_cases i <;> fin_cases j <;> simp

/-- The hook intermediate has the actual four-site mask stated in the manuscript. -/
theorem one_negative_threeComponentU_negativeSites (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    negativeSites (Q.threeComponentU ell x u hℓ hx hu) =
      {(2,0), (3,0), (4,0), (4,1)} := by
  ext p
  rcases p with ⟨i,j⟩
  simp only [negativeSites, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Q.one_negative_threeComponentU_negative_iff hN ell x u hℓ hx hu]
  fin_cases i <;> fin_cases j <;> simp

theorem one_negative_threeComponentU_negativeCount (Q : BetaDiagram 4)
    (hN : negativeCount Q = 1)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    negativeCount (Q.threeComponentU ell x u hℓ hx hu) = 4 := by
  rw [negativeCount, Q.one_negative_threeComponentU_negativeSites hN ell x u hℓ hx hu]
  decide

/-- The one-negative source exposes every arbitrary mate's actual placement and
recovers its core up to motion, with both singleton orders retained. -/
theorem one_negative_three_context_arbitrary_mate_recovery (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (P : ThreeComponentParameters) (middle : Bool)
    {k : ℕ} (E : BetaDiagram k) (hE : E.Connected)
    (he : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur = E.schur) :
    ∃ hrow : k = 7,
      let F := E.castOrder hrow
      ∃ (R : BetaDiagram 4) (T : ThreeComponentParameters),
        R.Normalized ∧ Q.MotionEquivalent R ∧
        ((P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell)) ∧
        (F.TranslationEquivalent (R.threeEndContext T) ∨
          F.TranslationEquivalent (R.threeMiddleContext T) ∨
          F.rotate.TranslationEquivalent (R.threeEndContext T)) := by
  obtain ⟨hrow,R,T,hRN,hRC,hfun,hpair,hform⟩ :=
    Q.three_context_arbitrary_mate_recovery hC hZ P middle E hE he
  have hR := Q.one_negative_rigidity hC hN.le
  exact ⟨hrow,R,T,hRN,hR 4 R hRC hfun.symm,hpair,hform⟩

/-- The one-negative leader and rank-response lower term exclude the full final middle tie. -/
theorem one_negative_middle_final_tie_nonzero (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters)
    (htie : P.left+P.u = P.right+P.v) (hnonrot : P.left ≠ P.right ∨ P.ell ≠ P.m) :
    complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference P.left P.left_pos -
      complete P.ell * complete (P.m+P.v) *
        Q.endpointDifference P.right P.right_pos ≠ 0 :=
  Q.middle_final_tie_nonzero
    (Q.endpointCoefficient_ne_zero_one_negative hC hZ hN hS)
    (Q.one_negative_four_lower_part hN hS) P htie hnonrot

/-- The one-negative endpoint leader excludes the final end-orientation tie. -/
theorem one_negative_end_orientation_tie_nonzero (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters) :
    complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference (P.left+P.right) (by
          have := P.left_pos; have := P.right_pos; omega) -
      (threeComponentA P).schur * Q.endpointDifference P.right P.right_pos ≠ 0 :=
  Q.end_orientation_tie_nonzero
    (Q.endpointCoefficient_ne_zero_one_negative hC hZ hN hS) P

/-- The first end/middle cross tie is excluded by the actual one-negative response. -/
theorem one_negative_three_cross_first_tie_exclusion (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (P : ThreeComponentParameters) (htie : P.v = P.left+P.u)
    (R : BetaDiagram 4) (hR : R = Q ∨ R = Q.rotate) :
    -(complete P.ell * complete P.m * (R.extendBottom P.v P.v_pos).schur) ≠
      -(complete P.ell * complete (P.m+P.v) * Q.schur) +
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  apply Q.three_cross_first_tie_exclusion hC
    (Q.positiveCorner_of_connected_zeroFree hC hZ) P htie
  · have h := Q.one_negative_cross_resonance_one hC hZ hN P.ell P.left P.u P.ell_pos
      (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos
    simpa only [← htie] using h
  · exact hR

/-- The second end/middle cross tie uses the same derived one-negative resonance. -/
theorem one_negative_three_cross_second_tie_exclusion (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (P : ThreeComponentParameters) (htie : P.v = P.left+P.u)
    (R : BetaDiagram 4) (hR : R = Q ∨ R = Q.rotate) :
    -(complete P.ell * complete P.m * (R.extendBottom P.v P.v_pos).schur) +
        (threeComponentA P).schur * Q.schur ≠
      -(complete P.ell * complete (P.m+P.v) * Q.schur) +
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  apply Q.three_cross_second_tie_exclusion hC P htie
  · have h := Q.one_negative_cross_resonance_one hC hZ hN P.ell P.left P.u P.ell_pos
      (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos
    simpa only [← htie] using h
  · exact hR

/-- The actual one-negative U intermediate satisfies the exact source hook class.
No pattern or normalization is imposed on a mate. -/
theorem one_negative_threeComponentU_rotationRigid (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).RotationRigid := by
  apply (Q.threeComponentU ell x u hℓ hx hu).hook_negatives_rigidity (by omega)
    (Q.threeComponentU_connected
      (Q.positiveCorner_of_connected_zeroFree hC hZ) ell x u hℓ hx hu)
  intro i j
  rw [Q.one_negative_threeComponentU_negative_iff hN ell x u hℓ hx hu i j]
  fin_cases i <;> fin_cases j <;> simp

/-- Rotation retains the unique actual southwest negative site. -/
theorem one_negative_rotate_count (Q : BetaDiagram 4) (hN : negativeCount Q = 1) :
    negativeCount Q.rotate = 1 := by
  have hs : negativeSites Q.rotate = {(3,0)} := by
    ext p
    rcases p with ⟨i,j⟩
    simp only [negativeSites,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [Q.rotate_negative_iff,Q.one_negative_site_iff hN]
    fin_cases i <;> fin_cases j <;> simp
  rw [negativeCount,hs]
  simp

theorem one_negative_threeComponentZ_rotationRigid (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (m y v : ℤ) (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).RotationRigid := by
  have hU := Q.rotate.one_negative_threeComponentU_rotationRigid
    (Q.rotate_connected hC) (Q.rotate_zeroFree hZ) (Q.one_negative_rotate_count hN)
    m y v hm hy hv
  exact (Q.rotate.threeComponentU m y v hm hy hv).rotate.rotationRigid_shifted
    ((Q.rotate.threeComponentU m y v hm hy hv).rotationRigid_rotate hU)
    (y+v-Q.col 3)

/-- Uniform fixed-parameter end orientation rigidity for a nonsymmetric one-negative core. -/
theorem one_negative_threeEndContext_orientation_ne (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters) :
    (Q.threeEndContext P).schur ≠ (Q.rotate.threeEndContext P).schur :=
  Q.threeEndContext_orientation_ne_of_coefficient
    (Q.endpointCoefficient_ne_zero_one_negative hC hZ hN hS) P

/-- Uniform fixed-parameter middle orientation rigidity outside whole-parent rotation. -/
theorem one_negative_threeMiddleContext_orientation_ne (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters)
    (hnonrot : P.left ≠ P.right ∨ P.ell ≠ P.m ∨ P.u ≠ P.v) :
    (Q.threeMiddleContext P).schur ≠ (Q.rotate.threeMiddleContext P).schur :=
  Q.threeMiddleContext_orientation_ne_of_coefficient
    (Q.endpointCoefficient_ne_zero_one_negative hC hZ hN hS)
    (Q.one_negative_four_lower_part hN hS) P hnonrot

/-- The two actual four-row source geometries, not a bundle of unproved classification inputs. -/
def FourPlacementSource (Q : BetaDiagram 4) : Prop :=
  Q.Dense ∨ (Q.Connected ∧ Q.ZeroFree ∧ negativeCount Q = 1)

theorem FourPlacementSource.connected {Q : BetaDiagram 4} (h : Q.FourPlacementSource) :
    Q.Connected := by
  rcases h with h | h
  · exact h.connected (by omega)
  · exact h.1

theorem FourPlacementSource.zeroFree {Q : BetaDiagram 4} (h : Q.FourPlacementSource) :
    Q.ZeroFree := by
  rcases h with h | h
  · exact h.zeroFree
  · exact h.2.1

theorem FourPlacementSource.rotationRigid {Q : BetaDiagram 4} (h : Q.FourPlacementSource) :
    Q.RotationRigid := by
  rcases h with h | h
  · exact Q.rotationRigid_of_nonnegative (h.connected (by omega)) h.nonnegative
  · exact Q.one_negative_rigidity h.1 h.2.2.le

theorem FourPlacementSource.coefficient_ne_zero {Q : BetaDiagram 4}
    (h : Q.FourPlacementSource) (hS : ¬ Q.Symmetric) : Q.endpointCoefficient ≠ 0 := by
  rcases h with h | h
  · exact Q.endpointCoefficient_ne_zero_dense h hS
  · exact Q.endpointCoefficient_ne_zero_one_negative h.1 h.2.1 h.2.2 hS

theorem FourPlacementSource.lower_part {Q : BetaDiagram 4}
    (h : Q.FourPlacementSource) (hS : ¬ Q.Symmetric) (t : ℤ) (ht : 0 < t) :
    Q.endpointDifference t ht ≠ complete (Q.endpointKappa+t)*Q.endpointCoefficient := by
  rcases h with h | h
  · exact Q.dense_four_lower_part h hS t ht
  · exact Q.one_negative_four_lower_part h.2.2 hS t ht

theorem FourPlacementSource.off_southwest_nonnegative {Q : BetaDiagram 4}
    (h : Q.FourPlacementSource) (i j : Fin 4) (hoff : i ≠ 3 ∨ j ≠ 0) :
    Q.col j ≤ Q.row i := by
  rcases h with h | h
  · exact (h i j).le
  · exact Q.nonnegative_off_southwest_of_one_negative h.2.2.le i j hoff

/-- Source-family membership is recovered from Schur equality itself, not assumed of a mate. -/
theorem FourPlacementSource.of_schur_eq {Q : BetaDiagram 4}
    (hQ : Q.FourPlacementSource) (R : BetaDiagram 4) (he : Q.schur = R.schur) :
    R.FourPlacementSource := by
  have hRC : R.Connected := by
    apply R.connected_of_schur_irreducible (by omega)
    rw [← he]
    exact Q.schur_irreducible hQ.connected
  have hRZ := Q.zeroFree_of_schur_eq R hQ.connected hRC hQ.zeroFree he
  have hcount := Q.negativeCount_eq_of_schur_eq R he
  rcases hQ with hD | hN
  · have hQN : negativeCount Q = 0 := by
      unfold negativeCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hn : Q.row p.1 < Q.col p.2 := by simpa only [negativeSites,
        Finset.mem_filter,Finset.mem_univ,true_and] using hp
      exact not_lt_of_ge (hD p.1 p.2).le hn
    have hRN : negativeSites R = ∅ := by
      apply Finset.card_eq_zero.mp
      change negativeCount R = 0
      rw [← hcount,hQN]
    left
    intro i j
    have hnot : ¬ R.row i < R.col j := by
      intro h
      have hm : (i,j) ∈ negativeSites R := by simp [negativeSites,h]
      rw [hRN] at hm
      simpa using hm
    have hne := hRZ i j
    omega
  · exact Or.inr ⟨hRC,hRZ,by rw [← hcount,hN.2.2]⟩

theorem FourPlacementSource.u_rigidity {Q : BetaDiagram 4}
    (h : Q.FourPlacementSource) (ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).RotationRigid := by
  rcases h with h | h
  · exact Q.dense_threeComponentU_rotationRigid h ell x u hℓ hx hu
  · exact Q.one_negative_threeComponentU_rotationRigid h.1 h.2.1 h.2.2 ell x u hℓ hx hu

theorem FourPlacementSource.z_rigidity {Q : BetaDiagram 4}
    (h : Q.FourPlacementSource) (m y v : ℤ)
    (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).RotationRigid := by
  rcases h with h | h
  · exact Q.dense_threeComponentZ_rotationRigid h m y v hm hy hv
  · exact Q.one_negative_threeComponentZ_rotationRigid h.1 h.2.1 h.2.2 m y v hm hy hv

theorem FourPlacementSource.cross_two_scalar {Q : BetaDiagram 4}
    (h : Q.FourPlacementSource) (s x u : ℤ)
    (hs : 0 < s) (hx : s < x) (hu : 0 < u) (η : ℚ) (hη : η ≠ 0) :
    complete (s+u)*Q.endpointDifference x (by omega) -
      complete s*Q.endpointDifference (x+u) (by omega) ≠
        MvPolynomial.C η*(complete (s+(x+u))*Q.schur) := by
  rcases h with h | h
  · exact Q.dense_cross_resonance_two_scalar h s x u hs hx hu η hη
  · exact Q.one_negative_cross_resonance_two_scalar h.1 h.2.1 h.2.2 s x u hs hx hu η hη

/-- Equality of U functions identifies all four core rows and columns.
The source and mate patterns of the full parent play no role. -/
theorem FourPlacementSource.u_function_recovers_core {Q : BetaDiagram 4}
    (hQ : Q.FourPlacementSource) (R : BetaDiagram 4) (hR : R.FourPlacementSource)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u)
    (he : (Q.threeComponentU ell x u hℓ hx hu).schur =
      (R.threeComponentU ell x u hℓ hx hu).schur) : Q.TranslationEquivalent R := by
  let U := Q.threeComponentU ell x u hℓ hx hu
  let V := R.threeComponentU ell x u hℓ hx hu
  have hUC := Q.threeComponentU_connected
    (Q.positiveCorner_of_connected_zeroFree hQ.connected hQ.zeroFree) ell x u hℓ hx hu
  have hVC := R.threeComponentU_connected
    (R.positiveCorner_of_connected_zeroFree hR.connected hR.zeroFree) ell x u hℓ hx hu
  have hrigid := hQ.u_rigidity ell x u hℓ hx hu
  rcases (U.rotationRigid_iff_same_order).mp hrigid V hVC he.symm with htr | hrot
  · exact Q.threeComponentU_translation_core R ell x u hℓ hx hu htr
  · obtain ⟨c,hr,hco⟩ := hrot
    have hneg : U.row 2 < U.col 0 := by
      have htop := Q.row_strictAnti (show (0 : Fin 4) < 1 by decide)
      change Q.row 1 < Q.row 0+x-ell
      omega
    have hweak : V.col 2 ≤ V.row 4 := by
      change R.col 1 ≤ R.row 3
      exact hR.off_southwest_nonnegative 3 1 (Or.inr (by decide))
    have hr₂ := hr 2
    have hco₀ := hco 0
    change U.row 2 = c-V.col 2 at hr₂
    change U.col 0 = c-V.row 4 at hco₀
    omega

/-- The exceptional M₂/M₀ comparison is excluded for every source core orientation.
It is a comparison of actual U functions, not a marker certificate. -/
theorem FourPlacementSource.u_ne_scalar_tied_response {Q : BetaDiagram 4}
    (hQ : Q.FourPlacementSource) (R : BetaDiagram 4) (hfun : Q.schur = R.schur)
    (s x u : ℤ) (hs : 0 < s) (hx : s < x) (hu : 0 < u) (η : ℚ) (hη : η ≠ 0) :
    (Q.threeComponentU s x u hs hx hu).schur ≠
      (R.threeComponentU s x u hs hx hu).schur+
        MvPolynomial.C η*(complete (s+(x+u))*R.schur) := by
  have hR := hQ.of_schur_eq R hfun
  have hcore := (Q.rotationRigid_iff_same_order).mp hQ.rotationRigid R hR.connected hfun.symm
  have hn : MvPolynomial.C η*(complete (s+(x+u))*R.schur) ≠ 0 :=
    mul_ne_zero (MvPolynomial.C_ne_zero.mpr hη)
      (mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega)) R.schur_ne_zero)
  intro he
  rcases hcore with htr | hrot
  · have hU := (Q.threeComponentU_of_core_translation R htr s x u hs hx hu).schur_eq
    rw [hU] at he
    apply hn
    linear_combination -he
  · have htr := (Q.translation_rotate_iff_rotation R).mpr hrot
    have hU := (Q.threeComponentU_of_core_translation R.rotate htr s x u hs hx hu).schur_eq
    rw [hU,threeComponentU_schur,threeComponentU_schur,
      rotate_extendTop_schur,rotate_extendTop_schur] at he
    apply hR.cross_two_scalar s x u hs hx hu (-η) (neg_ne_zero.mpr hη)
    unfold endpointDifference
    rw [MvPolynomial.C_neg]
    linear_combination -he

/-- The common span, first marker, and singleton data are consequences of full
parent equality.  The comparison core's source geometry is recovered as well. -/
theorem placement_common_data (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters) (b c : Bool)
    (he : (if b then Q.threeMiddleContext P else Q.threeEndContext P).schur =
      (if c then R.threeMiddleContext T else R.threeEndContext T).schur) :
    R.FourPlacementSource ∧ Q.schur = R.schur ∧ Q.largestLabel = R.largestLabel ∧
      ((P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell)) ∧
      min P.u P.v = min T.u T.v ∧
      P.left+P.right+P.u+P.v = T.left+T.right+T.u+T.v ∧
      (let D := if b then Q.threeMiddleContext P else Q.threeEndContext P
       let E := if c then R.threeMiddleContext T else R.threeEndContext T
       MvPolynomial.pderiv D.borderSecondGenerator
          (eraseGenerator D.borderLargestGenerator D.schur) =
         MvPolynomial.pderiv E.borderSecondGenerator
          (eraseGenerator E.borderLargestGenerator E.schur)) := by
  have hrec := three_context_core_recovery Q R hQ.connected P T b c he
  have hR := hQ.of_schur_eq R hrec.2.1
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hrec.2.1
  have hq := three_context_min_margin_recovery Q R hQ.connected hR.connected P T b c he
  let D := if b then Q.threeMiddleContext P else Q.threeEndContext P
  let E := if c then R.threeMiddleContext T else R.threeEndContext T
  have hDC : D.Connected := by
    cases b <;> simp only [D,Bool.false_eq_true,if_false,if_true]
    · exact Q.threeEndContext_connected P
    · exact Q.threeMiddleContext_connected P
  have hEC : E.Connected := by
    cases c <;> simp only [E,Bool.false_eq_true,if_false,if_true]
    · exact R.threeEndContext_connected T
    · exact R.threeMiddleContext_connected T
  have hN := D.largestLabel_eq_of_schur_eq E hDC hEC he
  have hDN : D.largestLabel = Q.largestLabel+P.left+P.right+P.u+P.v := by
    cases b <;> simp [D]
  have hEN : E.largestLabel = R.largestLabel+T.left+T.right+T.u+T.v := by
    cases c <;> simp [E]
  have htotal : P.left+P.right+P.u+P.v = T.left+T.right+T.u+T.v := by
    rw [hDN,hEN,hS] at hN
    omega
  have hDm : min D.topMargin D.bottomMargin = min P.u P.v := by
    cases b <;> simp [D,threeEndContext,threeMiddleContext,singletonContext]
  have hEm : min E.topMargin E.bottomMargin = min T.u T.v := by
    cases c <;> simp [E,threeEndContext,threeMiddleContext,singletonContext]
  have hsecond : D.secondLabel = E.secondLabel := by
    unfold secondLabel
    rw [hN,hDm,hEm,hq]
  have hGN : D.borderLargestGenerator = E.borderLargestGenerator := by
    apply Subtype.ext
    simp only [borderLargestGenerator,hN]
  have hGK : D.borderSecondGenerator = E.borderSecondGenerator := by
    apply Subtype.ext
    simp only [borderSecondGenerator,hsecond]
  refine ⟨hR,hrec.2.1,hS,hrec.2.2,hq,htotal,?_⟩
  have hmarker := congrArg (fun p : CompleteRing =>
    MvPolynomial.pderiv D.borderSecondGenerator (eraseGenerator D.borderLargestGenerator p)) he
  change MvPolynomial.pderiv D.borderSecondGenerator
      (eraseGenerator D.borderLargestGenerator D.schur) =
    MvPolynomial.pderiv E.borderSecondGenerator
      (eraseGenerator E.borderLargestGenerator E.schur)
  rw [hGN,hGK]
  simpa only [hGN,hGK] using hmarker

end BetaDiagram
end SkewJacobiNegative

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- The first middle marker after cancelling its actual connected core factor. -/
noncomputable def middleFirstResponse (P : ThreeComponentParameters) : CompleteRing :=
  if P.u = P.v then
    complete P.m * complete (P.ell + P.u) +
      complete P.ell * complete (P.m + P.u)
  else complete P.m * complete (P.ell + P.u)

theorem threeMiddleContext_first_response (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (huv : P.u ≤ P.v) :
    let D := Q.threeMiddleContext P
    MvPolynomial.pderiv D.borderSecondGenerator
      (eraseGenerator D.borderLargestGenerator D.schur) =
        -(Q.schur * middleFirstResponse P) := by
  dsimp only
  have heq :
      MvPolynomial.pderiv (Q.threeMiddleContext P).borderSecondGenerator
        (eraseGenerator (Q.threeMiddleContext P).borderLargestGenerator
          (Q.threeMiddleContext P).schur) =
      MvPolynomial.pderiv
        ((Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderSecondGenerator
        (eraseGenerator
          ((Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderLargestGenerator
          (Q.threeMiddleContext P).schur) := by
    simp only [threeMiddleContext, singletonContext, shifted_borderLargestGenerator,
      shifted_borderSecondGenerator, threeMiddleCore]
  rw [heq]
  by_cases ht : P.u = P.v
  · rw [Q.threeMiddleContext_tied_marker P ht, middleFirstResponse, if_pos ht]
  · rw [Q.threeMiddleContext_top_marker P (by omega), middleFirstResponse, if_neg ht]
    ring

/-- The first markers of independently parameterized actual middle parents agree. -/
theorem threeMiddleContext_first_response_eq (Q R : BetaDiagram 4)
    (hQ : Q.Connected) (hR : R.Connected) (P T : ThreeComponentParameters)
    (hP : P.u ≤ P.v) (hT : T.u ≤ T.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    P.u = T.u ∧ middleFirstResponse P = middleFirstResponse T := by
  have hfun := (three_context_core_recovery Q R hQ P T true true he).2.1
  have hmin := three_context_min_margin_recovery Q R hQ hR P T true true he
  simp only [min_eq_left hP, min_eq_left hT] at hmin
  let D := Q.threeMiddleContext P
  let E := R.threeMiddleContext T
  have hl := D.largestLabel_eq_of_schur_eq E
    (Q.threeMiddleContext_connected P) (R.threeMiddleContext_connected T) he
  have hPm := Q.threeMiddleContext_margins P
  have hTm := R.threeMiddleContext_margins T
  have hs : D.secondLabel = E.secondLabel := by
    unfold secondLabel
    rw [hPm.1,hPm.2,hTm.1,hTm.2,min_eq_left hP,min_eq_left hT,hl,hmin]
  have hg : D.borderLargestGenerator = E.borderLargestGenerator := by
    apply Subtype.ext
    simp only [borderLargestGenerator, hl]
  have hsg : D.borderSecondGenerator = E.borderSecondGenerator := by
    apply Subtype.ext
    simp only [borderSecondGenerator, hs]
  have hd := Q.threeMiddleContext_first_response P hP
  have ht := R.threeMiddleContext_first_response T hT
  dsimp only at hd ht
  have hmarkers : -(Q.schur * middleFirstResponse P) =
      -(R.schur * middleFirstResponse T) := by
    rw [← hd, ← ht]
    change MvPolynomial.pderiv D.borderSecondGenerator
      (eraseGenerator D.borderLargestGenerator D.schur) =
      MvPolynomial.pderiv E.borderSecondGenerator
      (eraseGenerator E.borderLargestGenerator E.schur)
    rw [hg, hsg, he]
  refine ⟨hmin, mul_left_cancel₀ Q.schur_ne_zero ?_⟩
  rw [← hfun] at hmarkers
  exact neg_injective hmarkers

/-- This evaluation uses independent complete coordinates, not a finite alphabet. -/
theorem middleFirstResponse_ones (P : ThreeComponentParameters) :
    MvPolynomial.eval (fun _ => (1 : ℚ)) (middleFirstResponse P) =
      if P.u = P.v then 2 else 1 := by
  have ha : 0 < P.ell + P.u := by have := P.ell_pos; have := P.u_pos; omega
  have hb : 0 < P.m + P.u := by have := P.m_pos; have := P.u_pos; omega
  unfold middleFirstResponse
  split_ifs <;>
    norm_num [complete_of_pos P.ell_pos, complete_of_pos P.m_pos,
      complete_of_pos ha, complete_of_pos hb]

/-- Strict and tied middle regimes do not mix; a strict marker fixes the singleton order. -/
theorem threeMiddleContext_first_alignment (Q R : BetaDiagram 4)
    (hQ : Q.Connected) (hR : R.Connected) (P T : ThreeComponentParameters)
    (hP : P.u ≤ P.v) (hT : T.u ≤ T.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    P.u = T.u ∧ (P.u = P.v ↔ T.u = T.v) ∧
      (P.u < P.v → P.ell = T.ell ∧ P.m = T.m) := by
  obtain ⟨hu, hr⟩ := threeMiddleContext_first_response_eq Q R hQ hR P T hP hT he
  have hp := congrArg (MvPolynomial.eval (fun _ => (1 : ℚ))) hr
  rw [middleFirstResponse_ones, middleFirstResponse_ones] at hp
  have hphase : P.u = P.v ↔ T.u = T.v := by
    by_cases h₁ : P.u = P.v <;> by_cases h₂ : T.u = T.v <;> simp_all
  refine ⟨hu, hphase, ?_⟩
  intro hstrict
  have hPn : P.u ≠ P.v := ne_of_lt hstrict
  have hTn : T.u ≠ T.v := by intro h; exact hPn (hphase.mpr h)
  rw [middleFirstResponse, middleFirstResponse, if_neg hPn, if_neg hTn] at hr
  have hpair := (three_context_core_recovery Q R hQ P T true true he).2.2
  have ha : 0 < P.ell + P.u := by have := P.ell_pos; have := P.u_pos; omega
  have hb : 0 < T.ell + T.u := by have := T.ell_pos; have := T.u_pos; omega
  have hext := singleton_pair_recovery P.m (P.ell + P.u)
    T.m (T.ell + T.u) P.m_pos ha T.m_pos hb hr
  rcases hpair with ⟨hℓ, hm⟩ | ⟨hℓ, hm⟩
  · exact ⟨hℓ, hm⟩
  · rcases hext with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨by omega, hx⟩
    · have := P.u_pos
      omega

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- Both exterior residual contributions survive when their levels coincide. -/
theorem four_border_residual_response (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (k : ℕ+)
    (hkw : Q.largestLabel + w ≤ (k.val : ℤ))
    (hkv : Q.largestLabel + v ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.positiveBorder w v hw hv).cornerResidual =
      (if (k.val : ℤ) = Q.largestLabel + w then -(Q.extendBottom v hv).schur else 0) +
      (if (k.val : ℤ) = Q.largestLabel + v then -(Q.extendTop w hw).schur else 0) := by
  by_cases hew : (k.val : ℤ) = Q.largestLabel + w
  · rcases lt_trichotomy v w with h | h | h
    · have hne : (k.val : ℤ) ≠ Q.largestLabel + v := by omega
      rw [if_pos hew, if_neg hne, add_zero]
      exact Q.four_border_residual_bottom w v hw hv h k hew
    · subst v
      have hg : k = (Q.positiveBorder w w hw hw).borderSecondGenerator := by
        apply Subtype.ext
        apply Int.ofNat.inj
        change (k.val : ℤ) = ((Q.positiveBorder w w hw hw).borderSecondGenerator.val : ℤ)
        rw [borderSecondGenerator_int, four_border_secondLabel, max_self]
        exact hew
      rw [if_pos hew, if_pos hew, hg, ← positiveBorder_erased_corner,
        positiveBorder_second_derivative_erased,
        SkewJacobiNegative.FourRowBorders.BetaDiagram.positiveBorder_tied_first_derivative]
      norm_num <;> ring
    · omega
  · by_cases hev : (k.val : ℤ) = Q.largestLabel + v
    · rw [if_neg hew, if_pos hev, zero_add]
      exact Q.four_border_residual_top w v hw hv (by omega) k hev
    · rw [if_neg hew, if_neg hev, zero_add]
      apply Q.four_border_residual_above w v hw hv k
      apply max_lt <;> omega

/-- The four private-corner terms removed in the moving-separation comparison. -/
noncomputable def middleCornerLeadingPart (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : CompleteRing :=
  Q.schur *
    (complete (P.ell + P.u) * complete (P.m + P.v) *
        complete (Q.largestLabel + P.left + P.right) -
      complete P.ell * complete (P.m + P.v) *
        complete (Q.largestLabel + P.left + P.right + P.u) -
      complete (P.ell + P.u) * complete P.m *
        complete (Q.largestLabel + P.left + P.right + P.v) +
      complete P.ell * complete P.m *
        complete (Q.largestLabel + P.left + P.right + P.u + P.v))

noncomputable def middleCornerRemainder (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : CompleteRing :=
  complete (P.ell + P.u) * complete (P.m + P.v) *
      (Q.positiveBorder P.left P.right P.left_pos P.right_pos).cornerResidual -
    complete P.ell * complete (P.m + P.v) *
      (Q.positiveBorder (P.left + P.u) P.right
        (by have := P.left_pos; have := P.u_pos; omega) P.right_pos).cornerResidual -
    complete (P.ell + P.u) * complete P.m *
      (Q.positiveBorder P.left (P.right + P.v) P.left_pos
        (by have := P.right_pos; have := P.v_pos; omega)).cornerResidual +
    complete P.ell * complete P.m *
      (Q.positiveBorder (P.left + P.u) (P.right + P.v)
        (by have := P.left_pos; have := P.u_pos; omega)
        (by have := P.right_pos; have := P.v_pos; omega)).cornerResidual

theorem threeMiddleContext_corner_expansion (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).schur =
      middleCornerLeadingPart Q P + middleCornerRemainder Q P := by
  have hLu : 0 < P.left + P.u := by have := P.left_pos; have := P.u_pos; omega
  have hRv : 0 < P.right + P.v := by have := P.right_pos; have := P.v_pos; omega
  rw [threeMiddleContext_schur,
    Q.four_border_corner_split P.left P.right P.left_pos P.right_pos,
    Q.four_border_corner_split (P.left + P.u) P.right hLu P.right_pos,
    Q.four_border_corner_split P.left (P.right + P.v) P.left_pos hRv,
    Q.four_border_corner_split (P.left + P.u) (P.right + P.v) hLu hRv]
  have h₂ : Q.largestLabel + (P.left + P.u) + P.right =
      Q.largestLabel + P.left + P.right + P.u := by ring
  have h₃ : Q.largestLabel + P.left + (P.right + P.v) =
      Q.largestLabel + P.left + P.right + P.v := by ring
  have h₄ : Q.largestLabel + (P.left + P.u) + (P.right + P.v) =
      Q.largestLabel + P.left + P.right + P.u + P.v := by ring
  rw [h₂, h₃, h₄]
  unfold middleCornerLeadingPart middleCornerRemainder
  ring

/-- Actual residual response at or above both moving exterior levels. -/
theorem middleCornerRemainder_response (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (k : ℕ+)
    (hkL : Q.largestLabel + (P.left + P.u) ≤ (k.val : ℤ))
    (hkR : Q.largestLabel + (P.right + P.v) ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k (middleCornerRemainder Q P) =
      (if (k.val : ℤ) = Q.largestLabel + (P.left + P.u) then
        complete P.ell *
          (Q.threeComponentZ P.m P.right P.v P.m_pos
            (by have := P.g₂_pos; unfold ThreeComponentParameters.right; omega) P.v_pos).schur
        else 0) +
      (if (k.val : ℤ) = Q.largestLabel + (P.right + P.v) then
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur
        else 0) := by
  have hS := Q.largestLabel_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hLu : 0 < P.left + P.u := by have := P.left_pos; omega
  have hRv : 0 < P.right + P.v := by have := P.right_pos; omega
  have hLne : (k.val : ℤ) ≠ Q.largestLabel + P.left := by omega
  have hRne : (k.val : ℤ) ≠ Q.largestLabel + P.right := by omega
  have hd₁ := Q.four_border_residual_above P.left P.right P.left_pos P.right_pos k
    (by apply max_lt <;> omega)
  have hd₂ := Q.four_border_residual_response (P.left + P.u) P.right hLu P.right_pos k
    hkL (by omega)
  have hd₃ := Q.four_border_residual_response P.left (P.right + P.v) P.left_pos hRv k
    (by omega) hkR
  have hd₄ := Q.four_border_residual_response (P.left + P.u) (P.right + P.v) hLu hRv k
    hkL hkR
  simp only [if_neg hLne, if_neg hRne, zero_add, add_zero] at hd₂ hd₃
  have hℓ0 : MvPolynomial.pderiv k (complete P.ell) = 0 := by
    rw [pderiv_complete_label, if_neg (by unfold ThreeComponentParameters.left at hkL; omega)]
  have hm0 : MvPolynomial.pderiv k (complete P.m) = 0 := by
    rw [pderiv_complete_label, if_neg (by unfold ThreeComponentParameters.right at hkR; omega)]
  have ha0 : MvPolynomial.pderiv k (complete (P.ell + P.u)) = 0 := by
    rw [pderiv_complete_label, if_neg (by unfold ThreeComponentParameters.left at hkL; omega)]
  have hb0 : MvPolynomial.pderiv k (complete (P.m + P.v)) = 0 := by
    rw [pderiv_complete_label, if_neg (by unfold ThreeComponentParameters.right at hkR; omega)]
  rw [middleCornerRemainder, threeComponentZ_schur, threeComponentU_schur]
  simp only [map_add, map_sub, MvPolynomial.pderiv_mul, hℓ0, hm0, ha0, hb0,
    hd₁, hd₂, hd₃, hd₄, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  split_ifs <;> ring

/-- The moving-separation coefficient for independent genuine core orientations. -/
theorem threeMiddleContext_movement_response (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u) (hv : P.v = T.v)
    (hsum : P.left + P.right = T.left + T.right) (hmove : P.left < T.left) :
    let K := max (Q.largestLabel + T.left + P.u) (Q.largestLabel + P.right + P.v)
    let k : ℕ+ := ⟨K.toNat, by
      have := Q.largestLabel_pos; have := T.left_pos; have := P.u_pos
      have := le_max_left (Q.largestLabel + T.left + P.u)
        (Q.largestLabel + P.right + P.v); omega⟩
    (if (k.val : ℤ) = Q.largestLabel + T.left + P.u then
      complete P.ell *
        (R.threeComponentZ T.m T.right T.v T.m_pos
          (by have := T.g₂_pos; unfold ThreeComponentParameters.right; omega) T.v_pos).schur
      else 0) -
    (if (k.val : ℤ) = Q.largestLabel + P.right + P.v then
      complete P.m *
        (Q.threeComponentU P.ell P.left P.u P.ell_pos
          (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur
      else 0) = 0 := by
  dsimp only
  let K := max (Q.largestLabel + T.left + P.u) (Q.largestLabel + P.right + P.v)
  let k : ℕ+ := ⟨K.toNat, by
    have := Q.largestLabel_pos; have := T.left_pos; have := P.u_pos
    have := le_max_left (Q.largestLabel + T.left + P.u)
      (Q.largestLabel + P.right + P.v); omega⟩
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hk : (k.val : ℤ) = K := by
    have := Q.largestLabel_pos; have := T.left_pos; have := P.u_pos
    have := le_max_left (Q.largestLabel + T.left + P.u)
      (Q.largestLabel + P.right + P.v)
    dsimp [k, K]; omega
  have hk₁ : Q.largestLabel + T.left + P.u ≤ (k.val : ℤ) := by
    rw [hk]; exact le_max_left _ _
  have hk₂ : Q.largestLabel + P.right + P.v ≤ (k.val : ℤ) := by
    rw [hk]; exact le_max_right _ _
  have hright : T.right < P.right := by omega
  have hlead : middleCornerLeadingPart Q P = middleCornerLeadingPart R T := by
    have hb : R.largestLabel + P.left + P.right =
        R.largestLabel + T.left + T.right := by omega
    unfold middleCornerLeadingPart
    rw [hfun, hS, hℓ, hm, hu, hv, hb]
  have hrem : middleCornerRemainder R T - middleCornerRemainder Q P = 0 := by
    rw [threeMiddleContext_corner_expansion, threeMiddleContext_corner_expansion, hlead] at he
    linear_combination -he
  have hd := congrArg (MvPolynomial.pderiv k) hrem
  rw [map_sub, map_zero,
    middleCornerRemainder_response R T k (by omega) (by omega),
    middleCornerRemainder_response Q P k (by omega) (by omega)] at hd
  have hPT : (k.val : ℤ) ≠ Q.largestLabel + (P.left + P.u) := by omega
  have hTB : (k.val : ℤ) ≠ R.largestLabel + (T.right + T.v) := by omega
  simp only [if_neg hPT, if_neg hTB, zero_add, add_zero] at hd
  simpa only [k,K,← hℓ, ← hS, ← hu, add_assoc] using hd

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- The connected order-six factors in the M₂ comparison are actual singleton contexts. -/
theorem threeMiddleContext_six_row_factorization (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).schur =
      complete (P.m + P.v) *
        (Q.singletonContext P.ell P.u P.right P.g₁
          P.ell_pos P.u_pos P.right_pos P.g₁_pos).schur -
      complete P.m *
        (Q.singletonContext P.ell P.u (P.right + P.v) P.g₁
          P.ell_pos P.u_pos (by have := P.right_pos; have := P.v_pos; omega)
          P.g₁_pos).schur := by
  rw [threeMiddleContext_schur, singletonContext_schur, singletonContext_schur]
  simp only [ThreeComponentParameters.left]
  ring

/-- A coordinate factor is recovered from products with actual connected nonlinear factors. -/
theorem singleton_times_connected_recovery {n k : ℕ}
    (A : BetaDiagram (n + 2)) (B : BetaDiagram (k + 2))
    (hA : A.Connected) (hB : B.Connected)
    (s t : ℤ) (hs : 0 < s) (ht : 0 < t)
    (he : complete s * A.schur = complete t * B.schur) :
    s = t ∧ A.schur = B.schur := by
  have hd : complete s ∣ complete t * B.schur := by
    rw [← he]
    exact dvd_mul_right _ _
  have hst : s = t := by
    rcases (complete_prime s hs).dvd_mul.mp hd with h | h
    · exact (complete_dvd_complete_iff s t hs ht).mp h
    · exact False.elim (B.complete_not_dvd_connected hB s hs h)
  refine ⟨hst, ?_⟩
  rw [← hst] at he
  exact mul_left_cancel₀ ((complete_ne_zero_iff _).mpr hs.le) he

theorem singletonContext_bottom_parameter_congr (Q : BetaDiagram 4)
    (ell u g : ℤ) (hEll : 0 < ell) (hu : 0 < u) (hg : 0 < g)
    {v w : ℤ} (he : v = w) (hv : 0 < v) (hw : 0 < w) :
    (Q.singletonContext ell u v g hEll hu hv hg).schur =
      (Q.singletonContext ell u w g hEll hu hw hg).schur := by
  cases he
  rfl

theorem sub_common_polynomial_cancel (a b c : CompleteRing) (he : a-c=b-c) :
    a = b := sub_left_injective he

theorem positiveBorder_schur_parameter_congr {n : ℕ} (Q : BetaDiagram (n+2))
    {u v x y : ℤ} (he : u = x) (hf : v = y)
    (hu : 0 < u) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) :
    (Q.positiveBorder u v hu hv).schur = (Q.positiveBorder x y hx hy).schur := by
  cases he
  cases hf
  rfl

/-- The actual U recovery fixes the core, and the connected six-row factors then fix v and R. -/
theorem threeMiddleContext_remaining_right_parameters (Q R : BetaDiagram 4)
    (P T : ThreeComponentParameters)
    (hcore : Q.TranslationEquivalent R)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (hL : P.left = T.left) (hRv : P.right + P.v = T.right + T.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    P = T ∧ Q.threeMiddleContext P = R.threeMiddleContext T := by
  have hg₁ : P.g₁ = T.g₁ := by
    unfold ThreeComponentParameters.left at hL
    omega
  obtain ⟨c, hr, hc⟩ := hcore
  have hQR : Q = R.shifted c := eq_of_lists Q (R.shifted c) (funext hr) (funext hc)
  have hborder (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
      (Q.positiveBorder x y hx hy).schur = (R.positiveBorder x y hx hy).schur := by
    rw [hQR, shifted_positiveBorder, shifted_schur]
  have hctx (y : ℤ) (hy : 0 < y) :
      (Q.singletonContext P.ell P.u y P.g₁
        P.ell_pos P.u_pos hy P.g₁_pos).schur =
      (R.singletonContext T.ell T.u y T.g₁
        T.ell_pos T.u_pos hy T.g₁_pos).schur := by
    rw [singletonContext_schur, singletonContext_schur]
    rw [hborder, hborder]
    simp only [hℓ, hu, hg₁]
  have hcommon :
      (Q.singletonContext P.ell P.u (P.right + P.v) P.g₁
        P.ell_pos P.u_pos (by have := P.right_pos; have := P.v_pos; omega) P.g₁_pos).schur =
      (R.singletonContext T.ell T.u (T.right + T.v) T.g₁
        T.ell_pos T.u_pos (by have := T.right_pos; have := T.v_pos; omega) T.g₁_pos).schur := by
    rw [hctx]
    exact singletonContext_bottom_parameter_congr R T.ell T.u T.g₁
      T.ell_pos T.u_pos T.g₁_pos hRv
      (by have := P.right_pos; have := P.v_pos; omega)
      (by have := T.right_pos; have := T.v_pos; omega)
  rw [threeMiddleContext_six_row_factorization,
    threeMiddleContext_six_row_factorization, hcommon, hm] at he
  have hprod :
      complete (P.m + P.v) *
        (Q.singletonContext P.ell P.u P.right P.g₁
          P.ell_pos P.u_pos P.right_pos P.g₁_pos).schur =
      complete (T.m + T.v) *
        (R.singletonContext T.ell T.u T.right T.g₁
          T.ell_pos T.u_pos T.right_pos T.g₁_pos).schur := by
    have h := sub_common_polynomial_cancel _ _ _ he
    simpa only [hm] using h
  obtain ⟨hb, _⟩ := singleton_times_connected_recovery _ _
    (Q.singletonContext_connected P.ell P.u P.right P.g₁
      P.ell_pos P.u_pos P.right_pos P.g₁_pos)
    (R.singletonContext_connected T.ell T.u T.right T.g₁
      T.ell_pos T.u_pos T.right_pos T.g₁_pos)
    (P.m + P.v) (T.m + T.v)
    (by have := P.m_pos; have := P.v_pos; omega)
    (by have := T.m_pos; have := T.v_pos; omega) hprod
  have hv : P.v = T.v := by omega
  have hg₂ : P.g₂ = T.g₂ := by
    unfold ThreeComponentParameters.right at hRv
    omega
  have hPT := threeComponentParameters_eq_of_fields P T hℓ hm hg₁ hg₂ hu hv
  refine ⟨hPT, ?_⟩
  rw [hPT]
  exact Q.threeMiddleContext_of_core_translation R ⟨c, hr, hc⟩ T

/-- Fixed parameters recover core translation outside the whole-parent rotation configuration. -/
theorem threeMiddleContext_core_translation_at_fixed_parameters (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P : ThreeComponentParameters)
    (hnonrot : P.left ≠ P.right ∨ P.ell ≠ P.m ∨ P.u ≠ P.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext P).schur) :
    Q.TranslationEquivalent R := by
  have hfun := (three_context_core_recovery Q R hQ.connected P P true true he).2.1
  obtain htr | hrot := (Q.rotationRigid_iff_same_order).mp hQ.rotationRigid
    R hR.connected hfun.symm
  · exact htr
  · by_cases hS : Q.Symmetric
    · exact Q.translation_of_rotation_of_symmetric R hS hrot
    · have hRQ := Q.rotated_core_translation R hrot
      have hp := R.threeMiddleContext_of_core_translation Q.rotate hRQ P
      have hbad : (Q.threeMiddleContext P).schur = (Q.rotate.threeMiddleContext P).schur :=
        he.trans (congrArg (fun D => D.schur) hp)
      exact (Q.threeMiddleContext_orientation_ne_of_coefficient
        (hQ.coefficient_ne_zero hS) (hQ.lower_part hS) P hnonrot hbad).elim

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

theorem threeMiddleContext_total_extent_recovery (Q R : BetaDiagram 4)
    (hQ : Q.Connected) (P T : ThreeComponentParameters)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    Q.largestLabel + P.left + P.right + P.u + P.v =
      R.largestLabel + T.left + T.right + T.u + T.v := by
  have h := (Q.threeMiddleContext P).largestLabel_eq_of_schur_eq
    (R.threeMiddleContext T) (Q.threeMiddleContext_connected P)
    (R.threeMiddleContext_connected T) he
  simpa only [threeMiddleContext_largestLabel] using h

/-- The two removed leading terms agree after the first marker has aligned its singleton data. -/
theorem threeMiddleContext_shared_leading_eq (Q R : BetaDiagram 4)
    (hQ : Q.Connected) (P T : ThreeComponentParameters)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    Q.threeSharedLeadingPart P = R.threeSharedLeadingPart T := by
  have hfun := (three_context_core_recovery Q R hQ P T true true he).2.1
  have hN := threeMiddleContext_total_extent_recovery Q R hQ P T he
  have hN' : Q.largestLabel + P.left + P.right + P.v =
      R.largestLabel + T.left + T.right + T.v := by omega
  unfold threeSharedLeadingPart
  rw [hN,hN',hfun,hℓ,hm,hu]

/-- Generalized third response also gives the vanishing above the prescribed third level. -/
theorem threeMiddleContext_third_response_at_or_above (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (k : ℕ+)
    (hk₁ : Q.largestLabel + P.left + P.right + P.u ≤ (k.val : ℤ))
    (hk₂ : Q.largestLabel + P.right + P.v ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k
      ((Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P) =
      (if (k.val : ℤ) = Q.largestLabel + P.left + P.right + P.u then
        -(complete P.ell * complete (P.m + P.v) * Q.schur) else 0) +
      (if (k.val : ℤ) = Q.largestLabel + P.right + P.v then
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur
        else 0) := by
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hpoly : (Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P =
      middleCornerRemainder Q P + Q.schur *
        (complete (P.ell + P.u) * complete (P.m + P.v) *
            complete (Q.largestLabel + P.left + P.right) -
          complete P.ell * complete (P.m + P.v) *
            complete (Q.largestLabel + P.left + P.right + P.u)) := by
    rw [threeMiddleContext_corner_expansion]
    unfold middleCornerLeadingPart threeSharedLeadingPart
    ring
  have hf0 := Q.pderiv_schur_above k (by omega)
  have ha0 : MvPolynomial.pderiv k (complete (P.ell + P.u)) = 0 := by
    rw [pderiv_complete_label, if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  have hb0 : MvPolynomial.pderiv k (complete (P.m + P.v)) = 0 := by
    rw [pderiv_complete_label, if_neg (by unfold ThreeComponentParameters.right at hk₂; omega)]
  have hℓ0 : MvPolynomial.pderiv k (complete P.ell) = 0 := by
    rw [pderiv_complete_label, if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  have hsmall : MvPolynomial.pderiv k
      (complete (Q.largestLabel + P.left + P.right)) = 0 := by
    rw [pderiv_complete_label, if_neg (by omega)]
  have hlong : MvPolynomial.pderiv k
      (complete (Q.largestLabel + P.left + P.right + P.u)) =
      if (k.val : ℤ) = Q.largestLabel + P.left + P.right + P.u then 1 else 0 := by
    rw [pderiv_complete_label]
    simp only [eq_comm]
  have hrem := middleCornerRemainder_response Q P k (by omega) (by omega)
  have htop : (k.val : ℤ) ≠ Q.largestLabel + (P.left + P.u) := by omega
  rw [if_neg htop, zero_add] at hrem
  have hright : Q.largestLabel + (P.right + P.v) = Q.largestLabel + P.right + P.v := by ring
  rw [hright] at hrem
  rw [hpoly]
  simp only [map_add, map_sub, MvPolynomial.pderiv_mul, hf0, ha0, hb0, hℓ0,
    hsmall, hlong, hrem, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  split_ifs <;> ring

/-- Every third middle marker is nonzero, including M₀. -/
theorem threeMiddleContext_third_marker_ne_zero (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    MvPolynomial.pderiv (Q.threeThirdGenerator P)
      ((Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P) ≠ 0 := by
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hk : ((Q.threeThirdGenerator P).val : ℤ) =
      max (Q.largestLabel + P.left + P.right + P.u)
        (Q.largestLabel + P.right + P.v) := by
    rw [threeThirdGenerator_int, threeThirdIndex]
  rw [threeMiddleContext_third_marker]
  rcases lt_trichotomy P.v (P.left + P.u) with h | h | h
  · have hk₁ : ((Q.threeThirdGenerator P).val : ℤ) =
        Q.largestLabel + P.left + P.right + P.u := by
      rw [max_eq_left (by omega)] at hk
      exact hk
    have hk₂ : ((Q.threeThirdGenerator P).val : ℤ) ≠
        Q.largestLabel + P.right + P.v := by omega
    rw [if_pos hk₁, if_neg hk₂, add_zero]
    exact neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
        ((complete_ne_zero_iff _).mpr (by have := P.m_pos; omega))) Q.schur_ne_zero)
  · have hk₁ : ((Q.threeThirdGenerator P).val : ℤ) =
        Q.largestLabel + P.left + P.right + P.u := by
      rw [max_eq_left (by omega)] at hk
      exact hk
    have hk₂ : ((Q.threeThirdGenerator P).val : ℤ) =
        Q.largestLabel + P.right + P.v := by omega
    rw [if_pos hk₁, if_pos hk₂]
    intro hz
    apply Q.three_middle_tied_marker_not_dvd_core hQ.connected
      (Q.positiveCorner_of_connected_zeroFree hQ.connected hQ.zeroFree) P
    rw [hz]
    exact dvd_zero _
  · have hk₂ : ((Q.threeThirdGenerator P).val : ℤ) =
        Q.largestLabel + P.right + P.v := by
      rw [max_eq_right (by omega)] at hk
      exact hk
    have hk₁ : ((Q.threeThirdGenerator P).val : ℤ) ≠
        Q.largestLabel + P.left + P.right + P.u := by omega
    rw [if_neg hk₁, if_pos hk₂, zero_add]
    exact mul_ne_zero ((complete_ne_zero_iff _).mpr P.m_pos.le)
      (Q.threeComponentU P.ell P.left P.u P.ell_pos
        (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur_ne_zero

/-- The third index is recovered from full equality rather than supplied as input. -/
theorem threeMiddleContext_third_index_recovery (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    Q.threeThirdIndex P = R.threeThirdIndex T := by
  have hs := threeMiddleContext_shared_leading_eq Q R hQ.connected P T hℓ hm hu he
  have hr : (Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P =
      (R.threeMiddleContext T).schur - R.threeSharedLeadingPart T := by rw [he, hs]
  have hQ₁ : Q.largestLabel + P.left + P.right + P.u ≤ Q.threeThirdIndex P :=
    le_max_left _ _
  have hQ₂ : Q.largestLabel + P.right + P.v ≤ Q.threeThirdIndex P :=
    le_max_right _ _
  have hR₁ : R.largestLabel + T.left + T.right + T.u ≤ R.threeThirdIndex T :=
    le_max_left _ _
  have hR₂ : R.largestLabel + T.right + T.v ≤ R.threeThirdIndex T :=
    le_max_right _ _
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have hd := congrArg (MvPolynomial.pderiv (R.threeThirdGenerator T)) hr
    apply R.threeMiddleContext_third_marker_ne_zero hR T
    rw [← hd, threeMiddleContext_third_response_at_or_above Q P
      (R.threeThirdGenerator T) (by rw [threeThirdGenerator_int]; omega)
      (by rw [threeThirdGenerator_int]; omega)]
    rw [if_neg (by rw [threeThirdGenerator_int]; omega),
      if_neg (by rw [threeThirdGenerator_int]; omega), zero_add]
  · have hd := congrArg (MvPolynomial.pderiv (Q.threeThirdGenerator P)) hr
    apply Q.threeMiddleContext_third_marker_ne_zero hQ P
    rw [hd, threeMiddleContext_third_response_at_or_above R T
      (Q.threeThirdGenerator P) (by rw [threeThirdGenerator_int]; omega)
      (by rw [threeThirdGenerator_int]; omega)]
    rw [if_neg (by rw [threeThirdGenerator_int]; omega),
      if_neg (by rw [threeThirdGenerator_int]; omega), zero_add]

/-- Equality of actual third derivatives after recovery of their common index. -/
theorem threeMiddleContext_third_marker_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    MvPolynomial.pderiv (Q.threeThirdGenerator P)
      ((Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P) =
    MvPolynomial.pderiv (R.threeThirdGenerator T)
      ((R.threeMiddleContext T).schur - R.threeSharedLeadingPart T) := by
  have hs := threeMiddleContext_shared_leading_eq Q R hQ.connected P T hℓ hm hu he
  have hK := threeMiddleContext_third_index_recovery Q R hQ hR P T hℓ hm hu he
  have hg : Q.threeThirdGenerator P = R.threeThirdGenerator T := by
    apply Subtype.ext
    simp only [threeThirdGenerator, hK]
  rw [he, hs, hg]

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

noncomputable def middleU (Q : BetaDiagram 4) (P : ThreeComponentParameters) : BetaDiagram 5 :=
  Q.threeComponentU P.ell P.left P.u P.ell_pos
    (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos

theorem threeMiddleContext_third_M1 (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (h : P.v < P.left + P.u) :
    MvPolynomial.pderiv (Q.threeThirdGenerator P)
      ((Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P) =
      -(complete P.ell * complete (P.m + P.v) * Q.schur) := by
  have hk : ((Q.threeThirdGenerator P).val : ℤ) =
      Q.largestLabel + P.left + P.right + P.u := by
    rw [threeThirdGenerator_int, threeThirdIndex, max_eq_left (by omega)]
  rw [threeMiddleContext_third_marker, if_pos hk, if_neg (by omega), add_zero]

theorem threeMiddleContext_third_M2 (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (h : P.left + P.u < P.v) :
    MvPolynomial.pderiv (Q.threeThirdGenerator P)
      ((Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P) =
      complete P.m * (middleU Q P).schur := by
  have hk : ((Q.threeThirdGenerator P).val : ℤ) =
      Q.largestLabel + P.right + P.v := by
    rw [threeThirdGenerator_int, threeThirdIndex, max_eq_right (by omega)]
  rw [threeMiddleContext_third_marker, if_neg (by omega), if_pos hk, zero_add]
  rfl

theorem threeMiddleContext_third_M0 (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (h : P.v = P.left + P.u) :
    MvPolynomial.pderiv (Q.threeThirdGenerator P)
      ((Q.threeMiddleContext P).schur - Q.threeSharedLeadingPart P) =
      -(complete P.ell * complete (P.m + P.v) * Q.schur) +
        complete P.m * (middleU Q P).schur := by
  have hk₁ : ((Q.threeThirdGenerator P).val : ℤ) =
      Q.largestLabel + P.left + P.right + P.u := by
    rw [threeThirdGenerator_int, threeThirdIndex, max_eq_left (by omega)]
  have hk₂ : ((Q.threeThirdGenerator P).val : ℤ) =
      Q.largestLabel + P.right + P.v := by omega
  rw [threeMiddleContext_third_marker, if_pos hk₁, if_pos hk₂]
  rfl

/-- The exceptional M₂/M₀ comparison is excluded for independent actual middle parents. -/
theorem threeMiddleContext_M2_M0_ne (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hP : P.left + P.u < P.v) (hT : T.v = T.left + T.u) :
    (Q.threeMiddleContext P).schur ≠ (R.threeMiddleContext T).schur := by
  intro he
  have hLP := P.left_pos
  have hLT := T.left_pos
  have hpstrict : P.u < P.v := by omega
  have htstrict : T.u < T.v := by omega
  obtain ⟨hu, _, horder⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T hpstrict.le htstrict.le he
  obtain ⟨hℓ, hm⟩ := horder hpstrict
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hN := threeMiddleContext_total_extent_recovery Q R hQ.connected P T he
  have hK := threeMiddleContext_third_index_recovery Q R hQ hR P T hℓ hm hu he
  have hKP : Q.threeThirdIndex P = Q.largestLabel + P.right + P.v := by
    rw [threeThirdIndex, max_eq_right (by omega)]
  have hKT : R.threeThirdIndex T = R.largestLabel + T.right + T.v := by
    rw [threeThirdIndex, max_eq_right (by omega)]
  have hL : P.left = T.left := by rw [hKP, hKT] at hK; omega
  let U := middleU Q P
  let V := R.threeComponentU P.ell P.left P.u P.ell_pos
    (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos
  have hmark := threeMiddleContext_third_marker_eq Q R hQ hR P T hℓ hm hu he
  rw [threeMiddleContext_third_M2 Q P hP, threeMiddleContext_third_M0 R T hT] at hmark
  have hd : complete P.m * U.schur =
      -(complete P.ell * complete (P.m + T.v) * R.schur) + complete P.m * V.schur := by
    simpa only [U, V, middleU, ← hℓ, ← hm, ← hu, ← hL] using hmark
  have hdvd : complete P.m ∣ complete P.ell * complete (P.m + T.v) * R.schur := by
    apply dvd_neg.mp
    have h₁ : complete P.m ∣ complete P.m * U.schur := dvd_mul_right _ _
    rw [hd] at h₁
    have h₂ : complete P.m ∣ complete P.m * V.schur := dvd_mul_right _ _
    simpa only [add_sub_cancel_right] using dvd_sub h₁ h₂
  have hmℓ : P.m = P.ell := by
    rcases (complete_prime P.m P.m_pos).dvd_mul.mp hdvd with h | h
    · rcases (complete_prime P.m P.m_pos).dvd_mul.mp h with h | h
      · exact (complete_dvd_complete_iff P.m P.ell P.m_pos P.ell_pos).mp h
      · have hb := (complete_dvd_complete_iff P.m (P.m + T.v) P.m_pos
          (by have := T.v_pos; have := P.m_pos; omega)).mp h
        have := T.v_pos
        omega
    · exact False.elim (R.complete_not_dvd_connected hR.connected P.m P.m_pos h)
  have hlabel : P.m + T.v = P.ell + (P.left + P.u) := by omega
  apply hQ.u_ne_scalar_tied_response R hfun P.ell P.left P.u P.ell_pos
    (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos
    (-1) (by norm_num)
  apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.ell_pos.le)
  rw [hlabel, hmℓ] at hd
  change complete P.ell * U.schur =
    complete P.ell * (V.schur + MvPolynomial.C (-1) *
      (complete (P.ell + (P.left + P.u)) * R.schur))
  norm_num only [map_neg, map_one, neg_mul, one_mul]
  linear_combination hd

/-- M₂ recovers L and U, then connected six-row factorization fixes the right data. -/
theorem threeMiddleContext_M2_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hP : P.left + P.u < P.v) (hT : T.left + T.u < T.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    P = T ∧ Q.threeMiddleContext P = R.threeMiddleContext T := by
  have hLP := P.left_pos
  have hLT := T.left_pos
  have hpstrict : P.u < P.v := by omega
  have htstrict : T.u < T.v := by omega
  obtain ⟨hu, _, horder⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T hpstrict.le htstrict.le he
  obtain ⟨hℓ, hm⟩ := horder hpstrict
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hN := threeMiddleContext_total_extent_recovery Q R hQ.connected P T he
  have hK := threeMiddleContext_third_index_recovery Q R hQ hR P T hℓ hm hu he
  have hKP : Q.threeThirdIndex P = Q.largestLabel + P.right + P.v := by
    rw [threeThirdIndex, max_eq_right (by omega)]
  have hKT : R.threeThirdIndex T = R.largestLabel + T.right + T.v := by
    rw [threeThirdIndex, max_eq_right (by omega)]
  rw [hKP, hKT] at hK
  have hL : P.left = T.left := by omega
  have hRv : P.right + P.v = T.right + T.v := by omega
  have hd := threeMiddleContext_third_marker_eq Q R hQ hR P T hℓ hm hu he
  rw [threeMiddleContext_third_M2 Q P hP, threeMiddleContext_third_M2 R T hT] at hd
  have hU : (Q.threeComponentU P.ell P.left P.u P.ell_pos
      (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur =
      (R.threeComponentU P.ell P.left P.u P.ell_pos
      (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
    simpa only [middleU, ← hℓ, ← hm, ← hu, ← hL] using hd
  have hcore := hQ.u_function_recovers_core R hR P.ell P.left P.u P.ell_pos
    (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos hU
  exact threeMiddleContext_remaining_right_parameters Q R P T hcore hℓ hm hu hL hRv he

/-- M₀ fixes L,v,R and recovers the actual core translation through U. -/
theorem threeMiddleContext_M0_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hP : P.v = P.left + P.u) (hT : T.v = T.left + T.u)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    P = T ∧ Q.threeMiddleContext P = R.threeMiddleContext T := by
  have hLP := P.left_pos
  have hLT := T.left_pos
  have hpstrict : P.u < P.v := by omega
  have htstrict : T.u < T.v := by omega
  obtain ⟨hu, _, horder⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T hpstrict.le htstrict.le he
  obtain ⟨hℓ, hm⟩ := horder hpstrict
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hN := threeMiddleContext_total_extent_recovery Q R hQ.connected P T he
  have hK := threeMiddleContext_third_index_recovery Q R hQ hR P T hℓ hm hu he
  have hKP : Q.threeThirdIndex P = Q.largestLabel + P.right + P.v := by
    rw [threeThirdIndex, max_eq_right (by omega)]
  have hKT : R.threeThirdIndex T = R.largestLabel + T.right + T.v := by
    rw [threeThirdIndex, max_eq_right (by omega)]
  rw [hKP, hKT] at hK
  have hL : P.left = T.left := by omega
  have hv : P.v = T.v := by omega
  have hRR : P.right = T.right := by omega
  have hg₁ : P.g₁ = T.g₁ := by unfold ThreeComponentParameters.left at hL; omega
  have hg₂ : P.g₂ = T.g₂ := by unfold ThreeComponentParameters.right at hRR; omega
  have hPT := threeComponentParameters_eq_of_fields P T hℓ hm hg₁ hg₂ hu hv
  subst T
  have hd := threeMiddleContext_third_marker_eq Q R hQ hR P P rfl rfl rfl he
  rw [threeMiddleContext_third_M0 Q P hP,
    threeMiddleContext_third_M0 R P hT, ← hfun] at hd
  have hU : (middleU Q P).schur = (middleU R P).schur := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
    linear_combination hd
  have hcore := hQ.u_function_recovers_core R hR P.ell P.left P.u P.ell_pos
    (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos hU
  exact ⟨rfl, Q.threeMiddleContext_of_core_translation R hcore P⟩

/-- The recovered core divisor separates M₁ from M₂. -/
theorem threeMiddleContext_M1_M2_ne (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hPu : P.u < P.v)
    (hP : P.v < P.left + P.u) (hT : T.left + T.u < T.v) :
    (Q.threeMiddleContext P).schur ≠ (R.threeMiddleContext T).schur := by
  intro he
  have hLT := T.left_pos
  have hTu : T.u < T.v := by omega
  obtain ⟨hu, _, horder⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T hPu.le hTu.le he
  obtain ⟨hℓ, hm⟩ := horder hPu
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hd := threeMiddleContext_third_marker_eq Q R hQ hR P T hℓ hm hu he
  rw [threeMiddleContext_third_M1 Q P hP,
    threeMiddleContext_third_M2 R T hT] at hd
  apply R.three_middle_intermediate_marker_not_dvd_core hR.connected
    (R.positiveCorner_of_connected_zeroFree hR.connected hR.zeroFree) T
  change R.schur ∣ complete T.m * (middleU R T).schur
  rw [← hd, hfun]
  exact dvd_neg.mpr (dvd_mul_left _ _)

/-- The recovered core divisor separates M₁ from M₀. -/
theorem threeMiddleContext_M1_M0_ne (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hPu : P.u < P.v)
    (hP : P.v < P.left + P.u) (hT : T.v = T.left + T.u) :
    (Q.threeMiddleContext P).schur ≠ (R.threeMiddleContext T).schur := by
  intro he
  have hLT := T.left_pos
  have hTu : T.u < T.v := by omega
  obtain ⟨hu, _, horder⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T hPu.le hTu.le he
  obtain ⟨hℓ, hm⟩ := horder hPu
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hd := threeMiddleContext_third_marker_eq Q R hQ hR P T hℓ hm hu he
  rw [threeMiddleContext_third_M1 Q P hP,
    threeMiddleContext_third_M0 R T hT] at hd
  apply R.three_middle_tied_marker_not_dvd_core hR.connected
    (R.positiveCorner_of_connected_zeroFree hR.connected hR.zeroFree) T
  change R.schur ∣ -(complete T.ell * complete (T.m + T.v) * R.schur) +
    complete T.m * (middleU R T).schur
  rw [← hd, hfun]
  exact dvd_neg.mpr (dvd_mul_left _ _)

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- Equality of actual U and Z functions recovers both singleton/margin data
and literal rotation of the four-row cores. -/
theorem u_z_function_rotation_data (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (hfun : Q.schur = R.schur) (ell m x y u v : ℤ)
    (hℓ : 0 < ell) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    (hx : ell < x) (hy : m < y)
    (he : (Q.threeComponentU ell x u hℓ hx hu).schur =
      (R.threeComponentZ m y v hm hy hv).schur) :
    ell = m ∧ u = v ∧ x = y ∧ Q.RotationEquivalent R := by
  let U := Q.threeComponentU ell x u hℓ hx hu
  let V := R.threeComponentZ m y v hm hy hv
  have hVr (i : Fin 4) : V.row i.castSucc = R.row i+y+v-R.col 3 :=
    R.threeComponentZ_row_core m y v hm hy hv i
  have hVc (i : Fin 3) : V.col i.castSucc.castSucc = R.col i.castSucc+y+v-R.col 3 :=
    R.threeComponentZ_col_core m y v hm hy hv i
  have hVlast : V.col (Fin.last 4) = 0 := R.threeComponentZ_col_last m y v hm hy hv
  have hVpen : V.col (Fin.last 3).castSucc = v :=
    R.threeComponentZ_col_penultimate m y v hm hy hv
  have hVrowlast : V.row (Fin.last 4) = m+v := R.threeComponentZ_row_last m y v hm hy hv
  have hVC := R.threeComponentZ_connected
    (R.positiveCorner_of_connected_zeroFree hR.connected hR.zeroFree) m y v hm hy hv
  have hrigid := hQ.u_rigidity ell x u hℓ hx hu
  have hneg : U.row 2 < U.col 0 := by
    have htop := Q.row_strictAnti (show (0 : Fin 4) < 1 by decide)
    change Q.row 1 < Q.row 0+x-ell
    omega
  rcases (U.rotationRigid_iff_same_order).mp hrigid V hVC he.symm with htr | hrot
  · obtain ⟨c,hr,hco⟩ := htr
    have hweakR := hR.off_southwest_nonnegative (2 : Fin 4) 0 (Or.inl (by decide))
    have hweak : V.col 0 ≤ V.row 2 := by
      change V.col (0 : Fin 3).castSucc.castSucc ≤ V.row (2 : Fin 4).castSucc
      rw [hVc,hVr]
      change R.col 0+y+v-R.col 3 ≤ R.row 2+y+v-R.col 3
      omega
    have hr₂ := hr 2
    have hco₀ := hco 0
    omega
  · obtain ⟨c,hr,hco⟩ := hrot
    have hr₀ := hr 0
    change Q.row 0+x+u = c-V.col (Fin.last 4) at hr₀
    rw [hVlast,sub_zero] at hr₀
    have hr₁ := hr 1
    change Q.row 0+x = c-V.col (Fin.last 3).castSucc at hr₁
    rw [hVpen] at hr₁
    have huv : u = v := by omega
    have hc₀ := hco 0
    change Q.row 0+x-ell = c-V.row (Fin.last 4) at hc₀
    rw [hVrowlast] at hc₀
    have hℓm : ell = m := by omega
    have hc₄ := hco 4
    change Q.col 3 = c-V.row (0 : Fin 4).castSucc at hc₄
    rw [hVr] at hc₄
    have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
    change Q.row 0-Q.col 3 = R.row 0-R.col 3 at hS
    have hxy : x = y := by omega
    have hr₂ := hr 2
    have hr₃ := hr 3
    have hr₄ := hr 4
    change Q.row 1 = c-V.col (2 : Fin 3).castSucc.castSucc at hr₂
    change Q.row 2 = c-V.col (1 : Fin 3).castSucc.castSucc at hr₃
    change Q.row 3 = c-V.col (0 : Fin 3).castSucc.castSucc at hr₄
    rw [hVc] at hr₂ hr₃ hr₄
    change Q.row 1 = c-(R.col 2+y+v-R.col 3) at hr₂
    change Q.row 2 = c-(R.col 1+y+v-R.col 3) at hr₃
    change Q.row 3 = c-(R.col 0+y+v-R.col 3) at hr₄
    have hc₁ := hco 1
    have hc₂ := hco 2
    have hc₃ := hco 3
    change Q.col 0 = c-V.row (3 : Fin 4).castSucc at hc₁
    change Q.col 1 = c-V.row (2 : Fin 4).castSucc at hc₂
    change Q.col 2 = c-V.row (1 : Fin 4).castSucc at hc₃
    rw [hVr] at hc₁ hc₂ hc₃
    refine ⟨hℓm,huv,hxy,Q.row 0+R.col 3,?_,?_⟩
    · intro i
      fin_cases i
      · change Q.row 0 = Q.row 0+R.col 3-R.col 3
        ring
      · change Q.row 1 = Q.row 0+R.col 3-R.col 2
        omega
      · change Q.row 2 = Q.row 0+R.col 3-R.col 1
        omega
      · change Q.row 3 = Q.row 0+R.col 3-R.col 0
        omega
    · intro i
      fin_cases i
      · change Q.col 0 = Q.row 0+R.col 3-R.row 3
        omega
      · change Q.col 1 = Q.row 0+R.col 3-R.row 2
        omega
      · change Q.col 2 = Q.row 0+R.col 3-R.row 1
        omega
      · change Q.col 3 = Q.row 0+R.col 3-R.row 0
        omega

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- The parameter swap and core reflection are literal whole-parent rotation. -/
theorem threeMiddleContext_rotation (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).RotationEquivalent (Q.rotate.threeMiddleContext P.swap) := by
  refine ⟨Q.largestLabel+P.left+P.right+P.u+P.v,?_,?_⟩
  · intro i
    fin_cases i <;>
      simp [threeMiddleContext,singletonContext,singletonCore,rightSingletonCore,
        positiveBorder,rotate,shifted,largestLabel,ThreeComponentParameters.swap,
        ThreeComponentParameters.left,ThreeComponentParameters.right,
        Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.snoc,Fin.castPred,Fin.castLT] <;> ring
  · intro i
    fin_cases i <;>
      simp [threeMiddleContext,singletonContext,singletonCore,rightSingletonCore,
        positiveBorder,rotate,shifted,largestLabel,ThreeComponentParameters.swap,
        ThreeComponentParameters.left,ThreeComponentParameters.right,
        Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.snoc,Fin.castPred,Fin.castLT] <;> ring

theorem TranslationEquivalent.symm {n : ℕ} {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : E.TranslationEquivalent D := by
  obtain ⟨c,hr,hco⟩ := h
  refine ⟨-c,?_,?_⟩
  · intro i
    have h := hr i
    omega
  · intro i
    have h := hco i
    omega

theorem TranslationEquivalent.trans {n : ℕ} {D E F : BetaDiagram n}
    (h₁ : D.TranslationEquivalent E) (h₂ : E.TranslationEquivalent F) :
    D.TranslationEquivalent F := by
  obtain ⟨c,hr,hco⟩ := h₁
  obtain ⟨d,hr',hco'⟩ := h₂
  refine ⟨c+d,?_,?_⟩
  · intro i
    rw [hr i,hr' i]
    ring
  · intro i
    rw [hco i,hco' i]
    ring

theorem RotationEquivalent.symm {n : ℕ} {D E : BetaDiagram n}
    (h : D.RotationEquivalent E) : E.RotationEquivalent D := by
  obtain ⟨c,hr,hco⟩ := h
  refine ⟨c,?_,?_⟩
  · intro i
    have h := hco i.rev
    simp only [Fin.rev_rev] at h
    omega
  · intro i
    have h := hr i.rev
    simp only [Fin.rev_rev] at h
    omega

theorem motion_trans {n : ℕ} (D E F : BetaDiagram n)
    (h₁ : D.TranslationEquivalent E ∨ D.RotationEquivalent E)
    (h₂ : E.TranslationEquivalent F ∨ E.RotationEquivalent F) :
    D.TranslationEquivalent F ∨ D.RotationEquivalent F := by
  rcases h₁ with ⟨c,hr,hco⟩ | ⟨c,hr,hco⟩
  · rcases h₂ with ⟨d,hr',hco'⟩ | ⟨d,hr',hco'⟩
    · exact Or.inl (TranslationEquivalent.trans ⟨c,hr,hco⟩ ⟨d,hr',hco'⟩)
    · refine Or.inr ⟨c+d,?_,?_⟩
      · intro i
        rw [hr i,hr' i]
        ring
      · intro i
        rw [hco i,hco' i]
        ring
  · rcases h₂ with ⟨d,hr',hco'⟩ | ⟨d,hr',hco'⟩
    · refine Or.inr ⟨c-d,?_,?_⟩
      · intro i
        rw [hr i,hco' i.rev]
        ring
      · intro i
        rw [hco i,hr' i.rev]
        ring
    · refine Or.inl ⟨c-d,?_,?_⟩
      · intro i
        rw [hr i,hco' i.rev,Fin.rev_rev]
        ring
      · intro i
        rw [hco i,hr' i.rev,Fin.rev_rev]
        ring

theorem motion_symm {n : ℕ} (D E : BetaDiagram n)
    (h : D.TranslationEquivalent E ∨ D.RotationEquivalent E) :
    E.TranslationEquivalent D ∨ E.RotationEquivalent D := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- Moving-separation equality forces the complete data for whole-parent rotation. -/
theorem threeMiddleContext_moving_rotation_data (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u) (hv : P.v = T.v)
    (hsum : P.left + P.right = T.left + T.right) (hmove : P.left < T.left) :
    P.ell = P.m ∧ P.u = P.v ∧ P.left = T.right ∧ Q.RotationEquivalent R := by
  have hSpos := Q.largestLabel_pos
  have hLpos := T.left_pos
  have huPos := P.u_pos
  let a := Q.largestLabel + T.left + P.u
  let b := Q.largestLabel + P.right + P.v
  let k : ℕ+ := ⟨(max a b).toNat, by
    have := le_max_left a b
    dsimp [a] at *
    omega⟩
  have hk : (k.val : ℤ) = max a b := by
    have := le_max_left a b
    dsimp [k, a] at *
    omega
  let U := middleU Q P
  let Z := R.threeComponentZ T.m T.right T.v T.m_pos
    (by have := T.g₂_pos; unfold ThreeComponentParameters.right; omega) T.v_pos
  have hd := threeMiddleContext_movement_response Q R hQ hR P T he hℓ hm hu hv hsum hmove
  change (if (k.val : ℤ) = a then complete P.ell * Z.schur else 0) -
    (if (k.val : ℤ) = b then complete P.m * U.schur else 0) = 0 at hd
  have hab : a = b := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hkb : (k.val : ℤ) = b := by rw [max_eq_right h.le] at hk; exact hk
      have hka : (k.val : ℤ) ≠ a := by omega
      rw [if_neg hka, if_pos hkb, zero_sub] at hd
      exact neg_ne_zero.mpr (mul_ne_zero ((complete_ne_zero_iff _).mpr P.m_pos.le)
        U.schur_ne_zero) hd
    · have hka : (k.val : ℤ) = a := by rw [max_eq_left h.le] at hk; exact hk
      have hkb : (k.val : ℤ) ≠ b := by omega
      rw [if_pos hka, if_neg hkb, sub_zero] at hd
      exact mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le) Z.schur_ne_zero hd
  have hka : (k.val : ℤ) = a := by rw [← hab, max_self] at hk; exact hk
  have hkb : (k.val : ℤ) = b := hka.trans hab
  rw [if_pos hka, if_pos hkb] at hd
  have heprod : complete P.ell * Z.schur = complete P.m * U.schur := sub_eq_zero.mp hd
  have hEM : P.ell = P.m := by
    have hdiv : complete P.ell ∣ complete P.m * U.schur := by
      rw [← heprod]
      exact dvd_mul_right _ _
    rcases (complete_prime P.ell P.ell_pos).dvd_mul.mp hdiv with h | h
    · exact (complete_dvd_complete_iff P.ell P.m P.ell_pos P.m_pos).mp h
    · apply False.elim
      exact (Q.threeComponentU_complete_not_dvd
        (Q.positiveCorner_of_connected_zeroFree hQ.connected hQ.zeroFree)
        P.ell P.left P.u P.ell P.ell_pos
        (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega)
        P.u_pos P.ell_pos) h
  have hUZ : U.schur = Z.schur := by
    rw [← hEM] at heprod
    exact (mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.ell_pos.le) heprod).symm
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  obtain ⟨_, huv, hxy, hrot⟩ := u_z_function_rotation_data Q R hQ hR hfun
    P.ell T.m P.left T.right P.u T.v
    P.ell_pos T.m_pos P.u_pos T.v_pos
    (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega)
    (by have := T.g₂_pos; unfold ThreeComponentParameters.right; omega) hUZ
  exact ⟨hEM, by omega, hxy, hrot⟩

/-- With a strict minimum margin the moving-separation tie has no escape. -/
theorem threeMiddleContext_strict_fixed_margins_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hPu : P.u < P.v)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u) (hv : P.v = T.v)
    (hsum : P.left + P.right = T.left + T.right)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    P = T ∧ Q.threeMiddleContext P = R.threeMiddleContext T := by
  have hL : P.left = T.left := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hd := threeMiddleContext_moving_rotation_data Q R hQ hR P T he
        hℓ hm hu hv hsum h
      exact (ne_of_lt hPu) hd.2.1
    · have hd := threeMiddleContext_moving_rotation_data R Q hR hQ T P he.symm
        hℓ.symm hm.symm hu.symm hv.symm hsum.symm h
      have : P.u = P.v := by omega
      exact (ne_of_lt hPu) this
  have hRR : P.right = T.right := by omega
  have hg₁ : P.g₁ = T.g₁ := by unfold ThreeComponentParameters.left at hL; omega
  have hg₂ : P.g₂ = T.g₂ := by unfold ThreeComponentParameters.right at hRR; omega
  have hPT := threeComponentParameters_eq_of_fields P T hℓ hm hg₁ hg₂ hu hv
  subst T
  have hcore := threeMiddleContext_core_translation_at_fixed_parameters Q R hQ hR P
    (Or.inr (Or.inr (ne_of_lt hPu))) he
  exact ⟨rfl, Q.threeMiddleContext_of_core_translation R hcore P⟩

/-- Within M₁ the third level fixes v, and movement fixes both separations. -/
theorem threeMiddleContext_M1_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hPu : P.u < P.v) (hTu : T.u < T.v)
    (hP : P.v < P.left + P.u) (hT : T.v < T.left + T.u)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    P = T ∧ Q.threeMiddleContext P = R.threeMiddleContext T := by
  obtain ⟨hu, _, horder⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T hPu.le hTu.le he
  obtain ⟨hℓ, hm⟩ := horder hPu
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hN := threeMiddleContext_total_extent_recovery Q R hQ.connected P T he
  have hK := threeMiddleContext_third_index_recovery Q R hQ hR P T hℓ hm hu he
  have hKP : Q.threeThirdIndex P = Q.largestLabel + P.left + P.right + P.u := by
    rw [threeThirdIndex, max_eq_left (by omega)]
  have hKT : R.threeThirdIndex T = R.largestLabel + T.left + T.right + T.u := by
    rw [threeThirdIndex, max_eq_left (by omega)]
  rw [hKP, hKT] at hK
  have hv : P.v = T.v := by omega
  have hsum : P.left + P.right = T.left + T.right := by omega
  exact threeMiddleContext_strict_fixed_margins_eq Q R hQ hR P T hPu
    hℓ hm hu hv hsum he

/-- Complete strict-middle comparison after rotation aligns the smaller top margin. -/
theorem threeMiddleContext_strict_top_order_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hP : P.u < P.v) (hT : T.u ≤ T.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    Q.threeMiddleContext P = R.threeMiddleContext T := by
  obtain ⟨_, hphase, _⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T hP.le hT he
  have hTne : T.u ≠ T.v := by intro h; exact (ne_of_lt hP) (hphase.mpr h)
  have hTu : T.u < T.v := by omega
  rcases lt_trichotomy P.v (P.left + P.u) with hp | hp | hp
  · rcases lt_trichotomy T.v (T.left + T.u) with ht | ht | ht
    · exact (threeMiddleContext_M1_eq Q R hQ hR P T hP hTu hp ht he).2
    · exact (threeMiddleContext_M1_M0_ne Q R hQ hR P T hP hp ht he).elim
    · exact (threeMiddleContext_M1_M2_ne Q R hQ hR P T hP hp ht he).elim
  · rcases lt_trichotomy T.v (T.left + T.u) with ht | ht | ht
    · exact (threeMiddleContext_M1_M0_ne R Q hR hQ T P hTu ht hp he.symm).elim
    · exact (threeMiddleContext_M0_eq Q R hQ hR P T hp ht he).2
    · exact (threeMiddleContext_M2_M0_ne R Q hR hQ T P ht hp he.symm).elim
  · rcases lt_trichotomy T.v (T.left + T.u) with ht | ht | ht
    · exact (threeMiddleContext_M1_M2_ne R Q hR hQ T P hTu ht hp he.symm).elim
    · exact (threeMiddleContext_M2_M0_ne Q R hQ hR P T hp ht he).elim
    · exact (threeMiddleContext_M2_eq Q R hQ hR P T hp ht he).2

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

theorem RotationEquivalent.schur_eq {n : ℕ} {D E : BetaDiagram n}
    (h : D.RotationEquivalent E) : D.schur = E.schur :=
  ((D.translation_rotate_iff_rotation E).mpr h).schur_eq.trans E.rotate_schur

theorem threeMiddleContext_rotation_from_core (Q R : BetaDiagram 4)
    (P T : ThreeComponentParameters) (hT : T = P.swap)
    (hcore : Q.RotationEquivalent R) :
    (Q.threeMiddleContext P).RotationEquivalent (R.threeMiddleContext T) := by
  have hRQ := Q.rotated_core_translation R hcore
  subst T
  rw [R.threeMiddleContext_of_core_translation Q.rotate hRQ P.swap]
  exact threeMiddleContext_rotation Q P

/-- Fixed-parameter equality retains exactly the whole-parent rotation exception. -/
theorem threeMiddleContext_fixed_parameters_motion (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P : ThreeComponentParameters)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext P).schur) :
    (Q.threeMiddleContext P).TranslationEquivalent (R.threeMiddleContext P) ∨
      (Q.threeMiddleContext P).RotationEquivalent (R.threeMiddleContext P) := by
  have hfun := (three_context_core_recovery Q R hQ.connected P P true true he).2.1
  obtain htr | hrot := (Q.rotationRigid_iff_same_order).mp hQ.rotationRigid
    R hR.connected hfun.symm
  · rw [Q.threeMiddleContext_of_core_translation R htr P]
    exact Or.inl ⟨0,fun _ => by simp,fun _ => by simp⟩
  · by_cases hS : Q.Symmetric
    · have htr := Q.translation_of_rotation_of_symmetric R hS hrot
      rw [Q.threeMiddleContext_of_core_translation R htr P]
      exact Or.inl ⟨0,fun _ => by simp,fun _ => by simp⟩
    · by_cases hn : P.left ≠ P.right ∨ P.ell ≠ P.m ∨ P.u ≠ P.v
      · have hRQ := Q.rotated_core_translation R hrot
        have hp := R.threeMiddleContext_of_core_translation Q.rotate hRQ P
        have hbad : (Q.threeMiddleContext P).schur = (Q.rotate.threeMiddleContext P).schur :=
          he.trans (congrArg (fun D => D.schur) hp)
        exact (Q.threeMiddleContext_orientation_ne_of_coefficient
          (hQ.coefficient_ne_zero hS) (hQ.lower_part hS) P hn hbad).elim
      · have hLR : P.left = P.right := by tauto
        have hEM : P.ell = P.m := by tauto
        have huv : P.u = P.v := by tauto
        have hg : P.g₁ = P.g₂ := by
          unfold ThreeComponentParameters.left ThreeComponentParameters.right at hLR
          omega
        have hswap : P = P.swap := by
          apply threeComponentParameters_eq_of_fields <;>
            simp only [ThreeComponentParameters.swap] <;> omega
        exact Or.inr (threeMiddleContext_rotation_from_core Q R P P hswap hrot)

/-- At tied margins, movement fixes the separations or gives whole-parent rotation data. -/
theorem threeMiddleContext_tied_ordered_motion (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hPu : P.u = P.v) (hTu : T.u ≤ T.v)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    (Q.threeMiddleContext P).TranslationEquivalent (R.threeMiddleContext T) ∨
      (Q.threeMiddleContext P).RotationEquivalent (R.threeMiddleContext T) := by
  obtain ⟨hu,hphase,_⟩ := threeMiddleContext_first_alignment Q R hQ.connected hR.connected
    P T (by omega) hTu he
  have hTv : T.u = T.v := hphase.mp hPu
  have hv : P.v = T.v := by omega
  have hfun := (three_context_core_recovery Q R hQ.connected P T true true he).2.1
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hN := threeMiddleContext_total_extent_recovery Q R hQ.connected P T he
  have hsum : P.left+P.right = T.left+T.right := by omega
  by_cases hL : P.left = T.left
  · have hRR : P.right = T.right := by omega
    have hg₁ : P.g₁ = T.g₁ := by unfold ThreeComponentParameters.left at hL; omega
    have hg₂ : P.g₂ = T.g₂ := by unfold ThreeComponentParameters.right at hRR; omega
    have hPT := threeComponentParameters_eq_of_fields P T hℓ hm hg₁ hg₂ hu hv
    subst T
    exact threeMiddleContext_fixed_parameters_motion Q R hQ hR P he
  · have hdata : P.ell = P.m ∧ P.left = T.right ∧ Q.RotationEquivalent R := by
      rcases lt_or_gt_of_ne hL with h | h
      · obtain ⟨hEM,_,hxy,hrot⟩ := threeMiddleContext_moving_rotation_data
          Q R hQ hR P T he hℓ hm hu hv hsum h
        exact ⟨hEM,hxy,hrot⟩
      · obtain ⟨hEM,_,hxy,hrot⟩ := threeMiddleContext_moving_rotation_data
          R Q hR hQ T P he.symm hℓ.symm hm.symm hu.symm hv.symm hsum.symm h
        exact ⟨by omega,by omega,hrot.symm⟩
    obtain ⟨hEM,hxy,hrot⟩ := hdata
    have hxy' : T.left = P.right := by omega
    have hg₁ : T.g₁ = P.g₂ := by
      unfold ThreeComponentParameters.left ThreeComponentParameters.right at hxy'
      omega
    have hg₂ : T.g₂ = P.g₁ := by
      unfold ThreeComponentParameters.left ThreeComponentParameters.right at hxy
      omega
    have hswap : T = P.swap := by
      apply threeComponentParameters_eq_of_fields <;>
        simp only [ThreeComponentParameters.swap] <;> omega
    exact Or.inr (threeMiddleContext_rotation_from_core Q R P T hswap hrot)

/-- Tied singleton orders are aligned by rotation, retaining their multiplicities. -/
theorem threeMiddleContext_top_order_motion (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hP : P.u ≤ P.v) (hT : T.u ≤ T.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    (Q.threeMiddleContext P).TranslationEquivalent (R.threeMiddleContext T) ∨
      (Q.threeMiddleContext P).RotationEquivalent (R.threeMiddleContext T) := by
  by_cases htie : P.u = P.v
  · have hpair := (three_context_core_recovery Q R hQ.connected P T true true he).2.2
    rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩
    · exact threeMiddleContext_tied_ordered_motion Q R hQ hR P T htie hT hℓ hm he
    · have hRR : R.rotate.FourPlacementSource := hR.of_schur_eq R.rotate R.rotate_schur.symm
      have hrot := threeMiddleContext_rotation R T
      have horder : T.swap.u ≤ T.swap.v := by
        have hphase := (threeMiddleContext_first_alignment Q R hQ.connected hR.connected
          P T hP hT he).2.1
        have htv := hphase.mp htie
        simp only [ThreeComponentParameters.swap]
        omega
      have hout := threeMiddleContext_tied_ordered_motion Q R.rotate hQ hRR P T.swap
        htie horder (by simpa only [ThreeComponentParameters.swap] using hℓ)
        (by simpa only [ThreeComponentParameters.swap] using hm) (he.trans hrot.schur_eq)
      exact motion_trans _ _ _ hout (Or.inr hrot.symm)
  · have hpstrict : P.u < P.v := by omega
    rw [threeMiddleContext_strict_top_order_eq Q R hQ hR P T hpstrict hT he]
    exact Or.inl ⟨0,fun _ => by simp,fun _ => by simp⟩

theorem threeMiddleContext_source_top_order_motion (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hP : P.u ≤ P.v)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    (Q.threeMiddleContext P).TranslationEquivalent (R.threeMiddleContext T) ∨
      (Q.threeMiddleContext P).RotationEquivalent (R.threeMiddleContext T) := by
  by_cases hT : T.u ≤ T.v
  · exact threeMiddleContext_top_order_motion Q R hQ hR P T hP hT he
  · have hRR : R.rotate.FourPlacementSource := hR.of_schur_eq R.rotate R.rotate_schur.symm
    have hrot := threeMiddleContext_rotation R T
    have hswaporder : T.swap.u ≤ T.swap.v := by
      simp only [ThreeComponentParameters.swap]
      omega
    have hout := threeMiddleContext_top_order_motion Q R.rotate hQ hRR P T.swap
      hP hswaporder (he.trans hrot.schur_eq)
    exact motion_trans _ _ _ hout (Or.inr hrot.symm)

/-- Full middle-placement rigidity for independent positive source parameters. -/
theorem threeMiddleContext_rigidity (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (he : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur) :
    (Q.threeMiddleContext P).TranslationEquivalent (R.threeMiddleContext T) ∨
      (Q.threeMiddleContext P).RotationEquivalent (R.threeMiddleContext T) := by
  by_cases hP : P.u ≤ P.v
  · exact threeMiddleContext_source_top_order_motion Q R hQ hR P T hP he
  · have hQR : Q.rotate.FourPlacementSource := hQ.of_schur_eq Q.rotate Q.rotate_schur.symm
    have hrot := threeMiddleContext_rotation Q P
    have hswaporder : P.swap.u ≤ P.swap.v := by
      simp only [ThreeComponentParameters.swap]
      omega
    have hout := threeMiddleContext_source_top_order_motion Q.rotate R hQR hR P.swap T
      hswaporder (hrot.schur_eq.symm.trans he)
    exact motion_trans _ _ _ (Or.inr hrot) hout

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

theorem endpoint_bottom_of_core_translation (Q R : BetaDiagram 4)
    (h : Q.TranslationEquivalent R) (t : ℤ) (ht : 0 < t) :
    (Q.extendBottom t ht).schur = (R.extendBottom t ht).schur := by
  obtain ⟨c,hr,hco⟩ := h
  have he : (Q.extendBottom t ht).TranslationEquivalent (R.extendBottom t ht) := by
    refine ⟨c,?_,?_⟩
    · intro i
      exact hr i
    · intro j
      have hh := hco j
      simp only [extendBottom]
      split_ifs <;> omega
  exact he.schur_eq

theorem endpoint_top_of_core_translation (Q R : BetaDiagram 4)
    (h : Q.TranslationEquivalent R) (t : ℤ) (ht : 0 < t) :
    (Q.extendTop t ht).schur = (R.extendTop t ht).schur := by
  obtain ⟨c,hr,hco⟩ := h
  have he : (Q.extendTop t ht).TranslationEquivalent (R.extendTop t ht) := by
    refine ⟨c,?_,?_⟩
    · intro i
      have hh := hr i
      simp only [extendTop]
      split_ifs <;> omega
    · intro j
      exact hco j
  exact he.schur_eq

/-- Equal positive bottom extensions identify the actual core translation. -/
theorem bottom_endpoint_core_recovery (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (hfun : Q.schur = R.schur) (t : ℤ) (ht : 0 < t)
    (he : (Q.extendBottom t ht).schur = (R.extendBottom t ht).schur) :
    Q.TranslationEquivalent R := by
  rcases (Q.rotationRigid_iff_same_order).mp hQ.rotationRigid R hR.connected hfun.symm
      with htr | hrot
  · exact htr
  · by_cases hS : Q.Symmetric
    · exact Q.translation_of_rotation_of_symmetric R hS hrot
    · have hRQ := Q.rotated_core_translation R hrot
      have hr := endpoint_bottom_of_core_translation R Q.rotate hRQ t ht
      rw [rotate_extendBottom_schur] at hr
      have hz : Q.endpointDifference t ht = 0 := by
        unfold endpointDifference
        exact sub_eq_zero.mpr (he.trans hr).symm
      exact False.elim (Q.endpointDifference_ne_zero_of_coefficient
        (hQ.coefficient_ne_zero hS) t ht hz)

/-- Every end first marker is read directly from its actual margin regime. -/
noncomputable def endFirstResponse (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    CompleteRing :=
  if P.u < P.v then -(complete (P.ell+P.u)*complete P.m*Q.schur)
  else if P.v < P.u then
    -(complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur)
  else -(complete P.m*(complete (P.ell+P.u)*Q.schur+
    complete P.ell*(Q.extendBottom P.u P.u_pos).schur))

theorem endFirstResponse_top (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (h : P.u < P.v) :
    endFirstResponse Q P = -(complete (P.ell+P.u)*complete P.m*Q.schur) := by
  simp only [endFirstResponse, if_pos h]

theorem endFirstResponse_bottom (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (h : P.v < P.u) :
    endFirstResponse Q P =
      -(complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur) := by
  simp only [endFirstResponse, if_neg (show ¬ P.u < P.v by omega), if_pos h]

theorem endFirstResponse_tied (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (h : P.u = P.v) :
    endFirstResponse Q P = -(complete P.m*(complete (P.ell+P.u)*Q.schur+
      complete P.ell*(Q.extendBottom P.u P.u_pos).schur)) := by
  simp only [endFirstResponse, if_neg (show ¬ P.u < P.v by omega),
    if_neg (show ¬ P.v < P.u by omega)]

theorem threeEndContext_first_response (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    let D := Q.threeEndContext P
    MvPolynomial.pderiv D.borderSecondGenerator
      (eraseGenerator D.borderLargestGenerator D.schur) = endFirstResponse Q P := by
  dsimp only
  have hg :
      MvPolynomial.pderiv (Q.threeEndContext P).borderSecondGenerator
        (eraseGenerator (Q.threeEndContext P).borderLargestGenerator
          (Q.threeEndContext P).schur) =
      MvPolynomial.pderiv
        ((Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderSecondGenerator
        (eraseGenerator
          ((Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderLargestGenerator
          (Q.threeEndContext P).schur) := by
    simp only [threeEndContext,singletonContext,shifted_borderLargestGenerator,
      shifted_borderSecondGenerator,threeEndCore]
  rw [hg]
  unfold endFirstResponse
  rcases lt_trichotomy P.u P.v with h | h | h
  · rw [if_pos h,threeEndContext_top_marker _ _ h]
  · rw [if_neg (by omega),if_neg (by omega),threeEndContext_tied_marker _ _ h]
  · rw [if_neg (by omega),if_pos h,threeEndContext_bottom_marker _ _ h]

/-- The end bottom and tied regimes have no connected-core divisor. -/
theorem endFirstResponse_core_divisor (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    Q.schur ∣ endFirstResponse Q P ↔ P.u < P.v := by
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (Q.schur_irreducible hQ.connected)
  rcases lt_trichotomy P.u P.v with h | h | h
  · simp only [endFirstResponse,if_pos h]
    exact ⟨fun _ => h,fun _ => dvd_neg.mpr (dvd_mul_left _ _)⟩
  · have hn : ¬ Q.schur ∣ endFirstResponse Q P := by
      intro hd
      rw [endFirstResponse_tied Q P h] at hd
      have hdiv := dvd_neg.mp hd
      rcases hprime.dvd_mul.mp hdiv with hd | hd
      · exact Q.connected_four_schur_not_dvd_complete hQ.connected P.m P.m_pos hd
      · have hd' := dvd_sub hd (dvd_mul_left Q.schur (complete (P.ell+P.u)))
        have hbottom : Q.schur ∣ complete P.ell*(Q.extendBottom P.u P.u_pos).schur := by
          simpa only [add_sub_cancel_left] using hd'
        rcases hprime.dvd_mul.mp hbottom with hd | hd
        · exact Q.connected_four_schur_not_dvd_complete hQ.connected P.ell P.ell_pos hd
        · exact Q.connected_schur_not_dvd_bottom_endpoint hQ.connected P.u P.u_pos hd
    exact ⟨fun hd => (hn hd).elim,fun ht => (by omega : False).elim⟩
  · have hn := Q.three_end_bottom_marker_not_dvd_core hQ.connected P
    rw [endFirstResponse_bottom Q P h]
    exact ⟨fun hd => (hn hd).elim,fun ht => (by omega : False).elim⟩

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

theorem threeEndContext_first_response_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    endFirstResponse Q P = endFirstResponse R T := by
  have hm := (placement_common_data Q R hQ P T false false he).2.2.2.2.2.2
  simp only [Bool.false_eq_true,if_false] at hm
  rw [threeEndContext_first_response,threeEndContext_first_response] at hm
  exact hm

/-- Among non-top end regimes only the strict bottom marker has the full singleton content. -/
theorem endFirstResponse_singleton_content (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) (hP : P.v ≤ P.u) :
    complete P.ell*complete P.m ∣ endFirstResponse Q P ↔ P.v < P.u := by
  by_cases h : P.v < P.u
  · rw [endFirstResponse_bottom Q P h]
    exact ⟨fun _ => h,fun _ => dvd_neg.mpr (dvd_mul_right _ _)⟩
  · have huv : P.u = P.v := by omega
    have hn := Q.singleton_tied_marker_divisibility hQ.connected
      P.ell P.u P.ell_pos P.u_pos
    have hnot : ¬ complete P.ell*complete P.m ∣ endFirstResponse Q P := by
      intro hd
      rw [endFirstResponse_tied Q P huv] at hd
      obtain ⟨w,hw⟩ := dvd_neg.mp hd
      apply hn.1
      refine ⟨w,?_⟩
      apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
      linear_combination hw
    exact ⟨fun hd => (hnot hd).elim,fun ht => (h ht).elim⟩

/-- All three first end regimes are recovered from actual full Schur equality. -/
theorem threeEndContext_first_phase (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    (P.u < P.v ↔ T.u < T.v) ∧ (P.v < P.u ↔ T.v < T.u) ∧
      (P.u = P.v ↔ T.u = T.v) := by
  have hd := placement_common_data Q R hQ P T false false he
  have hfun := hd.2.1
  have hpair := hd.2.2.2.1
  have hr := threeEndContext_first_response_eq Q R hQ P T he
  have htop : P.u < P.v ↔ T.u < T.v := by
    rw [← Q.endFirstResponse_core_divisor hQ P,
      ← R.endFirstResponse_core_divisor hR T,hfun,hr]
  have hprod : complete P.ell*complete P.m = complete T.ell*complete T.m := by
    rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩ <;> rw [hℓ,hm] <;> ring
  have hbottom : P.v < P.u ↔ T.v < T.u := by
    by_cases hp : P.u < P.v
    · have ht := htop.mp hp
      constructor <;> intro h <;> omega
    · have ht : ¬ T.u < T.v := by intro h; exact hp (htop.mpr h)
      rw [← Q.endFirstResponse_singleton_content hQ P (by omega),
        ← R.endFirstResponse_singleton_content hR T (by omega),hprod,hr]
  refine ⟨htop,hbottom,?_⟩
  constructor
  · intro hp
    have h₁ : ¬ T.u < T.v := by intro h; have := htop.mpr h; omega
    have h₂ : ¬ T.v < T.u := by intro h; have := hbottom.mpr h; omega
    omega
  · intro ht
    have h₁ : ¬ P.u < P.v := by intro h; have := htop.mp h; omega
    have h₂ : ¬ P.v < P.u := by intro h; have := hbottom.mp h; omega
    omega

/-- A strict top first end marker recovers the extended singleton order and its margin. -/
theorem threeEndContext_top_first_recovery (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hP : P.u < P.v)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P.u = T.u ∧ P.ell = T.ell ∧ P.m = T.m := by
  have hT := (threeEndContext_first_phase Q R hQ hR P T he).1.mp hP
  have hdata := placement_common_data Q R hQ P T false false he
  have hfun := hdata.2.1
  have hpair := hdata.2.2.2.1
  have hq := hdata.2.2.2.2.1
  have hu : P.u = T.u := by simpa only [min_eq_left hP.le,min_eq_left hT.le] using hq
  have hr := threeEndContext_first_response_eq Q R hQ P T he
  simp only [endFirstResponse,if_pos hP,if_pos hT] at hr
  have hp : complete P.m*complete (P.ell+P.u) =
      complete T.m*complete (T.ell+T.u) := by
    apply mul_right_cancel₀ R.schur_ne_zero
    rw [hfun] at hr
    linear_combination neg_injective hr
  have hx := singleton_pair_recovery P.m (P.ell+P.u) T.m (T.ell+T.u)
    P.m_pos (by have := P.ell_pos; have := P.u_pos; omega)
    T.m_pos (by have := T.ell_pos; have := T.u_pos; omega) hp
  refine ⟨hu,?_⟩
  rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩
  · exact ⟨hℓ,hm⟩
  · rcases hx with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact ⟨by omega,hx⟩
    · have := P.u_pos
      omega

theorem end_tied_first_not_dvd_first_singleton (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters)
    (hP : P.u = P.v) (hne : P.ell ≠ P.m) :
    ¬ complete P.ell ∣ endFirstResponse Q P := by
  intro hd
  rw [endFirstResponse_tied Q P hP] at hd
  rcases (complete_prime P.ell P.ell_pos).dvd_mul.mp (dvd_neg.mp hd) with h | h
  · exact hne ((complete_dvd_complete_iff P.ell P.m P.ell_pos P.m_pos).mp h)
  · exact (Q.singleton_tied_marker_divisibility hQ.connected
      P.ell P.u P.ell_pos P.u_pos).1 h

/-- Tied first end markers fix their singleton order and the actual core translation. -/
theorem threeEndContext_tied_first_recovery (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hP : P.u = P.v)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P.u = T.u ∧ P.v = T.v ∧ P.ell = T.ell ∧ P.m = T.m ∧ Q.TranslationEquivalent R := by
  have hT := (threeEndContext_first_phase Q R hQ hR P T he).2.2.mp hP
  have hd := placement_common_data Q R hQ P T false false he
  have hfun := hd.2.1
  have hpair := hd.2.2.2.1
  have hq := hd.2.2.2.2.1
  have hu : P.u = T.u := by
    simpa only [hP,hT,min_self] using hq
  have hv : P.v = T.v := by omega
  have hr := threeEndContext_first_response_eq Q R hQ P T he
  have horder : P.ell = T.ell ∧ P.m = T.m := by
    rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩
    · exact ⟨hℓ,hm⟩
    · by_cases heq : P.ell = P.m
      · exact ⟨by omega,by omega⟩
      · apply False.elim
        apply end_tied_first_not_dvd_first_singleton Q hQ P hP heq
        rw [hr,hℓ]
        rw [endFirstResponse_tied R T hT]
        exact dvd_neg.mpr (dvd_mul_right _ _)
  obtain ⟨hℓ,hm⟩ := horder
  have hbottom : (Q.extendBottom P.u P.u_pos).schur =
      (R.extendBottom P.u P.u_pos).schur := by
    rw [endFirstResponse_tied Q P hP,endFirstResponse_tied R T hT] at hr
    rw [extendBottom_schur_parameter_congr R hu.symm T.u_pos P.u_pos] at hr
    simp only [← hℓ,← hm,← hu,← hfun] at hr
    have hinner := mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
      (neg_injective hr)
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.ell_pos.le)
    exact add_left_cancel hinner
  exact ⟨hu,hv,hℓ,hm,bottom_endpoint_core_recovery Q R hQ hR hfun P.u P.u_pos hbottom⟩

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- Cross-placement equality must have strict top minima on both aligned sides,
and fixes which singleton was extended. -/
theorem end_middle_first_alignment (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hT : T.u ≤ T.v)
    (he : (Q.threeEndContext P).schur = (R.threeMiddleContext T).schur) :
    P.u < P.v ∧ T.u < T.v ∧ P.u = T.u ∧ P.ell = T.ell ∧ P.m = T.m := by
  have hd := placement_common_data Q R hQ P T false true he
  have hfun := hd.2.1
  have hpair := hd.2.2.2.1
  have hq := hd.2.2.2.2.1
  have hr := hd.2.2.2.2.2.2
  simp only [Bool.false_eq_true,if_false,if_true] at hr
  rw [threeEndContext_first_response,threeMiddleContext_first_response _ _ hT] at hr
  have hP : P.u < P.v := by
    apply (Q.endFirstResponse_core_divisor hQ P).mp
    rw [hr,hfun]
    exact dvd_neg.mpr (dvd_mul_right _ _)
  have hu : P.u = T.u := by
    simpa only [min_eq_left hP.le,min_eq_left hT] using hq
  have hresp : complete P.m*complete (P.ell+P.u) = middleFirstResponse T := by
    simp only [endFirstResponse,if_pos hP] at hr
    apply mul_left_cancel₀ R.schur_ne_zero
    rw [hfun] at hr
    linear_combination neg_injective hr
  have hTne : T.u ≠ T.v := by
    intro ht
    have hev := congrArg (MvPolynomial.eval (fun _ => (1 : ℚ))) hresp
    rw [middleFirstResponse_ones,if_pos ht] at hev
    have hp : 0 < P.ell+P.u := by have := P.ell_pos; have := P.u_pos; omega
    simp [complete_of_pos P.m_pos,complete_of_pos hp] at hev
  have hTs : T.u < T.v := by omega
  rw [middleFirstResponse,if_neg hTne] at hresp
  have hext := singleton_pair_recovery P.m (P.ell+P.u) T.m (T.ell+T.u)
    P.m_pos (by have := P.ell_pos; have := P.u_pos; omega)
    T.m_pos (by have := T.ell_pos; have := T.u_pos; omega) hresp
  refine ⟨hP,hTs,hu,?_⟩
  rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩
  · exact ⟨hℓ,hm⟩
  · rcases hext with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact ⟨by omega,hx⟩
    · have := P.u_pos
      omega

theorem FourPlacementSource.cross_one {Q : BetaDiagram 4}
    (h : Q.FourPlacementSource) (s x u : ℤ)
    (hs : 0 < s) (hx : s < x) (hu : 0 < u) :
    complete (s+u)*(Q.extendTop x (by omega)).schur -
      complete (s+(x+u))*Q.schur -
      complete s*Q.endpointDifference (x+u) (by omega) ≠ 0 := by
  rcases h with h | h
  · exact Q.dense_cross_resonance_one h s x u hs hx hu
  · exact Q.one_negative_cross_resonance_one h.1 h.2.1 h.2.2 s x u hs hx hu

/-- The two cross-placement tie exclusions survive arbitrary source-core motion. -/
theorem cross_first_tie_any_core (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (hfun : Q.schur = R.schur) (T : ThreeComponentParameters)
    (htie : T.v = T.left+T.u) :
    -(complete T.ell*complete T.m*(Q.extendBottom T.v T.v_pos).schur) ≠
      -(complete T.ell*complete (T.m+T.v)*R.schur)+
        complete T.m*(middleU R T).schur := by
  have hres := hR.cross_one T.ell T.left T.u T.ell_pos
    (by have := T.g₁_pos; unfold ThreeComponentParameters.left; omega) T.u_pos
  have hres' : complete (T.ell+T.u)*(R.extendTop T.left T.left_pos).schur -
      complete (T.ell+T.v)*R.schur -
      complete T.ell*R.endpointDifference T.v T.v_pos ≠ 0 := by
    simpa only [← htie] using hres
  rcases (Q.rotationRigid_iff_same_order).mp hQ.rotationRigid R hR.connected hfun.symm
      with htr | hrot
  · rw [endpoint_bottom_of_core_translation Q R htr]
    exact R.three_cross_first_tie_exclusion hR.connected
      (R.positiveCorner_of_connected_zeroFree hR.connected hR.zeroFree) T htie
      hres' R (Or.inl rfl)
  · have htr := (Q.translation_rotate_iff_rotation R).mpr hrot
    rw [endpoint_bottom_of_core_translation Q R.rotate htr]
    exact R.three_cross_first_tie_exclusion hR.connected
      (R.positiveCorner_of_connected_zeroFree hR.connected hR.zeroFree) T htie
      hres' R.rotate (Or.inr rfl)

theorem cross_second_tie_any_core (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (hfun : Q.schur = R.schur) (T : ThreeComponentParameters)
    (htie : T.v = T.left+T.u) :
    -(complete T.ell*complete T.m*(Q.extendBottom T.v T.v_pos).schur)+
        (threeComponentA T).schur*R.schur ≠
      -(complete T.ell*complete (T.m+T.v)*R.schur)+
        complete T.m*(middleU R T).schur := by
  have hres := hR.cross_one T.ell T.left T.u T.ell_pos
    (by have := T.g₁_pos; unfold ThreeComponentParameters.left; omega) T.u_pos
  have hres' : complete (T.ell+T.u)*(R.extendTop T.left T.left_pos).schur -
      complete (T.ell+T.v)*R.schur -
      complete T.ell*R.endpointDifference T.v T.v_pos ≠ 0 := by
    simpa only [← htie] using hres
  rcases (Q.rotationRigid_iff_same_order).mp hQ.rotationRigid R hR.connected hfun.symm
      with htr | hrot
  · rw [endpoint_bottom_of_core_translation Q R htr]
    exact R.three_cross_second_tie_exclusion hR.connected T htie hres' R (Or.inl rfl)
  · have htr := (Q.translation_rotate_iff_rotation R).mpr hrot
    rw [endpoint_bottom_of_core_translation Q R.rotate htr]
    exact R.three_cross_second_tie_exclusion hR.connected T htie hres' R.rotate (Or.inr rfl)

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- The end third response at and above both actual candidate levels. -/
theorem threeEndContext_third_response_at_or_above (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (k : ℕ+)
    (hk₁ : Q.largestLabel+P.left+P.right+P.u ≤ (k.val : ℤ))
    (hk₂ : Q.largestLabel+P.right+P.v ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k ((Q.threeEndContext P).schur-Q.threeSharedLeadingPart P) =
      (if (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.u then
        -(complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur) else 0) +
      (if (k.val : ℤ) = Q.largestLabel+P.right+P.v then
        (threeComponentA P).schur*Q.schur else 0) := by
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hLR : 0 < P.left+P.right := by omega
  have hLRu : 0 < P.left+P.right+P.u := by omega
  let B₂ := Q.positiveBorder (P.left+P.right) P.v hLR P.v_pos
  let B₃ := Q.positiveBorder (P.left+P.right+P.u) P.v hLRu P.v_pos
  have hp : (Q.threeEndContext P).schur-Q.threeSharedLeadingPart P =
      (threeComponentA P).schur*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur -
      complete P.m*complete (P.ell+P.u)*B₂.cornerResidual +
      complete P.ell*complete P.m*B₃.cornerResidual := by
    rw [threeEndContext_schur,← threeComponentA_schur,
      Q.four_border_corner_split (P.left+P.right) P.v hLR P.v_pos,
      Q.four_border_corner_split (P.left+P.right+P.u) P.v hLRu P.v_pos]
    dsimp only [threeSharedLeadingPart,B₂,B₃]
    simp only [add_assoc]
    ring
  have hPhi := Q.four_border_largest_response P.right P.v P.right_pos P.v_pos k hk₂
  have hB₂ : MvPolynomial.pderiv k B₂.cornerResidual = 0 :=
    Q.four_border_residual_above _ _ _ _ k (by apply max_lt <;> omega)
  have hB₃ := Q.four_border_residual_response (P.left+P.right+P.u) P.v hLRu P.v_pos k
    (by omega) (by omega)
  have hlow : (k.val : ℤ) ≠ Q.largestLabel+P.v := by omega
  rw [if_neg hlow,add_zero] at hB₃
  have hA := (threeComponentA P).pderiv_schur_above k
    (by rw [threeComponentA_largestLabel];
        unfold ThreeComponentParameters.right at hk₁; omega)
  have hℓ0 : MvPolynomial.pderiv k (complete P.ell) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  have hm0 : MvPolynomial.pderiv k (complete P.m) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.right at hk₁; omega)]
  have ha0 : MvPolynomial.pderiv k (complete (P.ell+P.u)) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  have hB₃' : MvPolynomial.pderiv k B₃.cornerResidual =
      if (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.u then
        -(Q.extendBottom P.v P.v_pos).schur else 0 := by
    have hi : Q.largestLabel+(P.left+P.right+P.u) =
        Q.largestLabel+P.left+P.right+P.u := by ring
    exact hB₃.trans (congrArg (fun z : ℤ =>
      if (k.val : ℤ) = z then -(Q.extendBottom P.v P.v_pos).schur else 0) hi)
  rw [hp]
  simp only [map_add,map_sub,MvPolynomial.pderiv_mul,hA,hℓ0,hm0,ha0,hPhi,hB₂,hB₃',
    zero_mul,mul_zero,zero_add,add_zero,sub_zero]
  split_ifs <;> (try omega) <;> ring

/-- Every end third marker is nonzero, including the tied coefficient. -/
theorem threeEndContext_third_marker_ne_zero (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    MvPolynomial.pderiv (Q.threeThirdGenerator P)
      ((Q.threeEndContext P).schur-Q.threeSharedLeadingPart P) ≠ 0 := by
  rw [threeEndContext_third_marker]
  have hk : ((Q.threeThirdGenerator P).val : ℤ) =
      max (Q.largestLabel+P.left+P.right+P.u) (Q.largestLabel+P.right+P.v) := by
    rw [threeThirdGenerator_int,threeThirdIndex]
  rcases lt_trichotomy P.v (P.left+P.u) with h | h | h
  · have hk₁ : ((Q.threeThirdGenerator P).val : ℤ) =
        Q.largestLabel+P.left+P.right+P.u := by rw [max_eq_left (by omega)] at hk; exact hk
    rw [if_pos hk₁,if_neg (by omega),add_zero]
    exact neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
        ((complete_ne_zero_iff _).mpr P.m_pos.le))
      (Q.extendBottom P.v P.v_pos).schur_ne_zero)
  · have hk₁ : ((Q.threeThirdGenerator P).val : ℤ) =
        Q.largestLabel+P.left+P.right+P.u := by rw [max_eq_left (by omega)] at hk; exact hk
    rw [if_pos hk₁,if_pos (by omega)]
    intro hz
    apply Q.three_end_tied_marker_not_dvd_core hQ.connected P
    rw [hz]
    exact dvd_zero _
  · have hk₂ : ((Q.threeThirdGenerator P).val : ℤ) =
        Q.largestLabel+P.right+P.v := by rw [max_eq_right (by omega)] at hk; exact hk
    rw [if_neg (by omega),if_pos hk₂,zero_add]
    exact mul_ne_zero (threeComponentA P).schur_ne_zero Q.schur_ne_zero

theorem three_context_shared_leading_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters) (b c : Bool)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (if b then Q.threeMiddleContext P else Q.threeEndContext P).schur =
      (if c then R.threeMiddleContext T else R.threeEndContext T).schur) :
    Q.threeSharedLeadingPart P = R.threeSharedLeadingPart T := by
  have hd := placement_common_data Q R hQ P T b c he
  have hfun := hd.2.1
  have hS := hd.2.2.1
  have htotal := hd.2.2.2.2.2.1
  have hN : Q.largestLabel+P.left+P.right+P.u+P.v =
      R.largestLabel+T.left+T.right+T.u+T.v := by omega
  have hN' : Q.largestLabel+P.left+P.right+P.v =
      R.largestLabel+T.left+T.right+T.v := by omega
  unfold threeSharedLeadingPart
  rw [hN,hN',hfun,hℓ,hm,hu]

/-- Recovery of the third level for either actual placement, including cross comparisons. -/
theorem three_context_third_index_recovery (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (b c : Bool)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (if b then Q.threeMiddleContext P else Q.threeEndContext P).schur =
      (if c then R.threeMiddleContext T else R.threeEndContext T).schur) :
    Q.threeThirdIndex P = R.threeThirdIndex T := by
  have hs := three_context_shared_leading_eq Q R hQ P T b c hℓ hm hu he
  let F := if b then Q.threeMiddleContext P else Q.threeEndContext P
  let G := if c then R.threeMiddleContext T else R.threeEndContext T
  have hr : F.schur-Q.threeSharedLeadingPart P = G.schur-R.threeSharedLeadingPart T := by
    rw [he,hs]
  have hnQ : MvPolynomial.pderiv (Q.threeThirdGenerator P)
      (F.schur-Q.threeSharedLeadingPart P) ≠ 0 := by
    cases b <;> simp only [F,Bool.false_eq_true,if_false,if_true]
    · exact Q.threeEndContext_third_marker_ne_zero hQ P
    · exact Q.threeMiddleContext_third_marker_ne_zero hQ P
  have hnR : MvPolynomial.pderiv (R.threeThirdGenerator T)
      (G.schur-R.threeSharedLeadingPart T) ≠ 0 := by
    cases c <;> simp only [G,Bool.false_eq_true,if_false,if_true]
    · exact R.threeEndContext_third_marker_ne_zero hR T
    · exact R.threeMiddleContext_third_marker_ne_zero hR T
  have hzeroQ : ∀ (k : ℕ+), Q.threeThirdIndex P < (k.val : ℤ) →
      MvPolynomial.pderiv k (F.schur-Q.threeSharedLeadingPart P) = 0 := by
    intro k hk
    have h₁ := le_max_left (Q.largestLabel+P.left+P.right+P.u) (Q.largestLabel+P.right+P.v)
    have h₂ := le_max_right (Q.largestLabel+P.left+P.right+P.u) (Q.largestLabel+P.right+P.v)
    change max _ _ < (k.val : ℤ) at hk
    cases b <;> simp only [F,Bool.false_eq_true,if_false,if_true]
    · rw [threeEndContext_third_response_at_or_above Q P k (by omega) (by omega),
        if_neg (by omega),if_neg (by omega),zero_add]
    · rw [threeMiddleContext_third_response_at_or_above Q P k (by omega) (by omega),
        if_neg (by omega),if_neg (by omega),zero_add]
  have hzeroR : ∀ (k : ℕ+), R.threeThirdIndex T < (k.val : ℤ) →
      MvPolynomial.pderiv k (G.schur-R.threeSharedLeadingPart T) = 0 := by
    intro k hk
    have h₁ := le_max_left (R.largestLabel+T.left+T.right+T.u) (R.largestLabel+T.right+T.v)
    have h₂ := le_max_right (R.largestLabel+T.left+T.right+T.u) (R.largestLabel+T.right+T.v)
    change max _ _ < (k.val : ℤ) at hk
    cases c <;> simp only [G,Bool.false_eq_true,if_false,if_true]
    · rw [threeEndContext_third_response_at_or_above R T k (by omega) (by omega),
        if_neg (by omega),if_neg (by omega),zero_add]
    · rw [threeMiddleContext_third_response_at_or_above R T k (by omega) (by omega),
        if_neg (by omega),if_neg (by omega),zero_add]
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · apply hnR
    rw [← hr,hzeroQ _ (by rw [threeThirdGenerator_int]; exact h)]
  · apply hnQ
    rw [hr,hzeroR _ (by rw [threeThirdGenerator_int]; exact h)]

theorem three_context_third_marker_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (b c : Bool)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (if b then Q.threeMiddleContext P else Q.threeEndContext P).schur =
      (if c then R.threeMiddleContext T else R.threeEndContext T).schur) :
    MvPolynomial.pderiv (Q.threeThirdGenerator P)
      ((if b then Q.threeMiddleContext P else Q.threeEndContext P).schur-Q.threeSharedLeadingPart P) =
      MvPolynomial.pderiv (R.threeThirdGenerator T)
      ((if c then R.threeMiddleContext T else R.threeEndContext T).schur-R.threeSharedLeadingPart T) := by
  have hs := three_context_shared_leading_eq Q R hQ P T b c hℓ hm hu he
  have hK := three_context_third_index_recovery Q R hQ hR P T b c hℓ hm hu he
  have hg : Q.threeThirdGenerator P = R.threeThirdGenerator T := by
    apply Subtype.ext
    simp only [threeThirdGenerator,hK]
  rw [he,hs,hg]

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

noncomputable def endThirdResponse (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : CompleteRing :=
  MvPolynomial.pderiv (Q.threeThirdGenerator P)
    ((Q.threeEndContext P).schur-Q.threeSharedLeadingPart P)

theorem endThirdResponse_E1 (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (h : P.v < P.left+P.u) :
    endThirdResponse Q P =
      -(complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur) := by
  have hk : ((Q.threeThirdGenerator P).val : ℤ) =
      Q.largestLabel+P.left+P.right+P.u := by
    rw [threeThirdGenerator_int,threeThirdIndex,max_eq_left (by omega)]
  rw [endThirdResponse,threeEndContext_third_marker,if_pos hk,if_neg (by omega),add_zero]

theorem endThirdResponse_E2 (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (h : P.left+P.u < P.v) :
    endThirdResponse Q P = (threeComponentA P).schur*Q.schur := by
  have hk : ((Q.threeThirdGenerator P).val : ℤ) =
      Q.largestLabel+P.right+P.v := by
    rw [threeThirdGenerator_int,threeThirdIndex,max_eq_right (by omega)]
  rw [endThirdResponse,threeEndContext_third_marker,if_neg (by omega),if_pos hk,zero_add]

theorem endThirdResponse_E0 (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (h : P.v = P.left+P.u) :
    endThirdResponse Q P =
      -(complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur)+
        (threeComponentA P).schur*Q.schur := by
  have hk₁ : ((Q.threeThirdGenerator P).val : ℤ) =
      Q.largestLabel+P.left+P.right+P.u := by
    rw [threeThirdGenerator_int,threeThirdIndex,max_eq_left (by omega)]
  rw [endThirdResponse,threeEndContext_third_marker,if_pos hk₁,if_pos (by omega)]

theorem threeEndContext_third_index_recovery (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    Q.threeThirdIndex P = R.threeThirdIndex T :=
  three_context_third_index_recovery Q R hQ hR P T false false hℓ hm hu he

theorem threeEndContext_third_response_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    endThirdResponse Q P = endThirdResponse R T := by
  simpa only [Bool.false_eq_true,if_false,endThirdResponse] using
    three_context_third_marker_eq Q R hQ hR P T false false hℓ hm hu he

theorem endThirdResponse_core_divisor (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    Q.schur ∣ endThirdResponse Q P ↔ P.left+P.u < P.v := by
  rcases lt_trichotomy P.v (P.left+P.u) with h | h | h
  · rw [endThirdResponse_E1 Q P h]
    exact ⟨fun hd => (Q.three_end_bottom_marker_not_dvd_core hQ.connected P hd).elim,
      fun hh => (by omega : False).elim⟩
  · rw [endThirdResponse_E0 Q P h]
    exact ⟨fun hd => (Q.three_end_tied_marker_not_dvd_core hQ.connected P hd).elim,
      fun hh => (by omega : False).elim⟩
  · rw [endThirdResponse_E2 Q P h]
    exact ⟨fun _ => h,fun _ => dvd_mul_left _ _⟩

theorem endThirdResponse_second_content (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters)
    (hnot : ¬ P.left+P.u < P.v) :
    complete P.m ∣ endThirdResponse Q P ↔ P.v < P.left+P.u := by
  rcases lt_trichotomy P.v (P.left+P.u) with h | h | h
  · rw [endThirdResponse_E1 Q P h]
    constructor
    · intro _
      exact h
    · intro _
      refine ⟨-(complete P.ell*(Q.extendBottom P.v P.v_pos).schur),?_⟩
      ring
  · rw [endThirdResponse_E0 Q P h]
    exact ⟨fun hd => (Q.three_end_tied_marker_not_dvd_second_singleton
      hQ.connected P hd).elim,fun hh => (by omega : False).elim⟩
  · exact (hnot h).elim

theorem threeEndContext_third_phase (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    (P.v < P.left+P.u ↔ T.v < T.left+T.u) ∧
      (P.left+P.u < P.v ↔ T.left+T.u < T.v) ∧
      (P.v = P.left+P.u ↔ T.v = T.left+T.u) := by
  have hfun := (three_context_core_recovery Q R hQ.connected P T false false he).2.1
  have hc := threeEndContext_third_response_eq Q R hQ hR P T hℓ hm hu he
  have hsecond : P.left+P.u < P.v ↔ T.left+T.u < T.v := by
    rw [← endThirdResponse_core_divisor Q hQ P,
      ← endThirdResponse_core_divisor R hR T,hfun,hc]
  have hfirst : P.v < P.left+P.u ↔ T.v < T.left+T.u := by
    by_cases hP : P.left+P.u < P.v
    · have hT := hsecond.mp hP
      constructor <;> intro h <;> omega
    · have hT : ¬ T.left+T.u < T.v := by intro h; exact hP (hsecond.mpr h)
      rw [← endThirdResponse_second_content Q hQ P hP,
        ← endThirdResponse_second_content R hR T hT,hm,hc]
  refine ⟨hfirst,hsecond,?_⟩
  constructor
  · intro h
    have h₁ : ¬ T.v < T.left+T.u := by intro hh; have := hfirst.mpr hh; omega
    have h₂ : ¬ T.left+T.u < T.v := by intro hh; have := hsecond.mpr hh; omega
    omega
  · intro h
    have h₁ : ¬ P.v < P.left+P.u := by intro hh; have := hfirst.mp hh; omega
    have h₂ : ¬ P.left+P.u < P.v := by intro hh; have := hsecond.mp hh; omega
    omega

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- The complete nine third-marker comparisons exclude mixing end and middle
parents after whole-parent rotation has put the smaller middle margin on top. -/
theorem end_middle_top_order_ne (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hT : T.u ≤ T.v) :
    (Q.threeEndContext P).schur ≠ (R.threeMiddleContext T).schur := by
  intro he
  obtain ⟨hPu,hTu,hu,hℓ,hm⟩ := end_middle_first_alignment Q R hQ hR P T hT he
  obtain ⟨_,hfun,hS,_,_,htotal,_⟩ := placement_common_data Q R hQ P T false true he
  have hK := three_context_third_index_recovery Q R hQ hR P T false true hℓ hm hu he
  have hmark := three_context_third_marker_eq Q R hQ hR P T false true hℓ hm hu he
  simp only [Bool.false_eq_true,if_false,if_true] at hmark
  change endThirdResponse Q P =
    MvPolynomial.pderiv (R.threeThirdGenerator T)
      ((R.threeMiddleContext T).schur-R.threeSharedLeadingPart T) at hmark
  have hQR := R.positiveCorner_of_connected_zeroFree hR.connected hR.zeroFree
  rcases lt_trichotomy P.v (P.left+P.u) with hp | hp | hp
  · rcases lt_trichotomy T.v (T.left+T.u) with ht | ht | ht
    · rw [endThirdResponse_E1 Q P hp,threeMiddleContext_third_M1 R T ht] at hmark
      apply Q.three_end_bottom_marker_not_dvd_core hQ.connected P
      rw [hmark,hfun]
      exact dvd_neg.mpr (dvd_mul_left _ _)
    · have hv : P.v = T.v := by
        have hkP : Q.threeThirdIndex P = Q.largestLabel+P.left+P.right+P.u := by
          rw [threeThirdIndex,max_eq_left (by omega)]
        have hkT : R.threeThirdIndex T = R.largestLabel+T.left+T.right+T.u := by
          rw [threeThirdIndex,max_eq_left (by omega)]
        rw [hkP,hkT] at hK
        omega
      rw [endThirdResponse_E1 Q P hp,threeMiddleContext_third_M0 R T ht] at hmark
      apply cross_first_tie_any_core Q R hQ hR hfun T ht
      simpa only [hℓ,hm,hv,middleU] using hmark
    · rw [endThirdResponse_E1 Q P hp,threeMiddleContext_third_M2 R T ht] at hmark
      have hU : (middleU R T).schur =
          -(complete P.ell*(Q.extendBottom P.v P.v_pos).schur) := by
        apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
        rw [← hm] at hmark
        linear_combination -hmark
      apply R.threeComponentU_complete_not_dvd hQR T.ell T.left T.u T.ell
        T.ell_pos (by have := T.g₁_pos; unfold ThreeComponentParameters.left; omega)
        T.u_pos T.ell_pos
      change complete T.ell ∣ (middleU R T).schur
      rw [hU,← hℓ]
      exact dvd_neg.mpr (dvd_mul_right _ _)
  · rcases lt_trichotomy T.v (T.left+T.u) with ht | ht | ht
    · rw [endThirdResponse_E0 Q P hp,threeMiddleContext_third_M1 R T ht] at hmark
      apply Q.three_end_tied_marker_not_dvd_core hQ.connected P
      rw [hmark,hfun]
      exact dvd_neg.mpr (dvd_mul_left _ _)
    · have hv : P.v = T.v := by
        have hkP : Q.threeThirdIndex P = Q.largestLabel+P.left+P.right+P.u := by
          rw [threeThirdIndex,max_eq_left (by omega)]
        have hkT : R.threeThirdIndex T = R.largestLabel+T.left+T.right+T.u := by
          rw [threeThirdIndex,max_eq_left (by omega)]
        rw [hkP,hkT] at hK
        omega
      have hL : P.left = T.left := by omega
      have hA : (threeComponentA P).schur = (threeComponentA T).schur := by
        rw [threeComponentA_schur,threeComponentA_schur,hℓ,hm,hL,hu]
      rw [endThirdResponse_E0 Q P hp,threeMiddleContext_third_M0 R T ht,
        hA,hfun] at hmark
      apply cross_second_tie_any_core Q R hQ hR hfun T ht
      simpa only [hℓ,hm,hv,middleU] using hmark
    · rw [endThirdResponse_E0 Q P hp,threeMiddleContext_third_M2 R T ht] at hmark
      apply Q.three_end_tied_marker_not_dvd_second_singleton hQ.connected P
      rw [hmark,hm]
      exact dvd_mul_right _ _
  · rcases lt_trichotomy T.v (T.left+T.u) with ht | ht | ht
    · rw [endThirdResponse_E2 Q P hp,threeMiddleContext_third_M1 R T ht,hfun] at hmark
      have hA : (threeComponentA P).schur =
          -(complete T.ell*complete (T.m+T.v)) := by
        apply mul_right_cancel₀ R.schur_ne_zero
        linear_combination hmark
      apply threeComponentA_complete_not_dvd P P.ell P.ell_pos
      rw [hA,hℓ]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    · rw [endThirdResponse_E2 Q P hp,threeMiddleContext_third_M0 R T ht] at hmark
      apply R.three_middle_tied_marker_not_dvd_core hR.connected hQR T
      change R.schur ∣ -(complete T.ell*complete (T.m+T.v)*R.schur)+
        complete T.m*(middleU R T).schur
      rw [← hmark,hfun]
      exact dvd_mul_left _ _
    · rw [endThirdResponse_E2 Q P hp,threeMiddleContext_third_M2 R T ht] at hmark
      apply R.three_middle_intermediate_marker_not_dvd_core hR.connected hQR T
      change R.schur ∣ complete T.m*(middleU R T).schur
      rw [← hmark,hfun]
      exact dvd_mul_left _ _

/-- Full cross-placement separation, with either middle orientation and margin order. -/
theorem threeEndContext_ne_threeMiddleContext (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) :
    (Q.threeEndContext P).schur ≠ (R.threeMiddleContext T).schur := by
  by_cases hT : T.u ≤ T.v
  · exact end_middle_top_order_ne Q R hQ hR P T hT
  · have hRR : R.rotate.FourPlacementSource := hR.of_schur_eq R.rotate R.rotate_schur.symm
    have hrot := threeMiddleContext_rotation R T
    have horder : T.swap.u ≤ T.swap.v := by
      simp only [ThreeComponentParameters.swap]
      omega
    intro he
    exact end_middle_top_order_ne Q R.rotate hQ hRR P T.swap horder (he.trans hrot.schur_eq)

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem threeEndContext_positiveCorner (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : (Q.threeEndContext P).PositiveCorner :=
  (Q.singletonCore P.m P.g₂ P.m_pos P.g₂_pos).singletonContext_positiveCorner
    P.ell P.u P.v P.g₁ P.ell_pos P.u_pos P.v_pos P.g₁_pos

/-- The actual column list before normalization of the core. -/
theorem threeEndContext_cols_unaligned (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).col =
      ![Q.row 0+P.right+P.g₁+P.v,Q.row 0+P.g₂+P.v,
        P.v+Q.col 0,P.v+Q.col 1,P.v+Q.col 2,P.v+Q.col 3,Q.col 3] := by
  funext i
  fin_cases i <;>
    simp [threeEndContext,singletonContext,shifted,singletonCore,positiveBorder,
      ThreeComponentParameters.right,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,
      Fin.snoc,Fin.castPred,Fin.castLT] <;> ring

/-- Every complement is a genuine last-column diagram with its produced positive diagonal. -/
def threeEndColumnMinor (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (r : Fin 7) : BetaDiagram 6 :=
  (Q.threeEndContext P).lastColumnDiagram (Q.threeEndContext_positiveCorner P) r

/-- Deleting the first core row produces the connected moving-bottom complement. -/
theorem threeEndColumnMinor_core_zero_connected (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    (Q.threeEndColumnMinor P ((0 : Fin 4).natAdd 3)).Connected := by
  have hP := Q.positiveCorner_of_connected_zeroFree hQ.connected hQ.zeroFree
  have h₀ := hP (0 : Fin 3)
  have h₁ := hP (1 : Fin 3)
  have h₂ := hP (2 : Fin 3)
  change Q.col 0 < Q.row 1 at h₀
  change Q.col 1 < Q.row 2 at h₁
  change Q.col 2 < Q.row 3 at h₂
  have hℓ := P.ell_pos
  have hm := P.m_pos
  refine ⟨by omega,?_⟩
  intro i hi
  change (Q.threeEndContext P).col i.castSucc ≤
    (Q.threeEndContext P).row (((0 : Fin 4).natAdd 3).succAbove ⟨i.val+1,hi⟩)
  fin_cases i <;> norm_num only [Fin.val_mk,Fin.val_succ] at hi <;>
    norm_num [threeEndContext_rows,threeEndContext_cols_unaligned,Fin.succAbove,
      Fin.lt_def,Fin.le_def,ThreeComponentParameters.left,ThreeComponentParameters.right] <;> omega

theorem threeEndColumnMinor_core_zero_irreducible (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    Irreducible (Q.threeEndColumnMinor P ((0 : Fin 4).natAdd 3)).schur :=
  (Q.threeEndColumnMinor P ((0 : Fin 4).natAdd 3)).schur_irreducible
    (Q.threeEndColumnMinor_core_zero_connected hQ P)

theorem threeEndColumnMinor_core_span (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (j : Fin 4) :
    (Q.threeEndColumnMinor P (j.natAdd 3)).largestLabel =
      Q.largestLabel+P.left+P.right+P.u := by
  fin_cases j <;>
    norm_num [threeEndColumnMinor,lastColumnDiagram,largestLabel,threeEndContext_rows,
      threeEndContext_cols_unaligned,Fin.succAbove,Fin.lt_def,Fin.le_def] <;> ring

theorem threeEndColumnMinor_head_suffix (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (r : Fin 3) :
    (Q.threeEndColumnMinor P (r.castAdd 4)).suffix (a := 2) (b := 4) = Q.shifted P.v := by
  apply eq_of_lists
  · funext i
    fin_cases r <;> fin_cases i <;>
      norm_num [threeEndColumnMinor,lastColumnDiagram,suffix,shifted,threeEndContext_rows,
        Fin.succAbove,Fin.lt_def,Fin.le_def] <;> ring
  · funext i
    fin_cases r <;> fin_cases i <;>
      norm_num [threeEndColumnMinor,lastColumnDiagram,suffix,shifted,threeEndContext_cols_unaligned,
        Fin.succAbove,Fin.lt_def,Fin.le_def] <;> ring

theorem threeEndColumnMinor_head_matrix (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (r : Fin 3) :
    ((Q.threeEndColumnMinor P (r.castAdd 4)).betaPrefix (a := 2) (b := 4)).matrix =
      ![![![complete P.ell,complete (P.m+P.left)],
           ![complete (-P.g₁),complete P.m]],
        ![![complete (P.ell+P.u),complete (P.m+P.left+P.u)],
           ![complete (-P.g₁),complete P.m]],
        ![![complete (P.ell+P.u),complete (P.m+P.left+P.u)],
           ![complete P.ell,complete (P.m+P.left)]]] r := by
  apply Matrix.ext
  intro i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrix,threeEndColumnMinor,lastColumnDiagram,betaPrefix,threeEndContext_rows,
      threeEndContext_cols_unaligned,Fin.succAbove,Fin.lt_def,Fin.le_def,
      ThreeComponentParameters.left,ThreeComponentParameters.right] <;> congr 1 <;> ring

/-- The full first three complementary determinants factor at their genuine cut. -/
theorem threeEndColumnMinor_head_schur (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (r : Fin 3) :
    (Q.threeEndColumnMinor P (r.castAdd 4)).schur =
      ![complete P.ell*complete P.m*Q.schur,
        complete (P.ell+P.u)*complete P.m*Q.schur,
        (threeComponentA P).schur*Q.schur] r := by
  have hg := P.g₂_pos
  have hcut : (Q.threeEndColumnMinor P (r.castAdd 4)).row 2 <
      (Q.threeEndColumnMinor P (r.castAdd 4)).col 1 := by
    fin_cases r <;>
      norm_num [threeEndColumnMinor,lastColumnDiagram,threeEndContext_rows,
        threeEndContext_cols_unaligned,Fin.succAbove,Fin.lt_def,Fin.le_def] <;> omega
  rw [(Q.threeEndColumnMinor P (r.castAdd 4)).schur_factor_at_cut
    (a := 2) (b := 4) (by omega) (by omega) hcut,
    threeEndColumnMinor_head_suffix,shifted_schur]
  have hneg : complete (-P.g₁) = 0 := complete_of_neg (by have := P.g₁_pos; omega)
  change (((Q.threeEndColumnMinor P (r.castAdd 4)).betaPrefix
    (a := 2) (b := 4)).matrix).det*Q.schur = _
  rw [threeEndColumnMinor_head_matrix]
  fin_cases r
  · norm_num [Matrix.det_fin_two,hneg]
  · norm_num [Matrix.det_fin_two,hneg]
  · rw [Matrix.det_fin_two]
    change
      (complete (P.ell+P.u)*complete (P.m+P.left) -
        complete (P.m+P.left+P.u)*complete P.ell)*Q.schur =
      (threeComponentA P).schur*Q.schur
    rw [threeComponentA_schur,
      mul_comm (complete (P.m+P.left+P.u)) (complete P.ell)]

noncomputable def threeEndColumnInitial (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : CompleteRing :=
  complete P.ell*complete P.m*Q.schur*complete (Q.threeEndContext P).largestLabel -
    complete (P.ell+P.u)*complete P.m*Q.schur*
      complete ((Q.threeEndContext P).largestLabel-P.u) +
    (threeComponentA P).schur*Q.schur*complete (Q.largestLabel+P.right+P.v)

noncomputable def threeEndColumnResidual (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : CompleteRing :=
  - ∑ j : Fin 4, MvPolynomial.C ((-1 : ℚ)^j.val)*
      complete (Q.row j+P.v-Q.col 3)*(Q.threeEndColumnMinor P (j.natAdd 3)).schur

private theorem three_end_column_sum (f : Fin 7 → CompleteRing) :
    (∑ i,f i) = (∑ i : Fin 3,f (i.castAdd 4))+∑ j : Fin 4,f (j.natAdd 3) :=
  Fin.sum_univ_add (a := 3) (b := 4) f

theorem threeEndContext_column_expansion (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).schur = Q.threeEndColumnInitial P+Q.threeEndColumnResidual P := by
  let D := Q.threeEndContext P
  have hminor : ∀ r : Fin 7,
      (D.matrix.submatrix r.succAbove (Fin.last 6).succAbove).det =
        (Q.threeEndColumnMinor P r).schur := by
    intro r
    exact (D.lastColumnDiagram_schur (Q.threeEndContext_positiveCorner P) r).symm
  have h₀ : D.row 0-D.col 6 = D.largestLabel := rfl
  have h₁ : D.row 1-D.col 6 = D.largestLabel-P.u := by
    dsimp [D,largestLabel]
    rw [threeEndContext_rows,threeEndContext_cols_unaligned]
    norm_num <;> ring
  have h₂ : D.row 2-D.col 6 = Q.largestLabel+P.right+P.v := by
    dsimp [D,largestLabel]
    rw [threeEndContext_rows,threeEndContext_cols_unaligned]
    norm_num <;> ring
  have hcore : ∀ j : Fin 4,D.row (j.natAdd 3)-D.col 6 = Q.row j+P.v-Q.col 3 := by
    intro j
    fin_cases j <;> norm_num [D,threeEndContext_rows,threeEndContext_cols_unaligned] <;> ring
  have hc₀ : D.row 3-D.col 6 = Q.row 0+P.v-Q.col 3 := hcore 0
  have hc₁ : D.row 4-D.col 6 = Q.row 1+P.v-Q.col 3 := hcore 1
  have hc₂ : D.row 5-D.col 6 = Q.row 2+P.v-Q.col 3 := hcore 2
  have hc₃ : D.row 6-D.col 6 = Q.row 3+P.v-Q.col 3 := hcore 3
  change D.matrix.det = _
  rw [Matrix.det_succ_column D.matrix (Fin.last 6),three_end_column_sum]
  simp only [hminor]
  simp only [matrix,Matrix.of_apply]
  simp only [threeEndColumnMinor_head_schur,Fin.val_castAdd,Fin.val_natAdd,hcore]
  simp only [threeEndColumnInitial,threeEndColumnResidual,Fin.sum_univ_succ,
    Fin.val_zero,Fin.val_succ,h₀,h₁,h₂]
  norm_num only [Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,Fin.val_mk,
    Fin.castAdd,Fin.castLE,Fin.natAdd,Fin.last,Fin.succ,pow_zero,pow_succ,
    MvPolynomial.C_1,MvPolynomial.C_neg,zero_add,add_zero,mul_one,one_mul]
  change
    complete (D.row 0-D.col 6)*(complete P.ell*complete P.m*Q.schur) +
      (-1*complete (D.row 1-D.col 6)*(complete (P.ell+P.u)*complete P.m*Q.schur) +
        complete (D.row 2-D.col 6)*((threeComponentA P).schur*Q.schur)) +
      (-1*complete (D.row 3-D.col 6)*(Q.threeEndColumnMinor P 3).schur +
        (complete (D.row 4-D.col 6)*(Q.threeEndColumnMinor P 4).schur +
          (-1*complete (D.row 5-D.col 6)*(Q.threeEndColumnMinor P 5).schur +
            complete (D.row 6-D.col 6)*(Q.threeEndColumnMinor P 6).schur))) = _
  rw [h₀,h₁,h₂,hc₀,hc₁,hc₂,hc₃]
  dsimp only [D]
  ring
  all_goals rfl

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem four_extendBottom_positiveCorner (Q : BetaDiagram 4)
    (hP : Q.PositiveCorner) (v : ℤ) (hv : 0 < v) :
    (Q.extendBottom v hv).PositiveCorner := by
  intro i
  have hh := hP i
  fin_cases i <;> simpa [extendBottom] using hh

def threeEndCoreColumnMinor (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters)
    (j : Fin 4) : BetaDiagram 3 :=
  (Q.extendBottom P.v P.v_pos).lastColumnDiagram
    (four_extendBottom_positiveCorner Q
      (Q.positiveCorner_of_connected_zeroFree hQ.connected hQ.zeroFree) P.v P.v_pos) j

private theorem threeEndColumnMinor_core_positiveCorner (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) (j : Fin 4) :
    (Q.threeEndColumnMinor P (j.natAdd 3)).PositiveCorner := by
  have hP := Q.positiveCorner_of_connected_zeroFree hQ.connected hQ.zeroFree
  have h₀ := hP (0 : Fin 3)
  have h₁ := hP (1 : Fin 3)
  have h₂ := hP (2 : Fin 3)
  change Q.col 0 < Q.row 1 at h₀
  change Q.col 1 < Q.row 2 at h₁
  change Q.col 2 < Q.row 3 at h₂
  have hd₀ := Q.row_nonempty 0
  have hd₁ := Q.row_nonempty 1
  have hd₂ := Q.row_nonempty 2
  have hd₃ := Q.row_nonempty 3
  have hr₀ := Q.row_strictAnti (show (0 : Fin 4) < 1 by decide)
  have hr₁ := Q.row_strictAnti (show (1 : Fin 4) < 2 by decide)
  have hr₂ := Q.row_strictAnti (show (2 : Fin 4) < 3 by decide)
  have hℓ := P.ell_pos
  have hm := P.m_pos
  intro i
  fin_cases j <;> fin_cases i <;>
    norm_num [threeEndColumnMinor,lastColumnDiagram,threeEndContext_rows,
      threeEndContext_cols_unaligned,Fin.succAbove,Fin.lt_def,Fin.le_def,
      ThreeComponentParameters.left,ThreeComponentParameters.right] <;> omega

private theorem threeEndColumnMinor_core_suffix (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) (j : Fin 4) :
    let M := Q.threeEndColumnMinor P (j.natAdd 3)
    let C := M.cornerDiagram (threeEndColumnMinor_core_positiveCorner Q hQ P j)
    C.suffix (a := 2) (b := 3) = (Q.threeEndCoreColumnMinor hQ P j).shifted P.v := by
  dsimp only
  apply eq_of_lists
  · funext i
    fin_cases j <;> fin_cases i <;>
      norm_num [suffix,cornerDiagram,threeEndColumnMinor,threeEndCoreColumnMinor,
        lastColumnDiagram,shifted,extendBottom,threeEndContext_rows,
        Fin.succAbove,Fin.lt_def,Fin.le_def] <;> ring
  · funext i
    fin_cases j <;> fin_cases i <;>
      norm_num [suffix,cornerDiagram,threeEndColumnMinor,threeEndCoreColumnMinor,
        lastColumnDiagram,shifted,extendBottom,threeEndContext_cols_unaligned,
        Fin.succAbove,Fin.lt_def,Fin.le_def] <;> ring

private theorem threeEndColumnMinor_core_head (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) (j : Fin 4) :
    let M := Q.threeEndColumnMinor P (j.natAdd 3)
    let C := M.cornerDiagram (threeEndColumnMinor_core_positiveCorner Q hQ P j)
    (C.betaPrefix (a := 2) (b := 3)).matrix =
      ![![complete P.ell,complete (P.m+P.left)],![complete (-P.g₁),complete P.m]] := by
  dsimp only
  apply Matrix.ext
  intro a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [betaPrefix,cornerDiagram,matrix,threeEndColumnMinor,lastColumnDiagram,
      threeEndContext_rows,threeEndContext_cols_unaligned,Fin.succAbove,Fin.lt_def,
      Fin.le_def,ThreeComponentParameters.left,ThreeComponentParameters.right] <;> congr 1 <;> ring

private theorem two_schur_of_triangular_matrix (A : BetaDiagram 2)
    (l m w g : ℤ) (hg : 0 < g)
    (he : A.matrix = ![![complete l,complete w],![complete (-g),complete m]]) :
    A.schur = complete l*complete m := by
  rw [schur,he,Matrix.det_fin_two,complete_of_neg (show -g < 0 by omega)]
  simp [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]

/-- Signed corners of actual moving minors retain both singleton factors and the full core complement. -/
theorem threeEndColumnMinor_core_corner (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) (j : Fin 4) :
    (Q.threeEndColumnMinor P (j.natAdd 3)).cornerCoefficient =
      -(complete P.ell*complete P.m*(Q.threeEndCoreColumnMinor hQ P j).schur) := by
  let M := Q.threeEndColumnMinor P (j.natAdd 3)
  let hp := threeEndColumnMinor_core_positiveCorner Q hQ P j
  let C := M.cornerDiagram hp
  have hr₁ := Q.row_strictAnti.antitone (Fin.zero_le (1 : Fin 4))
  have hr₂ := Q.row_strictAnti.antitone (Fin.zero_le (2 : Fin 4))
  have hr₃ := Q.row_strictAnti.antitone (Fin.zero_le (3 : Fin 4))
  have hg := P.g₂_pos
  have hcut : C.row 2 < C.col 1 := by
    fin_cases j <;> norm_num [C,M,cornerDiagram,threeEndColumnMinor,lastColumnDiagram,
      threeEndContext_rows,threeEndContext_cols_unaligned,Fin.succAbove,Fin.lt_def,Fin.le_def] <;> omega
  have htail : C.suffix (a := 2) (b := 3) =
      (Q.threeEndCoreColumnMinor hQ P j).shifted P.v :=
    threeEndColumnMinor_core_suffix Q hQ P j
  have hhead : (C.betaPrefix (a := 2) (b := 3)).matrix =
      ![![complete P.ell,complete (P.m+P.left)],![complete (-P.g₁),complete P.m]] :=
    threeEndColumnMinor_core_head Q hQ P j
  have hschur : C.schur = complete P.ell*complete P.m*(Q.threeEndCoreColumnMinor hQ P j).schur := by
    rw [C.schur_factor_at_cut (a := 2) (b := 3) (by omega) (by omega) hcut,htail,shifted_schur]
    rw [two_schur_of_triangular_matrix (C.betaPrefix (a := 2) (b := 3))
      P.ell P.m (P.m+P.left) P.g₁ P.g₁_pos hhead]
  change (-1 : CompleteRing)^5*M.cornerPolynomial = _
  rw [← M.cornerDiagram_schur hp]
  change (-1 : CompleteRing)^5*C.schur = _
  rw [hschur]
  norm_num

private theorem threeEndCoreColumnMinor_expansion (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    (Q.extendBottom P.v P.v_pos).schur =
      - ∑ j : Fin 4,MvPolynomial.C ((-1 : ℚ)^j.val)*
        complete (Q.row j+P.v-Q.col 3)*(Q.threeEndCoreColumnMinor hQ P j).schur := by
  let E := Q.extendBottom P.v P.v_pos
  have hm : ∀ j : Fin 4,
      (E.matrix.submatrix j.succAbove (Fin.last 3).succAbove).det =
        (Q.threeEndCoreColumnMinor hQ P j).schur := by
    intro j
    exact (E.lastColumnDiagram_schur (four_extendBottom_positiveCorner Q
      (Q.positiveCorner_of_connected_zeroFree hQ.connected hQ.zeroFree) P.v P.v_pos) j).symm
  change E.matrix.det = _
  rw [Matrix.det_succ_column E.matrix (Fin.last 3)]
  simp only [hm]
  simp only [matrix,Matrix.of_apply,Fin.sum_univ_succ]
  norm_num [E,extendBottom] <;> ring

theorem threeEndColumnResidual_upper (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) (k : ℕ+)
    (hk : (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.u)
    (hlower : Q.largestLabel+P.v < (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.threeEndColumnResidual P) =
      -(complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur) := by
  have hentry : ∀ j : Fin 4,
      MvPolynomial.pderiv k (complete (Q.row j+P.v-Q.col 3)) = 0 := by
    intro j
    have hr := Q.row_strictAnti.antitone (Fin.zero_le j)
    rw [pderiv_complete_label,if_neg]
    change Q.row 0-Q.col 3+P.v < (k.val : ℤ) at hlower
    omega
  have hminor : ∀ j : Fin 4,
      MvPolynomial.pderiv k (Q.threeEndColumnMinor P (j.natAdd 3)).schur =
        -(complete P.ell*complete P.m*(Q.threeEndCoreColumnMinor hQ P j).schur) := by
    intro j
    rw [(Q.threeEndColumnMinor P (j.natAdd 3)).pderiv_schur_at k
      (by rw [threeEndColumnMinor_core_span]; exact hk),threeEndColumnMinor_core_corner]
  have he := threeEndCoreColumnMinor_expansion Q hQ P
  rw [threeEndColumnResidual,map_neg,map_sum]
  simp only [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,hentry,hminor,
    zero_mul,mul_zero,zero_add,add_zero]
  calc
    _ = (complete P.ell*complete P.m) *
        (∑ j : Fin 4, MvPolynomial.C ((-1 : ℚ)^j.val)*
          complete (Q.row j+P.v-Q.col 3)*(Q.threeEndCoreColumnMinor hQ P j).schur) := by
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [he]; ring

theorem threeEndColumnResidual_above (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (k : ℕ+)
    (hupper : Q.largestLabel+P.left+P.right+P.u < (k.val : ℤ))
    (hlower : Q.largestLabel+P.v ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.threeEndColumnResidual P) =
      -(if (k.val : ℤ) = Q.largestLabel+P.v then
        (Q.threeEndColumnMinor P ((0 : Fin 4).natAdd 3)).schur else 0) := by
  have hminor : ∀ j : Fin 4,
      MvPolynomial.pderiv k (Q.threeEndColumnMinor P (j.natAdd 3)).schur = 0 := by
    intro j
    apply (Q.threeEndColumnMinor P (j.natAdd 3)).pderiv_schur_above k
    rw [threeEndColumnMinor_core_span]
    exact hupper
  have hentry : ∀ j : Fin 4,
      MvPolynomial.pderiv k (complete (Q.row j+P.v-Q.col 3)) =
        if j = 0 ∧ (k.val : ℤ) = Q.largestLabel+P.v then 1 else 0 := by
    intro j
    rw [pderiv_complete_label]
    by_cases hj : j = 0
    · subst j
      simp only [true_and]
      congr 1
      apply propext
      change Q.row 0+P.v-Q.col 3 = (k.val : ℤ) ↔
        (k.val : ℤ) = Q.row 0-Q.col 3+P.v
      constructor <;> intro hh <;> omega
    · have hr := Q.row_strictAnti (Fin.pos_iff_ne_zero.mpr hj)
      rw [if_neg (by change Q.row 0-Q.col 3+P.v ≤ (k.val : ℤ) at hlower; omega),
        if_neg (by tauto)]
  rw [threeEndColumnResidual,map_neg,map_sum]
  simp only [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,hentry,hminor,
    zero_mul,mul_zero,zero_add,add_zero]
  by_cases h : (k.val : ℤ) = Q.largestLabel+P.v <;> simp [h]

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

theorem threeEndColumnInitial_eq (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hfun : Q.schur = R.schur)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u) (hL : P.left = T.left)
    (hN : (Q.threeEndContext P).largestLabel = (R.threeEndContext T).largestLabel) :
    Q.threeEndColumnInitial P = R.threeEndColumnInitial T := by
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hRv : Q.largestLabel+P.right+P.v = R.largestLabel+T.right+T.v := by
    rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
    omega
  unfold threeEndColumnInitial
  rw [threeComponentA_schur,threeComponentA_schur,hfun,hℓ,hm,hu,hL,hN,hRv]

/-- Independent positive end parents cannot have different bottom margins once
their left data is recovered.  The equality-of-levels case uses the actual irreducible complement. -/
theorem threeEndContext_ne_of_bottom_increase (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hfun : Q.schur = R.schur)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u) (hL : P.left = T.left)
    (hv : P.v < T.v) :
    (Q.threeEndContext P).schur ≠ (R.threeEndContext T).schur := by
  intro he
  have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
    (R.threeEndContext T) (Q.threeEndContext_connected P) (R.threeEndContext_connected T) he
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hinitial := threeEndColumnInitial_eq Q R hQ hR P T hfun hℓ hm hu hL hN
  have hres : Q.threeEndColumnResidual P = R.threeEndColumnResidual T := by
    rw [threeEndContext_column_expansion,threeEndContext_column_expansion,hinitial] at he
    exact add_left_cancel he
  let U := Q.largestLabel+P.left+P.right+P.u
  let V := R.largestLabel+T.v
  have hupper : R.largestLabel+T.left+T.right+T.u < U := by
    rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
    dsimp [U]
    omega
  have hlower : Q.largestLabel+P.v < V := by dsimp [V]; omega
  have hU : 0 < U := by
    have hSpos := Q.largestLabel_pos
    have hLp := P.left_pos
    have hRp := P.right_pos
    have hup := P.u_pos
    dsimp [U]
    omega
  have hV : 0 < V := by have := R.largestLabel_pos; have := T.v_pos; dsimp [V]; omega
  let k : ℕ+ := ⟨(max U V).toNat,by have := le_max_left U V; omega⟩
  have hk : (k.val : ℤ) = max U V := by dsimp [k]; omega
  have hd := congrArg (MvPolynomial.pderiv k) hres
  let F := complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur
  let M := R.threeEndColumnMinor T ((0 : Fin 4).natAdd 3)
  have hF : F ≠ 0 := mul_ne_zero
    (mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
      ((complete_ne_zero_iff _).mpr P.m_pos.le)) (Q.extendBottom P.v P.v_pos).schur_ne_zero
  rcases lt_trichotomy U V with h | h | h
  · have hkv : (k.val : ℤ) = V := by rw [max_eq_right h.le] at hk; exact hk
    rw [Q.threeEndColumnResidual_above P k (by omega) (by omega),
      R.threeEndColumnResidual_above T k (by omega) (by dsimp [V] at hkv; omega),
      if_neg (by omega),if_pos (by dsimp [V] at hkv; exact hkv)] at hd
    exact M.schur_ne_zero (by simpa [M] using hd.symm)
  · have hku : (k.val : ℤ) = U := by rw [← h,max_self] at hk; exact hk
    rw [Q.threeEndColumnResidual_upper hQ P k hku (by omega),
      R.threeEndColumnResidual_above T k (by omega) (by dsimp [V] at h; omega),
      if_pos (by dsimp [V] at h; omega)] at hd
    have hprod : M.schur = complete P.ell*
        ((Q.extendBottom P.v P.v_pos).singletonCore P.m 1 P.m_pos (by norm_num)).schur := by
      rw [singletonCore_schur]
      dsimp [M] at hd ⊢
      linear_combination hd
    obtain hleft | hright :=
      (R.threeEndColumnMinor_core_zero_irreducible hR T).isUnit_or_isUnit hprod
    · exact (singletonDiagram P.ell P.ell_pos).schur_not_isUnit (by omega)
        (by simpa only [singletonDiagram_schur] using hleft)
    · exact ((Q.extendBottom P.v P.v_pos).singletonCore
        P.m 1 P.m_pos (by norm_num)).schur_not_isUnit (by omega) hright
  · have hku : (k.val : ℤ) = U := by rw [max_eq_left h.le] at hk; exact hk
    rw [Q.threeEndColumnResidual_upper hQ P k hku (by omega),
      R.threeEndColumnResidual_above T k (by omega) (by dsimp [V] at h; omega),
      if_neg (by dsimp [V] at h; omega)] at hd
    exact (neg_ne_zero.mpr hF) hd

theorem threeEndContext_parameters_of_left_data (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hfun : Q.schur = R.schur)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u) (hL : P.left = T.left)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) : P = T := by
  have hv : P.v = T.v := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact threeEndContext_ne_of_bottom_increase Q R hQ hR P T hfun hℓ hm hu hL h he
    · exact threeEndContext_ne_of_bottom_increase R Q hR hQ T P hfun.symm
        hℓ.symm hm.symm hu.symm hL.symm h he.symm
  have hS := Q.largestLabel_eq_of_schur_eq R hQ.connected hR.connected hfun
  have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
    (R.threeEndContext T) (Q.threeEndContext_connected P) (R.threeEndContext_connected T) he
  rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
  have hRright : P.right = T.right := by omega
  apply threeComponentParameters_eq_of_fields P T hℓ hm
  · unfold ThreeComponentParameters.left at hL
    omega
  · unfold ThreeComponentParameters.right at hRright
    omega
  · exact hu
  · exact hv

/-- The complete bottom marker after removal of its common final border term. -/
theorem threeEndContext_second_bottom_marker (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (k : ℕ+)
    (h₁ : Q.largestLabel+P.left+P.right+P.v ≤ (k.val : ℤ))
    (h₂ : P.m+P.left+P.u ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k ((Q.threeEndContext P).schur -
      complete P.ell*complete P.m*(Q.positiveBorder (P.left+P.right+P.u) P.v
        (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega) P.v_pos).schur) =
      -(if (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.v then
        complete P.m*complete (P.ell+P.u)*Q.schur else 0) -
      (if (k.val : ℤ) = P.m+P.left+P.u then
        complete P.ell*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur else 0) := by
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hg := P.g₁_pos
  have hLR : 0 < P.left+P.right := by omega
  have hA : MvPolynomial.pderiv k (threeComponentA P).schur =
      -(if (k.val : ℤ) = P.m+P.left+P.u then complete P.ell else 0) := by
    have ha : P.ell+P.u < (k.val : ℤ) := by unfold ThreeComponentParameters.left at h₂; omega
    have hb : P.m+P.left < (k.val : ℤ) := by omega
    have hc : P.ell < (k.val : ℤ) := by omega
    rw [threeComponentA_schur,map_sub,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,
      pderiv_complete_label,pderiv_complete_label,pderiv_complete_label,pderiv_complete_label]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    split_ifs <;> (try omega) <;>
      simp only [zero_mul,mul_zero,zero_add,add_zero,mul_one,zero_sub,neg_zero]
  have hm0 : MvPolynomial.pderiv k (complete P.m) = 0 := by
    rw [pderiv_complete_label,if_neg (by omega)]
  have ha0 : MvPolynomial.pderiv k (complete (P.ell+P.u)) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at h₂; omega)]
  have hΦ₁ := (Q.positiveBorder P.right P.v P.right_pos P.v_pos).pderiv_schur_above k
    (by rw [positiveBorder_largestLabel]; omega)
  have hΦ₂ := Q.four_border_largest_response (P.left+P.right) P.v hLR P.v_pos k (by omega)
  have hp : (Q.threeEndContext P).schur -
      complete P.ell*complete P.m*(Q.positiveBorder (P.left+P.right+P.u) P.v
        (by omega) P.v_pos).schur =
      (threeComponentA P).schur*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur -
        complete P.m*complete (P.ell+P.u)*(Q.positiveBorder (P.left+P.right) P.v hLR P.v_pos).schur := by
    rw [threeEndContext_schur,← threeComponentA_schur]
    ring
  rw [hp,map_sub,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,
    hA,hm0,ha0,hΦ₁,hΦ₂]
  simp only [zero_mul,mul_zero,zero_add,add_zero]
  have hi : Q.largestLabel+(P.left+P.right)+P.v = Q.largestLabel+P.left+P.right+P.v := by ring
  rw [hi]
  split_ifs <;> ring

theorem FourPlacementSource.end_core_translation_at_fixed_parameters
    {Q : BetaDiagram 4} (hQ : Q.FourPlacementSource) (R : BetaDiagram 4)
    (hfun : Q.schur = R.schur) (P : ThreeComponentParameters)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext P).schur) :
    Q.TranslationEquivalent R := by
  have hR := hQ.of_schur_eq R hfun
  rcases (Q.rotationRigid_iff_same_order).mp hQ.rotationRigid R hR.connected hfun.symm
      with htr | hrot
  · exact htr
  · by_cases hSym : Q.Symmetric
    · exact Q.translation_of_rotation_of_symmetric R hSym hrot
    · have htr := Q.rotated_core_translation R hrot
      have hp := (R.threeEndContext_of_core_translation Q.rotate htr P).schur_eq
      exact (Q.threeEndContext_orientation_ne_of_coefficient
        (hQ.coefficient_ne_zero hSym) P (he.trans hp)).elim

theorem threeEndContext_aligned_of_left_data (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hfun : Q.schur = R.schur)
    (hℓ : P.ell = T.ell) (hm : P.m = T.m) (hu : P.u = T.u) (hL : P.left = T.left)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P = T ∧ Q.TranslationEquivalent R ∧
      (Q.threeEndContext P).TranslationEquivalent (R.threeEndContext T) := by
  have hp := threeEndContext_parameters_of_left_data Q R hQ hR P T hfun hℓ hm hu hL he
  subst T
  have hcore := hQ.end_core_translation_at_fixed_parameters R hfun P he
  exact ⟨rfl,hcore,Q.threeEndContext_of_core_translation R hcore P⟩

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

/-- The bottom type-2 bracket is a genuine connected singleton parent. -/
def threeEndConnectedRemainder (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : BetaDiagram 6 :=
  Q.singletonContext P.m P.left P.v P.g₂ P.m_pos P.left_pos P.v_pos P.g₂_pos

theorem threeEndConnectedRemainder_connected (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) : (Q.threeEndConnectedRemainder P).Connected :=
  Q.singletonContext_connected P.m P.left P.v P.g₂ P.m_pos P.left_pos P.v_pos P.g₂_pos

theorem threeEndConnectedRemainder_schur (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeEndConnectedRemainder P).schur =
      complete (P.m+P.left)*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur -
      complete P.m*(Q.positiveBorder (P.left+P.right) P.v
        (by have := P.left_pos; have := P.right_pos; omega) P.v_pos).schur := by
  rw [threeEndConnectedRemainder,singletonContext_schur]
  have h₁ : P.m+P.g₂ = P.right := rfl
  have h₂ : P.m+P.g₂+P.left = P.left+P.right := by unfold ThreeComponentParameters.right; ring
  simp only [h₁,h₂]
  rw [positiveBorder_schur_parameter_congr Q
    (show P.right+P.left = P.left+P.right by ring) rfl
    (by have := P.right_pos; have := P.left_pos; omega) P.v_pos
    (by have := P.left_pos; have := P.right_pos; omega) P.v_pos]

theorem threeEndContext_connected_remainder_expansion (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).schur =
      complete (P.ell+P.u)*(Q.threeEndConnectedRemainder P).schur -
      complete P.ell*complete (P.m+P.left+P.u)*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur +
      complete P.ell*complete P.m*(Q.positiveBorder (P.left+P.right+P.u) P.v
        (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega) P.v_pos).schur := by
  rw [threeEndContext_schur,threeEndConnectedRemainder_schur]
  ring

/-- Strict bottom type-2 functions fix every margin and separation. -/
theorem threeEndContext_parameters_of_bottom_second_type (Q : BetaDiagram 4)
    (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v)
    (hmarker : complete P.ell*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur =
      complete T.ell*(Q.positiveBorder T.right T.v T.right_pos T.v_pos).schur)
    (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) : P = T := by
  let B := Q.positiveBorder P.right P.v P.right_pos P.v_pos
  let C := Q.positiveBorder T.right T.v T.right_pos T.v_pos
  have hdiv : complete P.ell ∣ complete T.ell*C.schur := by
    rw [← hmarker]
    exact dvd_mul_right _ _
  have hℓ : P.ell = T.ell := by
    rcases (complete_prime P.ell P.ell_pos).dvd_mul.mp hdiv with h | h
    · exact (complete_dvd_complete_iff P.ell T.ell P.ell_pos T.ell_pos).mp h
    · exact (C.complete_not_dvd_connected
        (Q.positiveBorder_connected T.right T.v T.right_pos T.v_pos) P.ell P.ell_pos h).elim
  have hm : P.m = T.m := by rcases hpair with h | h <;> omega
  have hborder : B.schur = C.schur := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr T.ell_pos.le)
    simpa only [B,C,hℓ] using hmarker
  have hR : P.right = T.right := by
    have hs := B.largestLabel_eq_of_schur_eq C
      (Q.positiveBorder_connected P.right P.v P.right_pos P.v_pos)
      (Q.positiveBorder_connected T.right T.v T.right_pos T.v_pos) hborder
    rw [positiveBorder_largestLabel,positiveBorder_largestLabel] at hs
    omega
  have hg₂ : P.g₂ = T.g₂ := by unfold ThreeComponentParameters.right at hR; omega
  have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
    (Q.threeEndContext T) (Q.threeEndContext_connected P) (Q.threeEndContext_connected T) he
  rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
  have hLu : P.left+P.u = T.left+T.u := by omega
  have hlast : P.left+P.right+P.u = T.left+T.right+T.u := by omega
  have hscalar : P.m+P.left+P.u = T.m+T.left+T.u := by omega
  have hprod : complete (P.ell+P.u)*(Q.threeEndConnectedRemainder P).schur =
      complete (T.ell+T.u)*(Q.threeEndConnectedRemainder T).schur := by
    have hh := he
    rw [threeEndContext_connected_remainder_expansion,threeEndContext_connected_remainder_expansion] at hh
    have hb : (Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur =
        (Q.positiveBorder T.right T.v T.right_pos T.v_pos).schur := hborder
    rw [positiveBorder_schur_parameter_congr Q hlast hv
      (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega) P.v_pos
      (by have := T.left_pos; have := T.right_pos; have := T.u_pos; omega) T.v_pos,
      hscalar,hb] at hh
    simp only [hℓ,hm,hv] at hh
    have hh' := sub_common_polynomial_cancel _ _ _ (add_right_cancel hh)
    simpa only [hℓ] using hh'
  have hd : complete (P.ell+P.u) ∣
      complete (T.ell+T.u)*(Q.threeEndConnectedRemainder T).schur := by
    rw [← hprod]
    exact dvd_mul_right _ _
  have hu : P.u = T.u := by
    have ha : 0 < P.ell+P.u := by have := P.ell_pos; have := P.u_pos; omega
    have hb : 0 < T.ell+T.u := by have := T.ell_pos; have := T.u_pos; omega
    rcases (complete_prime (P.ell+P.u) ha).dvd_mul.mp hd with h | h
    · have hh := (complete_dvd_complete_iff (P.ell+P.u) (T.ell+T.u) ha hb).mp h
      omega
    · exact ((Q.threeEndConnectedRemainder T).complete_not_dvd_connected
        (Q.threeEndConnectedRemainder_connected T) (P.ell+P.u) ha h).elim
  have hL : P.left = T.left := by omega
  have hg₁ : P.g₁ = T.g₁ := by unfold ThreeComponentParameters.left at hL; omega
  exact threeComponentParameters_eq_of_fields P T hℓ hm hg₁ hg₂ hu hv

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem threeEndContext_left_of_A_border_product (Q : BetaDiagram 4)
    (P T : ThreeComponentParameters) (hm : P.m = T.m) (hu : P.u = T.u)
    (he : (threeComponentA P).schur*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur =
      (threeComponentA T).schur*(Q.positiveBorder T.right T.v T.right_pos T.v_pos).schur) :
    P.left = T.left := by
  have hdiv : (threeComponentA P).schur ∣ (threeComponentA T).schur*
      (Q.positiveBorder T.right T.v T.right_pos T.v_pos).schur := by
    rw [← he]
    exact dvd_mul_right _ _
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp (threeComponentA_irreducible P)
  have hA : (threeComponentA P).schur = (threeComponentA T).schur := by
    rcases hprime.dvd_mul.mp hdiv with h | h
    · exact (threeComponentA P).schur_eq_of_connected_dvd (threeComponentA T)
        ((threeComponentA_dense P).connected (by omega))
        ((threeComponentA_dense T).connected (by omega)) h
    · exact (connected_schur_not_dvd_of_order_ne (threeComponentA P)
        (Q.positiveBorder T.right T.v T.right_pos T.v_pos)
        ((threeComponentA_dense P).connected (by omega))
        (Q.positiveBorder_connected T.right T.v T.right_pos T.v_pos) (by omega) h).elim
  have hs := (threeComponentA P).largestLabel_eq_of_schur_eq (threeComponentA T)
    ((threeComponentA_dense P).connected (by omega)) ((threeComponentA_dense T).connected (by omega)) hA
  rw [threeComponentA_largestLabel,threeComponentA_largestLabel] at hs
  omega

theorem threeEndContext_parameters_of_bottom_first_type (Q : BetaDiagram 4)
    (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v)
    (hlevel : Q.largestLabel+P.left+P.right+P.v = Q.largestLabel+T.left+T.right+T.v)
    (hmarker : complete P.m*complete (P.ell+P.u)*Q.schur =
      complete T.m*complete (T.ell+T.u)*Q.schur)
    (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) : P = T := by
  have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
    (Q.threeEndContext T) (Q.threeEndContext_connected P) (Q.threeEndContext_connected T) he
  rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
  have hu : P.u = T.u := by omega
  have hs := singleton_pair_recovery P.m (P.ell+P.u) T.m (T.ell+T.u)
    P.m_pos (by have := P.ell_pos; have := P.u_pos; omega)
    T.m_pos (by have := T.ell_pos; have := T.u_pos; omega)
    (mul_right_cancel₀ Q.schur_ne_zero hmarker)
  have hℓ : P.ell = T.ell := by
    have hup := P.u_pos
    rcases hpair with hpair | hpair <;> rcases hs with hs | hs <;> omega
  have hm : P.m = T.m := by rcases hpair with hpair | hpair <;> omega
  have hLR : P.left+P.right = T.left+T.right := by omega
  have hLRu : P.left+P.right+P.u = T.left+T.right+T.u := by omega
  have hprod : (threeComponentA P).schur*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur =
      (threeComponentA T).schur*(Q.positiveBorder T.right T.v T.right_pos T.v_pos).schur := by
    have hh := he
    rw [threeEndContext_schur,threeEndContext_schur,
      ← threeComponentA_schur,← threeComponentA_schur] at hh
    rw [positiveBorder_schur_parameter_congr Q hLR hv
      (by have := P.left_pos; have := P.right_pos; omega) P.v_pos
      (by have := T.left_pos; have := T.right_pos; omega) T.v_pos,
      positiveBorder_schur_parameter_congr Q hLRu hv
      (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega) P.v_pos
      (by have := T.left_pos; have := T.right_pos; have := T.u_pos; omega) T.v_pos] at hh
    simp only [hℓ,hm,hu] at hh
    linear_combination hh
  have hL := threeEndContext_left_of_A_border_product Q P T hm hu hprod
  have hR : P.right = T.right := by omega
  have hg₁ : P.g₁ = T.g₁ := by unfold ThreeComponentParameters.left at hL; omega
  have hg₂ : P.g₂ = T.g₂ := by unfold ThreeComponentParameters.right at hR; omega
  exact threeComponentParameters_eq_of_fields P T hℓ hm hg₁ hg₂ hu hv

theorem row_square_sum_eq_of_schur_eq {n k : ℕ}
    (D : BetaDiagram n) (E : BetaDiagram k) (he : D.schur = E.schur) :
    (∑ i : Fin n,(D.rowLength i : ℤ)^2) = ∑ i : Fin k,(E.rowLength i : ℤ)^2 := by
  have h := congrArg (Base.leastWeight Base.squareWeight.generatorWeight) he
  rw [leastWeight_eq_diagonal,leastWeight_eq_diagonal,diagonal_square_weight,diagonal_square_weight] at h
  exact_mod_cast h

theorem threeEndContext_row_square_sum (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    (∑ i : Fin 7,((Q.threeEndContext P).rowLength i : ℤ)^2) =
      (P.ell+P.u)^2+(P.m+P.left)^2+(Q.row 0-Q.col 0+P.right)^2+
      (Q.row 0-Q.col 1)^2+(Q.row 1-Q.col 2)^2+(Q.row 2-Q.col 3)^2+
      (Q.row 3-Q.col 3+P.v)^2 := by
  simp only [Fin.sum_univ_succ,rowLength,threeEndContext_rows,threeEndContext_cols_unaligned]
  norm_num
  unfold ThreeComponentParameters.left ThreeComponentParameters.right
  ring

/-- The actual square-weight invariant excludes singleton exchange at the bottom tie. -/
theorem threeEndContext_order_of_bottom_ties (Q : BetaDiagram 4)
    (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v)
    (hP : Q.largestLabel+P.left+P.right+P.v = P.m+P.left+P.u)
    (hT : Q.largestLabel+T.left+T.right+T.v = T.m+T.left+T.u)
    (hK : P.m+P.left+P.u = T.m+T.left+T.u)
    (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) :
    P.ell = T.ell ∧ P.m = T.m := by
  rcases hpair with hpair | hpair
  · exact hpair
  by_cases hsame : P.ell = P.m
  · constructor <;> omega
  have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
    (Q.threeEndContext T) (Q.threeEndContext_connected P) (Q.threeEndContext_connected T) he
  rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
  have hu : P.u = T.u := by omega
  have hsum : P.m+P.left = T.m+T.left := by omega
  have hg₂ : P.g₂ = T.g₂ := by unfold ThreeComponentParameters.right at hP hT; omega
  have hleftT : T.left = P.left+P.m-P.ell := by omega
  have hw := row_square_sum_eq_of_schur_eq (Q.threeEndContext P) (Q.threeEndContext T) he
  rw [threeEndContext_row_square_sum,threeEndContext_row_square_sum] at hw
  have hRT : T.right = P.ell+P.g₂ := by unfold ThreeComponentParameters.right; omega
  have hRP : P.right = P.m+P.g₂ := rfl
  rw [← hpair.1,← hpair.2,← hu,← hv,hleftT,hRT,hRP] at hw
  have hprod : (P.ell-P.m)*(P.u-(Q.row 0-Q.col 0+P.g₂)) = 0 := by nlinarith [hw]
  have hforced : P.u = Q.row 0-Q.col 0+P.g₂ := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact (hsame (sub_eq_zero.mp h)).elim
    · omega
  have hc := Q.col_strictAnti (show (0 : Fin 4) < 3 by decide)
  have hvp := P.v_pos
  change Q.row 0-Q.col 3+P.left+(P.m+P.g₂)+P.v = P.m+P.left+P.u at hP
  omega

theorem threeEndContext_parameters_of_bottom_ties (Q : BetaDiagram 4)
    (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v)
    (hP : Q.largestLabel+P.left+P.right+P.v = P.m+P.left+P.u)
    (hT : Q.largestLabel+T.left+T.right+T.v = T.m+T.left+T.u)
    (hK : P.m+P.left+P.u = T.m+T.left+T.u)
    (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) : P = T := by
  obtain ⟨hℓ,hm⟩ := threeEndContext_order_of_bottom_ties Q P T hpair hv hP hT hK he
  have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
    (Q.threeEndContext T) (Q.threeEndContext_connected P) (Q.threeEndContext_connected T) he
  rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
  have hu : P.u = T.u := by omega
  have hL : P.left = T.left := by omega
  have hR : P.right = T.right := by omega
  have hg₁ : P.g₁ = T.g₁ := by unfold ThreeComponentParameters.left at hL; omega
  have hg₂ : P.g₂ = T.g₂ := by unfold ThreeComponentParameters.right at hR; omega
  exact threeComponentParameters_eq_of_fields P T hℓ hm hg₁ hg₂ hu hv

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

noncomputable def endBottomF (Q : BetaDiagram 4) (P : ThreeComponentParameters) : CompleteRing :=
  complete P.m*complete (P.ell+P.u)*Q.schur
noncomputable def endBottomG (Q : BetaDiagram 4) (P : ThreeComponentParameters) : CompleteRing :=
  complete P.ell*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur
def endBottomB (Q : BetaDiagram 4) (P : ThreeComponentParameters) : ℤ :=
  Q.largestLabel+P.left+P.right+P.v
def endBottomZ (P : ThreeComponentParameters) : ℤ := P.m+P.left+P.u
def endBottomIndex (Q : BetaDiagram 4) (P : ThreeComponentParameters) : ℤ :=
  max (endBottomB Q P) (endBottomZ P)
noncomputable def endBottomValue (Q : BetaDiagram 4) (P : ThreeComponentParameters) : CompleteRing :=
  (if endBottomIndex Q P = endBottomB Q P then endBottomF Q P else 0)+
    (if endBottomIndex Q P = endBottomZ P then endBottomG Q P else 0)

theorem endBottomF_ne_zero (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    endBottomF Q P ≠ 0 :=
  mul_ne_zero (mul_ne_zero ((complete_ne_zero_iff _).mpr P.m_pos.le)
    ((complete_ne_zero_iff _).mpr (by have := P.ell_pos; have := P.u_pos; omega))) Q.schur_ne_zero
theorem endBottomG_ne_zero (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    endBottomG Q P ≠ 0 :=
  mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
    (Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur_ne_zero
theorem endBottomF_core_dvd (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    Q.schur ∣ endBottomF Q P := dvd_mul_left _ _

theorem endBottomG_core_not_dvd (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) : ¬ Q.schur ∣ endBottomG Q P := by
  intro hd
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hQ.connected)
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact Q.connected_four_schur_not_dvd_complete hQ.connected P.ell P.ell_pos hd
  · exact connected_schur_not_dvd_of_order_ne Q
      (Q.positiveBorder P.right P.v P.right_pos P.v_pos) hQ.connected
      (Q.positiveBorder_connected P.right P.v P.right_pos P.v_pos) (by omega) hd

theorem endBottomTie_core_not_dvd (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    ¬ Q.schur ∣ endBottomF Q P+endBottomG Q P := by
  intro hd
  apply endBottomG_core_not_dvd Q hQ P
  simpa only [add_sub_cancel_left] using dvd_sub hd (endBottomF_core_dvd Q P)
theorem endBottomTie_ne_zero (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) :
    endBottomF Q P+endBottomG Q P ≠ 0 := by
  intro hz
  apply endBottomTie_core_not_dvd Q hQ P
  rw [hz]
  exact dvd_zero _

theorem endBottomValue_first (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (h : endBottomZ P < endBottomB Q P) : endBottomValue Q P = endBottomF Q P := by
  simp only [endBottomValue,endBottomIndex,max_eq_left h.le,if_true,if_neg (ne_of_gt h),add_zero]
theorem endBottomValue_second (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (h : endBottomB Q P < endBottomZ P) : endBottomValue Q P = endBottomG Q P := by
  simp only [endBottomValue,endBottomIndex,max_eq_right h.le,if_neg (ne_of_gt h),if_true,zero_add]
theorem endBottomValue_tie (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (h : endBottomB Q P = endBottomZ P) :
    endBottomValue Q P = endBottomF Q P+endBottomG Q P := by
  simp only [endBottomValue,endBottomIndex,h,max_self,if_true]
theorem endBottomValue_ne_zero (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) : endBottomValue Q P ≠ 0 := by
  rcases lt_trichotomy (endBottomB Q P) (endBottomZ P) with h | h | h
  · rw [endBottomValue_second Q P h]
    exact endBottomG_ne_zero Q P
  · rw [endBottomValue_tie Q P h]
    exact endBottomTie_ne_zero Q hQ P
  · rw [endBottomValue_first Q P h]
    exact endBottomF_ne_zero Q P

theorem endBottomTie_not_singleton (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters)
    (hne : P.ell ≠ P.m) (s : ℤ) (hs : 0 < s) (hwhich : s = P.ell ∨ s = P.m) :
    ¬ complete s ∣ endBottomF Q P+endBottomG Q P := by
  rcases hwhich with rfl | rfl
  · have hF : ¬ complete P.ell ∣ endBottomF Q P := by
      intro hd
      rcases (complete_prime P.ell P.ell_pos).dvd_mul.mp hd with hd | hd
      · rcases (complete_prime P.ell P.ell_pos).dvd_mul.mp hd with hd | hd
        · exact hne ((complete_dvd_complete_iff P.ell P.m P.ell_pos P.m_pos).mp hd)
        · have hh := (complete_dvd_complete_iff P.ell (P.ell+P.u) P.ell_pos
            (by have := P.ell_pos; have := P.u_pos; omega)).mp hd
          have hu := P.u_pos
          omega
      · exact Q.complete_not_dvd_connected hQ.connected P.ell P.ell_pos hd
    intro hd
    apply hF
    have hG : complete P.ell ∣ endBottomG Q P := dvd_mul_right _ _
    simpa only [add_sub_cancel_right] using dvd_sub hd hG
  · have hG : ¬ complete P.m ∣ endBottomG Q P := by
      intro hd
      rcases (complete_prime P.m P.m_pos).dvd_mul.mp hd with hd | hd
      · exact hne ((complete_dvd_complete_iff P.m P.ell P.m_pos P.ell_pos).mp hd).symm
      · exact (Q.positiveBorder P.right P.v P.right_pos P.v_pos).complete_not_dvd_connected
          (Q.positiveBorder_connected P.right P.v P.right_pos P.v_pos) P.m P.m_pos hd
    intro hd
    apply hG
    have hF : complete P.m ∣ endBottomF Q P := by
      refine ⟨complete (P.ell+P.u)*Q.schur,?_⟩
      unfold endBottomF
      ring
    simpa only [add_sub_cancel_left] using dvd_sub hd hF

/-- The equal-singleton exception still recovers the same right border and leaves a nonzero term. -/
theorem endBottom_second_tie_ne (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v) (hK : endBottomIndex Q P = endBottomIndex Q T)
    (hP : endBottomB Q P < endBottomZ P) (hT : endBottomB Q T = endBottomZ T)
    (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) :
    endBottomG Q P ≠ endBottomF Q T+endBottomG Q T := by
  intro hc
  by_cases hsame : P.ell = P.m
  · have hℓ : P.ell = T.ell := by rcases hpair with hpair | hpair <;> omega
    have hm : P.m = T.m := by rcases hpair with hpair | hpair <;> omega
    have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
      (Q.threeEndContext T) (Q.threeEndContext_connected P) (Q.threeEndContext_connected T) he
    rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
    have hZ : endBottomZ P = endBottomZ T := by
      simpa only [endBottomIndex,max_eq_right hP.le,hT,max_self] using hK
    have hR : P.right = T.right := by unfold endBottomZ at hZ; omega
    have hG : endBottomG Q P = endBottomG Q T := by
      unfold endBottomG
      rw [positiveBorder_schur_parameter_congr Q hR hv
        P.right_pos P.v_pos T.right_pos T.v_pos,hℓ]
    rw [hG] at hc
    apply endBottomF_ne_zero Q T
    linear_combination -hc
  · have hne : T.ell ≠ T.m := by rcases hpair with hpair | hpair <;> omega
    have hwhich : P.ell = T.ell ∨ P.ell = T.m := by
      rcases hpair with hpair | hpair
      · exact Or.inl hpair.1
      · exact Or.inr hpair.1
    apply endBottomTie_not_singleton Q hQ T hne P.ell P.ell_pos hwhich
    rw [← hc]
    exact dvd_mul_right _ _

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

noncomputable def endBottomResidual (Q : BetaDiagram 4) (P : ThreeComponentParameters) : CompleteRing :=
  (Q.threeEndContext P).schur-complete P.ell*complete P.m*
    (Q.positiveBorder (P.left+P.right+P.u) P.v
      (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega) P.v_pos).schur
def endBottomGenerator (Q : BetaDiagram 4) (P : ThreeComponentParameters) : ℕ+ :=
  ⟨(endBottomIndex Q P).toNat,by
    have hm := P.m_pos
    have hL := P.left_pos
    have hu := P.u_pos
    have hk := le_max_right (endBottomB Q P) (endBottomZ P)
    unfold endBottomIndex endBottomZ at *
    omega⟩
theorem endBottomGenerator_int (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    ((endBottomGenerator Q P).val : ℤ) = endBottomIndex Q P := by
  have hm := P.m_pos
  have hL := P.left_pos
  have hu := P.u_pos
  have hk := le_max_right (endBottomB Q P) (endBottomZ P)
  change ((endBottomIndex Q P).toNat : ℤ) = endBottomIndex Q P
  exact Int.toNat_of_nonneg (by unfold endBottomIndex endBottomZ; omega)
theorem endBottomResidual_response (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) (k : ℕ+) (hB : endBottomB Q P ≤ (k.val : ℤ))
    (hZ : endBottomZ P ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k (endBottomResidual Q P) =
      -(if (k.val : ℤ) = endBottomB Q P then endBottomF Q P else 0)-
        (if (k.val : ℤ) = endBottomZ P then endBottomG Q P else 0) :=
  Q.threeEndContext_second_bottom_marker P k hB hZ
theorem endBottomResidual_at (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    MvPolynomial.pderiv (endBottomGenerator Q P) (endBottomResidual Q P) = -endBottomValue Q P := by
  rw [endBottomResidual_response Q P (endBottomGenerator Q P)
    (by rw [endBottomGenerator_int]; exact le_max_left _ _)
    (by rw [endBottomGenerator_int]; exact le_max_right _ _),endBottomGenerator_int]
  unfold endBottomValue
  ring
theorem endBottomResidual_above (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (k : ℕ+) (hk : endBottomIndex Q P < (k.val : ℤ)) :
    MvPolynomial.pderiv k (endBottomResidual Q P) = 0 := by
  have hB := le_max_left (endBottomB Q P) (endBottomZ P)
  have hZ := le_max_right (endBottomB Q P) (endBottomZ P)
  rw [endBottomResidual_response Q P k (by unfold endBottomIndex at hk; omega)
    (by unfold endBottomIndex at hk; omega),if_neg (by unfold endBottomIndex at hk; omega),
    if_neg (by unfold endBottomIndex at hk; omega)]
  ring

theorem endBottomResidual_eq (Q : BetaDiagram 4) (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v) (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) :
    endBottomResidual Q P = endBottomResidual Q T := by
  have hN := (Q.threeEndContext P).largestLabel_eq_of_schur_eq
    (Q.threeEndContext T) (Q.threeEndContext_connected P) (Q.threeEndContext_connected T) he
  rw [threeEndContext_largestLabel,threeEndContext_largestLabel] at hN
  have hW : P.left+P.right+P.u = T.left+T.right+T.u := by omega
  have hprod : complete P.ell*complete P.m = complete T.ell*complete T.m := by
    rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩ <;> rw [hℓ,hm] <;> ring
  unfold endBottomResidual
  rw [positiveBorder_schur_parameter_congr Q hW hv
    (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega) P.v_pos
    (by have := T.left_pos; have := T.right_pos; have := T.u_pos; omega) T.v_pos,
    he,hprod]

/-- Full equality recovers both the next actual level and its complete coefficient. -/
theorem endBottom_marker_recovery (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v) (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) :
    endBottomIndex Q P = endBottomIndex Q T ∧ endBottomValue Q P = endBottomValue Q T := by
  have hr := endBottomResidual_eq Q P T hpair hv he
  have hPne : MvPolynomial.pderiv (endBottomGenerator Q P) (endBottomResidual Q P) ≠ 0 := by
    rw [endBottomResidual_at]
    exact neg_ne_zero.mpr (endBottomValue_ne_zero Q hQ P)
  have hTne : MvPolynomial.pderiv (endBottomGenerator Q T) (endBottomResidual Q T) ≠ 0 := by
    rw [endBottomResidual_at]
    exact neg_ne_zero.mpr (endBottomValue_ne_zero Q hQ T)
  have hK : endBottomIndex Q P = endBottomIndex Q T := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hd := congrArg (MvPolynomial.pderiv (endBottomGenerator Q T)) hr
      rw [← hd,endBottomResidual_above Q P (endBottomGenerator Q T)
        (by rw [endBottomGenerator_int]; exact h)] at hTne
      exact hTne rfl
    · have hd := congrArg (MvPolynomial.pderiv (endBottomGenerator Q P)) hr
      rw [hd,endBottomResidual_above Q T (endBottomGenerator Q P)
        (by rw [endBottomGenerator_int]; exact h)] at hPne
      exact hPne rfl
  have hg : endBottomGenerator Q P = endBottomGenerator Q T := by
    apply Subtype.ext
    simp only [endBottomGenerator,hK]
  have hd := congrArg (MvPolynomial.pderiv (endBottomGenerator Q P)) hr
  rw [endBottomResidual_at,hg,endBottomResidual_at] at hd
  exact ⟨hK,neg_injective hd⟩

/-- All nine actual bottom-type comparisons recover the full parameter tuple. -/
theorem threeEndContext_parameters_of_bottom_data (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v) (he : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur) : P = T := by
  obtain ⟨hK,hc⟩ := endBottom_marker_recovery Q hQ P T hpair hv he
  have hpair' : (T.ell = P.ell ∧ T.m = P.m) ∨ (T.ell = P.m ∧ T.m = P.ell) := by
    rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩
    · exact Or.inl ⟨hℓ.symm,hm.symm⟩
    · exact Or.inr ⟨hm.symm,hℓ.symm⟩
  rcases lt_trichotomy (endBottomB Q P) (endBottomZ P) with hP | hP | hP
  · rw [endBottomValue_second Q P hP] at hc
    rcases lt_trichotomy (endBottomB Q T) (endBottomZ T) with hT | hT | hT
    · rw [endBottomValue_second Q T hT] at hc
      exact threeEndContext_parameters_of_bottom_second_type Q P T hpair hv hc he
    · rw [endBottomValue_tie Q T hT] at hc
      exact (endBottom_second_tie_ne Q hQ P T hpair hv hK hP hT he hc).elim
    · rw [endBottomValue_first Q T hT] at hc
      apply False.elim
      apply endBottomG_core_not_dvd Q hQ P
      rw [hc]
      exact endBottomF_core_dvd Q T
  · rw [endBottomValue_tie Q P hP] at hc
    rcases lt_trichotomy (endBottomB Q T) (endBottomZ T) with hT | hT | hT
    · rw [endBottomValue_second Q T hT] at hc
      exact (endBottom_second_tie_ne Q hQ T P hpair' hv.symm hK.symm hT hP he.symm hc.symm).elim
    · rw [endBottomValue_tie Q T hT] at hc
      have hz : endBottomZ P = endBottomZ T := by
        simpa only [endBottomIndex,hP,hT,max_self] using hK
      exact threeEndContext_parameters_of_bottom_ties Q P T hpair hv hP hT hz he
    · rw [endBottomValue_first Q T hT] at hc
      apply False.elim
      apply endBottomTie_core_not_dvd Q hQ P
      rw [hc]
      exact endBottomF_core_dvd Q T
  · rw [endBottomValue_first Q P hP] at hc
    rcases lt_trichotomy (endBottomB Q T) (endBottomZ T) with hT | hT | hT
    · rw [endBottomValue_second Q T hT] at hc
      apply False.elim
      apply endBottomG_core_not_dvd Q hQ T
      rw [← hc]
      exact endBottomF_core_dvd Q P
    · rw [endBottomValue_tie Q T hT] at hc
      apply False.elim
      apply endBottomTie_core_not_dvd Q hQ T
      rw [← hc]
      exact endBottomF_core_dvd Q P
    · rw [endBottomValue_first Q T hT] at hc
      have hb : endBottomB Q P = endBottomB Q T := by
        simpa only [endBottomIndex,max_eq_left hP.le,max_eq_left hT.le] using hK
      exact threeEndContext_parameters_of_bottom_first_type Q P T hpair hv hb hc he

theorem threeEndContext_bottom_rigidity (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters) (hP : P.v < P.u)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P = T ∧ Q.TranslationEquivalent R ∧
      (Q.threeEndContext P).TranslationEquivalent (R.threeEndContext T) := by
  obtain ⟨hR,hfun,hS,hpair,hq,htotal,hfirst⟩ := placement_common_data Q R hQ P T false false he
  have hT := (threeEndContext_first_phase Q R hQ hR P T he).2.1.mp hP
  have hv : P.v = T.v := by simpa only [min_eq_right hP.le,min_eq_right hT.le] using hq
  have hprod : complete P.ell*complete P.m = complete T.ell*complete T.m := by
    rcases hpair with ⟨hℓ,hm⟩ | ⟨hℓ,hm⟩ <;> rw [hℓ,hm] <;> ring
  have hr := threeEndContext_first_response_eq Q R hQ P T he
  simp only [endFirstResponse,if_neg (by omega : ¬ P.u < P.v),
    if_neg (by omega : ¬ T.u < T.v),if_pos hP,if_pos hT] at hr
  rw [extendBottom_schur_parameter_congr R hv.symm T.v_pos P.v_pos,hprod] at hr
  have hbottom : (Q.extendBottom P.v P.v_pos).schur = (R.extendBottom P.v P.v_pos).schur :=
    mul_left_cancel₀ (mul_ne_zero ((complete_ne_zero_iff _).mpr T.ell_pos.le)
      ((complete_ne_zero_iff _).mpr T.m_pos.le)) (neg_injective hr)
  have hcore := bottom_endpoint_core_recovery Q R hQ hR hfun P.v P.v_pos hbottom
  have hpoly : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur :=
    he.trans (Q.threeEndContext_of_core_translation R hcore T).schur_eq.symm
  have hPT := threeEndContext_parameters_of_bottom_data Q hQ P T hpair hv hpoly
  refine ⟨hPT,hcore,?_⟩
  rw [hPT]
  exact Q.threeEndContext_of_core_translation R hcore T

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

theorem threeEndContext_rigidity_of_known_bottom (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (hR : R.FourPlacementSource)
    (P T : ThreeComponentParameters) (hfun : Q.schur = R.schur)
    (hpair : (P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell))
    (hv : P.v = T.v)
    (hbottom : (Q.extendBottom P.v P.v_pos).schur = (R.extendBottom P.v P.v_pos).schur)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P = T ∧ Q.TranslationEquivalent R ∧
      (Q.threeEndContext P).TranslationEquivalent (R.threeEndContext T) := by
  have hcore := bottom_endpoint_core_recovery Q R hQ hR hfun P.v P.v_pos hbottom
  have hpoly : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur :=
    he.trans (Q.threeEndContext_of_core_translation R hcore T).schur_eq.symm
  have hPT := threeEndContext_parameters_of_bottom_data Q hQ P T hpair hv hpoly
  refine ⟨hPT,hcore,?_⟩
  rw [hPT]
  exact Q.threeEndContext_of_core_translation R hcore T

/-- Strict-top end recovery includes all three actual third-marker regimes. -/
theorem threeEndContext_top_rigidity (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters) (hPtop : P.u < P.v)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P = T ∧ Q.TranslationEquivalent R ∧
      (Q.threeEndContext P).TranslationEquivalent (R.threeEndContext T) := by
  obtain ⟨hR,hfun,hS,hpair,hq,htotal,hfirst⟩ := placement_common_data Q R hQ P T false false he
  obtain ⟨hu,hℓ,hm⟩ := threeEndContext_top_first_recovery Q R hQ hR P T hPtop he
  have hphase := threeEndContext_third_phase Q R hQ hR P T hℓ hm hu he
  have hK := threeEndContext_third_index_recovery Q R hQ hR P T hℓ hm hu he
  have hc := threeEndContext_third_response_eq Q R hQ hR P T hℓ hm hu he
  rcases lt_trichotomy P.v (P.left+P.u) with hP | hP | hP
  · have hT := hphase.1.mp hP
    have hkP : Q.threeThirdIndex P = Q.largestLabel+P.left+P.right+P.u := by
      rw [threeThirdIndex,max_eq_left (by omega)]
    have hkT : R.threeThirdIndex T = R.largestLabel+T.left+T.right+T.u := by
      rw [threeThirdIndex,max_eq_left (by omega)]
    rw [hkP,hkT] at hK
    have hv : P.v = T.v := by omega
    rw [endThirdResponse_E1 Q P hP,endThirdResponse_E1 R T hT,
      extendBottom_schur_parameter_congr R hv.symm T.v_pos P.v_pos] at hc
    simp only [← hℓ,← hm] at hc
    have hbottom : (Q.extendBottom P.v P.v_pos).schur = (R.extendBottom P.v P.v_pos).schur := by
      apply mul_left_cancel₀ (mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
        ((complete_ne_zero_iff _).mpr P.m_pos.le))
      exact neg_injective hc
    exact threeEndContext_rigidity_of_known_bottom Q R hQ hR P T hfun hpair hv hbottom he
  · have hT := hphase.2.2.mp hP
    have hkP : Q.threeThirdIndex P = Q.largestLabel+P.left+P.right+P.u := by
      rw [threeThirdIndex,max_eq_left (by omega)]
    have hkT : R.threeThirdIndex T = R.largestLabel+T.left+T.right+T.u := by
      rw [threeThirdIndex,max_eq_left (by omega)]
    rw [hkP,hkT] at hK
    have hv : P.v = T.v := by omega
    have hL : P.left = T.left := by omega
    have hA : (threeComponentA P).schur = (threeComponentA T).schur := by
      rw [threeComponentA_schur,threeComponentA_schur,hℓ,hm,hL,hu]
    rw [endThirdResponse_E0 Q P hP,endThirdResponse_E0 R T hT,
      extendBottom_schur_parameter_congr R hv.symm T.v_pos P.v_pos,
      hA,hfun] at hc
    simp only [← hℓ,← hm] at hc
    have hbottom : (Q.extendBottom P.v P.v_pos).schur = (R.extendBottom P.v P.v_pos).schur := by
      apply mul_left_cancel₀ (mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
        ((complete_ne_zero_iff _).mpr P.m_pos.le))
      exact neg_injective (add_right_cancel hc)
    exact threeEndContext_rigidity_of_known_bottom Q R hQ hR P T hfun hpair hv hbottom he
  · have hT := hphase.2.1.mp hP
    have hkP : Q.threeThirdIndex P = Q.largestLabel+P.right+P.v := by
      rw [threeThirdIndex,max_eq_right (by omega)]
    have hkT : R.threeThirdIndex T = R.largestLabel+T.right+T.v := by
      rw [threeThirdIndex,max_eq_right (by omega)]
    rw [hkP,hkT] at hK
    have hL : P.left = T.left := by omega
    exact threeEndContext_aligned_of_left_data Q R hQ hR P T hfun hℓ hm hu hL he

/-- Full end recovery imposes no source family, orientation, margin, or singleton
order restriction on the independently parameterized comparison core. -/
theorem threeEndContext_rigidity_between_contexts (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P = T ∧ Q.TranslationEquivalent R ∧
      (Q.threeEndContext P).TranslationEquivalent (R.threeEndContext T) := by
  rcases lt_trichotomy P.u P.v with h | h | h
  · exact threeEndContext_top_rigidity Q R hQ P T h he
  · obtain ⟨hR,hfun,hS,hpair,hq,htotal,hfirst⟩ := placement_common_data Q R hQ P T false false he
    obtain ⟨hu,hv,hℓ,hm,hcore⟩ := threeEndContext_tied_first_recovery Q R hQ hR P T h he
    have hpoly : (Q.threeEndContext P).schur = (Q.threeEndContext T).schur :=
      he.trans (Q.threeEndContext_of_core_translation R hcore T).schur_eq.symm
    have hPT := threeEndContext_parameters_of_bottom_data Q hQ P T hpair hv hpoly
    refine ⟨hPT,hcore,?_⟩
    rw [hPT]
    exact Q.threeEndContext_of_core_translation R hcore T
  · exact threeEndContext_bottom_rigidity Q R hQ P T h he

theorem translation_last_column_aligned_eq {n : ℕ}
    (D E : BetaDiagram (n+1)) (h : D.TranslationEquivalent E) :
    D.shifted (-D.col (Fin.last n)) = E.shifted (-E.col (Fin.last n)) := by
  obtain ⟨c,hr,hc⟩ := h
  have hlast := hc (Fin.last n)
  apply eq_of_lists
  · funext i
    change D.row i+(-D.col (Fin.last n)) = E.row i+(-E.col (Fin.last n))
    rw [hr i,hlast]
    ring
  · funext i
    change D.col i+(-D.col (Fin.last n)) = E.col i+(-E.col (Fin.last n))
    rw [hc i,hlast]
    ring

theorem threeEndContext_literal_aligned_recovery (Q R : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P T : ThreeComponentParameters)
    (he : (Q.threeEndContext P).schur = (R.threeEndContext T).schur) :
    P = T ∧ (Q.threeEndContext P).shifted (-Q.col 3) = (R.threeEndContext T).shifted (-R.col 3) := by
  obtain ⟨hPT,hcore,hparent⟩ := threeEndContext_rigidity_between_contexts Q R hQ P T he
  have hAligned := translation_last_column_aligned_eq (Q.threeEndContext P) (R.threeEndContext T) hparent
  have hQlast : (Q.threeEndContext P).col 6 = Q.col 3 := by
    rw [threeEndContext_cols_unaligned]
    norm_num
  have hRlast : (R.threeEndContext T).col 6 = R.col 3 := by
    rw [threeEndContext_cols_unaligned]
    norm_num
  change (Q.threeEndContext P).shifted (-(Q.threeEndContext P).col 6) =
    (R.threeEndContext T).shifted (-(R.threeEndContext T).col 6) at hAligned
  exact ⟨hPT,by simpa only [hQlast,hRlast] using hAligned⟩

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false


/-- The full end/middle classification applies against arbitrary connected mates
of every row count.  Only the actual four-row source geometry is assumed. -/
theorem fourPlacementSource_context_rotationRigid (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (P : ThreeComponentParameters) (b : Bool) :
    (if b then Q.threeMiddleContext P else Q.threeEndContext P).RotationRigid := by
  rw [rotationRigid_iff_same_order]
  intro E hEC he
  obtain ⟨hrow,R,T,hRN,hRC,hfun,hpair,hform⟩ :=
    Q.three_context_arbitrary_mate_recovery hQ.connected hQ.zeroFree P b E hEC he.symm
  have hcast : E.castOrder hrow = E := by
    have hr : hrow = rfl := Subsingleton.elim _ _
    rw [hr]
    rfl
  rw [hcast] at hform
  have hR := hQ.of_schur_eq R hfun
  cases b with
  | false =>
    simp only [Bool.false_eq_true,if_false] at he ⊢
    rcases hform with hform | hform | hform
    · have hp : (Q.threeEndContext P).schur = (R.threeEndContext T).schur :=
        he.symm.trans hform.schur_eq
      have hclass := (threeEndContext_rigidity_between_contexts Q R hQ P T hp).2.2
      exact Or.inl (hclass.trans hform.symm)
    · have hp : (Q.threeEndContext P).schur = (R.threeMiddleContext T).schur :=
        he.symm.trans hform.schur_eq
      exact (threeEndContext_ne_threeMiddleContext Q R hQ hR P T hp).elim
    · have hp : (Q.threeEndContext P).schur = (R.threeEndContext T).schur :=
        he.symm.trans (E.rotate_schur.symm.trans hform.schur_eq)
      have hclass := (threeEndContext_rigidity_between_contexts Q R hQ P T hp).2.2
      have hr := hclass.trans hform.symm
      exact Or.inr (((Q.threeEndContext P).translation_rotate_iff_rotation E).mp hr)
  | true =>
    simp only [if_true] at he ⊢
    rcases hform with hform | hform | hform
    · have hp : (R.threeEndContext T).schur = (Q.threeMiddleContext P).schur :=
        hform.schur_eq.symm.trans he
      exact (threeEndContext_ne_threeMiddleContext R Q hR hQ T P hp).elim
    · have hp : (Q.threeMiddleContext P).schur = (R.threeMiddleContext T).schur :=
        he.symm.trans hform.schur_eq
      have hclass := threeMiddleContext_rigidity Q R hQ hR P T hp
      exact motion_trans _ _ _ hclass (Or.inl hform.symm)
    · have hp : (R.threeEndContext T).schur = (Q.threeMiddleContext P).schur :=
        hform.schur_eq.symm.trans (E.rotate_schur.trans he)
      exact (threeEndContext_ne_threeMiddleContext R Q hR hQ T P hp).elim

/-- `thm:dense-three-component-rigidity`, for the actual end placement. -/
theorem dense_threeEndContext_rotationRigid (Q : BetaDiagram 4) (hD : Q.Dense)
    (P : ThreeComponentParameters) : (Q.threeEndContext P).RotationRigid :=
  fourPlacementSource_context_rotationRigid Q (Or.inl hD) P false

/-- `thm:dense-three-component-rigidity`, for the actual middle placement. -/
theorem dense_threeMiddleContext_rotationRigid (Q : BetaDiagram 4) (hD : Q.Dense)
    (P : ThreeComponentParameters) : (Q.threeMiddleContext P).RotationRigid :=
  fourPlacementSource_context_rotationRigid Q (Or.inl hD) P true

/-- `prop:one-negative-three-component-rigidity`, with arbitrary connected mates. -/
theorem one_negative_threeEndContext_rotationRigid (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (P : ThreeComponentParameters) : (Q.threeEndContext P).RotationRigid :=
  fourPlacementSource_context_rotationRigid Q (Or.inr ⟨hC,hZ,hN⟩) P false

theorem one_negative_threeMiddleContext_rotationRigid (Q : BetaDiagram 4)
    (hC : Q.Connected) (hZ : Q.ZeroFree) (hN : negativeCount Q = 1)
    (P : ThreeComponentParameters) : (Q.threeMiddleContext P).RotationRigid :=
  fourPlacementSource_context_rotationRigid Q (Or.inr ⟨hC,hZ,hN⟩) P true

/-- A source's actual maximal-cofactor product exposes its genuine placement and
therefore proves its full class.  No hypothesis is imposed on a mate's board or placement. -/
theorem three_component_cofactor_rotationRigid (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree) (Q : BetaDiagram 4)
    (hQ : Q.FourPlacementSource) (ell m : ℤ) (hℓ : 0 < ell) (hm : 0 < m)
    (hcof : D.cornerPolynomial = complete ell*complete m*Q.schur) : D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let C := D.cornerDiagram hP
  let K := C.componentDecomposition
  have hprod : complete ell*complete m*Q.schur = C.schur := by
    rw [cornerDiagram_schur,hcof]
  have hrel := C.component_matching_of_product K
    ([⟨1,singletonDiagram ell hℓ⟩,⟨1,singletonDiagram m hm⟩,⟨4,Q⟩] :
      List (Σ a : ℕ, BetaDiagram a))
    (by
      intro X hX
      simp at hX
      rcases hX with rfl | rfl | rfl
      · exact singletonDiagram_connected ell hℓ
      · exact singletonDiagram_connected m hm
      · exact hQ.connected)
    (by simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      singletonDiagram_schur,mul_one,mul_assoc] using hprod)
  have recover (F : BetaDiagram 7) (hFC : F.Connected) (hFZ : F.ZeroFree)
      (hFP : F.PositiveCorner) (hFcof : F.cornerPolynomial = complete ell*complete m*Q.schur)
      (R : BetaDiagram 4) (T : ThreeComponentParameters) (b : Bool)
      (htr : F.TranslationEquivalent (if b then R.threeMiddleContext T else R.threeEndContext T)) :
      F.RotationRigid := by
    let S := if b then R.threeMiddleContext T else R.threeEndContext T
    have hSC : S.Connected := by
      cases b <;> simp only [S,Bool.false_eq_true,if_false,if_true]
      · exact R.threeEndContext_connected T
      · exact R.threeMiddleContext_connected T
    have hc := F.cornerPolynomial_eq_of_schur_eq S hFC hSC htr.schur_eq
    have hSc : S.cornerPolynomial = complete T.ell*complete T.m*R.schur := by
      cases b <;> simp [S]
    rw [hFcof,hSc] at hc
    have hrec := three_product_core_recovery Q R hQ.connected ell m T.ell T.m
      hℓ hm T.ell_pos T.m_pos hc
    have hR := hQ.of_schur_eq R hrec.2.1
    exact rotationRigid_of_translation F S htr
      (fourPlacementSource_context_rotationRigid R hR T b)
  rcases C.three_cuts_of_factor_inventory K Q ell m hℓ hm hrel with hcuts | hcuts | hcuts
  · obtain ⟨R,T,_,htr⟩ := D.three_end_parent_of_cuts hP hcuts.1 hcuts.2
    exact recover D hD hZ hP hcof R T false htr
  · obtain ⟨R,T,_,htr⟩ := D.three_middle_parent_of_cuts hP hcuts.1 hcuts.2
    exact recover D hD hZ hP hcof R T true htr
  · have hcut₁ : D.rotate.row 2 < D.rotate.col 0 := by
      have h : D.row 6 < D.col 4 := hcuts.2
      change -D.col 4 < -D.row 6
      omega
    have hcut₂ : D.rotate.row 3 < D.rotate.col 1 := by
      have h : D.row 5 < D.col 3 := hcuts.1
      change -D.col 3 < -D.row 5
      omega
    have hRC := D.rotate_connected hD
    have hRZ := D.rotate_zeroFree hZ
    have hRP := D.rotate_positiveCorner hP
    obtain ⟨R,T,_,htr⟩ := D.rotate.three_end_parent_of_cuts hRP hcut₁ hcut₂
    have hc : D.rotate.cornerPolynomial = complete ell*complete m*Q.schur := by
      have he := D.cornerPolynomial_eq_of_schur_eq D.rotate hD hRC D.rotate_schur.symm
      rw [hcof] at he
      exact he.symm
    exact D.rotationRigid_of_rotate (recover D.rotate hRC hRZ hRP hc R T false htr)

end SkewJacobiNegative.BetaDiagram
