/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.CofactorDerivatives
import SkewCofactorIndependence.NonnegativeRigidity
import SkewCofactorIndependence.SymmetricCofactors

/-!
# The two boundary cofactors

The actual unsigned complementary diagrams in `lem:boundary-pair`.  Their
coefficient-one minimum-square monomials remove the proportionality scalar;
nonnegative rigidity then supplies the translation or rotation whose extrema
force symmetry of the parent.  Normalization is unnecessary for these steps.
-/
namespace SkewCofactorIndependence
open scoped BigOperators
namespace BetaDiagram
variable {n : ℕ}

/-- The full square-initial polynomial is a single monomial with coefficient one. -/
theorem square_initial_monomial (D : BetaDiagram n) :
    Base.initialForm Base.squareWeight.generatorWeight D.schur =
      MvPolynomial.monomial D.diagonalExponent 1 := by
  rw [D.schur_eq_integerLift, integerLift_initialForm]
  unfold integerSchur diagonalExponent
  rw [D.integerMatrix_eq_staircase,
    Base.monge_minor_initialForm Base.squareWeight D.neg_row_strictMono
      D.neg_col_strictMono D.neg_diagonal_feasible,
    Base.increasing_product_eq_monomial _ _ D.neg_diagonal_feasible]
  simp [integerLift, MvPolynomial.map_monomial]

/-- Constant multiplication preserves the genuine support minimum and initial polynomial. -/
theorem initialForm_rat_smul (w : ℕ+ → ℝ) (p : CompleteRing) (q : ℚ)
    (_hp : p ≠ 0) (hq : q ≠ 0) :
    Base.initialForm w (q • p) = q • Base.initialForm w p := by
  classical
  have hs : (q • p).support = p.support := by
    ext d
    simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul,
      smul_eq_mul, ne_eq, mul_eq_zero, hq, false_or]
  have hl : Base.leastWeight w (q • p) = Base.leastWeight w p := by
    unfold Base.leastWeight
    rw [hs]
  unfold Base.initialForm
  rw [hl]
  exact map_smul (MvPolynomial.weightedHomogeneousComponent w (Base.leastWeight w p)) q p

/-- Proportional actual Schur polynomials have scalar one, by their coefficient-one leaders. -/
theorem schur_eq_of_proportional (E F : BetaDiagram n) (q : ℚ)
    (he : E.schur = q • F.schur) : E.schur = F.schur := by
  classical
  have hq : q ≠ 0 := by
    intro h
    apply E.schur_ne_zero
    simpa [h] using he
  have hi := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [initialForm_rat_smul _ _ _ F.schur_ne_zero hq,
    E.square_initial_monomial, F.square_initial_monomial] at hi
  have hc := congrArg (fun p : CompleteRing => p.coeff E.diagonalExponent) hi
  by_cases hd : E.diagonalExponent = F.diagonalExponent
  · have hq1 : q = 1 := by simpa [hd] using hc.symm
    simpa [hq1] using he
  · have : (1 : ℚ) = 0 := by
      simp [MvPolynomial.coeff_monomial, Ne.symm hd] at hc
    exact False.elim (one_ne_zero this)

/-- A constant adjacent gap determines the entire strictly ordered list. -/
theorem affine_of_adjacent_gap (f : Fin (n + 1) → ℤ) (u : ℤ)
    (h : ∀ k : Fin n, f k.succ = f k.castSucc - u) :
    ∀ k : Fin (n + 1), f k = f 0 - (k.val : ℤ) * u := by
  intro k
  induction k using Fin.induction with
  | zero => simp
  | succ k ih =>
      rw [h k, ih]
      simp only [Fin.val_succ, Fin.val_castSucc]
      push_cast
      ring

/-- Common row and column gaps force the beta reflection, without fixing translation. -/
theorem symmetric_of_common_gap (D : BetaDiagram (n + 1)) (u : ℤ)
    (hr : ∀ k : Fin n, D.row k.succ = D.row k.castSucc - u)
    (hc : ∀ k : Fin n, D.col k.succ = D.col k.castSucc - u) : D.Symmetric := by
  have hrow := affine_of_adjacent_gap D.row u hr
  have hcol := affine_of_adjacent_gap D.col u hc
  refine ⟨D.row 0 + D.col (Fin.last n), ?_, ?_⟩
  · intro k
    rw [hrow k, hcol (Fin.last n), hcol k.rev]
    have hv : (k.rev.val : ℤ) = (n : ℤ) - k.val := by
      simp only [Fin.val_rev]
      omega
    rw [hv]
    push_cast
    ring
  · intro k
    rw [hcol k, hcol (Fin.last n), hrow k.rev]
    have hv : (k.rev.val : ℤ) = (n : ℤ) - k.val := by
      simp only [Fin.val_rev]
      omega
    rw [hv]
    push_cast
    ring

/-- Translating the boundary children forces the two omitted sites to be endpoints. -/
theorem boundary_translation_forces_symmetry (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (i j : Fin (n + 2)) (hi : i ≠ 0) (hj : j ≠ Fin.last (n + 1))
    (ht : (D.deleteSite hd 0 j).TranslationEquivalent
      (D.deleteSite hd i (Fin.last (n + 1)))) : D.Symmetric := by
  obtain ⟨c, hr, hc⟩ := ht
  have hrow0 : i.succAbove 0 = 0 := Fin.succAbove_ne_zero_zero hi
  have hcollast : j.succAbove (Fin.last n) = Fin.last (n + 1) :=
    Fin.succAbove_ne_last_last hj
  have htop := hr 0
  simp only [deleteSite, Fin.zero_succAbove, hrow0] at htop
  have hbottom := hc (Fin.last n)
  simp only [deleteSite, hcollast, Fin.succAbove_last] at hbottom
  have hneg : c < 0 := by
    have := D.row_strictAnti (show (0 : Fin (n + 2)) < (0 : Fin (n + 1)).succ by simp)
    omega
  have hilast : i = Fin.last (n + 1) := by
    by_contra hne
    have hil := Fin.succAbove_ne_last_last hne
    have h := hr (Fin.last n)
    simp only [deleteSite, Fin.zero_succAbove, hil] at h
    have hl : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
    rw [hl] at h
    omega
  have hjzero : j = 0 := by
    by_contra hne
    have hzero : j.succAbove 0 = 0 := Fin.succAbove_ne_zero_zero hne
    have h := hc 0
    simp only [deleteSite, hzero, Fin.succAbove_last] at h
    have he : (0 : Fin (n + 1)).castSucc = 0 := rfl
    rw [he] at h
    omega
  subst i
  subst j
  apply D.symmetric_of_common_gap (-c)
  · intro k
    have h := hr k
    simpa only [deleteSite, Fin.zero_succAbove, Fin.succAbove_last, sub_neg_eq_add] using h
  · intro k
    have h := hc k
    simpa only [deleteSite, Fin.zero_succAbove, Fin.succAbove_last, sub_neg_eq_add] using h

/-- Rotating the boundary children fixes the center by their shared outer extrema. -/
theorem boundary_rotation_forces_symmetry (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (i j : Fin (n + 2)) (hi : i ≠ 0) (hj : j ≠ Fin.last (n + 1))
    (ht : (D.deleteSite hd 0 j).RotationEquivalent
      (D.deleteSite hd i (Fin.last (n + 1)))) : D.Symmetric := by
  obtain ⟨c, hr, hc⟩ := ht
  have hrow0 : i.succAbove 0 = 0 := Fin.succAbove_ne_zero_zero hi
  have hcollast : j.succAbove (Fin.last n) = Fin.last (n + 1) :=
    Fin.succAbove_ne_last_last hj
  have he := hc (Fin.last n)
  simp only [deleteSite, hcollast, Fin.rev_last, hrow0] at he
  have hcenter : c = D.row 0 + D.col (Fin.last (n + 1)) := by omega
  have hfull : ∀ k : Fin (n + 2), D.row k = c - D.col k.rev := by
    intro k
    induction k using Fin.cases with
    | zero => simp [hcenter]
    | succ k =>
        have h := hr k
        simpa only [deleteSite, Fin.zero_succAbove, Fin.succAbove_last, Fin.rev_succ] using h
  refine ⟨c, hfull, ?_⟩
  intro k
  have h := hfull k.rev
  simp only [Fin.rev_rev] at h
  omega

/-- Boundary proportionality contradicts actual nonnegative rigidity. -/
theorem boundary_cofactor_not_proportional (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (hs : ¬ D.Symmetric) (i j : Fin (n + 2))
    (hi : i ≠ 0) (hj : j ≠ Fin.last (n + 1)) (q : ℚ) :
    D.cofactor 0 j ≠ q • D.cofactor i (Fin.last (n + 1)) := by
  intro he
  let E := D.deleteSite hd 0 j
  let F := D.deleteSite hd i (Fin.last (n + 1))
  have hu : E.schur =
      (((-1 : ℚ) ^ j.val)⁻¹ * q * (-1) ^ (i.val + (n + 1))) • F.schur := by
    rw [D.cofactor_eq_deleteSite hd, D.cofactor_eq_deleteSite hd] at he
    have hsign : (-1 : CompleteRing) ^ j.val = MvPolynomial.C ((-1 : ℚ) ^ j.val) := by simp
    have hsign' : (-1 : CompleteRing) ^ (i.val + (n + 1)) =
        MvPolynomial.C ((-1 : ℚ) ^ (i.val + (n + 1))) := by simp
    simp only [Fin.val_zero, Fin.val_last, zero_add] at he
    rw [hsign, hsign'] at he
    simp only [MvPolynomial.C_mul'] at he
    change ((-1 : ℚ) ^ j.val) • E.schur =
      q • (((-1 : ℚ) ^ (i.val + (n + 1))) • F.schur) at he
    rw [smul_smul] at he
    have hh := congrArg (fun p : CompleteRing => (((-1 : ℚ) ^ j.val)⁻¹) • p) he
    simpa [smul_smul, mul_assoc, pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0)] using hh
  have hp := E.schur_eq_of_proportional F _ hu
  have hdE := D.deleteSite_dense hd 0 j
  have hdF := D.deleteSite_dense hd i (Fin.last (n + 1))
  rcases E.nonnegative_rigidity_same_order F (hdE.connected (by omega))
      (hdF.connected (by omega)) hdE.nonnegative hp with ht | ht
  · exact hs (D.boundary_translation_forces_symmetry hd i j hi hj ht)
  · exact hs (D.boundary_rotation_forces_symmetry hd i j hi hj ht)

/-- In particular, the equal-degree pair of `lem:boundary-pair` is independent. -/
theorem boundary_pair_independent (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (hs : ¬ D.Symmetric) (i j : Fin (n + 2)) (hi : i ≠ 0)
    (hj : j ≠ Fin.last (n + 1)) (a b : ℚ)
    (he : a • D.cofactor 0 j + b • D.cofactor i (Fin.last (n + 1)) = 0) :
    a = 0 ∧ b = 0 := by
  by_cases ha : a = 0
  · refine ⟨ha, ?_⟩
    have hz : b • D.cofactor i (Fin.last (n + 1)) = 0 := by simpa [ha] using he
    exact (smul_eq_zero.mp hz).resolve_right (D.cofactor_ne_zero hd _ _)
  · exfalso
    apply D.boundary_cofactor_not_proportional hd hs i j hi hj (-a⁻¹ * b)
    have hh := congrArg (fun p : CompleteRing => a⁻¹ • p) he
    have hz : D.cofactor 0 j + (a⁻¹ * b) • D.cofactor i (Fin.last (n + 1)) = 0 := by
      simpa [smul_add, smul_smul, ha] using hh
    simpa only [neg_smul, neg_mul] using eq_neg_of_add_eq_zero_left hz

end BetaDiagram
end SkewCofactorIndependence
