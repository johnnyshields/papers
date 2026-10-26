/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CofactorActions

/-!
# Actual cofactor degrees and square moments

Formalizes `prop:stable-cofactor` and `eq:scalar-recovery` in
"Reconstruction from two boundary observations" (`sec:reconstruction`).
Ordinary homogeneous degrees and square-weight least weights of actual signed
cofactors are identified with the geometric moments.  Scalar recovery and
translation-class injectivity therefore apply to actual cofactor observations.
The length-aware tuple records its row count explicitly.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- Ordinary complete-function grading with an integer-valued degree. -/
def completeDegreeWeight (k : ℕ+) : ℤ := (k : ℕ)

/-- Feasible permutation terms all have the same ordinary degree. -/
theorem permutationTerm_degree_homogeneous {n : ℕ} (A d : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.IsWeightedHomogeneous completeDegreeWeight (permutationTerm A d σ)
      (∑ i, (d i - A i)) := by
  classical
  by_cases hf : matchingFeasible A d σ
  · have hprod := complete_prod_isWeightedHomogeneous Finset.univ
      (fun i => d (σ i) - A i) (fun k : ℕ => (k : ℤ)) (by simp)
      (fun i _ => sub_nonneg.mpr (hf i))
    have hsum : (∑ i, ((d (σ i) - A i).toNat : ℤ)) = ∑ i, (d i - A i) := by
      calc
        _ = ∑ i, (d (σ i) - A i) := by
          apply Finset.sum_congr rfl
          intro i _
          have h := hf i
          omega
        _ = _ := by
          simp only [Finset.sum_sub_distrib]
          rw [Equiv.sum_comp σ]
    rw [hsum] at hprod
    change MvPolynomial.IsWeightedHomogeneous completeDegreeWeight
      (∏ i, complete (d (σ i) - A i)) (∑ i, (d i - A i)) at hprod
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [permutationTerm, hs] using hprod
    · simpa [permutationTerm, hs] using hprod.neg
  · rw [permutationTerm_eq_zero A d σ hf]
    exact MvPolynomial.isWeightedHomogeneous_zero ℤ _ _

/-- Every staircase determinant is homogeneous in the ordinary complete grading. -/
theorem staircase_det_degree_homogeneous {n : ℕ} (A d : Fin n → ℤ) :
    MvPolynomial.IsWeightedHomogeneous completeDegreeWeight (staircaseMatrix A d).det
      (∑ i, (d i - A i)) := by
  classical
  rw [staircase_det_expansion]
  exact MvPolynomial.IsWeightedHomogeneous.sum Finset.univ (permutationTerm A d)
    (∑ i, (d i - A i)) (fun σ _ => permutationTerm_degree_homogeneous A d σ)

namespace Diagram

variable {n m : ℕ}

/-- The actual signed cofactor is homogeneous at its geometric first moment. -/
theorem cofactor_degree_homogeneous (X : Diagram n) (j : Fin (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous completeDegreeWeight (X.cofactor j)
      (X.peelDegree j) := by
  have hdet := staircase_det_degree_homogeneous X.rowParam
    (fun i => X.capShift (j.succAbove i))
  have hsign : MvPolynomial.IsWeightedHomogeneous completeDegreeWeight
      ((-1 : CompleteRing) ^ j.val) 0 := by
    have h := MvPolynomial.isWeightedHomogeneous_C completeDegreeWeight ((-1 : ℤ) ^ j.val)
    simpa using h
  unfold cofactor signedMaximalCofactor
  rw [capMatrix_minor_eq_staircase]
  simpa [peelDegree, peelIndex] using hsign.mul hdet

/-- The actual weighted total degree is finite and equals the first geometric moment. -/
theorem cofactor_weightedTotalDegree (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) :
    MvPolynomial.weightedTotalDegree' completeDegreeWeight (X.cofactor j) =
      (X.peelDegree j : WithBot ℤ) := by
  classical
  have hp := X.cofactor_ne_zero squareWeight hX j
  have hh := X.cofactor_degree_homogeneous j
  unfold MvPolynomial.weightedTotalDegree'
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    rw [hh (MvPolynomial.mem_support_iff.mp hd)]
  · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hp
    have h := Finset.le_sup (f := fun e =>
      (Finsupp.weight completeDegreeWeight e : WithBot ℤ)) hd
    simpa only [hh (MvPolynomial.mem_support_iff.mp hd)] using h

/-- Integer projection of the actual degree; connected cofactors never use the bottom default. -/
noncomputable def cofactorDegree (X : Diagram n) (j : Fin (n + 1)) : ℤ :=
  (MvPolynomial.weightedTotalDegree' completeDegreeWeight (X.cofactor j)).unbotD 0

theorem cofactorDegree_eq_peelDegree (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) : X.cofactorDegree j = X.peelDegree j := by
  unfold cofactorDegree
  rw [cofactor_weightedTotalDegree X hX j]
  rfl

/-- The square-weight least weight is the second geometric moment of the actual cofactor. -/
theorem cofactor_square_leastWeight (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) :
    leastWeight squareWeight.generatorWeight (X.cofactor j) = (X.peelSquare j : ℝ) := by
  rw [cofactor_leastWeight squareWeight X hX j]
  unfold peelSquare
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  have hn := X.peelIndex_nonneg hX j i
  have h : ((X.peelIndex j i).toNat : ℤ) = X.peelIndex j i := by omega
  have hr : ((X.peelIndex j i).toNat : ℝ) = (X.peelIndex j i : ℝ) := by
    exact_mod_cast h
  change ((X.peelIndex j i).toNat : ℝ) ^ 2 = (X.peelIndex j i : ℝ) ^ 2
  rw [hr]

/-- The actual square valuation is finite and equals the second geometric moment. -/
theorem cofactor_square_monomialValuation (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) :
    monomialValuation squareWeight.generatorWeight (X.cofactor j) =
      ((X.peelSquare j : ℝ) : WithTop ℝ) := by
  rw [monomialValuation_eq_coe (X.cofactor_ne_zero squareWeight hX j),
    cofactor_square_leastWeight X hX j]

/-- Adjacent drop of actual ordinary cofactor degrees. -/
noncomputable def cofactorDegreeDrop (X : Diagram n) (j : Fin n) : ℤ :=
  X.cofactorDegree j.castSucc - X.cofactorDegree j.succ

/-- Adjacent drop of actual square-weight least weights. -/
noncomputable def cofactorSquareDrop (X : Diagram n) (j : Fin n) : ℝ :=
  leastWeight squareWeight.generatorWeight (X.cofactor j.castSucc) -
    leastWeight squareWeight.generatorWeight (X.cofactor j.succ)

theorem cofactorDegreeDrop_eq (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    X.cofactorDegreeDrop j = X.degreeDrop j := by
  simp only [cofactorDegreeDrop, cofactorDegree_eq_peelDegree X hX, degreeDrop]

theorem cofactorSquareDrop_eq (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    X.cofactorSquareDrop j = (X.squareDrop j : ℝ) := by
  simp only [cofactorSquareDrop, cofactor_square_leastWeight X hX, squareDrop, Int.cast_sub]

theorem cofactorDegreeDrop_pos (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    0 < X.cofactorDegreeDrop j := by
  rw [cofactorDegreeDrop_eq X hX]
  exact X.degreeDrop_pos j

/-- The actual square-weight drop is an integer multiple of the actual positive degree drop. -/
theorem cofactor_degree_dvd_square_drop (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    ∃ s : ℤ, (s : ℝ) = X.cofactorSquareDrop j ∧ X.cofactorDegreeDrop j ∣ s := by
  refine ⟨X.squareDrop j, ?_, ?_⟩
  · exact (X.cofactorSquareDrop_eq hX j).symm
  · rw [cofactorDegreeDrop_eq X hX]
    exact X.degreeDrop_dvd_squareDrop j

theorem cofactorDegreeDrop_real_ne_zero (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    (X.cofactorDegreeDrop j : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt (X.cofactorDegreeDrop_pos hX j)

/-- Actual square-weight and degree drops recover the sum of the two exchanged indices. -/
theorem cofactorSquareDrop_div_degreeDrop (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    X.cofactorSquareDrop j / (X.cofactorDegreeDrop j : ℝ) =
      (X.exchangeRow j : ℝ) + (X.exchangeZero j : ℝ) := by
  apply (div_eq_iff (X.cofactorDegreeDrop_real_ne_zero hX j)).mpr
  rw [cofactorSquareDrop_eq X hX, cofactorDegreeDrop_eq X hX]
  have h : (X.squareDrop j : ℝ) = (X.degreeDrop j : ℝ) *
      ((X.exchangeRow j : ℝ) + (X.exchangeZero j : ℝ)) := by
    exact_mod_cast X.squareDrop_factor j
  simpa [mul_comm] using h

/-- Actual cofactor scalar-recovery formula for the row length. -/
theorem rowLength_cofactor_scalar_recovery (X : Diagram n) (hX : X.Connected) (j : Fin n) :
    (X.rowLength j : ℝ) =
      (X.cofactorSquareDrop j / (X.cofactorDegreeDrop j : ℝ) +
        (X.cofactorDegreeDrop j : ℝ)) / 2 := by
  rw [cofactorSquareDrop_div_degreeDrop X hX, cofactorDegreeDrop_eq X hX]
  have hd : (X.degreeDrop j : ℝ) =
      (X.exchangeRow j : ℝ) - (X.exchangeZero j : ℝ) := by
    exact_mod_cast X.degreeDrop_eq_exchange j
  have hr : (X.exchangeRow j : ℝ) = (X.rowLength j : ℝ) := by
    exact_mod_cast X.exchangeRow_eq_rowLength j
  rw [hd, hr]
  ring

/-- Actual cofactor scalar-recovery formula for the inserted overlap index. -/
theorem exchangeZero_cofactor_scalar_recovery (X : Diagram n) (hX : X.Connected)
    (j : Fin n) :
    (X.exchangeZero j : ℝ) =
      (X.cofactorSquareDrop j / (X.cofactorDegreeDrop j : ℝ) -
        (X.cofactorDegreeDrop j : ℝ)) / 2 := by
  rw [cofactorSquareDrop_div_degreeDrop X hX, cofactorDegreeDrop_eq X hX]
  have hd : (X.degreeDrop j : ℝ) =
      (X.exchangeRow j : ℝ) - (X.exchangeZero j : ℝ) := by
    exact_mod_cast X.degreeDrop_eq_exchange j
  rw [hd]
  ring

/-- Equal actual degree and square-valuation profiles determine the translation class. -/
theorem translationEquivalent_of_cofactor_profiles (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hd : ∀ j, MvPolynomial.weightedTotalDegree' completeDegreeWeight (X.cofactor j) =
      MvPolynomial.weightedTotalDegree' completeDegreeWeight (Y.cofactor j))
    (hs : ∀ j, leastWeight squareWeight.generatorWeight (X.cofactor j) =
      leastWeight squareWeight.generatorWeight (Y.cofactor j)) : TranslationEquivalent X Y := by
  apply translationEquivalent_of_profiles
  · intro j
    have h := hd j
    rw [cofactor_weightedTotalDegree X hX, cofactor_weightedTotalDegree Y hY] at h
    exact WithBot.coe_injective h
  · intro j
    have h := hs j
    rw [cofactor_square_leastWeight X hX, cofactor_square_leastWeight Y hY] at h
    exact_mod_cast h

/-- Equal full actual cofactor vectors determine a connected diagram up to translation. -/
theorem translationEquivalent_of_cofactor_eq (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (h : X.cofactor = Y.cofactor) :
    TranslationEquivalent X Y := by
  apply translationEquivalent_of_cofactor_profiles X Y hX hY
  · intro j
    rw [h]
  · intro j
    rw [h]

/-- A length-aware cofactor observation records the row count rather than discarding it. -/
noncomputable def cofactorTuple (X : Diagram n) : Σ r : ℕ, Fin (r + 1) → CompleteRing :=
  ⟨n, X.cofactor⟩

/-- Stable-cofactor injectivity with no common row count assumed in advance. -/
theorem translationEquivalent_of_cofactorTuple_eq (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (h : X.cofactorTuple = Y.cofactorTuple) :
    TranslationEquivalent X Y := by
  have hn : n = m := congrArg Sigma.fst h
  subst m
  have hc : X.cofactor = Y.cofactor := by
    simpa [cofactorTuple] using h
  exact translationEquivalent_of_cofactor_eq X Y hX hY hc

end Diagram
end SkewSchurReconstruction
