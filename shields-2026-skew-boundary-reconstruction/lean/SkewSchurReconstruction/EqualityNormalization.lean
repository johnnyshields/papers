/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CofactorActions
import SkewSchurReconstruction.GeneratorMonomials
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Equality normalization of skew Schur diagrams

Diagram equality producers for "Strict-Monge geometry of cofactor actions"
(`sec:geometry`) and "First-split localization and cap-fixed rigidity"
(`sec:localization`, `lem:equality-normalizes-cap`).  Equal actual skew Schur
functions recover the row-length multiset and row count.  The terminal generator
is proved to occur and to be the largest one; a common inner boundary then
aligns the complete cap grids.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators


/-- A staircase determinant cannot involve a generator above any bound on its entries. -/
theorem staircase_vars_bound {n : ℕ} (A d : Fin n → ℤ) (D : ℤ)
    (hb : ∀ i j, d j - A i ≤ D) (k : ℕ+)
    (hk : k ∈ (staircaseMatrix A d).det.vars) : (k.val : ℤ) ≤ D := by
  classical
  rw [staircase_det_expansion] at hk
  have hsum := MvPolynomial.vars_sum_subset Finset.univ (permutationTerm A d) hk
  obtain ⟨σ, _, hσ⟩ := Finset.mem_biUnion.mp hsum
  have hp : k ∈ (∏ i, complete (d (σ i) - A i)).vars := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [permutationTerm, hs] using hσ
    · simpa [permutationTerm, hs] using hσ
  have hprod := MvPolynomial.vars_prod (fun i => complete (d (σ i) - A i)) hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hprod
  exact complete_vars_bound _ D (hb i (σ i)) k hi

namespace Diagram

variable {n m : ℕ}

theorem rowLengthList_product_initialForm (X : Diagram n) (hX : X.Connected) :
    initialForm squareWeight.generatorWeight X.schurFunction =
      (X.rowLengthList.map (fun k : ℕ => complete (k : ℤ))).prod := by
  unfold schurFunction
  rw [cofactor_initialForm squareWeight X hX]
  simp only [Fin.val_zero, pow_zero, one_mul, rowLengthList, List.map_ofFn,
    List.prod_ofFn, Function.comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  have h : X.peelIndex 0 i = (X.rowLength i : ℤ) := by
    simpa [peelIndex] using (X.rowLength_eq_coordinates i).symm
  rw [h]

/-- Actual skew Schur equality recovers the entire row-length multiset. -/
theorem rowLength_multiset_eq_of_schurFunction_eq (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (h : X.schurFunction = Y.schurFunction) :
    (X.rowLengthList : Multiset ℕ) = (Y.rowLengthList : Multiset ℕ) := by
  apply (prod_complete_eq_iff_of_pos X.rowLengthList Y.rowLengthList
    X.rowLengthList_pos Y.rowLengthList_pos).mp
  have hi := congrArg (initialForm squareWeight.generatorWeight) h
  rwa [rowLengthList_product_initialForm X hX, rowLengthList_product_initialForm Y hY] at hi

/-- No common row count is assumed: it is produced by actual Schur equality. -/
theorem rowCount_eq_of_schurFunction_eq (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (h : X.schurFunction = Y.schurFunction) : n = m := by
  have hm := rowLength_multiset_eq_of_schurFunction_eq X Y hX hY h
  have hc := congrArg Multiset.card hm
  simpa [rowLengthList] using hc

/-- The terminal cap shift is strictly positive for every nonempty diagram. -/
theorem terminalShift_pos (X : Diagram n) (hn : 0 < n) : 0 < X.capShift (Fin.last n) := by
  have h := X.capShift_strictMono (show (0 : Fin (n + 1)) < Fin.last n by
    change 0 < n
    exact hn)
  simpa using h

/-- Every generator occurring in the actual skew Schur function is bounded by the terminal shift. -/
theorem schurFunction_vars_bound (X : Diagram n) (k : ℕ+)
    (hk : k ∈ X.schurFunction.vars) : (k.val : ℤ) ≤ X.capShift (Fin.last n) := by
  have he : X.schurFunction =
      (staircaseMatrix X.rowParam (fun i => X.capShift i.succ)).det := by
    simp only [schurFunction, cofactor, signedMaximalCofactor, Fin.val_zero,
      pow_zero, one_mul, capMatrix_minor_eq_staircase, Fin.zero_succAbove]
  rw [he] at hk
  apply staircase_vars_bound _ _ _ ?_ k hk
  intro i j
  have hc := X.capShift_strictMono.monotone (Fin.le_last j.succ)
  have ha := X.rowParam_nonneg i
  omega

/-- Explicit terminal-shift formula, with integer subtraction. -/
theorem terminalShift_eq (X : Diagram (n + 1)) :
    X.capShift (Fin.last (n + 1)) =
      (X.top : ℤ) - X.inner (Fin.last n) + n := by
  have he : Fin.last (n + 1) = (Fin.last n).succ := by
    apply Fin.ext
    rfl
  rw [he, capShift_succ]
  rfl

/-- The ordinary square Jacobi--Trudi matrix obtained by deleting cap column zero. -/
noncomputable def ordinaryMatrix (X : Diagram n) : Matrix (Fin n) (Fin n) CompleteRing :=
  staircaseMatrix X.rowParam (fun i => X.capShift i.succ)

theorem schurFunction_eq_det_ordinaryMatrix (X : Diagram n) :
    X.schurFunction = X.ordinaryMatrix.det := by
  simp only [schurFunction, cofactor, signedMaximalCofactor, Fin.val_zero,
    pow_zero, one_mul, capMatrix_minor_eq_staircase, Fin.zero_succAbove, ordinaryMatrix]

/-- The positive free-generator index of the terminal cap shift. -/
noncomputable def terminalGenerator (X : Diagram (n + 1)) : ℕ+ :=
  ⟨(X.capShift (Fin.last (n + 1))).toNat, by
    have h := X.terminalShift_pos (Nat.succ_pos n)
    omega⟩

theorem terminalGenerator_cast (X : Diagram (n + 1)) :
    (X.terminalGenerator.val : ℤ) = X.capShift (Fin.last (n + 1)) := by
  have h := X.terminalShift_pos (Nat.succ_pos n)
  change ((X.capShift (Fin.last (n + 1))).toNat : ℤ) =
    X.capShift (Fin.last (n + 1))
  omega

private theorem rowParam_succ_pos (X : Diagram (n + 1)) (i : Fin n) :
    0 < X.rowParam i.succ := by
  have h := X.rowParam_strictMono (show (0 : Fin (n + 1)) < i.succ by
    change 0 < i.val + 1
    omega)
  have hz : X.rowParam (0 : Fin (n + 1)) = 0 := by simp [rowParam, top]
  rwa [hz] at h

private theorem ordinary_minor_eq (X : Diagram (n + 1)) (j : Fin (n + 1)) :
    X.ordinaryMatrix.submatrix Fin.succ j.succAbove =
      staircaseMatrix (fun i => X.rowParam i.succ)
        (fun i => X.capShift (j.succAbove i).succ) := by
  ext i k
  rfl

private theorem ordinary_minor_terminal_nonzero (X : Diagram (n + 1)) (hX : X.Connected) :
    (X.ordinaryMatrix.submatrix Fin.succ (Fin.last n).succAbove).det ≠ 0 := by
  rw [ordinary_minor_eq]
  apply monge_minor_ne_zero squareWeight
  · intro i j hij
    apply X.rowParam_strictMono
    change i.val + 1 < j.val + 1
    exact Nat.add_lt_add_right hij 1
  · intro i j hij
    simp only [Fin.succAbove_last]
    apply X.capShift_strictMono
    change i.val + 1 < j.val + 1
    exact Nat.add_lt_add_right hij 1
  · intro i
    simpa only [Fin.succAbove_last, Fin.castSucc_succ] using X.diagonal_feasible hX i.succ

private theorem pderiv_complete_lt (a : ℤ) (k : ℕ+) (ha : a < (k.val : ℤ)) :
    MvPolynomial.pderiv k (complete a) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hk
  have h := complete_vars_bound a a le_rfl k hk
  omega

/-- Differentiation isolates the unique top-right terminal entry and its complementary minor. -/
theorem terminalGenerator_pderiv (X : Diagram (n + 1)) :
    MvPolynomial.pderiv X.terminalGenerator X.schurFunction =
      (-1 : CompleteRing) ^ n *
        (X.ordinaryMatrix.submatrix Fin.succ (Fin.last n).succAbove).det := by
  classical
  let T : ℤ := X.capShift (Fin.last (n + 1))
  have hcast := X.terminalGenerator_cast
  have hminor : ∀ j : Fin (n + 1),
      MvPolynomial.pderiv X.terminalGenerator
        (X.ordinaryMatrix.submatrix Fin.succ j.succAbove).det = 0 := by
    intro j
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hk
    rw [ordinary_minor_eq] at hk
    have hb : ∀ i k : Fin n,
        X.capShift (j.succAbove k).succ - X.rowParam i.succ ≤ T - 1 := by
      intro i k
      have hc := X.capShift_strictMono.monotone (Fin.le_last (j.succAbove k).succ)
      have ha := rowParam_succ_pos X i
      dsimp [T]
      omega
    have h := staircase_vars_bound _ _ (T - 1) hb X.terminalGenerator hk
    dsimp [T] at h
    omega
  have htop : ∀ j : Fin (n + 1),
      MvPolynomial.pderiv X.terminalGenerator (X.ordinaryMatrix 0 j) =
        if j = Fin.last n then 1 else 0 := by
    intro j
    have hr : X.rowParam (0 : Fin (n + 1)) = 0 := rowParam_zero X (Nat.succ_pos n)
    simp only [ordinaryMatrix, staircaseMatrix, Matrix.of_apply, hr, sub_zero]
    by_cases hj : j = Fin.last n
    · subst j
      have he : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl
      rw [he]
      rw [ite_eq_left rfl]
      change MvPolynomial.pderiv X.terminalGenerator
        (complete (X.capShift (Fin.last (n + 1)))) = 1
      have hx : complete (X.capShift (Fin.last (n + 1))) =
          MvPolynomial.X X.terminalGenerator := complete_of_pos (X.terminalShift_pos (by omega))
      rw [hx]
      exact MvPolynomial.pderiv_X_self _
    · rw [ite_eq_right hj]
      apply pderiv_complete_lt
      rw [hcast]
      apply X.capShift_strictMono
      have h : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hj
      change j.val + 1 < n + 1
      change j.val < n at h
      omega
  rw [schurFunction_eq_det_ordinaryMatrix, Matrix.det_succ_row_zero, map_sum]
  have hterm : ∀ j : Fin (n + 1),
      MvPolynomial.pderiv X.terminalGenerator
        ((-1 : CompleteRing) ^ j.val * X.ordinaryMatrix 0 j *
          (X.ordinaryMatrix.submatrix Fin.succ j.succAbove).det) =
        if j = Fin.last n then (-1 : CompleteRing) ^ n *
          (X.ordinaryMatrix.submatrix Fin.succ (Fin.last n).succAbove).det else 0 := by
    intro j
    by_cases hj : j = Fin.last n
    · subst j
      have hmj : MvPolynomial.pderiv X.terminalGenerator
          (X.ordinaryMatrix.submatrix Fin.succ Fin.castSucc).det = 0 := by
        simpa only [Fin.succAbove_last] using hminor (Fin.last n)
      simp [Derivation.leibniz, smul_eq_mul, hmj, htop, mul_comm]
    · simp [Derivation.leibniz, smul_eq_mul, hminor, htop, hj]
  simp_rw [hterm]
  simp

/-- The terminal generator really occurs; its complementary minor is nonzero even for one row. -/
theorem terminalGenerator_mem_vars (X : Diagram (n + 1)) (hX : X.Connected) :
    X.terminalGenerator ∈ X.schurFunction.vars := by
  by_contra h
  have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars h
  rw [terminalGenerator_pderiv] at hz
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (ordinary_minor_terminal_nonzero X hX) hz

/-- The largest positive generator occurring in a connected skew Schur function. -/
theorem terminalGenerator_largest (X : Diagram (n + 1)) (hX : X.Connected) :
    X.terminalGenerator ∈ X.schurFunction.vars ∧
      ∀ k ∈ X.schurFunction.vars, k.val ≤ X.terminalGenerator.val := by
  refine ⟨X.terminalGenerator_mem_vars hX, ?_⟩
  intro k hk
  have h := X.schurFunction_vars_bound k hk
  rw [← terminalGenerator_cast] at h
  exact_mod_cast h

/-- Actual skew Schur equality identifies terminal cap shifts, without a common row count. -/
theorem terminalShift_eq_of_schurFunction_eq (X : Diagram (n + 1)) (Y : Diagram (m + 1))
    (hX : X.Connected) (hY : Y.Connected) (h : X.schurFunction = Y.schurFunction) :
    X.capShift (Fin.last (n + 1)) = Y.capShift (Fin.last (m + 1)) := by
  have hx := X.terminalGenerator_mem_vars hX
  have hy := Y.terminalGenerator_mem_vars hY
  rw [h] at hx
  rw [← h] at hy
  have hxy := Y.schurFunction_vars_bound X.terminalGenerator hx
  have hyx := X.schurFunction_vars_bound Y.terminalGenerator hy
  rw [X.terminalGenerator_cast] at hxy
  rw [Y.terminalGenerator_cast] at hyx
  omega

/-- `lem:equality-normalizes-cap`: a common inner boundary and actual Schur equality align caps. -/
theorem equality_normalizes_cap (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (h : X.schurFunction = Y.schurFunction)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j) :
    n = m ∧ X.top = Y.top ∧
      ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), i.val = j.val → X.capShift i = Y.capShift j := by
  have hn := rowCount_eq_of_schurFunction_eq X Y hX hY h
  subst m
  have ht : X.top = Y.top := by
    cases n with
    | zero => simp
    | succ n =>
      have hs := terminalShift_eq_of_schurFunction_eq X Y hX hY h
      rw [terminalShift_eq, terminalShift_eq] at hs
      have hi := hinner (Fin.last n) (Fin.last n) rfl
      omega
  refine ⟨rfl, ht, ?_⟩
  intro i j hij
  have he : i = j := Fin.ext hij
  subst j
  by_cases hi : i.val = 0
  · simp [capShift, hi]
  · have hp : i.val - 1 < n := by omega
    have hin := hinner ⟨i.val - 1, hp⟩ ⟨i.val - 1, hp⟩ rfl
    simp only [capShift, dite_eq_right hi, ht, hin]

end Diagram
end SkewSchurReconstruction
