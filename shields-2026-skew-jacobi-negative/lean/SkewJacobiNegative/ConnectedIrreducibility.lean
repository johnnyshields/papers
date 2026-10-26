/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.CornerMinors
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Connected Schur irreducibility

The actual beta-diagram induction implementing the corrected
Barekat--Reiner--van Willigenburg argument consumed in `sec:boundary`.
Condensation is applied to the original matrix; the two irreducible factors
are its actual first-row and last-row deletions.  The corner coefficient
uses weakly feasible overlaps rather than a positive-diagonal surrogate.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

open scoped BigOperators

variable {n : ℕ}

/-- Reindex the order by an already proved equality of natural numbers. -/
def reindexOrder {m : ℕ} (D : BetaDiagram n) (h : m = n) : BetaDiagram m where
  row i := D.row (Fin.cast h i)
  col i := D.col (Fin.cast h i)
  row_strictAnti := by intro i j hij; exact D.row_strictAnti (by simpa using hij)
  col_strictAnti := by intro i j hij; exact D.col_strictAnti (by simpa using hij)
  row_nonempty i := D.row_nonempty (Fin.cast h i)

/-- Reindexing does not change the actual polynomial. -/
theorem reindexOrder_schur {m : ℕ} (D : BetaDiagram n) (h : m = n) :
    (D.reindexOrder h).schur = D.schur := by
  subst m
  rfl

/-- Delete the first row and the corresponding first column beta. -/
def tail (D : BetaDiagram (n + 1)) : BetaDiagram n where
  row i := D.row i.succ
  col i := D.col i.succ
  row_strictAnti := D.row_strictAnti.comp_strictMono Fin.strictMono_succ
  col_strictAnti := D.col_strictAnti.comp_strictMono Fin.strictMono_succ
  row_nonempty i := D.row_nonempty i.succ

/-- Delete the last row and the corresponding last column beta. -/
def init (D : BetaDiagram (n + 1)) : BetaDiagram n where
  row i := D.row i.castSucc
  col i := D.col i.castSucc
  row_strictAnti := D.row_strictAnti.comp_strictMono Fin.strictMono_castSucc
  col_strictAnti := D.col_strictAnti.comp_strictMono Fin.strictMono_castSucc
  row_nonempty i := D.row_nonempty i.castSucc

/-- An actual contiguous restriction retains every adjacent overlap. -/
theorem tail_connected (D : BetaDiagram (n + 1)) (hD : D.Connected) (hn : 0 < n) :
    D.tail.Connected := by
  refine ⟨hn, ?_⟩
  intro i hi
  exact hD.2 i.succ (by simp only [Fin.val_succ]; omega)

/-- The other contiguous restriction is connected as well. -/
theorem init_connected (D : BetaDiagram (n + 1)) (hD : D.Connected) (hn : 0 < n) :
    D.init.Connected := by
  refine ⟨hn, ?_⟩
  intro i hi
  exact hD.2 i.castSucc (by simp only [Fin.val_castSucc]; omega)

/-- Weighted degrees of row-deletion minors are produced from their beta sums. -/
theorem tail_area (D : BetaDiagram (n + 1)) :
    D.tail.area = D.area - D.rowLength 0 := by
  unfold area tail rowLength
  simp only
  rw [Fin.sum_univ_succ D.row, Fin.sum_univ_succ D.col]
  ring

/-- The last-row deletion removes exactly the last row length. -/
theorem init_area (D : BetaDiagram (n + 1)) :
    D.init.area = D.area - D.rowLength (Fin.last n) := by
  unfold area init rowLength
  simp only
  rw [Fin.sum_univ_castSucc D.row, Fin.sum_univ_castSucc D.col]
  ring

/-- Exact area of the weak-diagonal corner board. -/
theorem corner_area (D : BetaDiagram (n + 1)) :
    (∑ i : Fin n, D.row i.succ) - (∑ i : Fin n, D.col i.castSucc) =
      D.area - D.largestLabel := by
  unfold area largestLabel
  rw [Fin.sum_univ_succ D.row, Fin.sum_univ_castSucc D.col]
  ring

/-- Homogeneity of the signed private coefficient, including padded index zeros. -/
theorem cornerCoefficient_reverse_homogeneous (D : BetaDiagram (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight D.cornerCoefficient
      (-((D.area - D.largestLabel : ℤ) : ℝ)) := by
  have hp := betaBoard_reverse_homogeneous (fun i : Fin n => D.row i.succ)
    (fun i : Fin n => D.col i.castSucc)
  rw [D.corner_area] at hp
  have hs : (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) := by simp
  unfold cornerCoefficient
  rw [hs]
  exact hp.C_mul _

/-- The private coefficient has strictly smaller degree than either row-deletion minor. -/
theorem corner_degree_lt_tail (D : BetaDiagram (n + 2)) :
    D.area - D.largestLabel < D.tail.area := by
  rw [D.tail_area]
  have hc := D.col_strictAnti (show (0 : Fin (n + 2)) < Fin.last (n + 1) by
    simp [Fin.lt_def])
  dsimp [largestLabel, rowLength]
  omega

/-- The second strict degree comparison used in the corrected argument. -/
theorem corner_degree_lt_init (D : BetaDiagram (n + 2)) :
    D.area - D.largestLabel < D.init.area := by
  rw [D.init_area]
  have hr := D.row_strictAnti (show (0 : Fin (n + 2)) < Fin.last (n + 1) by
    simp [Fin.lt_def])
  dsimp [largestLabel, rowLength]
  omega

/-- Actual doubly deleted interior determinant in the condensation identity. -/
noncomputable def condensationInterior (D : BetaDiagram (n + 2)) : CompleteRing :=
  (D.matrix.submatrix (fun i : Fin n => i.castSucc.succ)
    (fun j : Fin n => j.castSucc.succ)).det

/-- The opposite corner with the sign required by the linear coefficient. -/
noncomputable def condensationOpposite (D : BetaDiagram (n + 2)) : CompleteRing :=
  (-1) ^ (n + 1) * (D.matrix.submatrix Fin.castSucc Fin.succ).det

set_option maxHeartbeats 1000000 in
-- Specializing Desnanot--Jacobi elaborates several nested submatrix identities.
set_option backward.isDefEq.respectTransparency false in
/-- Desnanot--Jacobi specialized to the four actual geometric minors. -/
theorem schur_condensation (D : BetaDiagram (n + 2)) :
    D.schur * D.condensationInterior =
      D.tail.schur * D.init.schur - D.cornerCoefficient * D.condensationOpposite := by
  have hd := Shields.desnanot_jacobi D.matrix
  have ht : D.matrix.submatrix Fin.succ Fin.succ = D.tail.matrix := rfl
  have hi : D.matrix.submatrix Fin.castSucc Fin.castSucc = D.init.matrix := rfl
  have hc : D.matrix.submatrix Fin.succ Fin.castSucc = D.cornerBoard := rfl
  rw [ht, hi, hc] at hd
  change D.schur * D.condensationInterior =
    D.tail.schur * D.init.schur -
      D.cornerPolynomial * (D.matrix.submatrix Fin.castSucc Fin.succ).det at hd
  have hs : (-1 : CompleteRing) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  unfold cornerCoefficient condensationOpposite
  rw [mul_mul_mul_comm, hs, one_mul]
  simpa only [mul_comm] using hd

set_option backward.isDefEq.respectTransparency false in
/-- A single nonempty row is an independent generator, hence irreducible. -/
theorem schur_irreducible_one (D : BetaDiagram 1) : Irreducible D.schur := by
  have hp : 0 < D.row 0 - D.col 0 := sub_pos.mpr (D.row_nonempty 0)
  have h := MvPolynomial.irreducible_mul_X_add
    (1 : CompleteRing) 0 (⟨(D.row 0 - D.col 0).toNat, by omega⟩ : ℕ+)
    one_ne_zero (by simp) (by simp) (by
      intro d hd _
      exact isUnit_of_dvd_one hd)
  simpa [schur, matrix, Matrix.det_unique, complete_of_pos hp] using h

set_option backward.isDefEq.respectTransparency false in
/-- Connected skew Schur functions are irreducible in the rational complete ring. -/
theorem schur_irreducible (D : BetaDiagram n) (hD : D.Connected) :
    Irreducible D.schur := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => exact False.elim (by simpa [Connected] using hD.1)
      | succ n =>
          cases n with
          | zero => exact D.schur_irreducible_one
          | succ n =>
              have hT := ih (n + 1) (by omega) D.tail
                (D.tail_connected hD (by omega))
              have hI := ih (n + 1) (by omega) D.init
                (D.init_connected hD (by omega))
              apply irreducible_corner_of_condensation D.schur D.cornerCoefficient
                D.cornerResidual D.condensationInterior D.tail.schur D.init.schur
                D.condensationOpposite
                (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+)
                ((D.area - D.largestLabel : ℤ) : ℝ) (D.tail.area : ℝ) (D.init.area : ℝ)
              · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
                  (D.cornerPolynomial_ne_zero hD)
              · exact hT
              · exact hI
              · exact D.cornerCoefficient_reverse_homogeneous
              · exact D.tail.schur_reverse_homogeneous
              · exact D.init.schur_reverse_homogeneous
              · exact_mod_cast D.corner_degree_lt_tail
              · exact_mod_cast D.corner_degree_lt_init
              · intro hv
                rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
                · have hn := MvPolynomial.vars_pow (-1 : CompleteRing) (n + 1) hv
                  simp only [MvPolynomial.vars_neg, MvPolynomial.vars_one,
                    Finset.notMem_empty] at hn
                · exact D.largest_not_mem_corner hv
              · exact D.largest_not_mem_residual
              · exact D.schur_corner_split
              · exact D.schur_condensation

/-- No nonempty Schur determinant is a unit; ordinary degree witnesses this directly. -/
theorem schur_not_isUnit (D : BetaDiagram n) (hn : 0 < n) : ¬ IsUnit D.schur := by
  intro h
  have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h).2
  rw [D.schur_totalDegree] at hz
  omega

/-- Prefix beta lists at a proposed disconnected cut. -/
def betaPrefix {a b : ℕ} (D : BetaDiagram (a + b)) : BetaDiagram a where
  row i := D.row (i.castAdd b)
  col i := D.col (i.castAdd b)
  row_strictAnti := by
    intro i j hij
    apply D.row_strictAnti
    change i.val < j.val
    exact hij
  col_strictAnti := by
    intro i j hij
    apply D.col_strictAnti
    change i.val < j.val
    exact hij
  row_nonempty i := D.row_nonempty (i.castAdd b)

/-- Suffix beta lists at the same cut. -/
def suffix {a b : ℕ} (D : BetaDiagram (a + b)) : BetaDiagram b where
  row i := D.row (i.natAdd a)
  col i := D.col (i.natAdd a)
  row_strictAnti := by intro i j hij; exact D.row_strictAnti (by simpa using hij)
  col_strictAnti := by intro i j hij; exact D.col_strictAnti (by simpa using hij)
  row_nonempty i := D.row_nonempty (i.natAdd a)

set_option backward.isDefEq.respectTransparency false in
/-- At a disconnected cut every lower-left matrix entry vanishes. -/
theorem schur_factor_at_cut {a b : ℕ} (D : BetaDiagram (a + b))
    (ha : 0 < a) (hb : 0 < b)
    (hcut : D.row ⟨a, by omega⟩ < D.col ⟨a - 1, by omega⟩) :
    D.schur = D.betaPrefix.schur * D.suffix.schur := by
  classical
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  let B : Matrix (Fin a) (Fin b) CompleteRing :=
    D.matrix.submatrix (Fin.castAdd b) (Fin.natAdd a)
  have hm : D.matrix.submatrix e e =
      Matrix.fromBlocks D.betaPrefix.matrix B 0 D.suffix.matrix := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · change complete (D.row (i.natAdd a) - D.col (j.castAdd b)) = 0
      apply complete_of_neg
      have hr := D.row_strictAnti.antitone
        (show (⟨a, by omega⟩ : Fin (a + b)) ≤ i.natAdd a by
          change a ≤ a + i.val
          omega)
      have hc := D.col_strictAnti.antitone
        (show j.castAdd b ≤ (⟨a - 1, by omega⟩ : Fin (a + b)) by
          change j.val ≤ a - 1
          omega)
      omega
    · rfl
  have hd := Matrix.det_submatrix_equiv_self e D.matrix
  rw [hm, Matrix.det_fromBlocks_zero₂₁] at hd
  exact hd.symm

set_option backward.isDefEq.respectTransparency false in
/-- Algebraic irreducibility forces every nonempty realization to be connected. -/
theorem connected_of_schur_irreducible (D : BetaDiagram n) (hn : 0 < n)
    (hp : Irreducible D.schur) : D.Connected := by
  classical
  refine ⟨hn, ?_⟩
  intro i hi
  by_contra hc
  let a := i.val + 1
  let b := n - a
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [a, b]; omega
  have he : a + b = n := by dsimp [a, b]; omega
  let E : BetaDiagram (a + b) := D.reindexOrder he
  have hcut : E.row ⟨a, by omega⟩ < E.col ⟨a - 1, by omega⟩ := by
    have hr : Fin.cast he (⟨a, by omega⟩ : Fin (a + b)) = ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      rfl
    have hc' : Fin.cast he (⟨a - 1, by omega⟩ : Fin (a + b)) = i := by
      apply Fin.ext
      change i.val + 1 - 1 = i.val
      omega
    change D.row (Fin.cast he _) < D.col (Fin.cast he _)
    rw [hr, hc']
    omega
  have hf := E.schur_factor_at_cut ha hb hcut
  have hpe : Irreducible E.schur := by rw [D.reindexOrder_schur he]; exact hp
  rcases hpe.isUnit_or_isUnit hf with h | h
  · exact E.betaPrefix.schur_not_isUnit ha h
  · exact E.suffix.schur_not_isUnit hb h

/-- Connectedness of an unknown equal realization is a produced consequence. -/
theorem connected_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram n)
    (hD : D.Connected) (he : D.schur = E.schur) : E.Connected := by
  apply E.connected_of_schur_irreducible hD.1
  rw [← he]
  exact D.schur_irreducible hD

set_option backward.isDefEq.respectTransparency false in
/-- Repeated actual disconnected cuts factor the polynomial into connected nonempty diagrams. -/
theorem exists_connected_component_factorization (D : BetaDiagram n) :
    ∃ cs : List (Σ k : ℕ, BetaDiagram k),
      (∀ C ∈ cs, C.2.Connected) ∧
      (cs.map Sigma.fst).sum = n ∧
      D.schur = (cs.map (fun C => C.2.schur)).prod := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        refine ⟨[], by simp, by simp, ?_⟩
        simp [schur, Matrix.det_isEmpty]
      · have hn' : 0 < n := by omega
        by_cases hD : D.Connected
        · exact ⟨[⟨n, D⟩], by simpa using hD, by simp, by simp⟩
        · have hbad : ¬ ∀ i : Fin n, ∀ hi : i.val + 1 < n,
              D.col i ≤ D.row ⟨i.val + 1, hi⟩ := by
            intro hc
            exact hD ⟨hn', hc⟩
          push Not at hbad
          obtain ⟨i, hi, hcut⟩ := hbad
          let a := i.val + 1
          let b := n - a
          have ha : 0 < a := by dsimp [a]; omega
          have hb : 0 < b := by dsimp [a, b]; omega
          have he : a + b = n := by dsimp [a, b]; omega
          let E : BetaDiagram (a + b) := D.reindexOrder he
          have hcutE : E.row ⟨a, by omega⟩ < E.col ⟨a - 1, by omega⟩ := by
            have hr : Fin.cast he (⟨a, by omega⟩ : Fin (a + b)) =
                ⟨i.val + 1, hi⟩ := by apply Fin.ext; rfl
            have hc : Fin.cast he (⟨a - 1, by omega⟩ : Fin (a + b)) = i := by
              apply Fin.ext
              change i.val + 1 - 1 = i.val
              omega
            change D.row (Fin.cast he _) < D.col (Fin.cast he _)
            rw [hr, hc]
            exact hcut
          obtain ⟨xs, hxC, hxN, hxP⟩ := ih a (by omega) E.betaPrefix
          obtain ⟨ys, hyC, hyN, hyP⟩ := ih b (by omega) E.suffix
          refine ⟨xs ++ ys, ?_, ?_, ?_⟩
          · intro C hC
            rcases List.mem_append.mp hC with hx | hy
            · exact hxC C hx
            · exact hyC C hy
          · rw [List.map_append, List.sum_append, hxN, hyN]
            exact he
          · rw [List.map_append, List.prod_append, ← hxP, ← hyP,
              ← E.schur_factor_at_cut ha hb hcutE, D.reindexOrder_schur he]

end BetaDiagram
end SkewJacobiNegative
