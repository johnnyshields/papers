/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NoEscape
import Mathlib.Data.ZMod.Basic

/-!
# Recovery from a private residue column

Formalizes `lem:private-residue-column` in
`shields-2026-skew-class-inflation.tex`.  Every complementary minor of the
last column is proved nonzero from the connected full beta board, allowing
zero complementary diagonal entries.  Residue separation makes each row
beta a private, genuinely occurring polynomial variable.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

namespace BetaDiagram

/-- Connectedness makes each last-column complementary diagonal weakly feasible. -/
theorem last_column_minor_ne_zero {n : ℕ} (D : BetaDiagram (n + 1))
    (hD : D.Connected) (r : Fin (n + 1)) :
    (D.matrix.submatrix r.succAbove (Fin.last n).succAbove).det ≠ 0 := by
  have hm : D.matrix.submatrix r.succAbove (Fin.last n).succAbove =
      betaBoard (fun i => D.row (r.succAbove i)) (fun j => D.col j.castSucc) := by
    apply Matrix.ext
    intro i j
    simp [BetaDiagram.matrix, betaBoard, Fin.succAbove_last]
  rw [hm]
  apply betaBoard_det_ne_zero
  · exact D.row_strictAnti.comp_strictMono (Fin.strictMono_succAbove r)
  · exact D.col_strictAnti.comp_strictMono Fin.strictMono_castSucc
  · intro i
    by_cases hi : i.castSucc < r
    · rw [Fin.succAbove_of_castSucc_lt _ _ hi]
      exact (D.row_nonempty _).le
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hi)]
      exact hD.2 i.castSucc (by simp only [Fin.val_castSucc]; omega)

/-- A private entry in the last column actually occurs in the determinant. -/
theorem private_last_variable_occurs {n : ℕ} (D : BetaDiagram (n + 1))
    (hD : D.Connected) (v : ℕ+) (r : Fin (n + 1))
    (he : D.matrix r (Fin.last n) = MvPolynomial.X v)
    (hp : ∀ i j, i ≠ r ∨ j ≠ Fin.last n → v ∉ (D.matrix i j).vars) :
    v ∈ D.schur.vars := by
  by_contra ha
  have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars ha
  change MvPolynomial.pderiv v D.matrix.det = 0 at hz
  rw [pderiv_det_private D.matrix v r (Fin.last n) he hp] at hz
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (last_column_minor_ne_zero D hD r) hz

/-- Residue constraints separate each terminal-column variable from every other entry. -/
theorem residue_private_last {n : ℕ} (D : BetaDiagram (n + 1))
    {q : ℕ} (R S : Set (ZMod q))
    (hr : ∀ i, (D.row i : ZMod q) ∈ R)
    (hc : ∀ j, j ≠ Fin.last n → (D.col j : ZMod q) ∈ S)
    (hs : ∀ x ∈ R, ∀ y ∈ S, x - y ∉ R)
    (hz : D.col (Fin.last n) = 0) (r : Fin (n + 1))
    (v : ℕ+) (hv : (v : ℤ) = D.row r) :
    ∀ i j, i ≠ r ∨ j ≠ Fin.last n → v ∉ (D.matrix i j).vars := by
  intro i j hij hm
  have he : (v : ℤ) = D.row i - D.col j := (mem_vars_complete_iff _ v).mp hm
  by_cases hj : j = Fin.last n
  · rw [hj, hz, sub_zero, hv] at he
    have hir : i = r := D.row_strictAnti.injective he.symm
    exact hij.elim (fun h => h hir) (fun h => h hj)
  · have hcast : (D.row r : ZMod q) = (D.row i : ZMod q) - (D.col j : ZMod q) := by
      rw [← Int.cast_sub, ← he, hv]
    have hmR := hr r
    rw [hcast] at hmR
    exact hs _ (hr i) _ (hc j hj) hmR

/-- Exact support reading: the allowed-residue generators are precisely all the row betas. -/
theorem private_residue_support {n : ℕ} (D : BetaDiagram (n + 1))
    (hD : D.Connected) {q : ℕ} (R S : Set (ZMod q))
    (hr : ∀ i, (D.row i : ZMod q) ∈ R)
    (hc : ∀ j, j ≠ Fin.last n → (D.col j : ZMod q) ∈ S)
    (hs : ∀ x ∈ R, ∀ y ∈ S, x - y ∉ R)
    (hz : D.col (Fin.last n) = 0) (v : ℕ+)
    (hv : ((v : ℤ) : ZMod q) ∈ R) :
    v ∈ D.schur.vars ↔ ∃ i, D.row i = (v : ℤ) := by
  classical
  constructor
  · intro hm
    by_contra hn
    push Not at hn
    apply not_mem_vars_det D.matrix v ?_ hm
    intro i j he
    have he : (v : ℤ) = D.row i - D.col j := (mem_vars_complete_iff _ v).mp he
    by_cases hj : j = Fin.last n
    · rw [hj, hz, sub_zero] at he
      exact hn i he.symm
    · have hcast : ((v : ℤ) : ZMod q) =
          (D.row i : ZMod q) - (D.col j : ZMod q) := by rw [← Int.cast_sub, he]
      rw [hcast] at hv
      exact hs _ (hr i) _ (hc j hj) hv
  · rintro ⟨r, hrv⟩
    apply private_last_variable_occurs D hD v r
    · change complete (D.row r - D.col (Fin.last n)) = MvPolynomial.X v
      rw [hz, sub_zero, hrv]
      exact complete_nat v
    · exact residue_private_last D R S hr hc hs hz r v hrv.symm

/-- Every row beta occurs, with no positivity premise beyond normalization and connectedness. -/
theorem row_beta_occurs {n : ℕ} (D : BetaDiagram (n + 1))
    (hD : D.Connected) {q : ℕ} (R S : Set (ZMod q))
    (hr : ∀ i, (D.row i : ZMod q) ∈ R)
    (hc : ∀ j, j ≠ Fin.last n → (D.col j : ZMod q) ∈ S)
    (hs : ∀ x ∈ R, ∀ y ∈ S, x - y ∉ R)
    (hz : D.col (Fin.last n) = 0) (r : Fin (n + 1)) :
    ∃ v : ℕ+, (v : ℤ) = D.row r ∧ v ∈ D.schur.vars := by
  have hp : 0 < D.row r := by
    have ho := D.col_strictAnti.antitone (Fin.le_last r)
    have hn := D.row_nonempty r
    omega
  let v : ℕ+ := ⟨(D.row r).toNat, by omega⟩
  have hv : (v : ℤ) = D.row r := by dsimp [v]; omega
  refine ⟨v, hv, ?_⟩
  apply (private_residue_support D hD R S hr hc hs hz v ?_).mpr ⟨r, hv.symm⟩
  rw [hv]
  exact hr r

/-- With the same residue constraints, polynomial equality recovers the entire ordered row list. -/
theorem row_list_eq_of_private_residues {n : ℕ} (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected) {q : ℕ} (R S : Set (ZMod q))
    (hrD : ∀ i, (D.row i : ZMod q) ∈ R)
    (hrE : ∀ i, (E.row i : ZMod q) ∈ R)
    (hcD : ∀ j, j ≠ Fin.last n → (D.col j : ZMod q) ∈ S)
    (hcE : ∀ j, j ≠ Fin.last n → (E.col j : ZMod q) ∈ S)
    (hs : ∀ x ∈ R, ∀ y ∈ S, x - y ∉ R)
    (hzD : D.col (Fin.last n) = 0) (hzE : E.col (Fin.last n) = 0)
    (he : D.schur = E.schur) : D.row = E.row := by
  have step (A B : BetaDiagram (n + 1)) (hA : A.Connected) (hB : B.Connected)
      (hrA : ∀ i, (A.row i : ZMod q) ∈ R)
      (hrB : ∀ i, (B.row i : ZMod q) ∈ R)
      (hcA : ∀ j, j ≠ Fin.last n → (A.col j : ZMod q) ∈ S)
      (hcB : ∀ j, j ≠ Fin.last n → (B.col j : ZMod q) ∈ S)
      (hzA : A.col (Fin.last n) = 0) (hzB : B.col (Fin.last n) = 0)
      (he : A.schur = B.schur) : Set.range A.row ⊆ Set.range B.row := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨v, hv, hm⟩ := row_beta_occurs A hA R S hrA hcA hs hzA i
    have hvR : ((v : ℤ) : ZMod q) ∈ R := by rw [hv]; exact hrA i
    rw [he] at hm
    obtain ⟨j, hj⟩ := (private_residue_support B hB R S hrB hcB hs hzB v hvR).mp hm
    exact ⟨j, hj.trans hv⟩
  apply (D.row_strictAnti.range_inj_of_wellFoundedGT E.row_strictAnti).mp
  exact Set.Subset.antisymm
    (step D E hD hE hrD hrE hcD hcE hzD hzE he)
    (step E D hE hD hrE hrD hcE hcD hzE hzD he.symm)

end BetaDiagram
end SkewClassInflation
