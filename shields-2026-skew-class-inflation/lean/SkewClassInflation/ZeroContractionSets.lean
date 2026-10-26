/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.UnitJoinCoefficients
import SkewJacobiNegative.RestorationGeometry

/-!
# Zero-seam contraction cancels the actual common beta sets

Formalizes the full-list contraction mechanism used in
`thm:two-row-thin-class` of `shields-2026-skew-class-inflation.tex`.
Each zero contraction deletes the same coordinate from the two strict
lists.  At the end, thickness and positive remaining gaps prove that
nothing common remains.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Gluing SkewJacobiNegative.Staircase
open SkewJacobiNegative.GeneralHessenberg

/-- Puncturing a strict finite list erases precisely its selected coordinate from the actual set. -/
theorem image_delete_index {n : ℕ} (f : Fin (n + 1) → ℤ) (hf : Function.Injective f)
    (r : Fin (n + 1)) :
    Finset.univ.image (fun i => f (r.succAbove i)) = (Finset.univ.image f).erase (f r) := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne r i (hf h), ⟨r.succAbove i, rfl⟩⟩
  · rintro ⟨hne, j, hj⟩
    have hjr : j ≠ r := fun h => hne (by simpa only [h] using hj.symm)
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hjr
    exact ⟨i, by rw [hi]; exact hj⟩

/-- An actual contraction removes exactly the designated lower-row beta. -/
theorem contract_rowSet {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    (contract P c).toBetaDiagram.rowSet =
      P.toBetaDiagram.rowSet.erase (P.xi c.succ) := by
  change Finset.univ.image (contract P c).xi = _
  rw [(contract_beta P c).1]
  exact image_delete_index P.xi P.xi_strictAnti.injective c.succ

/-- Its lower list loses exactly the designated upper-column beta. -/
theorem contract_colSet {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    (contract P c).toBetaDiagram.colSet =
      P.toBetaDiagram.colSet.erase (P.zeta c.castSucc) := by
  change Finset.univ.image (contract P c).zeta = _
  rw [(contract_beta P c).2]
  exact image_delete_index P.zeta P.zeta_strictAnti.injective c.castSucc

/-- Erasing the same coordinate from both lists preserves their ordered set differences. -/
theorem erase_common_sdiff (A B : Finset ℤ) (z : ℤ) (hA : z ∈ A) (hB : z ∈ B) :
    A.erase z \ B.erase z = A \ B := by
  classical
  ext x
  by_cases hx : x = z
  · subst x; simp [hA, hB]
  · simp [Finset.mem_sdiff, hx]

/-- A zero seam is a common beta, so its contraction preserves both residual beta sets. -/
theorem contract_zero_residualSets {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1))
    (hc : P.g c = 0) :
    (contract P c).toBetaDiagram.rowSet \ (contract P c).toBetaDiagram.colSet =
      P.toBetaDiagram.rowSet \ P.toBetaDiagram.colSet ∧
    (contract P c).toBetaDiagram.colSet \ (contract P c).toBetaDiagram.rowSet =
      P.toBetaDiagram.colSet \ P.toBetaDiagram.rowSet := by
  classical
  have hz : P.xi c.succ = P.zeta c.castSucc := by
    have h := P.xi_succ_sub_zeta_castSucc c
    rw [hc] at h
    omega
  have hr : P.xi c.succ ∈ P.toBetaDiagram.rowSet :=
    Finset.mem_image.mpr ⟨c.succ, Finset.mem_univ _, rfl⟩
  have hl : P.xi c.succ ∈ P.toBetaDiagram.colSet := by
    rw [hz]
    exact Finset.mem_image.mpr ⟨c.castSucc, Finset.mem_univ _, rfl⟩
  rw [contract_rowSet, contract_colSet, ← hz]
  exact ⟨erase_common_sdiff _ _ _ hr hl, erase_common_sdiff _ _ _ hl hr⟩

/-- Zero contractions preserve genuine Hessenberg thickness at every recursive stage. -/
theorem contractAllZeros_thick {n : ℕ} (P : Profile n) (hP : Thick P) :
    Thick (contractAllZeros P).2 := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1), (P.lift rowShiftTwoOne).g c = (1 : ℕ+).val
    · rw [show contractAllZeros P = contractAllZeros (contract P (Classical.choose h)) by
          simp only [contractAllZeros, dite_eq_left h]]
      exact ih _ (contract_thick hP _)
    · rw [show contractAllZeros P = ⟨n + 1, P⟩ by
          simp only [contractAllZeros, dite_eq_right h]]
      exact hP

/-- Both residual set differences are invariant through every actual zero contraction. -/
theorem contractAllZeros_residualSets {n : ℕ} (P : Profile n) :
    (contractAllZeros P).2.toBetaDiagram.rowSet \ (contractAllZeros P).2.toBetaDiagram.colSet =
      P.toBetaDiagram.rowSet \ P.toBetaDiagram.colSet ∧
    (contractAllZeros P).2.toBetaDiagram.colSet \ (contractAllZeros P).2.toBetaDiagram.rowSet =
      P.toBetaDiagram.colSet \ P.toBetaDiagram.rowSet := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1), (P.lift rowShiftTwoOne).g c = (1 : ℕ+).val
    · rw [show contractAllZeros P = contractAllZeros (contract P (Classical.choose h)) by
          simp only [contractAllZeros, dite_eq_left h]]
      have hz : P.g (Classical.choose h) = 0 := by
        have hh := Classical.choose_spec h
        change 2 * P.g (Classical.choose h) + 1 = 1 at hh
        omega
      have hr := contract_zero_residualSets P (Classical.choose h) hz
      have hi := ih (contract P (Classical.choose h))
      exact ⟨hi.1.trans hr.1, hi.2.trans hr.2⟩
    · rw [show contractAllZeros P = ⟨n + 1, P⟩ by
          simp only [contractAllZeros, dite_eq_right h]]
      exact ⟨rfl, rfl⟩

/-- Once no unit remains, the full beta lists are exactly the uncanceled original supports. -/
theorem contractAllZeros_sets {n : ℕ} (P : Profile n) (hP : Thick P) :
    (contractAllZeros P).2.toBetaDiagram.rowSet =
      P.toBetaDiagram.rowSet \ P.toBetaDiagram.colSet ∧
    (contractAllZeros P).2.toBetaDiagram.colSet =
      P.toBetaDiagram.colSet \ P.toBetaDiagram.rowSet := by
  classical
  let C := (contractAllZeros P).2.toBetaDiagram
  have hz : C.ZeroFree := thick_positive_gaps_zeroFree _ (contractAllZeros_thick P hP)
    (contractAllZeros_gap_pos P)
  have hd : Disjoint C.rowSet C.colSet := by
    apply Finset.disjoint_left.mpr
    intro z hr hc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
    exact hz i j (hi.trans hj.symm)
  have hi := contractAllZeros_residualSets P
  rw [Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm] at hi
  exact hi

end SkewClassInflation
