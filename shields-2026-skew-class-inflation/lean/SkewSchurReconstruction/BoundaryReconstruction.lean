/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/BoundaryReconstruction.lean

import SkewSchurReconstruction.PrefixReconstruction
import SkewSchurReconstruction.CofactorSchur
import SkewSchurReconstruction.CappedExtensions

/-!
# Reconstruction from two boundary observations

The two injectivity statements of `thm:boundary-reconstruction` in
«Reconstruction from two boundary observations» (`sec:reconstruction`) of
`shields-2026-skew-boundary-reconstruction.tex`.  Neither boundary nor the row count
is supplied to the reconstruction.  Sorry-free.
-/

namespace SkewSchurReconstruction

namespace TranslationEquivalent

/-- Translating both boundaries preserves every ordered row length. -/
theorem rowLength_eq {n m : ℕ} {X : Diagram n} {Y : Diagram m}
    (h : TranslationEquivalent X Y) (i : Fin n) (j : Fin m) (hij : i.val = j.val) :
    X.rowLength i = Y.rowLength j := by
  obtain ⟨_, t, ht⟩ := h
  obtain ⟨ho, hi⟩ := ht i j hij
  have hx := X.row_nonempty i
  have hy := Y.row_nonempty j
  dsimp [Diagram.rowLength]
  omega

end TranslationEquivalent

namespace Diagram

variable {n : ℕ}

/-- First-row-deletion observations reconstruct both boundaries, with unknown row count. -/
theorem boundary_reconstruction_deletion {n m : ℕ}
    (X : Diagram (n + 1)) (Y : Diagram (m + 1)) (hX : X.Connected) (hY : Y.Connected)
    (hs : X.schurFunction = Y.schurFunction)
    (hchild : X.deleteFirstRow.schurFunction = Y.deleteFirstRow.schurFunction) :
    TranslationEquivalent X Y := by
  apply translationEquivalent_of_two_cofactors_eq X Y hX hY hs
  rw [cofactor_one_eq_neg_deleteFirstRow, cofactor_one_eq_neg_deleteFirstRow, hchild]

/-- A positive northeast extension and the original function reconstruct the parent. -/
theorem boundary_reconstruction_extension {n m : ℕ}
    (X : Diagram n) (Y : Diagram m) (hX : X.Connected) (hY : Y.Connected)
    (a : ℕ) (ha : 0 < a) (hs : X.schurFunction = Y.schurFunction)
    (hext : (X.extendNortheast a ha).schurFunction =
      (Y.extendNortheast a ha).schurFunction) : TranslationEquivalent X Y := by
  have ht := boundary_reconstruction_deletion (X.extendNortheast a ha)
    (Y.extendNortheast a ha) (X.extendNortheast_connected a ha hX)
    (Y.extendNortheast_connected a ha hY) hext (by simpa using hs)
  simpa only [deleteFirstRow_extendNortheast] using ht.deleteFirstRow

/-- Complete-function degree of the original Schur polynomial is its number of cells. -/
theorem cofactorDegree_zero (X : Diagram n) (hX : X.Connected) :
    X.cofactorDegree 0 = ∑ i, (X.rowLength i : ℤ) := by
  rw [cofactorDegree_eq_peelDegree X hX 0]
  unfold peelDegree
  apply Finset.sum_congr rfl
  intro i _
  simpa [peelIndex] using (X.rowLength_eq_coordinates i).symm

/-- Attaching a positive row adds exactly its length to the actual Schur degree. -/
theorem extension_schur_degree (X : Diagram n) (hX : X.Connected)
    (a : ℕ) (ha : 0 < a) :
    (X.extendNortheast a ha).cofactorDegree 0 = X.cofactorDegree 0 + a := by
  rw [cofactorDegree_zero _ (X.extendNortheast_connected a ha hX),
    cofactorDegree_zero X hX, Fin.sum_univ_succ, extendNortheast_rowLength_zero]
  have hrows : ∀ i : Fin n, (X.extendNortheast a ha).rowLength i.succ = X.rowLength i := by
    intro i
    simp only [rowLength, extendNortheast_outer_succ, extendNortheast_inner_succ]
  simp_rw [hrows]
  ring

/-- The observed unordered pair; no cap lengths are encoded in the polynomial values. -/
noncomputable def extensionObservations (X : Diagram n) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) : Finset CompleteRing := by
  classical
  exact {(X.extendNortheast a ha).schurFunction, (X.extendNortheast b hb).schurFunction}

theorem extensionObservations_comm (X : Diagram n) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    X.extensionObservations a b ha hb = X.extensionObservations b a hb ha :=
  Finset.pair_comm _ _

private noncomputable def polynomialDegree (p : CompleteRing) : ℤ :=
  (MvPolynomial.weightedTotalDegree' completeDegreeWeight p).unbotD 0

private theorem degree_extension (X : Diagram n) (hX : X.Connected)
    (a : ℕ) (ha : 0 < a) :
    polynomialDegree (X.extendNortheast a ha).schurFunction = X.cofactorDegree 0 + a := by
  exact extension_schur_degree X hX a ha

/-- Degree order identifies which member of each unordered pair is the shorter extension. -/
theorem ordered_extension_observations {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a < b) (hcd : c < d)
    (hobs : X.extensionObservations a b ha hb = Y.extensionObservations c d hc hd) :
    (X.extendNortheast a ha).schurFunction = (Y.extendNortheast c hc).schurFunction ∧
      (X.extendNortheast b hb).schurFunction = (Y.extendNortheast d hd).schurFunction := by
  classical
  let F := (X.extendNortheast a ha).schurFunction
  let H := (X.extendNortheast b hb).schurFunction
  let G := (Y.extendNortheast c hc).schurFunction
  let J := (Y.extendNortheast d hd).schurFunction
  have hdx : polynomialDegree F < polynomialDegree H := by
    dsimp [F, H]
    rw [degree_extension X hX a ha, degree_extension X hX b hb]
    omega
  have hdy : polynomialDegree G < polynomialDegree J := by
    dsimp [G, J]
    rw [degree_extension Y hY c hc, degree_extension Y hY d hd]
    omega
  have hne : F ≠ H := fun h => (ne_of_lt hdx) (congrArg polynomialDegree h)
  have hx : F = G ∨ F = J := by
    have hm : F ∈ X.extensionObservations a b ha hb := by simp [extensionObservations, F]
    rw [hobs] at hm
    simpa only [extensionObservations, Finset.mem_insert, Finset.mem_singleton, G, J] using hm
  have hy : H = G ∨ H = J := by
    have hm : H ∈ X.extensionObservations a b ha hb := by simp [extensionObservations, H]
    rw [hobs] at hm
    simpa only [extensionObservations, Finset.mem_insert, Finset.mem_singleton, G, J] using hm
  rcases hx with hfg | hfj
  · have hng : H ≠ G := fun h => hne (hfg.trans h.symm)
    exact ⟨hfg, hy.resolve_left hng⟩
  · have hnj : H ≠ J := fun h => hne (hfj.trans h.symm)
    have hhg := hy.resolve_right hnj
    have hrev : polynomialDegree J < polynomialDegree G := by simpa only [hfj, hhg] using hdx
    exact False.elim ((not_lt_of_ge hdy.le) hrev)

/-- Two distinct ordered extensions recover the diagram and both previously unknown lengths. -/
theorem two_positive_extensions_ordered {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a < b) (hcd : c < d)
    (hobs : X.extensionObservations a b ha hb = Y.extensionObservations c d hc hd) :
    TranslationEquivalent X Y ∧ a = c ∧ b = d := by
  obtain ⟨hF, hH⟩ := ordered_extension_observations X Y hX hY a b c d
    ha hb hc hd hab hcd hobs
  have hdf := congrArg polynomialDegree hF
  have hdh := congrArg polynomialDegree hH
  rw [degree_extension X hX a ha, degree_extension Y hY c hc] at hdf
  rw [degree_extension X hX b hb, degree_extension Y hY d hd] at hdh
  let g := b - a
  have hg : 0 < g := by dsimp [g]; omega
  have hgap : d - c = g := by dsimp [g]; omega
  have habg : a + g = b := by dsimp [g]; omega
  have hcdg : c + g = d := by omega
  let ZX := (X.extendNortheast a ha).extendNortheast g hg
  let ZY := (Y.extendNortheast c hc).extendNortheast g hg
  have hZX : ZX.Connected := (X.extendNortheast a ha).extendNortheast_connected g hg
    (X.extendNortheast_connected a ha hX)
  have hZY : ZY.Connected := (Y.extendNortheast c hc).extendNortheast_connected g hg
    (Y.extendNortheast_connected c hc hY)
  have hZ : ZX.schurFunction = ZY.schurFunction := by
    dsimp [ZX, ZY]
    rw [schurFunction_iterated_extendNortheast X a g ha hg,
      schurFunction_iterated_extendNortheast Y c g hc hg]
    have hx := congrArg
      (fun k : {k : ℕ // 0 < k} => (X.extendNortheast k.val k.property).schurFunction)
      (show (⟨a + g, by omega⟩ : {k : ℕ // 0 < k}) = ⟨b, hb⟩ from Subtype.ext habg)
    have hy := congrArg
      (fun k : {k : ℕ // 0 < k} => (Y.extendNortheast k.val k.property).schurFunction)
      (show (⟨c + g, by omega⟩ : {k : ℕ // 0 < k}) = ⟨d, hd⟩ from Subtype.ext hcdg)
    rw [hx, hy, hF, hH]
  have hchild : ZX.deleteFirstRow.schurFunction = ZY.deleteFirstRow.schurFunction := by
    simpa only [ZX, ZY, deleteFirstRow_extendNortheast] using hF
  have ht := boundary_reconstruction_deletion ZX ZY hZX hZY hZ hchild
  have hparents : TranslationEquivalent X Y := by
    simpa only [ZX, ZY, deleteFirstRow_extendNortheast] using ht.deleteFirstRow.deleteFirstRow
  let ix : Fin (n + 1 + 1) := ⟨1, by omega⟩
  let iy : Fin (m + 1 + 1) := ⟨1, by omega⟩
  have hlen := ht.rowLength_eq ix iy rfl
  have hxlen : ZX.rowLength ix = a := by
    change ZX.rowLength (0 : Fin (n + 1)).succ = a
    simp only [ZX, rowLength, extendNortheast_outer_succ, extendNortheast_inner_succ]
    exact X.extendNortheast_rowLength_zero a ha
  have hylen : ZY.rowLength iy = c := by
    change ZY.rowLength (0 : Fin (m + 1)).succ = c
    simp only [ZY, rowLength, extendNortheast_outer_succ, extendNortheast_inner_succ]
    exact Y.extendNortheast_rowLength_zero c hc
  have hac : a = c := hxlen.symm.trans (hlen.trans hylen)
  exact ⟨hparents, hac, by omega⟩

/-- `cor:two-positive-extensions`, including recovery of the unsupplied unordered lengths. -/
theorem two_positive_extensions {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hobs : X.extensionObservations a b ha hb = Y.extensionObservations c d hc hd) :
    TranslationEquivalent X Y ∧ ({a, b} : Finset ℕ) = {c, d} := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hcd with hcd | hdc
    · obtain ⟨ht, rfl, rfl⟩ := two_positive_extensions_ordered X Y hX hY a b c d
        ha hb hc hd hab hcd hobs
      exact ⟨ht, rfl⟩
    · have ho := hobs.trans (extensionObservations_comm Y c d hc hd)
      obtain ⟨ht, rfl, rfl⟩ := two_positive_extensions_ordered X Y hX hY a b d c
        ha hb hd hc hab hdc ho
      exact ⟨ht, Finset.pair_comm _ _⟩
  · rcases lt_or_gt_of_ne hcd with hcd | hdc
    · have ho := (extensionObservations_comm X b a hb ha).trans hobs
      obtain ⟨ht, rfl, rfl⟩ := two_positive_extensions_ordered X Y hX hY b a c d
        hb ha hc hd hba hcd ho
      exact ⟨ht, Finset.pair_comm _ _⟩
    · have ho := (extensionObservations_comm X b a hb ha).trans
        (hobs.trans (extensionObservations_comm Y c d hc hd))
      obtain ⟨ht, rfl, rfl⟩ := two_positive_extensions_ordered X Y hX hY b a d c
        hb ha hd hc hba hdc ho
      exact ⟨ht, rfl⟩

end Diagram
end SkewSchurReconstruction
