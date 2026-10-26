/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ComponentIntervals
import SkewGluing.InteriorProfile

/-!
# Ordered blocks of the actual complementary matrix

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Block cuts are computed from the original
complementary row and column endpoints. The original matrix is block upper triangular for
this produced partition; no triangularity hypothesis is supplied. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Previous index in the same complementary list; the value at zero is harmless. -/
def previousIndex {n : ℕ} (i : Fin n) : Fin n := ⟨i.val - 1, by omega⟩

/-- A new block starts where the actual lower adjacent original entry vanishes. -/
def interiorCuts {n : ℕ} (P : Profile n) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < i.val ∧ P.xi i.succ < P.zeta (previousIndex i).castSucc

/-- Ordered block label from all actual preceding breaks. -/
def interiorBlock {n : ℕ} (P : Profile n) (i : Fin n) : ℕ :=
  ((interiorCuts P).filter fun k => k ≤ i).card

/-- The produced labels follow the original row order. -/
theorem interiorBlock_mono {n : ℕ} (P : Profile n) : Monotone (interiorBlock P) := by
  classical
  intro i j hij
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hc, hki⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨hc, hki.trans hij⟩

/-- Every produced block is an interval in the original complementary list. -/
theorem interiorBlock_interval {n : ℕ} (P : Profile n) {i j k : Fin n}
    (hij : i ≤ j) (hjk : j ≤ k) (hik : interiorBlock P i = interiorBlock P k) :
    interiorBlock P j = interiorBlock P i := by
  apply le_antisymm
  · exact hik ▸ interiorBlock_mono P hjk
  · exact interiorBlock_mono P hij

/-- A genuine cut strictly separates the labels on its two sides. -/
theorem interiorBlock_lt_of_cut {n : ℕ} (P : Profile n) {i j k : Fin n}
    (hk : k ∈ interiorCuts P) (hjk : j < k) (hki : k ≤ i) :
    interiorBlock P j < interiorBlock P i := by
  classical
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨hc, hlj⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hc, hlj.trans (hjk.le.trans hki)⟩
  · intro hrev
    have h := hrev (Finset.mem_filter.mpr ⟨hk, hki⟩)
    exact (not_le_of_gt hjk) (Finset.mem_filter.mp h).2

/-- Distinct block labels produce a genuine endpoint cut between the two indices. -/
theorem exists_interiorCut_of_block_lt {n : ℕ} (P : Profile n) (i j : Fin n)
    (h : interiorBlock P j < interiorBlock P i) :
    ∃ k ∈ interiorCuts P, j < k ∧ k ≤ i := by
  classical
  by_contra! hn
  have hs : (interiorCuts P).filter (fun k => k ≤ i) ⊆
      (interiorCuts P).filter (fun k => k ≤ j) := by
    intro k hk
    obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr
      ⟨hc, le_of_not_gt (fun hj => (not_lt_of_ge hi) (hn k hc hj))⟩
  exact (not_le_of_gt h) (Finset.card_le_card hs)

/-- The original complementary polynomial matrix is block upper triangular. -/
theorem interior_polynomial_blockTriangular {n : ℕ} (P : Profile n) :
    (jtMatrix (fun i : Fin n => P.xi i.succ)
      (fun j => P.zeta j.castSucc)).BlockTriangular (interiorBlock P) := by
  intro i j hij
  obtain ⟨k, hk, hjk, hki⟩ := exists_interiorCut_of_block_lt P i j hij
  have hb := (Finset.mem_filter.mp hk).2.2
  have hr := P.xi_strictAnti.antitone (show k.succ ≤ i.succ by
    change k.val + 1 ≤ i.val + 1
    have h := Fin.le_def.mp hki
    omega)
  have hc := P.zeta_strictAnti.antitone
    (show j.castSucc ≤ (previousIndex k).castSucc by
      change j.val ≤ k.val - 1
      have h := Fin.lt_def.mp hjk
      omega)
  change hh (P.xi i.succ - P.zeta j.castSucc) = 0
  apply hh_of_neg
  omega

/-- Embedding into the original rational field preserves the produced block partition. -/
theorem interior_original_blockTriangular {n : ℕ} (P : Profile n) :
    (intervalMatrix (fun i : Fin n => P.xi i.succ)
      (fun j => P.zeta j.castSucc)).BlockTriangular (interiorBlock P) := by
  intro i j hij
  have h := interior_polynomial_blockTriangular P hij
  change originalMap (hh (P.xi i.succ - P.zeta j.castSucc)) = 0
  rw [show hh (P.xi i.succ - P.zeta j.castSucc) = 0 from h, map_zero]

/-- An empty actual interior row is isolated in its own block, not omitted. -/
theorem interior_empty_row_isolated {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.xi i.succ = P.zeta i.castSucc) (j : Fin n)
    (hj : interiorBlock P j = interiorBlock P i) : j = i := by
  classical
  rcases lt_trichotomy j i with hji | hji | hij
  · have hic : i ∈ interiorCuts P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have h := Fin.lt_def.mp hji
        omega
      · rw [hi]
        apply P.zeta_strictAnti
        change i.val - 1 < i.val
        have h := Fin.lt_def.mp hji
        omega
    have h := interiorBlock_lt_of_cut P hic hji le_rfl
    omega
  · exact hji
  · let k : Fin n := ⟨i.val + 1, by have h := Fin.lt_def.mp hij; omega⟩
    have hprev : previousIndex k = i := by
      apply Fin.ext
      simp [previousIndex, k]
    have hkc : k ∈ interiorCuts P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, by simp [k], ?_⟩
      rw [hprev, ← hi]
      apply P.xi_strictAnti
      change i.val + 1 < k.val + 1
      simp [k]
    have hik : i < k := by change i.val < i.val + 1; omega
    have hkj : k ≤ j := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
    have h := interiorBlock_lt_of_cut P hkc hik hkj
    omega

/-- The isolated empty row contributes its actual unit `h_0`, with no empty determinant proxy. -/
theorem interior_empty_row_pivot {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.xi i.succ = P.zeta i.castSucc) :
    intervalMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc) i i = 1 := by
  change originalMap (hh (P.xi i.succ - P.zeta i.castSucc)) = 1
  rw [hi, sub_self, hh_zero, map_one]

/-- A block containing one nonempty interior row contains no empty rows. -/
theorem interior_block_row_nonempty {n : ℕ} (P : Profile n) {i j : Fin n}
    (hi : P.zeta i.castSucc < P.xi i.succ)
    (hj : interiorBlock P j = interiorBlock P i) :
    P.zeta j.castSucc < P.xi j.succ := by
  have hle := P.zeta_le_xi_succ j
  by_contra hn
  have he : P.xi j.succ = P.zeta j.castSucc := by omega
  have hij := interior_empty_row_isolated P j he i hj.symm
  subst j
  omega

/-- Consecutive rows of one produced nonempty block have the actual connected overlap. -/
theorem interior_block_adjacent_overlap {n : ℕ} (P : Profile n) {i j : Fin n}
    (hnext : j.val = i.val + 1) (hblock : interiorBlock P j = interiorBlock P i) :
    P.zeta i.castSucc ≤ P.xi j.succ := by
  have hp : previousIndex j = i := by
    apply Fin.ext
    simp [previousIndex, hnext]
  by_contra hn
  have hcut : j ∈ interiorCuts P := by
    simp only [interiorCuts, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by omega, ?_⟩
    rw [hp]
    exact lt_of_not_ge hn
  have h := interiorBlock_lt_of_cut P hcut
    (show i < j by change i.val < j.val; omega) le_rfl
  omega

end SkewCornerDescent.Matrix
