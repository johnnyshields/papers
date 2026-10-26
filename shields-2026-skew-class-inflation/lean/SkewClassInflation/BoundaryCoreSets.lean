/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryRestoration
import SkewClassInflation.ThinBetaSets

/-!
# Literal retained beta sets of the boundary core

Formalizes `eq:boundary-core-lists` in
`shields-2026-skew-class-inflation.tex`.  The sorted coordinate formula is
identified with the two set unions, retaining the extra top row and the
terminal zero also at total size one.  Sorry-free.
-/

namespace SkewClassInflation.BoundaryParameters

open SkewJacobiNegative

variable (B : BoundaryParameters)

/-- The retained upper set is exactly the unshifted nonsuffix grid and the shifted suffix grid. -/
theorem core_rowSet (M : ℕ) (hM : 0 < M) (T : Finset ℕ) (hT : T ⊆ Finset.Ioo 0 M) :
    (B.core M hM T).rowSet =
      (Finset.Icc 1 M \ T).image (fun k : ℕ => (B.q : ℤ) * k) ∪
        (insert M T).image (fun k : ℕ => (B.q : ℤ) * k + B.p) := by
  classical
  have hnM : M ∉ T := fun h => (Nat.lt_irrefl M) (Finset.mem_Ioo.mp (hT h)).2
  ext x
  simp only [BetaDiagram.rowSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    change B.upper M T i = x at hi
    by_cases hi0 : i.val = 0
    · right
      refine ⟨M, Finset.mem_insert_self _ _, ?_⟩
      simpa only [upper, ite_eq_left hi0, mul_comm] using hi
    · by_cases hi1 : i.val = 1
      · left
        refine ⟨M, Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, hnM⟩, ?_⟩
        simpa only [upper, ite_eq_right hi0, ite_eq_left hi1] using hi
      · let k := M + 1 - i.val
        have hib := i.isLt
        have hk : 0 < k ∧ k < M := by dsimp [k]; omega
        have hki : ((M : ℤ) + 1 - i.val) = k := by dsimp [k]; omega
        rw [upper, ite_eq_right hi0, ite_eq_right hi1] at hi
        by_cases hkt : k ∈ T
        · right
          refine ⟨k, Finset.mem_insert_of_mem hkt, ?_⟩
          change M + 1 - i.val ∈ T at hkt
          simpa only [hki, bit, ite_eq_left hkt] using hi
        · left
          refine ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hk.1, hk.2.le⟩, hkt⟩, ?_⟩
          change M + 1 - i.val ∉ T at hkt
          simpa only [hki, bit, ite_eq_right hkt, Nat.cast_zero, add_zero] using hi
  · rintro (⟨k, hk, hx⟩ | ⟨k, hk, hx⟩)
    · obtain ⟨hkM, hkt⟩ := Finset.mem_sdiff.mp hk
      obtain ⟨hk0, hkM⟩ := Finset.mem_Icc.mp hkM
      by_cases hkm : k = M
      · refine ⟨⟨1, by omega⟩, ?_⟩
        change B.upper M T ⟨1, by omega⟩ = x
        simpa [upper, hkm] using hx
      · let i : Fin (M + 1) := ⟨M + 1 - k, by omega⟩
        refine ⟨i, ?_⟩
        have hi0 : i.val ≠ 0 := by dsimp [i]; omega
        have hi1 : i.val ≠ 1 := by dsimp [i]; omega
        have hik : M + 1 - i.val = k := by dsimp [i]; omega
        have hki : (M : ℤ) + 1 - i.val = k := by dsimp [i]; omega
        change B.upper M T i = x
        rw [upper, ite_eq_right hi0, ite_eq_right hi1, hik, bit,
          ite_eq_right hkt, Nat.cast_zero, add_zero, hki]
        exact hx
    · rcases Finset.mem_insert.mp hk with hkm | hkt
      · refine ⟨0, ?_⟩
        change B.upper M T 0 = x
        simpa only [upper, Fin.val_zero, ite_true, hkm] using hx
      · have hkM := Finset.mem_Ioo.mp (hT hkt)
        let i : Fin (M + 1) := ⟨M + 1 - k, by omega⟩
        refine ⟨i, ?_⟩
        have hi0 : i.val ≠ 0 := by dsimp [i]; omega
        have hi1 : i.val ≠ 1 := by dsimp [i]; omega
        have hik : M + 1 - i.val = k := by dsimp [i]; omega
        have hki : (M : ℤ) + 1 - i.val = k := by dsimp [i]; omega
        change B.upper M T i = x
        rw [upper, ite_eq_right hi0, ite_eq_right hi1, hik, bit, ite_eq_left hkt, hki]
        exact hx

/-- The retained lower set is the fixed shifted positive grid together with zero. -/
theorem core_colSet (M : ℕ) (hM : 0 < M) (T : Finset ℕ) :
    (B.core M hM T).colSet =
      (Finset.Icc 1 M).image (fun k : ℕ => (B.q : ℤ) * k - B.a) ∪ {0} := by
  classical
  ext x
  simp only [BetaDiagram.colSet, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    change B.lower M i = x at hi
    by_cases him : i.val = M
    · right
      simpa only [lower, ite_eq_left him] using hi.symm
    · left
      have hi' := i.isLt
      refine ⟨M - i.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [lower, ite_eq_right him] at hi
      have hki : ((M - i.val : ℕ) : ℤ) = (M : ℤ) - i.val := by omega
      rw [hki]
      exact hi
  · rintro (⟨k, hk, hx⟩ | hx)
    · obtain ⟨hk0, hkM⟩ := Finset.mem_Icc.mp hk
      let i : Fin (M + 1) := ⟨M - k, by omega⟩
      refine ⟨i, ?_⟩
      have him : i.val ≠ M := by dsimp [i]; omega
      have hki : (M : ℤ) - i.val = k := by dsimp [i]; omega
      change B.lower M i = x
      rw [lower, ite_eq_right him, hki]
      exact hx
    · refine ⟨Fin.last M, ?_⟩
      change B.lower M (Fin.last M) = x
      simpa only [lower, Fin.val_last, ite_true] using hx.symm

end SkewClassInflation.BoundaryParameters
