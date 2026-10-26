/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroContractionSets

/-!
# Retained exterior rows of the total zero contraction

The orientation producer used in `thm:two-row-thin-class` of
`shields-2026-skew-class-inflation.tex`.  A positive exterior gap proves
that the corresponding extremal beta coordinate is not canceled.  Exact
full-set cancellation then retains the original exterior row length.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase

/-- The maximum of a nonempty decreasing list stays fixed if its extremum is not erased. -/
theorem antitone_max_after_difference {n m : ℕ} (f : Fin (n + 1) → ℤ) (g : Fin (m + 1) → ℤ)
    (hf : Antitone f) (hg : Antitone g) (T : Finset ℤ)
    (he : Finset.univ.image g = Finset.univ.image f \ T) (ht : f 0 ∉ T) : g 0 = f 0 := by
  have hg0 : g 0 ∈ Finset.univ.image f := by
    have hmem : g 0 ∈ Finset.univ.image f \ T := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp hmem).1
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hg0
  have hle : g 0 ≤ f 0 := by rw [← hi]; exact hf (Fin.zero_le i)
  have hf0 : f 0 ∈ Finset.univ.image g := by
    rw [he]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩, ht⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hf0
  exact le_antisymm hle (by rw [← hj]; exact hg (Fin.zero_le j))

/-- The minimum has the same retention property at the opposite end of the full lists. -/
theorem antitone_min_after_difference {n m : ℕ} (f : Fin (n + 1) → ℤ) (g : Fin (m + 1) → ℤ)
    (hf : Antitone f) (hg : Antitone g) (T : Finset ℤ)
    (he : Finset.univ.image g = Finset.univ.image f \ T) (ht : f (Fin.last n) ∉ T) :
    g (Fin.last m) = f (Fin.last n) := by
  have hg0 : g (Fin.last m) ∈ Finset.univ.image f := by
    have hmem : g (Fin.last m) ∈ Finset.univ.image f \ T := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp hmem).1
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hg0
  have hle : f (Fin.last n) ≤ g (Fin.last m) := by rw [← hi]; exact hf (Fin.le_last i)
  have hf0 : f (Fin.last n) ∈ Finset.univ.image g := by
    rw [he]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, rfl⟩, ht⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hf0
  exact le_antisymm (by rw [← hj]; exact hg (Fin.le_last j)) hle

/-- The private largest upper beta is never a column beta of a valid profile. -/
theorem first_upper_not_column {n : ℕ} (P : Profile n) : P.xi 0 ∉ P.toBetaDiagram.colSet := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  change P.zeta j = P.xi 0 at hj
  have hz := P.zeta_strictAnti.antitone (Fin.zero_le j)
  have hr := P.xi_sub_zeta 0
  have hp := P.r_pos 0
  omega

/-- A positive first gap prevents cancellation of the first lower beta. -/
theorem first_lower_not_row {n : ℕ} (P : Profile n) (hP : Thick P)
    (hg : ∀ j : Fin n, j.val = 0 → 0 < P.g j) : P.zeta 0 ∉ P.toBetaDiagram.rowSet := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  change P.xi i = P.zeta 0 at hi
  by_cases hi0 : i = 0
  · subst i
    have hr := P.xi_sub_zeta 0
    have hp := P.r_pos 0
    omega
  · have hi0' : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    by_cases hi1 : i.val = 1
    · let j : Fin n := ⟨0, by have := i.isLt; omega⟩
      have hs : j.succ = i := Fin.ext (by dsimp [j]; omega)
      have hc : j.castSucc = 0 := Fin.ext rfl
      have hgap := P.xi_succ_sub_zeta_castSucc j
      rw [hs, hc, hi] at hgap
      have hp := hg j rfl
      omega
    · have hn := hP.hessenberg i 0 (by simp only [Fin.val_zero]; omega)
      omega

/-- A positive last gap prevents cancellation of the last upper beta. -/
theorem last_upper_not_column {n : ℕ} (P : Profile n) (hP : Thick P)
    (hg : ∀ j : Fin n, j.val + 1 = n → 0 < P.g j) :
    P.xi (Fin.last n) ∉ P.toBetaDiagram.colSet := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  change P.zeta i = P.xi (Fin.last n) at hi
  by_cases hil : i = Fin.last n
  · subst i
    have hr := P.xi_sub_zeta (Fin.last n)
    have hp := P.r_pos (Fin.last n)
    omega
  · have hiM : i.val ≠ n := fun h => hil (Fin.ext h)
    have hib := i.isLt
    by_cases hi1 : i.val + 1 = n
    · let j : Fin n := ⟨i.val, by omega⟩
      have hs : j.succ = Fin.last n := Fin.ext hi1
      have hc : j.castSucc = i := Fin.ext rfl
      have hgap := P.xi_succ_sub_zeta_castSucc j
      rw [hs, hc, ← hi] at hgap
      have hp := hg j hi1
      omega
    · have hn := hP.hessenberg (Fin.last n) i (by simp only [Fin.val_last]; omega)
      omega

/-- A positive exterior gap retains the entire first row through all actual zero contractions. -/
theorem contractAllZeros_first_row {n : ℕ} (P : Profile n) (hP : Thick P)
    (hg : ∀ j : Fin n, j.val = 0 → 0 < P.g j) :
    (contractAllZeros P).2.r 0 = P.r 0 := by
  let C := (contractAllZeros P).2
  obtain ⟨hr, hc⟩ := contractAllZeros_sets P hP
  have hx := antitone_max_after_difference P.xi C.xi P.xi_strictAnti.antitone
    C.xi_strictAnti.antitone P.toBetaDiagram.colSet hr (first_upper_not_column P)
  have hz := antitone_max_after_difference P.zeta C.zeta P.zeta_strictAnti.antitone
    C.zeta_strictAnti.antitone P.toBetaDiagram.rowSet hc (first_lower_not_row P hP hg)
  have hCr := C.xi_sub_zeta 0
  have hPr := P.xi_sub_zeta 0
  rw [hx, hz] at hCr
  exact_mod_cast hCr.symm.trans hPr

/-- The corresponding last exterior row is retained under the produced opposite gap condition. -/
theorem contractAllZeros_last_row {n : ℕ} (P : Profile n) (hP : Thick P)
    (hg : ∀ j : Fin n, j.val + 1 = n → 0 < P.g j) :
    (contractAllZeros P).2.r (Fin.last (contractAllZeros P).1) = P.r (Fin.last n) := by
  let C := (contractAllZeros P).2
  obtain ⟨hr, _⟩ := contractAllZeros_sets P hP
  have hx := antitone_min_after_difference P.xi C.xi P.xi_strictAnti.antitone
    C.xi_strictAnti.antitone P.toBetaDiagram.colSet hr (last_upper_not_column P hP hg)
  have hCr := C.xi_sub_zeta (Fin.last (contractAllZeros P).1)
  have hPr := P.xi_sub_zeta (Fin.last n)
  rw [hx, C.zeta_last] at hCr
  rw [P.zeta_last] at hPr
  exact_mod_cast hCr.symm.trans hPr

/-- The full span is retained without any extra exterior-gap hypothesis. -/
theorem contractAllZeros_span {n : ℕ} (P : Profile n) (hP : Thick P) :
    (contractAllZeros P).2.xi 0 = P.xi 0 := by
  have hr := (contractAllZeros_sets P hP).1
  exact antitone_max_after_difference P.xi (contractAllZeros P).2.xi
    P.xi_strictAnti.antitone (contractAllZeros P).2.xi_strictAnti.antitone
    P.toBetaDiagram.colSet hr (first_upper_not_column P)

end SkewClassInflation
