/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.NonVCells
import SkewGluing.Mark

/-!
# The actual ordinary mark of the infinite family

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-family`). The lower column, displacement, and ordinary
horizontal attachment are the stated literal data. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- The stated two-cell column mark, with its actual horizontal displacement. -/
def nonVMark (k : ℕ) : MarkedInner where
  E := nonVDiagram k
  W := {(-1, 0), (0, 0)}
  v := (-1, (k : ℤ) - 1)
  case := .a

/-- The translated upper copy is the actual eastern two-cell column. -/
theorem nonVMark_upper (k : ℕ) :
    (nonVMark k).upper = {(-2, (k : ℤ) - 1), (-1, (k : ℤ) - 1)} := by
  simp [MarkedInner.upper, nonVMark, SkewGluing.translate, Prod.mk_add_mk]

/-- The geometric period is exactly `k`. -/
theorem nonVMark_period (k : ℕ) : (nonVMark k).period = k := by
  simp [MarkedInner.period, nonVMark, content]

/-- The actual lower copy has width two, independent of `k`. -/
theorem nonVMark_width (k : ℕ) : (nonVMark k).width = 2 := by
  change span {((-1 : ℤ), (0 : ℤ)), (0, 0)} = 2
  decide

/-- The two marked copies satisfy the strict period-width inequality exactly in the regime used. -/
theorem nonVMark_isNarrow (k : ℕ) (hk : 3 ≤ k) : (nonVMark k).IsNarrow := by
  unfold MarkedInner.IsNarrow
  rw [nonVMark_width, nonVMark_period]
  omega

/-- Middle membership retains both extreme residual cells and the entire middle row. -/
theorem mem_nonVMark_middle (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) :
    (a, b) ∈ (nonVMark k).middle ↔
      (a = 0 ∧ b = 1) ∨ (a = -1 ∧ 1 ≤ b ∧ b < (k : ℤ) - 1) ∨
        (a = -2 ∧ b = (k : ℤ) - 2) := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  rw [MarkedInner.middle, nonVMark_upper]
  change (a, b) ∈ nonVDiagram k \ ({(-1, 0), (0, 0)} ∪
    {(-2, (k : ℤ) - 1), (-1, (k : ℤ) - 1)}) ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, mem_nonVDiagram,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- Original-coordinate content bounds for every cell of the infinite family. -/
theorem nonVDiagram_content_bounds (k : ℕ) (hk : 3 ≤ k) {a b : ℤ}
    (h : (a, b) ∈ nonVDiagram k) : 0 ≤ b - a ∧ b - a ≤ (k : ℤ) + 1 := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  rw [mem_nonVDiagram] at h
  omega

/-- The actual southwest content is zero. -/
theorem nonVDiagram_minContent (k : ℕ) (hk : 3 ≤ k) :
    minContent (nonVDiagram k) = 0 := by
  apply minContent_eq_of
  · exact Finset.mem_image.mpr ⟨(0, 0), by simp [mem_nonVDiagram], rfl⟩
  · intro t ht
    obtain ⟨⟨a, b⟩, hm, he⟩ := Finset.mem_image.mp ht
    change b - a = t at he
    have := nonVDiagram_content_bounds k hk hm
    omega

/-- The actual northeast content is `k+1`. -/
theorem nonVDiagram_maxContent (k : ℕ) (hk : 3 ≤ k) :
    maxContent (nonVDiagram k) = (k : ℤ) + 1 := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  apply maxContent_eq_of
  · refine Finset.mem_image.mpr ⟨(-2, (k : ℤ) - 1), ?_, ?_⟩
    · rw [mem_nonVDiagram]; omega
    · dsimp [content]; ring
  · intro t ht
    obtain ⟨⟨a, b⟩, hm, he⟩ := Finset.mem_image.mp ht
    change b - a = t at he
    have := nonVDiagram_content_bounds k hk hm
    omega

/-- Every literal middle cell has content between its two retained cap cells. -/
theorem nonVMark_middle_content_bounds (k : ℕ) (hk : 3 ≤ k) {a b : ℤ}
    (h : (a, b) ∈ (nonVMark k).middle) : 1 ≤ b - a ∧ b - a ≤ (k : ℤ) := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  rw [mem_nonVMark_middle k hk] at h
  omega

/-- The middle's actual southwest content is one. -/
theorem nonVMark_middle_minContent (k : ℕ) (hk : 3 ≤ k) :
    minContent (nonVMark k).middle = 1 := by
  apply minContent_eq_of
  · refine Finset.mem_image.mpr ⟨(0, 1), ?_, rfl⟩
    rw [mem_nonVMark_middle k hk]; omega
  · intro t ht
    obtain ⟨⟨a, b⟩, hm, he⟩ := Finset.mem_image.mp ht
    change b - a = t at he
    have := nonVMark_middle_content_bounds k hk hm
    omega

/-- The middle's actual northeast content is `k`. -/
theorem nonVMark_middle_maxContent (k : ℕ) (hk : 3 ≤ k) :
    maxContent (nonVMark k).middle = k := by
  apply maxContent_eq_of
  · refine Finset.mem_image.mpr ⟨(-2, (k : ℤ) - 2), ?_, ?_⟩
    · rw [mem_nonVMark_middle k hk]; omega
    · dsimp [content]; ring
  · intro t ht
    obtain ⟨⟨a, b⟩, hm, he⟩ := Finset.mem_image.mp ht
    change b - a = t at he
    have := nonVMark_middle_content_bounds k hk hm
    omega

end SkewCornerDescent
