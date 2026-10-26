/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkBasics
import SkewClassInflation.HatMarkTranslation

/-!
# Empty hatted marks in the bi-infinite two-row chain

Hypothesis IV for the actual chart in `lem:subthreshold-transport`
of `shields-2026-skew-class-inflation.tex`.  The row coordinate
restricts every potentially diagonal-adjacent copy to two explicit
periods; the strict threshold inequality excludes both intervals.
Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- Exact membership in every copy of the actual bi-infinite inflated-inner chain. -/
theorem mem_inflationPeriodic (t : ℕ) (i j : ℤ) :
    (i, j) ∈ (B.inflationMark t).periodicUnion ↔
      ∃ k : ℤ,
        (i + k = 0 ∧ (B.b : ℤ) - B.c - 1 ≤ j - k * ((B.boundary.q : ℤ) - 1) ∧
          j - k * ((B.boundary.q : ℤ) - 1) < (B.boundary.q : ℤ) + t - 1) ∨
        (i + k = 1 ∧ 0 ≤ j - k * ((B.boundary.q : ℤ) - 1) ∧
          j - k * ((B.boundary.q : ℤ) - 1) < (B.b : ℤ) + t) := by
  change (∃ k : ℤ, (i, j) - k • (-1, (B.boundary.q : ℤ) - 1) ∈ B.innerCells t) ↔ _
  apply exists_congr
  intro k
  have he : (i, j) - k • (-1, (B.boundary.q : ℤ) - 1) =
      (i + k, j - k * ((B.boundary.q : ℤ) - 1)) := by
    ext <;> simp
  rw [he, B.mem_innerCells]

/-- No literal marked cell has a diagonal neighbor in any copy of the infinite chain. -/
theorem inflationMark_hatMark_empty (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).hatMark (B.inflationMark t).W = ∅ := by
  have hq := B.boundary_q_eq
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    have := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hab := B.a_lt_b
  have hc := B.c_pos
  ext x
  rw [Set.mem_empty_iff_false, iff_false]
  obtain ⟨i, j⟩ := x
  intro hx
  rcases hx with hx | hx
  · have hw := hx.2
    change (i + 1, j + 1) ∈ lowerMark t at hw
    rw [mem_lowerMark] at hw
    have hh := hx.1
    rw [B.mem_inflationPeriodic] at hh
    obtain ⟨k, hk | hk⟩ := hh
    · have he : k = 0 := by omega
      subst k
      norm_num at hk
      omega
    · have he : k = 1 := by omega
      subst k
      norm_num at hk
      omega
  · have hw := hx.1
    change (i, j) ∈ lowerMark t at hw
    rw [mem_lowerMark] at hw
    have hh := hx.2
    change (i + 1, j + 1) ∈ (B.inflationMark t).periodicUnion at hh
    rw [B.mem_inflationPeriodic] at hh
    obtain ⟨k, hk | hk⟩ := hh
    · have he : k = -2 := by omega
      subst k
      norm_num at hk
      omega
    · have he : k = -1 := by omega
      subst k
      norm_num at hk
      omega

/-- Hypothesis IV holds for all marked and middle copies in the actual infinite amalgamation. -/
theorem inflationMark_noHatAdjacency (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).NoHatAdjacency :=
  noHatAdjacency_of_hatMark_empty _ (B.inflationMark_hatMark_empty t ht)

end SkewClassInflation.ThinParameters
