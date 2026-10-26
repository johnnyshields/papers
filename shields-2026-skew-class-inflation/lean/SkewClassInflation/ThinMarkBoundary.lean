/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkAttachments

/-!
# The exact legality boundary of the specified inflation chart

The chart boundary discussed in `rem:chart-boundary` of
`shields-2026-skew-class-inflation.tex`.  At and above the threshold,
a concrete rectangle witness shows that deleting the specified upper
mark leaves a non-skew cell set.  This excludes this literal chart,
not every possible chart on the same diagram.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- At or above the threshold, the specified upper-mark complement violates skew convexity. -/
theorem upper_mark_removal_not_skew (t : ℕ) (ht : B.boundary.p ≤ t) :
    ¬ IsSkew ((B.inflationMark t).E \ (B.inflationMark t).upper) := by
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    have := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hq := B.boundary_q_eq
  have hab := B.a_lt_b
  have hca := B.c_lt_a
  have hc := B.c_pos
  have hpp := B.boundary.p_pos
  let D := (B.inflationMark t).E \ (B.inflationMark t).upper
  have hx : (0, (B.boundary.q : ℤ) - 2) ∈ D := by
    rw [Finset.mem_sdiff]
    constructor
    · change (0, (B.boundary.q : ℤ) - 2) ∈ B.innerCells t
      rw [B.mem_innerCells]
      left
      exact ⟨rfl, by omega, by omega⟩
    · rw [B.mem_upperMark]
      omega
  have hy : (1, (B.boundary.q : ℤ) - 1) ∈ D := by
    rw [Finset.mem_sdiff]
    constructor
    · change (1, (B.boundary.q : ℤ) - 1) ∈ B.innerCells t
      rw [B.mem_innerCells]
      right
      exact ⟨rfl, by omega, by omega⟩
    · rw [B.mem_upperMark]
      omega
  intro hskew
  have hmissing := hskew.mem hx hy (by norm_num) (by omega)
    (show (0 : ℤ) ≤ 0 by omega) (show (0 : ℤ) ≤ 1 by omega)
    (show (B.boundary.q : ℤ) - 2 ≤ B.boundary.q - 1 by omega) (le_rfl)
  have hnot := (Finset.mem_sdiff.mp hmissing).2
  apply hnot
  rw [B.mem_upperMark]
  exact ⟨rfl, le_rfl, by omega⟩

/-- These specified literal marks are legal exactly below the sharp inflation boundary. -/
theorem inflationMark_legal_iff (t : ℕ) : (B.inflationMark t).IsLegal ↔ t < B.boundary.p := by
  constructor
  · intro h
    by_contra hn
    have hrem := h.2.2.2.1.2.1
    exact B.upper_mark_removal_not_skew t (by omega) hrem
  · exact B.inflationMark_legal t

end SkewClassInflation.ThinParameters
