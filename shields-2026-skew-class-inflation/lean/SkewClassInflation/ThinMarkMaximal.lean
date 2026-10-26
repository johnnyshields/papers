/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkBasics

/-!
# Maximality of the literal terminal marks

Hypothesis I for the chart in `lem:subthreshold-transport` of
`shields-2026-skew-class-inflation.tex`.  Each content diagonal of the
southwest mark contains only that marked cell of the actual inner;
therefore no strictly larger candidate can occupy the same diagonals.
Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- Every inner cell on a marked content diagonal is already in the mark. -/
theorem inner_cell_on_lower_mark_content (t : ℕ) (ht : t < B.boundary.p)
    (z : ℤ × ℤ) (hz : z ∈ B.innerCells t) (hc : content z ∈ contents (lowerMark t)) :
    z ∈ lowerMark t := by
  obtain ⟨r, s⟩ := z
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hc
  change (i, i + (s - r)) ∈ lowerMark t at hi
  rw [mem_lowerMark] at hi
  rw [B.mem_innerCells] at hz
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    have := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hab := B.a_lt_b
  rw [mem_lowerMark]
  rcases hz with hz | hz <;> omega

/-- The specified literal marks satisfy maximality below the exact threshold. -/
theorem inflationMark_maximal (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).IsMaximal := by
  intro W' hW' hstrict _ hcontents
  have hsub : W' ⊆ (B.inflationMark t).W := by
    intro z hz
    have hE := (Finset.mem_powerset.mp hW') hz
    have hc : content z ∈ contents (lowerMark t) := by
      change content z ∈ contents (B.inflationMark t).W
      rw [← hcontents]
      exact content_mem_contents hz
    exact B.inner_cell_on_lower_mark_content t ht z hE hc
  have hfalse := (not_lt_of_ge hsub) hstrict
  exact hfalse.elim

end SkewClassInflation.ThinParameters
