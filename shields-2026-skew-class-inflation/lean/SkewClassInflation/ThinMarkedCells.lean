/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.HorizontalCells
import SkewClassInflation.ThinPowerBetas

/-!
# The literal two-row inflation chart

The actual cells and both marked placements in
`eq:inflation-inner-cells` and `eq:inflation-marks` of
`shields-2026-skew-class-inflation.tex`.  The cell set is defined from
the inflated determinant profile, with the common coordinate translation
used by the manuscript.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- The actual inflated inner, in the manuscript's integer cell coordinates. -/
def innerCells (t : ℕ) : SkewGluing.Diagram :=
  translate (0, -1) (profileCells (Profile.inflate t (B.innerPower 1 (by decide))))

/-- The southwest mark is the first `t` cells of the lower row. -/
def lowerMark (t : ℕ) : SkewGluing.Diagram := translate (1, 0) (rowCells 0 t)

/-- The full literal case-(a) marked inner, including its specified displacement. -/
def inflationMark (t : ℕ) : MarkedInner where
  E := B.innerCells t
  W := lowerMark t
  v := (-1, (B.boundary.q : ℤ) - 1)
  case := .a

/-- The full actual cell profile is exactly the two integer intervals displayed in the paper. -/
theorem mem_innerCells (t : ℕ) (i j : ℤ) :
    (i, j) ∈ B.innerCells t ↔
      (i = 0 ∧ (B.b : ℤ) - B.c - 1 ≤ j ∧ j < (B.boundary.q : ℤ) + t - 1) ∨
      (i = 1 ∧ 0 ≤ j ∧ j < (B.b : ℤ) + t) := by
  let P := Profile.inflate t (B.innerPower 1 (by decide))
  have hx0 : P.xi 0 = (B.boundary.q : ℤ) + t := by
    rw [Profile.xi_inflate, B.innerPower_span]
    simp
  have hz0 : P.zeta 0 = (B.b : ℤ) - B.c := by
    rw [Profile.zeta_inflate, congrFun (B.innerPower_beta 1 (by decide)).2 0]
    norm_num [powerLower]
  have hx1 : P.xi 1 = (B.b : ℤ) + t := by
    rw [Profile.xi_inflate, congrFun (B.innerPower_beta 1 (by decide)).1 1]
    norm_num [powerUpper]
  have hz1 : P.zeta 1 = 0 := by
    change P.zeta (Fin.last 1) = 0
    exact P.zeta_last
  change (i, j) ∈ translate (0, -1) (profileCells P) ↔ _
  rw [mem_translate]
  have htranslate : (i, j) - (0, -1) = (i, j + 1) := by ext <;> simp
  rw [htranslate]
  rw [mem_profileCells]
  constructor
  · rintro ⟨k, hk, hlo, hhi⟩
    fin_cases k
    · left
      change P.zeta 0 + (0 : ℤ) ≤ j + 1 at hlo
      change j + 1 < P.xi 0 + (0 : ℤ) at hhi
      rw [hz0] at hlo
      rw [hx0] at hhi
      norm_num at hk hlo hhi
      exact ⟨hk.symm, by omega, by omega⟩
    · right
      change P.zeta 1 + (1 : ℤ) ≤ j + 1 at hlo
      change j + 1 < P.xi 1 + (1 : ℤ) at hhi
      rw [hz1] at hlo
      rw [hx1] at hhi
      norm_num at hk hlo hhi
      exact ⟨hk.symm, by omega, by omega⟩
  · rintro (⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩)
    · refine ⟨0, rfl, ?_, ?_⟩
      · rw [hz0]; norm_num; omega
      · rw [hx0]; norm_num; omega
    · refine ⟨1, rfl, ?_, ?_⟩
      · rw [hz1]; norm_num; omega
      · rw [hx1]; norm_num; omega

/-- Southwest mark membership is its literal lower-row interval. -/
theorem mem_lowerMark (t : ℕ) (i j : ℤ) :
    (i, j) ∈ lowerMark t ↔ i = 1 ∧ 0 ≤ j ∧ j < t := by
  rw [lowerMark, mem_translate]
  have htranslate : (i, j) - (1, 0) = (i - 1, j) := by ext <;> simp
  rw [htranslate]
  rw [mem_rowCells]
  omega

/-- The specified displacement produces exactly the displayed northeast mark. -/
theorem mem_upperMark (t : ℕ) (i j : ℤ) :
    (i, j) ∈ (B.inflationMark t).upper ↔
      i = 0 ∧ (B.boundary.q : ℤ) - 1 ≤ j ∧ j < (B.boundary.q : ℤ) + t - 1 := by
  rw [MarkedInner.upper, mem_translate]
  change (i + 1, j - ((B.boundary.q : ℤ) - 1)) ∈ lowerMark t ↔ _
  rw [mem_lowerMark]
  omega

/-- The actual chart inner is a connected skew diagram, not an abstract profile proxy. -/
theorem innerCells_connected (t : ℕ) : IsConnectedSkew (B.innerCells t) :=
  isConnectedSkew_translate _ (profileCells_connected _)

end SkewClassInflation.ThinParameters
