/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Local.Diagonals
import SkewGluing.Local.Assemble

/-!
# Composition coordinates

TODO-COPIED: coordinate and interval declarations from
skew-factor-gluing/lean/SkewGluing/Local/ComposeRows.lean and ComposeOrd.lean.
Supplies actual copy coordinates for `lem:row-amalgamation` in
`shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps».
Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner}

/-- The row of the origin `L_ω(d)` for the cell `d = (i, i + j)` of `D`, by `eq:gluing-offsets`. -/
def originRow (ω : MarkedInner) (D : Diagram) (j i : ℤ) : ℤ :=
  match ω.case with
  | .a => j * ω.rowShift + i
  | .b => j * ω.rowShift - i
  | .c => j * ω.rowShift + (i - diagLo D j)
  | .d => j * ω.rowShift - (diagHi D j - i)

/-- The least origin row over the diagonal `j` of `D`. -/
def oRowLo (ω : MarkedInner) (D : Diagram) (j : ℤ) : ℤ :=
  match ω.case with
  | .a => j * ω.rowShift + diagLo D j
  | .b => j * ω.rowShift - diagHi D j
  | .c => j * ω.rowShift
  | .d => j * ω.rowShift - (diagHi D j - diagLo D j)

/-- The greatest origin row over the diagonal `j` of `D`. -/
def oRowHi (ω : MarkedInner) (D : Diagram) (j : ℤ) : ℤ :=
  match ω.case with
  | .a => j * ω.rowShift + diagHi D j
  | .b => j * ω.rowShift - diagLo D j
  | .c => j * ω.rowShift + (diagHi D j - diagLo D j)
  | .d => j * ω.rowShift

theorem origin_fst (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) :
    (ω.origin D d).1 = ω.originRow D (content d) d.1 := by
  unfold origin originRow
  cases ω.case <;> simp [rowShift, eCell, content]

theorem cell_sub_origin (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) (k r : ℤ) :
    ω.cell k r - ω.origin D d =
      ω.cell (k - content d * ω.period) (r - (ω.origin D d).1) := by
  have hc := content_origin ω D d
  unfold content at hc
  unfold cell
  ext
  · simp
  · simp only [Prod.snd_sub, content]; omega

variable {D : Diagram}

theorem mem_D (hD : IsConnectedSkew D) {i j : ℤ} :
    (i, i + j) ∈ D ↔ minContent D ≤ j ∧ j ≤ maxContent D ∧ diagLo D j ≤ i ∧ i ≤ diagHi D j := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  rw [hs.mem_iff, hs.mem_contents_iff]
  tauto

theorem IsLegalNonempty.mem_main (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) {k r : ℤ} :
    (∃ d ∈ D, ω.cell k r ∈ translate (ω.origin D d) ω.E) ↔
      ∃ j i, minContent D ≤ j ∧ j ≤ maxContent D ∧ diagLo D j ≤ i ∧ i ≤ diagHi D j ∧
        0 ≤ k - j * ω.period ∧ k - j * ω.period ≤ ω.period + ω.widthZ - 1 ∧
        ω.lo (k - j * ω.period) ≤ r - ω.originRow D j i ∧
        r - ω.originRow D j i ≤ ω.hi (k - j * ω.period) := by
  constructor
  · rintro ⟨d, hd, hx⟩
    obtain ⟨d1, d2⟩ := d
    have hdc : content (d1, d2) = d2 - d1 := rfl
    have hd' : (d1, d1 + (d2 - d1)) ∈ D := by simpa using hd
    rw [mem_D hD] at hd'
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst] at hx
    simp only [hdc] at hx
    exact ⟨d2 - d1, d1, hd'.1, hd'.2.1, hd'.2.2.1, hd'.2.2.2, by omega,
      by omega, by omega, by omega⟩
  · rintro ⟨j, i, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨(i, i + j), (mem_D hD).mpr ⟨h1, h2, h3, h4⟩, ?_⟩
    have hdc : content (i, i + j) = j := by simp [content]
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst, hdc]
    exact ⟨h5, h6, h7, h8⟩

theorem range_j {q w J j a : ℤ} (hq : 0 < q) (hwq : w < q) (h0 : 0 ≤ a) (h1 : a < q)
    (_hw : 0 ≤ w) (h2 : 0 ≤ J * q + a - j * q) (h3 : J * q + a - j * q ≤ q + w - 1) :
    j = J ∨ (j = J - 1 ∧ a < w) := by
  by_cases hj : j ≤ J - 2
  · have := mul_le_mul_of_nonneg_right hj hq.le
    nlinarith
  · by_cases hj1 : J + 1 ≤ j
    · have := mul_le_mul_of_nonneg_right hj1 hq.le
      nlinarith
    · by_cases hj2 : j = J
      · exact Or.inl hj2
      · have : j = J - 1 := by omega
        subst this
        right
        refine ⟨rfl, ?_⟩
        have : (J - 1) * q = J * q - q := by ring
        omega

/-- The rows of the copies of `E` at the diagonal `j` of `D`, on the diagonal of `E` of relative
content `b`, when `lo b ≤ hi b`, form the interval `[oRowLo j + ℓ_b, oRowHi j + h_b]`. -/
theorem piece_iff (hD : IsConnectedSkew D) {j A B r : ℤ} (hA : A ≤ B)
    (hj : minContent D ≤ j ∧ j ≤ maxContent D) :
    (∃ i, diagLo D j ≤ i ∧ i ≤ diagHi D j ∧ A ≤ r - ω.originRow D j i ∧
      r - ω.originRow D j i ≤ B) ↔ ω.oRowLo D j + A ≤ r ∧ r ≤ ω.oRowHi D j + B := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hne : diagLo D j ≤ diagHi D j := diagLo_le_diagHi (hs.mem_contents_iff.mpr hj)
  unfold originRow oRowLo oRowHi
  cases ω.case
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (r - j * ω.rowShift - B), by omega, by omega, by omega, by omega⟩
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (A + j * ω.rowShift - r), by omega, by omega, by omega, by omega⟩
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (r - j * ω.rowShift + diagLo D j - B), by omega, by omega, by omega,
        by omega⟩
  · simp only
    constructor
    · rintro ⟨i, h1, h2, h3, h4⟩; omega
    · intro h
      exact ⟨max (diagLo D j) (r - j * ω.rowShift + diagHi D j - B), by omega, by omega, by omega,
        by omega⟩

theorem oRow_le (hD : IsConnectedSkew D) {j : ℤ} (hj : minContent D ≤ j ∧ j ≤ maxContent D) :
    ω.oRowLo D j ≤ ω.oRowHi D j := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hne : diagLo D j ≤ diagHi D j := diagLo_le_diagHi (hs.mem_contents_iff.mpr hj)
  unfold oRowLo oRowHi
  cases ω.case <;> simp only <;> omega

theorem D_bits (hD : IsConnectedSkew D) {J : ℤ} (h1 : minContent D + 1 ≤ J)
    (h2 : J ≤ maxContent D) :
    (diagLo D (J - 1) - diagLo D J = 0 ∨ diagLo D (J - 1) - diagLo D J = 1) ∧
    (diagHi D (J - 1) - diagHi D J = 0 ∨ diagHi D (J - 1) - diagHi D J = 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have m1 : J ∈ contents D := hs.mem_contents_iff.mpr ⟨by omega, h2⟩
  have m2 : J - 1 ∈ contents D := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have := hs.2.2.2.1 J m1 m2
  simp only [bitA, bitB, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

theorem D_ends (hD : IsConnectedSkew D) :
    diagLo D (minContent D) = diagHi D (minContent D) ∧
      diagLo D (maxContent D) = diagHi D (maxContent D) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hne := hD.2.1
  refine ⟨hs.2.2.2.2 _ (minContent_mem hne) (Or.inl ?_), hs.2.2.2.2 _ (maxContent_mem hne)
    (Or.inr ?_)⟩
  · intro hm; have := minContent_le hm; omega
  · intro hm; have := le_maxContent hm; omega

end MarkedInner
end SkewGluing
