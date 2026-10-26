/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/LeftPieces.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem.LeftX
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem.RightPieces

/-!
# The copies of `\overline O`, `W`, `\overline W` left behind by a ribbon removable on the left

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the three families of pieces of thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`) for a ribbon `leftStrip D j₀ m` removable on the left from
`D`.

A diagonal `j` of the window with a single cell (`rLone`) loses its cell; the copy `E + j v` then
leaves a copy of `\overline O` at `j v`, a copy of `W` at `(j + 1) v` if the cell has no box to
its east (`lLoneE`) and a copy of `\overline W` at `j v` if it has no box to its south
(`lLoneS`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner}

/-- The lone diagonals whose cell has no box to its east. -/
def lLoneE (D : Diagram) (j0 : ℤ) (m : ℕ) : Finset ℤ :=
  (rLone D j0 m).filter fun j => (diagLo D j, diagLo D j + (j + 1)) ∉ D

/-- The lone diagonals whose cell has no box to its south. -/
def lLoneS (D : Diagram) (j0 : ℤ) (m : ℕ) : Finset ℤ :=
  (rLone D j0 m).filter fun j => (diagLo D j + 1, (diagLo D j + 1) + (j - 1)) ∉ D

/-- The copies of `W` at `(j + 1) v`, `j` lone with no box to the east. -/
def lPieceU (ω : MarkedInner) (D : Diagram) (j0 : ℤ) (m : ℕ) : Diagram :=
  (lLoneE D j0 m).biUnion fun j => translate ((j + 1) • ω.v) ω.W

/-- The copies of `\overline W` at `j v`, `j` lone with no box to the south. -/
def lPieceS (ω : MarkedInner) (D : Diagram) (j0 : ℤ) (m : ℕ) : Diagram :=
  (lLoneS D j0 m).biUnion fun j => translate (j • ω.v) (hatMarkFin ω)

theorem mem_lLoneE {D : Diagram} (hD : IsSkew D) {j0 : ℤ} {m : ℕ} {J : ℤ} :
    J ∈ lLoneE D j0 m ↔ J ∈ rLone D j0 m ∧
      ¬ (J + 1 ∈ contents D ∧ diagLo D (J + 1) ≤ diagLo D J ∧
        diagLo D J ≤ diagHi D (J + 1)) := by
  unfold lLoneE
  rw [Finset.mem_filter, mem_skew_iff hD]

theorem mem_lLoneS {D : Diagram} (hD : IsSkew D) {j0 : ℤ} {m : ℕ} {J : ℤ} :
    J ∈ lLoneS D j0 m ↔ J ∈ rLone D j0 m ∧
      ¬ (J - 1 ∈ contents D ∧ diagLo D (J - 1) ≤ diagLo D J + 1 ∧
        diagLo D J + 1 ≤ diagHi D (J - 1)) := by
  unfold lLoneS
  rw [Finset.mem_filter, mem_skew_iff hD]

theorem mem_lPieceU (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
    {D : Diagram} {j0 : ℤ} {m : ℕ} {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ lPieceU ω D j0 m ↔
      J - 1 ∈ lLoneE D j0 m ∧ a < ω.widthZ ∧ ω.lo a ≤ r - J * ω.rowShift ∧
        r - J * ω.rowShift ≤ ω.hi a - (if s ≤ a then 1 else 0) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold lPieceU
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    rw [mem_translate_smul_cell, mem_W_cell h hc hph] at hx
    have e : J * ω.period + a - (j + 1) * ω.period = (J - (j + 1)) * ω.period + a := by ring
    rw [e] at hx
    have hJ := blk_eq (q := ω.period) (J := J) (j := j + 1) (by omega) ha0 haq hx.1 (by omega) rfl
    subst hJ
    have e2 : (j + 1 - (j + 1)) * ω.period + a = a := by ring
    rw [e2] at hx
    refine ⟨by simpa using hj, by omega, hx.2.2.1, hx.2.2.2⟩
  · rintro ⟨hj, h1, h2, h3⟩
    refine ⟨J - 1, hj, ?_⟩
    rw [mem_translate_smul_cell, mem_W_cell h hc hph]
    have e : J * ω.period + a - (J - 1 + 1) * ω.period = a := by ring
    have e' : (J - 1 + 1) * ω.rowShift = J * ω.rowShift := by ring
    rw [e, e']
    exact ⟨ha0, by omega, h2, h3⟩

theorem mem_lPieceS (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
    {D : Diagram} {j0 : ℤ} {m : ℕ} {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ lPieceS ω D j0 m ↔
      J ∈ lLoneS D j0 m ∧ a < ω.widthZ ∧ ω.lo a ≤ r - J * ω.rowShift ∧
        r - J * ω.rowShift ≤ ω.hi a - (if t ≤ a then 1 else 0) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold lPieceS
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    rw [mem_translate_smul_cell, mem_hatMarkFin_cell h hc hph] at hx
    have e : J * ω.period + a - j * ω.period = (J - j) * ω.period + a := by ring
    rw [e] at hx
    have hJ := blk_eq (q := ω.period) (J := J) (j := j) (by omega) ha0 haq hx.1 (by omega) rfl
    subst hJ
    have e2 : (J - J) * ω.period + a = a := by ring
    rw [e2] at hx
    exact ⟨hj, by omega, hx.2.2.1, hx.2.2.2⟩
  · rintro ⟨hj, h1, h2, h3⟩
    refine ⟨J, hj, ?_⟩
    rw [mem_translate_smul_cell, mem_hatMarkFin_cell h hc hph]
    have e : J * ω.period + a - J * ω.period = a := by ring
    rw [e]
    exact ⟨ha0, by omega, h2, h3⟩

end Rem

end Corner

end Plan

end SkewMarkedFactor.Gluing
