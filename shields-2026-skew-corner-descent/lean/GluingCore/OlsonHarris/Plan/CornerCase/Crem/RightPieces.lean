-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/CornerCase/Crem/RightPieces.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.RightX
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.Pieces

/-!
# The copies of `\overline O`, `W`, `\overline W` left behind by a ribbon removable on the right

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the three families of pieces of thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`) for a ribbon `windowRibbon D j₀ m` removable on the right
from `D`.

A diagonal `j` of the window with a single cell (`rLone`) loses its cell; the copy `E + j v`
then leaves a copy of `\overline O` at `j v`, a copy of `W` at `j v` if the cell has no box to its
west (`rLoneW`) and a copy of `\overline W` at `(j + 1) v` if it has no box to its north
(`rLoneN`).

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner}

theorem cell_sub_smul_v (ω : MarkedInner) (k r j : ℤ) :
    ω.cell k r - j • ω.v = ω.cell (k - j * ω.period) (r - j * ω.rowShift) := by
  have := period_eq ω
  unfold cell rowShift at *
  ext
  · simp
  · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
    rw [v_eq ω] at *
    simp only [rowShift] at *
    nlinarith

theorem mem_translate_smul_cell (ω : MarkedInner) (S : Diagram) (k r j : ℤ) :
    ω.cell k r ∈ translate (j • ω.v) S ↔
      ω.cell (k - j * ω.period) (r - j * ω.rowShift) ∈ S := by
  rw [mem_translate, cell_sub_smul_v]

theorem blk_eq {q J j a a' : ℤ} (hq : 0 < q) (ha0 : 0 ≤ a) (ha1 : a < q) (h0 : 0 ≤ a')
    (h1 : a' < q) (h : a' = (J - j) * q + a) : J = j := by
  rcases lt_trichotomy (J - j) 0 with hl | he | hg
  · have := mul_le_mul_of_nonneg_right (by omega : J - j ≤ -1) hq.le
    omega
  · omega
  · have := mul_le_mul_of_nonneg_right (by omega : 1 ≤ J - j) hq.le
    omega

/-- The diagonals of the window that have a single cell. -/
def rLone (D : Diagram) (j0 : ℤ) (m : ℕ) : Finset ℤ :=
  (Finset.Ico j0 (j0 + m)).filter fun j => diagLo D j = diagHi D j

/-- The lone diagonals whose cell has no box to its west. -/
def rLoneW (D : Diagram) (j0 : ℤ) (m : ℕ) : Finset ℤ :=
  (rLone D j0 m).filter fun j => (diagLo D j, diagLo D j + (j - 1)) ∉ D

/-- The lone diagonals whose cell has no box to its north. -/
def rLoneN (D : Diagram) (j0 : ℤ) (m : ℕ) : Finset ℤ :=
  (rLone D j0 m).filter fun j => (diagLo D j - 1, (diagLo D j - 1) + (j + 1)) ∉ D

/-- The copies of `\overline O` at `j v`, `j` lone. -/
def rPieceO (ω : MarkedInner) (D : Diagram) (j0 : ℤ) (m : ℕ) : Diagram :=
  (rLone D j0 m).biUnion fun j => translate (j • ω.v) (hatMiddleFin ω)

/-- The copies of `W` at `j v`, `j` lone with no box to the west. -/
def rPieceW (ω : MarkedInner) (D : Diagram) (j0 : ℤ) (m : ℕ) : Diagram :=
  (rLoneW D j0 m).biUnion fun j => translate (j • ω.v) ω.W

/-- The copies of `\overline W` at `(j + 1) v`, `j` lone with no box to the north. -/
def rPieceN (ω : MarkedInner) (D : Diagram) (j0 : ℤ) (m : ℕ) : Diagram :=
  (rLoneN D j0 m).biUnion fun j => translate ((j + 1) • ω.v) (hatMarkFin ω)

theorem mem_rLone {D : Diagram} {j0 : ℤ} {m : ℕ} {j : ℤ} :
    j ∈ rLone D j0 m ↔ (j0 ≤ j ∧ j < j0 + m) ∧ diagLo D j = diagHi D j := by
  unfold rLone
  rw [Finset.mem_filter, Finset.mem_Ico]

theorem mem_rLoneW {D : Diagram} (hD : IsSkew D) {j0 : ℤ} {m : ℕ} {J : ℤ} :
    J ∈ rLoneW D j0 m ↔ J ∈ rLone D j0 m ∧
      ¬ (J - 1 ∈ contents D ∧ diagLo D (J - 1) ≤ diagLo D J ∧
        diagLo D J ≤ diagHi D (J - 1)) := by
  unfold rLoneW
  rw [Finset.mem_filter, mem_skew_iff hD]

theorem mem_rLoneN {D : Diagram} (hD : IsSkew D) {j0 : ℤ} {m : ℕ} {J : ℤ} :
    J ∈ rLoneN D j0 m ↔ J ∈ rLone D j0 m ∧
      ¬ (J + 1 ∈ contents D ∧ diagLo D (J + 1) ≤ diagLo D J - 1 ∧
        diagLo D J - 1 ≤ diagHi D (J + 1)) := by
  unfold rLoneN
  rw [Finset.mem_filter, mem_skew_iff hD]

theorem mem_rPieceO (h : ω.IsLegalNonempty) {D : Diagram} {j0 : ℤ} {m : ℕ} {J a r : ℤ}
    (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ rPieceO ω D j0 m ↔
      J ∈ rLone D j0 m ∧ ω.widthZ ≤ a ∧ ω.lo a ≤ r - J * ω.rowShift ∧
        r - J * ω.rowShift + 1 ≤ ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold rPieceO
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    rw [mem_translate_smul_cell, mem_hatMiddleFin_cell h] at hx
    have e : J * ω.period + a - j * ω.period = (J - j) * ω.period + a := by ring
    rw [e] at hx
    have hJ := blk_eq (q := ω.period) (J := J) (j := j) (by omega) ha0 haq (by omega) hx.2.1
      rfl
    subst hJ
    have e2 : (J - J) * ω.period + a = a := by ring
    rw [e2] at hx
    exact ⟨hj, hx.1, hx.2.2.1, hx.2.2.2⟩
  · rintro ⟨hj, h1, h2, h3⟩
    refine ⟨J, hj, ?_⟩
    rw [mem_translate_smul_cell, mem_hatMiddleFin_cell h]
    have e : J * ω.period + a - J * ω.period = a := by ring
    rw [e]
    exact ⟨h1, haq, h2, h3⟩

theorem mem_rPieceW (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
    {D : Diagram} {j0 : ℤ} {m : ℕ} {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ rPieceW ω D j0 m ↔
      J ∈ rLoneW D j0 m ∧ a < ω.widthZ ∧ ω.lo a ≤ r - J * ω.rowShift ∧
        r - J * ω.rowShift ≤ ω.hi a - (if s ≤ a then 1 else 0) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold rPieceW
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    rw [mem_translate_smul_cell, mem_W_cell h hc hph] at hx
    have e : J * ω.period + a - j * ω.period = (J - j) * ω.period + a := by ring
    rw [e] at hx
    have hJ := blk_eq (q := ω.period) (J := J) (j := j) (by omega) ha0 haq hx.1 (by omega) rfl
    subst hJ
    have e2 : (J - J) * ω.period + a = a := by ring
    rw [e2] at hx
    exact ⟨hj, by omega, hx.2.2.1, hx.2.2.2⟩
  · rintro ⟨hj, h1, h2, h3⟩
    refine ⟨J, hj, ?_⟩
    rw [mem_translate_smul_cell, mem_W_cell h hc hph]
    have e : J * ω.period + a - J * ω.period = a := by ring
    rw [e]
    exact ⟨ha0, by omega, h2, h3⟩

theorem mem_rPieceN (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
    {D : Diagram} {j0 : ℤ} {m : ℕ} {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ rPieceN ω D j0 m ↔
      J - 1 ∈ rLoneN D j0 m ∧ a < ω.widthZ ∧ ω.lo a ≤ r - J * ω.rowShift ∧
        r - J * ω.rowShift ≤ ω.hi a - (if t ≤ a then 1 else 0) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold rPieceN
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    rw [mem_translate_smul_cell, mem_hatMarkFin_cell h hc hph] at hx
    have e : J * ω.period + a - (j + 1) * ω.period = (J - (j + 1)) * ω.period + a := by ring
    rw [e] at hx
    have hJ := blk_eq (q := ω.period) (J := J) (j := j + 1) (by omega) ha0 haq hx.1 (by omega) rfl
    subst hJ
    have e2 : (j + 1 - (j + 1)) * ω.period + a = a := by ring
    rw [e2] at hx
    have e3 : (j + 1) * ω.rowShift = (j + 1) * ω.rowShift := rfl
    refine ⟨by simpa using hj, by omega, hx.2.2.1, hx.2.2.2⟩
  · rintro ⟨hj, h1, h2, h3⟩
    refine ⟨J - 1, hj, ?_⟩
    rw [mem_translate_smul_cell, mem_hatMarkFin_cell h hc hph]
    have e : J * ω.period + a - (J - 1 + 1) * ω.period = a := by ring
    have e' : (J - 1 + 1) * ω.rowShift = J * ω.rowShift := by ring
    rw [e, e']
    exact ⟨ha0, by omega, h2, h3⟩

end Rem

end Corner

end Plan

end GluingCore
