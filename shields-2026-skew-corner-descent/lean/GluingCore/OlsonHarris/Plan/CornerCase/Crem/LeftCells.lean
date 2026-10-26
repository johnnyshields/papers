-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/CornerCase/Crem/LeftCells.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.RightCells
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.ArithLeft
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.LeftPieces

/-!
# The cell identity for a ribbon removable on the left

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`) for a ribbon `A = leftStrip D j₀ m` removable on the left
from the connected skew `D`, and a legal mark of case (c).

`left_cell_iff`: the cells of `D ∘_ω E` outside the lift `cornerLift ω D m t A` are the cells of
`(D \ A) ∘_ω E` together with the copies of `\overline O`, `W`, `\overline W` of
`rPieceO`, `lPieceU`, `lPieceS`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner} {D : Diagram} {j0 : ℤ} {m : ℕ}

theorem minContent_leftStrip (hm : 0 < m) : minContent (leftStrip D j0 m) = j0 := by
  have hmem : ∀ k, k ∈ contents (leftStrip D j0 m) ↔ ∃ y ∈ leftStrip D j0 m, content y = k := by
    intro k
    unfold contents
    rw [Finset.mem_image]
  refine minContent_eq_of ((hmem j0).mpr ⟨(diagLo D j0, diagLo D j0 + j0), ?_, by simp [content]⟩)
    ?_
  · rw [mem_leftStrip]
    simp only [content]
    have e : diagLo D j0 + j0 - diagLo D j0 = j0 := by ring
    rw [e]
    exact ⟨le_rfl, by omega, rfl⟩
  · intro k hk
    obtain ⟨y, hy, rfl⟩ := (hmem k).mp hk
    exact (mem_leftStrip.mp hy).1

/-- **The cell identity for a ribbon removable on the left** (thesis Lemma 5.5.8). -/
theorem left_cell_iff (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) (hw : LeftWindow D j0 m) {J a r : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ ω.compose D \ cornerLift ω D m t (leftStrip D j0 m) ↔
      (ω.cell (J * ω.period + a) r ∈ Fp ω (D \ leftStrip D j0 m) ∨
        ω.cell (J * ω.period + a) r ∈ rPieceO ω D j0 m ∨
        ω.cell (J * ω.period + a) r ∈ lPieceU ω D j0 m ∨
        ω.cell (J * ω.period + a) r ∈ lPieceS ω D j0 m) := by
  have hD := hw.conn
  obtain ⟨hmem, hhl, hbl, hbh, hend⟩ := outer_facts hD
  have hq := h.width_lt_period
  have hwpos := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hts := h.phases_lt (Or.inl hc) hph
  have hF := h.isConnectedSkew_compose hD
  have hFs := isConnectedSkew_iff_diagonal.mp hF
  have hDne : D.Nonempty := hD.2.1
  have hXs := hw.isSkew_X
  have hminA : minContent (leftStrip D j0 m) = j0 := minContent_leftStrip hw.pos
  have hq0 : 0 < ω.period := by omega
  have hNcast : ((m * ω.period.toNat : ℕ) : ℤ) = (m : ℤ) * ω.period := by
    push_cast
    rw [Int.toNat_of_nonneg hq0.le]
  have hWin := window_iff (q := ω.period) (off := t) (j0 := j0) (m := (m : ℤ)) (J := J) (a := a)
    hq0 (by omega) (by omega) (by omega) ha0 haq
  -- the left side
  have hL : ω.cell (J * ω.period + a) r ∈ ω.compose D \
        cornerLift ω D m t (leftStrip D j0 m) ↔
      ω.cell (J * ω.period + a) r ∈ ω.compose D ∧
        ¬ (ω.cell (J * ω.period + a) r ∈ ω.compose D ∧
          ω.cell (J * ω.period + a) (r + 1) ∉ ω.compose D ∧
          (if t ≤ a then (j0 ≤ J ∧ J < j0 + (m : ℤ))
            else (j0 ≤ J - 1 ∧ J - 1 < j0 + (m : ℤ)))) := by
    rw [Finset.mem_sdiff]
    unfold cornerLift
    rw [mem_windowRibbon, hminA, hNcast, ← hWin]
    have hcont : content (ω.cell (J * ω.period + a) r) =
        minContent ω.E + (J * ω.period + a) := content_cell _ _ _
    rw [hcont]
    constructor
    · rintro ⟨hx, hnA⟩
      refine ⟨hx, fun ⟨_, hq1, hwn⟩ => hnA ⟨by omega, by omega, ?_⟩⟩
      have := (eq_diagHi_iff hFs hx).mpr (by rwa [cell_add_e])
      rw [hcont] at this
      exact this
    · rintro ⟨hx, hnA⟩
      refine ⟨hx, fun ⟨h1, h2, h3⟩ => hnA ⟨hx, ?_, by omega⟩⟩
      have := (eq_diagHi_iff hFs hx).mp (by rw [hcont]; exact h3)
      rwa [cell_add_e] at this
  have e1 := mem_compose_cP h hc hph hD.1 hDne (J := J) (r := r) ha0 haq
  have e2 := mem_compose_cP h hc hph hD.1 hDne (J := J) (r := r + 1) ha0 haq
  rw [hL, e1, e2, mem_Fp h hc hph hw.isSkew_X ha0 haq, mem_rPieceO h ha0 haq,
    mem_lPieceU h hc hph ha0 haq, mem_lPieceS h hc hph ha0 haq]
  have eρ : r + 1 - J * ω.rowShift = r - J * ω.rowShift + 1 := by ring
  rw [eρ]
  have hDs := hD.1
  have hXc : ∀ j, j ∈ contents (D \ leftStrip D j0 m) ↔
      j ∈ contents D ∧ ¬ (j0 ≤ j ∧ j < j0 + (m : ℤ) ∧ diagLo D j = diagHi D j) :=
    fun j => contents_XL hw
  have hX : cellFormP ω.widthZ a (ω.lo a) (ω.hi a) (r - J * ω.rowShift)
      (if a < t then 1 else if a < s then 0 else -1) (if s ≤ a then 1 else 0)
      (J ∈ contents (D \ leftStrip D j0 m)) (J - 1 ∈ contents (D \ leftStrip D j0 m))
      (height (D \ leftStrip D j0 m) J) (height (D \ leftStrip D j0 m) (J - 1))
      (diagLo (D \ leftStrip D j0 m) J + 1 = diagLo (D \ leftStrip D j0 m) (J - 1)) ↔
      cellFormP ω.widthZ a (ω.lo a) (ω.hi a) (r - J * ω.rowShift)
      (if a < t then 1 else if a < s then 0 else -1) (if s ≤ a then 1 else 0)
      (J ∈ contents (D \ leftStrip D j0 m)) (J - 1 ∈ contents (D \ leftStrip D j0 m))
      (diagHi D J - diagLo D J + 1 - (if j0 ≤ J ∧ J < j0 + (m : ℤ) then 1 else 0))
      (diagHi D (J - 1) - diagLo D (J - 1) + 1 -
        (if j0 ≤ J - 1 ∧ J - 1 < j0 + (m : ℤ) then 1 else 0))
      (diagLo D J + (if j0 ≤ J ∧ J < j0 + (m : ℤ) then 1 else 0) + 1 =
        diagLo D (J - 1) + (if j0 ≤ J - 1 ∧ J - 1 < j0 + (m : ℤ) then 1 else 0)) := by
    refine cellFormP_congr (fun hJ => ?_) (fun hJ1 => ?_) (fun hJ hJ1 => ?_)
    · unfold height
      rw [diagHi_XL hw hJ, diagLo_XL hw hJ]
      ring
    · unfold height
      rw [diagHi_XL hw hJ1, diagLo_XL hw hJ1]
      ring
    · rw [diagLo_XL hw hJ, diagLo_XL hw hJ1]
  have hD1 : ∀ x : ℤ, x ∈ contents D ↔ minContent D ≤ x ∧ x ≤ maxContent D := hmem
  have hw0 : minContent D ≤ j0 := ((hmem j0).mp hw.start).1
  have hw1 : j0 + (m : ℤ) - 1 ≤ maxContent D := ((hmem _).mp hw.stop).2
  have hS : J = j0 → ¬ (minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D) ∨
      diagLo D (J - 1) - diagLo D J = 1 := by
    rintro rfl
    rcases hw.startEnd with h1 | h1
    · left; rwa [hmem] at h1
    · right; exact h1
  have hT : J = j0 + (m : ℤ) → ¬ (minContent D ≤ J ∧ J ≤ maxContent D) ∨
      diagLo D J = diagLo D (J - 1) := by
    rintro rfl
    rcases hw.stopEnd with h1 | h1
    · left; rwa [hmem] at h1
    · right; exact h1
  have key := left_arith ω.widthZ s t ω.period a (ω.lo a) (ω.hi a) (r - J * ω.rowShift) J j0
    (m : ℤ) (minContent D) (maxContent D) (diagLo D J) (diagHi D J) (diagLo D (J - 1))
    (diagHi D (J - 1)) (if j0 ≤ J ∧ J < j0 + (m : ℤ) then 1 else 0)
    (if j0 ≤ J - 1 ∧ J - 1 < j0 + (m : ℤ) then 1 else 0) (J ∈ contents D)
    (J - 1 ∈ contents D) (j0 ≤ J ∧ J < j0 + (m : ℤ)) (j0 ≤ J - 1 ∧ J - 1 < j0 + (m : ℤ))
    (diagLo D J = diagHi D J) (diagLo D (J - 1) = diagHi D (J - 1))
    (diagLo D J + 1 = diagLo D (J - 1))
    (ind_iff _) (ind_iff _)
    (hmem J) (hmem (J - 1)) Iff.rfl Iff.rfl Iff.rfl Iff.rfl Iff.rfl ha0 haq hq hts ht1 hs2
    (h.lo_le_hi ha0 (by omega))
    (fun hwa => W_row_bound h hc hph ha0 (by omega)) (by exact_mod_cast hw.pos) hw0 hw1
    (hhl J) (hhl (J - 1)) (hbl J) (hbh J) (hend J) (hend (J - 1)) hS hT
  rw [hX, hXc J, hXc (J - 1), mem_lLoneE hDs, mem_lLoneS hDs, sub_add_cancel, mem_rLone,
    mem_rLone]
  simp only [and_assoc] at key ⊢
  exact key




end Rem

end Corner

end Plan

end GluingCore
