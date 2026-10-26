-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/Ranges.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.Sep
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.Pieces

/-!
# The contents of the pieces of a case-(c) composite

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`).

For a legal mark of case (c), `W` and `\overline W` lie on the contents `[c₀, c₀ + w - 1]`,
`\overline O` on `[c₀ + w + 1, c₀ + q - 2]` (the diagonals `w` and `q - 1` of `E` have a single
cell, `lem:gluing-local` (1)), and every cell of `X ∘_ω E` lies in the block
`[c₀ + j q, c₀ + j q + q + w - 1]` of a diagonal `j` of `X` (`content_compose_block`).

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner}

/-- All cells of `S` have content in `[lo, hi]`. -/
def CIn (S : Diagram) (lo hi : ℤ) : Prop := ∀ y ∈ S, lo ≤ content y ∧ content y ≤ hi

theorem sep_of_cin {A B : Diagram} {l1 h1 l2 h2 : ℤ} (hA : CIn A l1 h1) (hB : CIn B l2 h2)
    (h : h1 + 2 ≤ l2 ∨ h2 + 2 ≤ l1) : Sep A B := by
  intro x hx y hy
  have := hA x hx
  have := hB y hy
  rcases h with h | h
  · rw [abs_of_nonpos (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]; omega

theorem cin_translate_smul {S : Diagram} {lo hi : ℤ} (h : CIn S lo hi) (j : ℤ) :
    CIn (translate (j • ω.v) S) (lo + j * ω.period) (hi + j * ω.period) := by
  intro x hx
  rw [mem_translate] at hx
  have := h _ hx
  have e : content x = content (x - j • ω.v) + j * ω.period := by
    have hp : content ω.v = ω.period := rfl
    rw [content_sub, content_smul, hp]
    ring
  omega

theorem cin_hatMiddleFin (h : ω.IsLegalNonempty) :
    CIn (hatMiddleFin ω) (minContent ω.E + ω.widthZ + 1) (minContent ω.E + ω.period - 2) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  intro y hy
  obtain ⟨a, r, rfl⟩ := ω.exists_cell y
  rw [mem_hatMiddleFin_cell h] at hy
  rw [content_cell]
  have h1 := h.lo_w_eq_hi_w
  have h2 := h.lo_pred_period_eq_hi
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have : a ≠ ω.widthZ := by
    rintro rfl; omega
  have : a ≠ ω.period - 1 := by
    rintro rfl; omega
  omega

theorem cin_W (h : ω.IsLegalNonempty) :
    CIn ω.W (minContent ω.E) (minContent ω.E + ω.widthZ - 1) := by
  intro y hy
  have hb := (h.nonemptyMark.content_bounds h.isConnectedSkew_E).1 y hy
  unfold MarkedInner.widthZ
  omega

theorem cin_hatMarkFin (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) :
    CIn (hatMarkFin ω) (minContent ω.E) (minContent ω.E + ω.widthZ - 1) := by
  intro y hy
  obtain ⟨a, r, rfl⟩ := ω.exists_cell y
  rw [mem_hatMarkFin_cell h hc hph] at hy
  rw [content_cell]
  omega

theorem content_compose_block (h : ω.IsLegalNonempty) {X : Diagram} (hXne : X.Nonempty)
    {x : ℤ × ℤ} (hx : x ∈ ω.compose X) :
    ∃ j ∈ contents X, minContent ω.E + j * ω.period ≤ content x ∧
      content x ≤ minContent ω.E + j * ω.period + ω.period + ω.widthZ - 1 := by
  have hb := (h.nonemptyMark.content_bounds h.isConnectedSkew_E).2
  have hUE := h.nonemptyMark.2.2.2.1
  have hs : content ω.supplementalShift = 0 := content_supplementalShift ω
  have hwz : ω.widthZ = (ω.width : ℤ) := rfl
  rw [mem_compose hXne] at hx
  rcases hx with ⟨d, hd, hx⟩ | ⟨d, hd, -, hx⟩
  · refine ⟨content d, content_mem_contents hd, ?_⟩
    rw [mem_translate] at hx
    have := hb _ hx
    have e := content_sub x (ω.origin X d)
    rw [content_origin] at e
    omega
  · refine ⟨content d, content_mem_contents hd, ?_⟩
    rw [mem_translate] at hx
    have := hb _ (hUE hx)
    have e := content_sub x (ω.origin X d + ω.supplementalShift)
    rw [content_add, content_origin, hs] at e
    omega

theorem mul_step {q a b : ℤ} (hq : 0 < q) (h : a < b) : a * q + q ≤ b * q := by
  nlinarith

theorem far_facts {q : ℤ} (hq : 0 < q) (j j' : ℤ) :
    (j' < j → j' * q + q ≤ j * q) ∧ (j < j' → j * q + q ≤ j' * q) ∧
    (j' + 1 < j → j' * q + 2 * q ≤ j * q) ∧ (j + 1 < j' → j * q + 2 * q ≤ j' * q) := by
  refine ⟨fun h => mul_step hq h, fun h => mul_step hq h, fun h => ?_, fun h => ?_⟩
  · have := mul_step hq h
    nlinarith
  · have := mul_step hq h
    nlinarith

theorem far_facts' {q : ℤ} (hq : 0 < q) (j j' : ℤ) :
    (j' < j → j' * q + q ≤ j * q) ∧ (j < j' → j * q + q ≤ j' * q) := by
  constructor <;> intro h <;> nlinarith

/-- Pieces on the blocks `j` and `j'` of the contents: separated when their offsets within the
blocks are. -/
theorem sep_blocks {q : ℤ} (hq : 0 < q) {c0 α β α' β' j j' lo hi lo' hi' : ℤ} {S S' : Diagram}
    (hS : CIn S lo hi) (hS' : CIn S' lo' hi')
    (e1 : lo = c0 + α + j * q) (e2 : hi = c0 + β + j * q) (e3 : lo' = c0 + α' + j' * q)
    (e4 : hi' = c0 + β' + j' * q)
    (h1 : β + 2 ≤ α' + q) (h2 : β' + 2 ≤ α + q)
    (h3 : j = j' → β + 2 ≤ α' ∨ β' + 2 ≤ α) : Sep S S' := by
  obtain ⟨f1, f2⟩ := far_facts' hq j j'
  refine sep_of_cin hS hS' ?_
  rcases lt_trichotomy j j' with hl | he | hg
  · have := f2 hl; left; omega
  · subst he
    rcases h3 rfl with h | h
    · left; omega
    · right; omega
  · have := f1 hg; right; omega

end Rem

end Corner

end Plan

end GluingCore
