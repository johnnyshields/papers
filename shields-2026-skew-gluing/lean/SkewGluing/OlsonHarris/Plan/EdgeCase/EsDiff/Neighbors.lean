import SkewGluing.OlsonHarris.Plan.EdgeCase.EsDiff.LocalEmpty

/-!
# The copies at the cells around a removable cell

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): the bookkeeping behind thesis
Lemma 5.4.3 (`OlsonHarris2024HopfApplications`).

For a mark of case (a) the copy at the cell `d` is `E + org d` with
`org d = c(d) v + d₁ e`.  For a cell `b` of a skew diagram `X` with no cell of `X` to its northwest,
every other cell `d` of `X` whose copy can meet or touch the copy at `b` (that is, with
`|c(d) - c(b)| ≤ 1`) lies to the east of `b`, to the south of `b`, or further southeast, in which
case `b` has neighbors to the east, south and southeast (`nbr_cases`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewGluing

namespace Plan

namespace EsDiff

open scoped Classical

open SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- The origin of the copy at the cell `d`, for a mark of case (a): `c(d) v + d₁ e`. -/
def org (ω : MarkedInner) (d : ℤ × ℤ) : ℤ × ℤ := content d • ω.v + d.1 • eCell

/-- The displacement from the copy at `b` to the copy at `d`. -/
def sigma (ω : MarkedInner) (b d : ℤ × ℤ) : ℤ × ℤ :=
  (content d - content b) • ω.v + (d.1 - b.1) • eCell

theorem origin_eq (hc : ω.case = .a) (D : Diagram) (d : ℤ × ℤ) : ω.origin D d = org ω d := by
  simp only [MarkedInner.origin, org, hc]

theorem org_eq (ω : MarkedInner) (b d : ℤ × ℤ) : org ω d = org ω b + sigma ω b d := by
  simp only [org, sigma, sub_smul]
  abel

theorem content_sigma (ω : MarkedInner) (b d : ℤ × ℤ) :
    content (sigma ω b d) = (content d - content b) * ω.period := by
  have h1 : content ω.v = ω.period := rfl
  have h2 : ∀ s : ℤ, content (s • eCell) = 0 := by intro s; simp [content, eCell]
  simp only [sigma, content_add, content_smul, h1, h2, add_zero]

theorem mem_translate_org {ω : MarkedInner} {b d z : ℤ × ℤ} :
    z ∈ translate (org ω d) ω.E ↔ (z - org ω b) - sigma ω b d ∈ ω.E := by
  rw [mem_translate, org_eq ω b d, sub_add_eq_sub_sub]

theorem content_org (ω : MarkedInner) (d : ℤ × ℤ) :
    content (org ω d) = content d * ω.period := by
  have h1 : content ω.v = ω.period := rfl
  have h2 : ∀ s : ℤ, content (s • eCell) = 0 := by intro s; simp [content, eCell]
  simp only [org, content_add, content_smul, h1, h2, add_zero]

/-- Cells of the copies at `b` and `d` whose contents differ by at most one force the contents of
`b` and `d` to differ by at most one. -/
theorem content_diff_le_one (hω : ω.IsLegal) {b d z z' : ℤ × ℤ}
    (hz : z ∈ translate (org ω b) ω.E) (hz' : z' ∈ translate (org ω d) ω.E)
    (h1 : content z ≤ content z' + 1) (h2 : content z' ≤ content z + 1) :
    content d ≤ content b + 1 ∧ content b ≤ content d + 1 := by
  have hq : 0 < ω.period := hω.period_pos
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  have c1 := hω.copy_content (mem_translate.mp hz)
  have c2 := hω.copy_content (mem_translate.mp hz')
  rw [content_sub, content_org] at c1 c2
  constructor
  · by_contra hcon
    have : (content b + 2) * ω.period ≤ content d * ω.period :=
      mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith
  · by_contra hcon
    have : (content d + 2) * ω.period ≤ content b * ω.period :=
      mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith

/-- The cells around a cell `b` of a skew diagram with no cell to its northwest. -/
theorem nbr_cases {X : Diagram} (hX : IsSkew X) {b : ℤ × ℤ} (hb : b ∈ X)
    (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) {d : ℤ × ℤ} (hd : d ∈ X) (hdb : d ≠ b) :
    d = (b.1, b.2 + 1) ∨ d = (b.1 + 1, b.2) ∨ content d + 2 ≤ content b ∨
      content b + 2 ≤ content d ∨
      ((b.1, b.2 + 1) ∈ X ∧ (b.1 + 1, b.2) ∈ X ∧ (b.1 + 1, b.2 + 1) ∈ X ∧
        ((content d = content b + 1 ∧ b.1 ≤ d.1) ∨ (content d = content b ∧ b.1 + 1 ≤ d.1) ∨
          (content d = content b - 1 ∧ b.1 + 1 ≤ d.1))) := by
  obtain ⟨d1, d2⟩ := d
  obtain ⟨b1, b2⟩ := b
  simp only [content] at *
  by_cases hfar : d2 - d1 + 2 ≤ b2 - b1 ∨ b2 - b1 + 2 ≤ d2 - d1
  · omega
  have hle1 : b1 ≤ d1 := by
    by_contra hlt
    have := hmin (d1, d2) hd (by simp only; omega) (by simp only; omega)
    simp only [Prod.mk.injEq] at this
    omega
  have hle2 : b2 ≤ d2 := by
    by_contra hlt
    have := hmin (d1, d2) hd (by simp only; omega) (by simp only; omega)
    simp only [Prod.mk.injEq] at this
    omega
  by_cases e1 : d1 = b1 ∧ d2 = b2 + 1
  · left; simp only [Prod.mk.injEq]; exact e1
  by_cases e2 : d1 = b1 + 1 ∧ d2 = b2
  · right; left; simp only [Prod.mk.injEq]; exact e2
  right; right; right; right
  have hne : d1 ≠ b1 ∨ d2 ≠ b2 := by
    by_contra hcon
    push Not at hcon
    exact hdb (by rw [hcon.1, hcon.2])
  have hd1 : b1 + 1 ≤ d1 ∨ (d1 = b1 ∧ b2 + 2 ≤ d2) := by omega
  have hd2 : b2 + 1 ≤ d2 := by omega
  refine ⟨?_, ?_, ?_, by omega⟩
  · exact hX.mem (a := b1) (b := b2) (c := d1) (d := d2) hb hd hle1 hle2 le_rfl (by omega)
      (by omega) (by omega)
  · exact hX.mem (a := b1) (b := b2) (c := d1) (d := d2) hb hd hle1 hle2 (by omega) (by omega)
      le_rfl (by omega)
  · exact hX.mem (a := b1) (b := b2) (c := d1) (d := d2) hb hd hle1 hle2 (by omega) (by omega)
      (by omega) (by omega)

end EsDiff

end Plan

end SkewGluing
