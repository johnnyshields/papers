-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/Young.lean
import GluingCore.OlsonHarris.Plan.MurnaghanNakayama.RowMoveDet

/-!
# Ribbons removable from a skew diagram of Young diagrams

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`).

For `X = λ / μ` the ribbons `Y` that are downsets of `X` are the differences `ν / μ` of Young
diagrams `μ ≤ ν ≤ λ` (`exists_young_of_isDownsetIn`), and then `X \ Y = λ / ν`
(`skewDiagram_sdiff`).

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace MN

theorem le_of_rowLen_le {a b : YoungDiagram} (h : ∀ i, a.rowLen i ≤ b.rowLen i) : a ≤ b := by
  intro c hc
  obtain ⟨i, x⟩ := c
  rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
  have := h i
  omega

theorem rowLen_le_of_le {a b : YoungDiagram} (h : a ≤ b) (i : ℕ) : a.rowLen i ≤ b.rowLen i := by
  by_contra hcon
  push Not at hcon
  have h1 : (i, b.rowLen i) ∈ a := YoungDiagram.mem_iff_lt_rowLen.mpr hcon
  have h2 := h h1
  rw [YoungDiagram.mem_iff_lt_rowLen] at h2
  omega

theorem skewDiagram_sdiff {lam nu mu : YoungDiagram} (h1 : mu ≤ nu) :
    skewDiagram lam mu \ skewDiagram nu mu = skewDiagram lam nu := by
  ext ⟨a, b⟩
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨h2, h3⟩
    obtain ⟨i, x, rfl, rfl, h4, h5⟩ := mem_skewDiagram_iff.mp h2
    refine mem_skewDiagram_iff.mpr ⟨i, x, rfl, rfl, ?_, h5⟩
    by_contra hcon
    exact h3 (mem_skewDiagram_iff.mpr ⟨i, x, rfl, rfl, h4, by omega⟩)
  · intro h2
    obtain ⟨i, x, rfl, rfl, h4, h5⟩ := mem_skewDiagram_iff.mp h2
    have := rowLen_le_of_le h1 i
    refine ⟨mem_skewDiagram_iff.mpr ⟨i, x, rfl, rfl, by omega, h5⟩, fun h3 => ?_⟩
    obtain ⟨i', x', h6, h7, h8, h9⟩ := mem_skewDiagram_iff.mp h3
    have e1 : i = i' := by exact_mod_cast h6
    have e2 : x = x' := by exact_mod_cast h7
    subst e1 e2
    omega

theorem skewDiagram_subset {lam nu mu : YoungDiagram} (h : nu ≤ lam) :
    skewDiagram nu mu ⊆ skewDiagram lam mu := by
  rintro ⟨a, b⟩ hab
  obtain ⟨i, x, rfl, rfl, h4, h5⟩ := mem_skewDiagram_iff.mp hab
  have := rowLen_le_of_le h i
  exact mem_skewDiagram_iff.mpr ⟨i, x, rfl, rfl, h4, by omega⟩

theorem isDownsetIn_skewDiagram {lam nu mu : YoungDiagram} (h : nu ≤ lam) :
    IsDownsetIn (skewDiagram lam mu) (skewDiagram nu mu) := by
  refine ⟨skewDiagram_subset h, ?_⟩
  rintro ⟨a, b⟩ hx ⟨a', b'⟩ hy h1 h2
  obtain ⟨i, x, rfl, rfl, h4, h5⟩ := mem_skewDiagram_iff.mp hx
  obtain ⟨i', x', rfl, rfl, h6, h7⟩ := mem_skewDiagram_iff.mp hy
  have h1' : (i : ℤ) ≤ i' := h1
  have h2' : (x : ℤ) ≤ x' := h2
  have hii : i ≤ i' := by exact_mod_cast h1'
  have hxx : x ≤ x' := by exact_mod_cast h2'
  have := nu.rowLen_anti i i' hii
  exact mem_skewDiagram_iff.mpr ⟨i, x, rfl, rfl, h4, by omega⟩

/-- A downset `Y` of `λ / μ` is the difference `ν / μ` for a Young diagram `ν` with
`μ ≤ ν ≤ λ`. -/
theorem exists_young_of_isDownsetIn {lam mu : YoungDiagram} {Y : Diagram} (hmu : mu ≤ lam)
    (hY : IsDownsetIn (skewDiagram lam mu) Y) :
    ∃ nu : YoungDiagram, mu ≤ nu ∧ nu ≤ lam ∧ Y = skewDiagram nu mu := by
  classical
  have hmem : ∀ i x : ℕ, ((i : ℤ), (x : ℤ)) ∈ Y →
      mu.rowLen i ≤ x ∧ x < lam.rowLen i := fun i x h =>
    (mem_skewDiagram_nat_iff i x).mp (hY.1 h)
  let N : Finset (ℕ × ℕ) := mu.cells ∪ (lam.cells.filter fun p => ((p.1 : ℤ), (p.2 : ℤ)) ∈ Y)
  have hN : ∀ p : ℕ × ℕ, p ∈ N ↔ p ∈ mu ∨ ((p.1 : ℤ), (p.2 : ℤ)) ∈ Y := by
    intro p
    simp only [N, Finset.mem_union, Finset.mem_filter, YoungDiagram.mem_cells]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨?_, h⟩
        obtain ⟨i, x⟩ := p
        rw [YoungDiagram.mem_iff_lt_rowLen]
        exact (hmem i x h).2
  let nu : YoungDiagram :=
    { cells := N
      isLowerSet := by
        intro q p hpq hq
        rw [Finset.mem_coe, hN] at hq ⊢
        rcases hq with hq | hq
        · exact Or.inl (mu.isLowerSet hpq hq)
        · obtain ⟨p1, p2⟩ := p
          obtain ⟨i', x'⟩ := q
          obtain ⟨hi, hx⟩ := Prod.mk_le_mk.mp hpq
          by_cases hpm : (p1, p2) ∈ mu
          · exact Or.inl hpm
          · right
            obtain ⟨hq1, hq2⟩ := hmem i' x' hq
            have hpl : (p1, p2) ∈ lam := by
              refine lam.isLowerSet hpq ?_
              rw [Finset.mem_coe, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
              exact hq2
            have hpX : ((p1 : ℤ), (p2 : ℤ)) ∈ skewDiagram lam mu :=
              (mem_skewDiagram_nat_iff p1 p2).mpr ⟨by
                rw [YoungDiagram.mem_iff_lt_rowLen] at hpm; omega,
                by rw [YoungDiagram.mem_iff_lt_rowLen] at hpl; exact hpl⟩
            have hi' : (p1 : ℤ) ≤ i' := by exact_mod_cast hi
            have hx' : (p2 : ℤ) ≤ x' := by exact_mod_cast hx
            exact hY.2 _ hpX _ hq hi' hx' }
  have hnu : ∀ i x : ℕ, (i, x) ∈ nu ↔ (i, x) ∈ mu ∨ ((i : ℤ), (x : ℤ)) ∈ Y := fun i x => hN (i, x)
  have hmunu : mu ≤ nu := fun p hp => (hN p).mpr (Or.inl hp)
  refine ⟨nu, hmunu, ?_, ?_⟩
  · rintro ⟨i, x⟩ hp
    rcases (hnu i x).mp hp with h | h
    · exact hmu h
    · rw [YoungDiagram.mem_iff_lt_rowLen]
      exact (hmem i x h).2
  · ext ⟨a, b⟩
    constructor
    · intro hab
      obtain ⟨i, x, rfl, rfl, h4, h5⟩ := mem_skewDiagram_iff.mp (hY.1 hab)
      refine mem_skewDiagram_iff.mpr ⟨i, x, rfl, rfl, h4, ?_⟩
      have := (hnu i x).mpr (Or.inr hab)
      rwa [YoungDiagram.mem_iff_lt_rowLen] at this
    · intro hab
      obtain ⟨i, x, rfl, rfl, h4, h5⟩ := mem_skewDiagram_iff.mp hab
      have h6 : (i, x) ∈ nu := YoungDiagram.mem_iff_lt_rowLen.mpr h5
      rcases (hnu i x).mp h6 with h | h
      · rw [YoungDiagram.mem_iff_lt_rowLen] at h
        omega
      · exact h

end MN

end Plan

end GluingCore
