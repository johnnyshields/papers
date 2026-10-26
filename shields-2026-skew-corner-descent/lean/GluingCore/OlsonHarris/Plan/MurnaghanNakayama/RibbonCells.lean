-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/RibbonCells.lean
import GluingCore.OlsonHarris.Plan.Defs
import GluingCore.CellSchurTableau

/-!
# Ribbons among skew diagrams: a recognition criterion

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the vocabulary of thesis §5.1.3
(`OlsonHarris2024HopfApplications`) on which the Murnaghan–Nakayama rule is read.

* `mem_skewDiagram_iff`: the cells of `skewDiagram ν μ` by row lengths.
* `isConnectedSkew_of_injOn_interval`: a skew diagram with one cell per occupied diagonal and
  contents forming an interval is connected (hence a ribbon).
* `isRibbon_injOn_content`, `isRibbon_contents_eq`: the converse, a ribbon has one cell per
  diagonal and its contents form an interval.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace MN

/-- A ribbon has at most one cell on every diagonal. -/
theorem isRibbon_injOn_content {Y : Diagram} (h : IsRibbon Y) :
    Set.InjOn content (Y : Set (ℤ × ℤ)) := by
  have hcard : (Y.image content).card = Y.card := by
    have := h.2
    unfold span contents at this
    omega
  exact Finset.card_image_iff.mp hcard

/-- The contents of a ribbon fill an interval. -/
theorem isRibbon_contents_eq {Y : Diagram} (h : IsRibbon Y) :
    contents Y = Finset.Icc (minContent Y) (maxContent Y) :=
  (isConnectedSkew_iff_diagonal.mp h.1).contents_eq

theorem mem_skewDiagram_iff {lam mu : YoungDiagram} {a b : ℤ} :
    (a, b) ∈ skewDiagram lam mu ↔
      ∃ i j : ℕ, a = i ∧ b = j ∧ mu.rowLen i ≤ j ∧ j < lam.rowLen i := by
  constructor
  · intro h
    obtain ⟨i, j, h'⟩ := nat_cell_of_mem_skewDiagram h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    rw [mem_skewDiagram_nat, Shields.mem_skewCells, YoungDiagram.mem_iff_lt_rowLen,
      YoungDiagram.mem_iff_lt_rowLen] at h
    exact ⟨i, j, rfl, rfl, by omega, h.1⟩
  · rintro ⟨i, j, rfl, rfl, h1, h2⟩
    rw [mem_skewDiagram_nat, Shields.mem_skewCells, YoungDiagram.mem_iff_lt_rowLen,
      YoungDiagram.mem_iff_lt_rowLen]
    omega

theorem mem_skewDiagram_nat_iff {lam mu : YoungDiagram} (i j : ℕ) :
    ((i : ℤ), (j : ℤ)) ∈ skewDiagram lam mu ↔ mu.rowLen i ≤ j ∧ j < lam.rowLen i := by
  rw [mem_skewDiagram_iff]
  constructor
  · rintro ⟨i', j', h1, h2, h3, h4⟩
    obtain rfl : i = i' := by exact_mod_cast h1
    obtain rfl : j = j' := by exact_mod_cast h2
    exact ⟨h3, h4⟩
  · rintro ⟨h3, h4⟩
    exact ⟨i, j, rfl, rfl, h3, h4⟩

/-- On a diagram with one cell per diagonal the diagonal `k` has a unique row. -/
theorem exists_unique_row_of_injOn {D : Diagram} (hinj : Set.InjOn content (D : Set (ℤ × ℤ)))
    {k : ℤ} (hk : k ∈ contents D) : ∃ r, (r, r + k) ∈ D ∧ ∀ s, (s, s + k) ∈ D → s = r := by
  obtain ⟨r, hr⟩ := mem_contents_iff.mp hk
  refine ⟨r, hr, fun s hs => ?_⟩
  have := hinj (Finset.mem_coe.mpr hs) (Finset.mem_coe.mpr hr) (by simp [content])
  simpa using congrArg Prod.fst this

/-- **Recognition of ribbons.**  A skew diagram with at most one cell on every diagonal and
whose contents fill an interval is connected. -/
theorem isConnectedSkew_of_injOn_interval {D : Diagram} (hs : IsSkew D) (hne : D.Nonempty)
    (hinj : Set.InjOn content (D : Set (ℤ × ℤ)))
    (hint : ∀ x ∈ D, ∀ y ∈ D, ∀ k ∈ Finset.Icc (content x) (content y), k ∈ contents D) :
    IsConnectedSkew D := by
  rw [isConnectedSkew_iff_diagonal]
  have hdiag : ∀ k ∈ contents D, diagLo D k = diagHi D k := by
    intro k hk
    obtain ⟨r, hr, hu⟩ := exists_unique_row_of_injOn hinj hk
    rw [diagLo_eq_of hr (fun i hi => (hu i hi).ge), diagHi_eq_of hr (fun i hi => (hu i hi).le)]
  refine ⟨hne, hint, ?_, ?_, ?_⟩
  · intro x hx y hy hxy i hi
    have : x = y := hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
    subst this
    have hi' : i = x.1 := le_antisymm (Finset.mem_Icc.mp hi).2 (Finset.mem_Icc.mp hi).1
    subst hi'
    simpa [content] using hx
  · intro k hk hk1
    obtain ⟨r, hr, hu⟩ := exists_unique_row_of_injOn hinj hk
    obtain ⟨r', hr', hu'⟩ := exists_unique_row_of_injOn hinj hk1
    have hlo : diagLo D k = r := diagLo_eq_of hr (fun i hi => (hu i hi).ge)
    have hlo' : diagLo D (k - 1) = r' := diagLo_eq_of hr' (fun i hi => (hu' i hi).ge)
    have hhi : diagHi D k = r := diagHi_eq_of hr (fun i hi => (hu i hi).le)
    have hhi' : diagHi D (k - 1) = r' := diagHi_eq_of hr' (fun i hi => (hu' i hi).le)
    have key : r' - r = 0 ∨ r' - r = 1 := by
      by_contra hcon
      push Not at hcon
      rcases lt_or_ge r r' with h | h
      · -- `r + 2 ≤ r'`: the cell `(r' - 1, r' + k - 2)` is a second cell of diagonal `k - 1`
        have hr2 : r + 2 ≤ r' := by omega
        have hm : (r' - 1, r' - 1 + (k - 1)) ∈ D :=
          hs.mem hr hr' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have := hu' _ hm
        omega
      · -- `r' < r`: the cell `(r', r' + k)` is a second cell of diagonal `k`
        have hr2 : r' < r := by omega
        have hm : (r', r' + k) ∈ D :=
          hs.mem hr' hr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have := hu _ hm
        omega
    simp only [bitA, bitB, hlo, hlo', hhi, hhi', Finset.mem_insert, Finset.mem_singleton]
    exact ⟨key, key⟩
  · intro k hk _
    exact hdiag k hk

/-- A skew diagram with one cell per diagonal and interval of contents is a ribbon. -/
theorem isRibbon_of_injOn_interval {D : Diagram} (hs : IsSkew D) (hne : D.Nonempty)
    (hinj : Set.InjOn content (D : Set (ℤ × ℤ)))
    (hint : ∀ x ∈ D, ∀ y ∈ D, ∀ k ∈ Finset.Icc (content x) (content y), k ∈ contents D) :
    IsRibbon D := by
  refine ⟨isConnectedSkew_of_injOn_interval hs hne hinj hint, ?_⟩
  unfold span contents
  exact (Finset.card_image_of_injOn hinj).symm

end MN

end Plan

end GluingCore
