/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FullWindowRoot

/-!
# Proper nonline root at a nonribbon full-window boundary

Supports `shields-2026-skew-corner-descent.tex`, «The full-window boundary»
(`lem:boundary-full-window`).

The reconstructed band retains an actual southeast interior cell. Its two neighboring
cells have distinct rows and columns, proving that it is neither a row nor a column.
The inner and the line outer both have at least two cells.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- An actual interior cell witnesses proper size and failure of both line shapes. -/
theorem interior_nonempty_proper_cells {E : Diagram}
    (hE : (diagramInterior E).Nonempty) :
    2 ≤ E.card ∧ ∃ x ∈ E, ∃ y ∈ E, x.1 ≠ y.1 ∧ x.2 ≠ y.2 := by
  obtain ⟨x, hx⟩ := hE
  obtain ⟨hxE, hxeE⟩ := Finset.mem_filter.mp hx
  have hrow : x.1 ≠ (x + eCell).1 := by
    change x.1 ≠ x.1 + 1
    omega
  have hcol : x.2 ≠ (x + eCell).2 := by
    change x.2 ≠ x.2 + 1
    omega
  have hne : x ≠ x + eCell := fun h => hrow (congrArg Prod.fst h)
  have hsub : ({x, x + eCell} : Diagram) ⊆ E := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxE
    · exact hxeE
  refine ⟨?_, x, hxE, x + eCell, hxeE, hrow, hcol⟩
  simpa only [Finset.card_pair hne] using Finset.card_le_card hsub

/-- The ordinary nonribbon full-window boundary produces a proper actual nonline root. -/
theorem fullWindow_boundary_proper_root {D : Diagram} (hD : IsConnectedSkew D)
    (b : ℕ) (hb : 2 ≤ b) (δ : ℤ) (hδ : 0 < δ) (v : ℤ × ℤ)
    (hv : content v = δ) (hmin : minContent D = 0)
    (hmax : maxContent D = (b : ℤ) * δ - 1)
    (hwindow : upperFullWindow D b δ = translate v (lowerFullWindow D b δ))
    (hcut : diagLo D (δ - 1) = diagHi D (δ - 1))
    (hjoin : CellAdj (ne (firstContentBand D δ)) (sw (firstContentBand D δ) + v))
    (hinterior : (diagramInterior D).Nonempty) :
    ∃ E : Diagram, IsConnectedSkew E ∧ span E = δ.toNat ∧
      (emptyMarkH E).IsLegal ∧ 2 ≤ E.card ∧
      (∃ x ∈ E, ∃ y ∈ E, x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
      2 ≤ (horizontalRow b).card ∧ 2 ≤ (verticalColumn b).card ∧
      (D = (emptyMarkH E).compose (horizontalRow b) ∨
        D = (emptyMarkH E).compose (verticalColumn b)) := by
  obtain ⟨E, hE, hs, hlegal, hroot, hi⟩ :=
    fullWindow_boundary_root hD b hb δ hδ v hv hmin hmax hwindow hcut hjoin
  obtain ⟨hcard, hnonline⟩ := interior_nonempty_proper_cells (hi hinterior)
  exact ⟨E, hE, hs, hlegal, hcard, hnonline,
    by simpa only [horizontalRow_card] using hb,
    by simpa only [verticalColumn_card] using hb, hroot⟩

end SkewCornerDescent
