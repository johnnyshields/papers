/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.UniversalOmegaComponents
import SkewCornerDescent.Matrix.PrimeOrder

/-!
# Full corner inventory under whole-diagram transposition

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Southeast erosion, every actual corner component, its span, the complete
cofactor power, and the selected prime multiplicity all transport together.
No column component is replaced by an isolated row surrogate. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- Southeast erosion commutes with whole-diagram transposition. -/
theorem diagramInterior_transpose (D : Diagram) :
    diagramInterior (transpose D) = transpose (diagramInterior D) := by
  ext x
  simp only [diagramInterior, Finset.mem_filter, mem_transpose]
  change (x.swap ∈ D ∧ (x + (1, 1)).swap ∈ D) ↔
    (x.swap ∈ D ∧ x.swap + (1, 1) ∈ D)
  rfl

/-- Every actual all-column corner inventory becomes an actual all-row
corner inventory when the whole source is transposed. -/
theorem all_column_corner_transpose_rows (D : Diagram)
    (hc : ∀ C ∈ edgeComponents (diagramInterior D), (C.image Prod.snd).card = 1) :
    ∀ C ∈ edgeComponents (diagramInterior (transpose D)), (C.image Prod.fst).card = 1 := by
  intro C hC
  rw [diagramInterior_transpose, edgeComponents_transpose] at hC
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
  have h := hc B hB
  simpa only [transpose, Finset.image_image, Function.comp_def, Prod.fst_swap] using h

/-- The complete maximal-component span bound transports to all transposed
components, not only to the selected component. -/
theorem corner_span_bound_transpose (D : Diagram) (N : ℕ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior D), span C ≤ N) :
    ∀ C ∈ edgeComponents (diagramInterior (transpose D)), span C ≤ N := by
  intro C hC
  rw [diagramInterior_transpose, edgeComponents_transpose] at hC
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
  rw [span_transpose]
  exact hmax B hB

/-- Prime order is preserved by the existing polynomial Schur involution,
including zero inputs under the same natural-valued convention. -/
theorem primeOrder_schurInvolution (f g : Lambda) :
    Matrix.primeOrder (schurInvolution f) (schurInvolution g) = Matrix.primeOrder f g := by
  unfold Matrix.primeOrder
  have h := emultiplicity_map_eq schurInvolutionEquiv (a := f) (b := g)
  exact congrArg ENat.toNat h

/-- A literal full corner-cofactor power transports to the full transposed
source with the same exponent and no loss of component multiplicity. -/
theorem corner_power_transpose (D : Diagram) (hs : IsSkew D) (Λ : Lambda) (b : ℕ)
    (h : cellSchur (diagramInterior D) hs.interior = Λ ^ b) :
    cellSchur (diagramInterior (transpose D)) (isSkew_transpose hs).interior =
      schurInvolution Λ ^ b := by
  have ht := congrArg schurInvolution h
  rw [schurInvolution_skew_cellSchur, map_pow] at ht
  have he := diagramInterior_transpose D
  rw [cellSchur_congr he _ (isSkew_transpose hs.interior)]
  exact ht

end SkewCornerDescent
