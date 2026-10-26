/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SeamCoefficients

/-!
# Genuine component inventory at a distinguished positive seam

The connected factor inventory used in `eq:cut-components` of
`shields-2026-skew-class-inflation.tex`.  Only nonempty canonical cut
blocks are enumerated; each carries its actual full determinant and row count.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase

/-- The actual connected components after all seams of the specified positive value are cut. -/
noncomputable def distinguishedCutInventory {n : ℕ} (P : Profile n) (z : ℕ+) :
    List (Σ k, BetaDiagram k) :=
  Finset.univ.toList.map (fun b : CutBlock P z =>
    ⟨blockSize P z b + 1, (cutComponent P z b).toBetaDiagram⟩)

/-- Every enumerated cut factor is a genuine nonempty connected full board. -/
theorem distinguishedCutInventory_connected {n : ℕ} (P : Profile n) (z : ℕ+)
    (X : Σ k, BetaDiagram k) (hX : X ∈ distinguishedCutInventory P z) : X.2.Connected := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hX
  exact cutComponent_connected P z b

/-- The enumerated full component functions multiply to the actual constant coefficient. -/
theorem distinguishedCutInventory_product {n : ℕ} (P : Profile n) (hP : Staircase.Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) :
    ((distinguishedCutInventory P z).map (fun X => X.2.schur)).prod =
      eraseGenerator z P.toBetaDiagram.schur := by
  rw [distinguished_cut_product P hP z hr]
  simp only [distinguishedCutInventory, List.map_map, Function.comp_def, Finset.prod_map_toList]

end SkewClassInflation
