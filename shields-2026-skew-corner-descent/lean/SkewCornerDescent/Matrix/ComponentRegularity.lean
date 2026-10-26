/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.SelectedCoordinate
import SkewGluing.SchurAssociates

/-!
# Regular complementary component factors

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Distinct connected component Schur
functions are regular at the selected prime, including ties in generator span.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A distinct actual connected Schur function is not divisible by the selected prime.
No strict span inequality is needed, so maximal-span ties are included. -/
theorem not_dvd_distinct_component {D E : Diagram}
    (hD : IsConnectedSkew D) (hE : IsConnectedSkew E)
    (hne : cellSchur D hD.1 ≠ cellSchur E hE.1) :
    ¬ cellSchur D hD.1 ∣ cellSchur E hE.1 := by
  intro hd
  exact hne (cellSchur_eq_of_associated hD.1 hE.1
    ((irreducible_cellSchur hD).associated_of_dvd (irreducible_cellSchur hE) hd))

/-- A finite product of distinct complementary connected factors is regular at the
selected prime. Repeated factors are retained as repeated indices, not deduplicated. -/
theorem not_dvd_complementary_product {ι : Type*} (s : Finset ι)
    {D : Diagram} (hD : IsConnectedSkew D) (E : ι → Diagram)
    (hE : ∀ i ∈ s, IsConnectedSkew (E i))
    (hne : ∀ i (hi : i ∈ s), cellSchur D hD.1 ≠ cellSchur (E i) (hE i hi).1) :
    ¬ cellSchur D hD.1 ∣ ∏ i ∈ s.attach, cellSchur (E i) (hE i i.property).1 := by
  have hp := (irreducible_cellSchur hD).prime
  rw [hp.dvd_finsetProd_iff]
  rintro ⟨i, _, hi⟩
  exact not_dvd_distinct_component hD (hE i i.property) (hne i i.property) hi

end SkewCornerDescent.Matrix
