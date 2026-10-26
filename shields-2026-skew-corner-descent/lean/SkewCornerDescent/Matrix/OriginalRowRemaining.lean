/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRowBlocks
import SkewCornerDescent.Matrix.OriginalEndpointProfiles
import SkewCornerDescent.Matrix.SelectedCoreSeries

/-!
# All-row source intervals have singleton unit blocks and empty selected cores

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Actual source index injection retains every unit occurrence. The all-row
geometric hypothesis supplies zero proper selected-row dimension, so both
complete selected-core polynomials are one. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- No two different full remaining occurrences belong to the same original
row block. The source's actual row-partition equivalence supplies the index
injection; a supplied unit-block proxy is not used. -/
theorem originalRemaining_label_injective_of_all_rows {n : ℕ} (P : Profile n)
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1) :
    Function.Injective (fun i : OriginalRemainingIndices (hD := hD) P =>
      interiorBlock P i.1.val) := by
  intro i j he
  have hi : originalRemovedRow (hD := hD) P i.1 i.2 =
      originalRemovedRow (hD := hD) P j.1 j.2 := by
    apply interiorBlock_injective_of_all_rows P hrows
    rw [originalRemovedRow_block, originalRemovedRow_block]
    exact he
  have hs : originalRowSplitEquiv (hD := hD) P (.inr i) =
      originalRowSplitEquiv (hD := hD) P (.inr j) := by
    rw [originalRowSplitEquiv_removed, originalRowSplitEquiv_removed, hi]
  exact Sum.inr_injective ((originalRowSplitEquiv (hD := hD) P).injective hs)

/-- A selected row has an empty proper minor, so both complete core profiles
are one, without a thick-core restriction. -/
theorem selected_core_polynomials_empty {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (hn : n = 0) :
    c.selectedCoreLeftPolynomial P hP = 1 ∧ c.selectedCoreRightPolynomial P hP = 1 := by
  subst n
  simp only [selectedCoreLeftPolynomial, selectedCoreRightPolynomial, ordinaryEndpointProfile,
    Finset.univ_eq_empty, Finset.sum_empty, sub_zero, and_self]

/-- On an all-row original inventory, each selected source occurrence supplies
both unit proper-core weights. The original geometric component hypothesis
produces the empty dimension. -/
theorem original_selected_core_polynomials_eq_one_of_all_rows {n : ℕ} (P : Profile n)
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    c.selectedCoreLeftPolynomial Q (originalSelectedProfile_schur P b).symm = 1 ∧
      c.selectedCoreRightPolynomial Q (originalSelectedProfile_schur P b).symm = 1 := by
  exact c.selected_core_polynomials_empty _ _ (interiorBlockLength_eq_zero_of_all_rows P hrows _)

end SkewCornerDescent.Matrix.SelectedCoordinate
