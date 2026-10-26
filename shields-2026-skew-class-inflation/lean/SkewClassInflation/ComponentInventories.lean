/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorMatching
import SkewClassInflation.ZeroSeamCoefficients

/-!
# Recovery of actual cut-component functions and sizes

Formalizes the factor-matching steps in `eq:cut-components` and
`thm:two-row-thin-class` of `shields-2026-skew-class-inflation.tex`.
All factors are the actual connected geometric cut components, with their
row counts recovered from the polynomial.  Multiplicities are retained.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Gluing SkewJacobiNegative.Staircase
open scoped BigOperators

/-- The finite geometric inventory of all components after cutting a positive seam value. -/
noncomputable def positiveCutInventory {n : ℕ} (P : Profile n) (z : ℕ+) :
    List (Σ k, BetaDiagram k) :=
  Finset.univ.toList.map (fun b : CutBlock P z =>
    ⟨blockSize P z b + 1, (cutComponent P z b).toBetaDiagram⟩)

/-- The finite geometric inventory after cutting every original zero seam. -/
noncomputable def zeroCutInventory {n : ℕ} (P : Profile n) : List (Σ k, BetaDiagram k) :=
  Finset.univ.toList.map (fun b : CutBlock (P.lift rowShiftTwoOne) 1 =>
    ⟨blockSize (P.lift rowShiftTwoOne) 1 b + 1, (zeroCutComponent P b).toBetaDiagram⟩)

/-- Every listed positive-seam component is genuinely connected. -/
theorem positiveCutInventory_connected {n : ℕ} (P : Profile n) (z : ℕ+)
    (X : Σ k, BetaDiagram k) (hX : X ∈ positiveCutInventory P z) : X.2.Connected := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hX
  exact (cutComponent P z b).toBetaDiagram_connected

/-- Every listed zero-seam component is genuinely connected. -/
theorem zeroCutInventory_connected {n : ℕ} (P : Profile n)
    (X : Σ k, BetaDiagram k) (hX : X ∈ zeroCutInventory P) : X.2.Connected := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hX
  exact (zeroCutComponent P b).toBetaDiagram_connected

/-- The inventory's polynomial product is the actual constant distinguished-seam coefficient. -/
theorem positiveCutInventory_product {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) :
    ((positiveCutInventory P z).map (fun X => X.2.schur)).prod =
      eraseGenerator z P.toBetaDiagram.schur := by
  rw [distinguished_cut_product P hP z hr]
  simp [positiveCutInventory, List.map_map]

/-- The zero-cut inventory's polynomial product is the actual retained-unit constant coefficient. -/
theorem zeroCutInventory_product {n : ℕ} (P : Profile n) (hP : Thick P) :
    ((zeroCutInventory P).map (fun X => X.2.schur)).prod = (unitSchur P).coeff 0 := by
  rw [zero_seam_constant_coefficient P hP]
  simp [zeroCutInventory, List.map_map]

/-- Equal full polynomials recover the positive-seam component functions and row counts together. -/
theorem positive_cut_inventory_matching {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : Thick P) (hQ : Thick Q) (z : ℕ+)
    (hrP : ∀ i, z.val < P.r i) (hrQ : ∀ i, z.val < Q.r i)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    Multiset.Rel (fun X Y : Σ k, BetaDiagram k => X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (positiveCutInventory P z : Multiset _) (positiveCutInventory Q z : Multiset _) := by
  apply BetaDiagram.product_component_matching _ _
    (positiveCutInventory_connected P z) (positiveCutInventory_connected Q z)
  rw [positiveCutInventory_product P hP z hrP, positiveCutInventory_product Q hQ z hrQ, he]

/-- Equal full polynomials recover all zero-seam component functions and sizes with multiplicity. -/
theorem zero_cut_inventory_matching {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : Thick P) (hQ : Thick Q)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    Multiset.Rel (fun X Y : Σ k, BetaDiagram k => X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (zeroCutInventory P : Multiset _) (zeroCutInventory Q : Multiset _) := by
  have hn := Nat.succ.inj (P.toBetaDiagram.row_count_of_schur_eq Q.toBetaDiagram he)
  subst m
  apply BetaDiagram.product_component_matching _ _
    (zeroCutInventory_connected P) (zeroCutInventory_connected Q)
  rw [zeroCutInventory_product P hP, zeroCutInventory_product Q hQ,
    unitSchur_eq_of_schur_eq P Q he]

end SkewClassInflation
