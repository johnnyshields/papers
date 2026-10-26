/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseSafeCuts
import SkewJacobiNegative.SingletonLift

/-!
# Recovery of the simultaneous minimum-cut inventory

The factor-recovery clause of `lem:staircase-minimum`: the erased
polynomial recovers actual connected component polynomials and row counts,
with multiplicities but without their order.
-/
namespace SkewJacobiNegative.Staircase
open Gluing
open scoped BigOperators

/-- Actual cut components as a finite inventory; its enumeration has no geometric order. -/
noncomputable def cutComponentInventory {n : ℕ} (P : Profile n) (z : ℕ+) :
    List (Σ k : ℕ, BetaDiagram k) :=
  Finset.univ.toList.map (fun b : CutBlock P z =>
    ⟨blockSize P z b + 1, (cutComponent P z b).toBetaDiagram⟩)

theorem cutComponentInventory_connected {n : ℕ} (P : Profile n) (z : ℕ+)
    (X : Σ k : ℕ, BetaDiagram k) (hX : X ∈ cutComponentInventory P z) :
    X.2.Connected := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hX
  exact cutComponent_connected P z b

theorem cutComponentInventory_product {n : ℕ} (P : Profile n) (z : ℕ+) :
    ((cutComponentInventory P z).map (fun X => X.2.schur)).prod =
      ∏ b : CutBlock P z, (cutComponent P z b).toBetaDiagram.schur := by
  classical
  simp [cutComponentInventory, List.map_map, Finset.prod_toList]

/-- Equality of the erased actual determinants recovers every component
polynomial and size in the same multiplicity-preserving matching. -/
theorem minimum_cut_inventory_matching {n m : ℕ} {P : Profile n} {Q : Profile m}
    (hP : Thick P) (hQ : Thick Q) (z : ℕ+)
    (hminP : ∀ j, z.val ≤ P.g j) (hoccP : ∃ j, P.g j = z.val)
    (hminQ : ∀ j, z.val ≤ Q.g j) (hoccQ : ∃ j, Q.g j = z.val)
    (he : eraseGenerator z P.toBetaDiagram.schur =
      eraseGenerator z Q.toBetaDiagram.schur) :
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k =>
      X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (cutComponentInventory P z : Multiset _) (cutComponentInventory Q z : Multiset _) := by
  apply BetaDiagram.product_component_matching
    (cutComponentInventory P z) (cutComponentInventory Q z)
    (cutComponentInventory_connected P z) (cutComponentInventory_connected Q z)
  rw [cutComponentInventory_product, cutComponentInventory_product,
    ← minimum_cut_product hP z hminP hoccP,
    ← minimum_cut_product hQ z hminQ hoccQ]
  exact he

end SkewJacobiNegative.Staircase
