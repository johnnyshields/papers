/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureProfileCycle
import SkewCornerDescent.Matrix.OriginalClosureCapProducts
import SkewCornerDescent.Matrix.OriginalVerticalUnitJoin
import SkewCornerDescent.Matrix.OriginalWindowCapNormalization

/-!
# Complete scalar products of both actual ordinary closures

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
Both ordinary directions supply their exact selected inventory, unchanged
true cap product, both entire internal source products and the actual central
response.  Vertical cap transport uses its full original source windows and
private join; no copied-cap or internal-product identity is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Either actual ordinary closure has exactly twice the original selected inventory. -/
theorem originalOrdinaryClosure_selected_count {n m : ℕ} (P : Profile n) (Q : Profile m)
    (z : ℤ × ℤ) (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P := by
  rcases hQ with hH | hV
  · exact originalHorizontalClosure_profile_selected_count P Q z hH
  · exact originalVerticalClosure_profile_selected_count P Q z hV

/-- Complete original true caps agree in both actual ordinary directions.
The vertical branch uses both whole source windows and its actual private join. -/
theorem originalOrdinaryClosure_true_cap_product {n m : ℕ} (P : Profile n) (Q : Profile m)
    (z : ℤ × ℤ) (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    c.originalTrueCapProduct Q = c.originalTrueCapProduct P := by
  rcases hQ with hH | hV
  · exact c.originalHorizontalClosure_true_cap_product P Q z hH hB
  · let L := P.xi 0
    let displacement := vH P.cells - eCell
    have htop : Q.xi 0 = 2 * L := originalVerticalClosure_profile_top P Q z hV
    have hsub : 2 * L - L = L := by omega
    have hlower : translate (-z) P.cells =
        Q.cells.filter (fun x => 0 ≤ content x ∧ content x < Q.xi 0 - L) := by
      rw [htop, hsub]
      exact (originalVerticalClosure_lower_window P Q z hV).symm
    have hwindow : Q.cells.filter (fun x => L ≤ content x ∧ content x < Q.xi 0) =
        translate displacement
          (Q.cells.filter fun x => 0 ≤ content x ∧ content x < Q.xi 0 - L) := by
      rw [← hlower, htop]
      dsimp only [L, displacement]
      rw [originalVerticalClosure_upper_window P Q z hV, translate_translate]
      congr 1
    have hprivate := originalVerticalClosure_profile_join_private P Q z hV
    have hcut : ∀ x ∈ diagramInterior Q.cells, content x ≠ L :=
      fun _ hx => privateDiagonal_avoids_interior hprivate.1 hx
    have hcut' : ∀ x ∈ diagramInterior Q.cells, content x ≠ Q.xi 0 - L := by
      rw [htop, hsub]
      exact hcut
    exact (c.originalWindow_true_cap_product Q P L displacement (-z) hwindow hlower
      hcut hcut' hB).2

/-- Both complete internal source lists and the actual central original
response exhaust either ordinary closure, without deduplicating equal values. -/
theorem originalOrdinaryClosure_internal_residue_product {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let center : Fin (originalSelectedCount (hD := hD) Q - 1) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by
        rw [originalOrdinaryClosure_selected_count P Q z hQ]
        omega⟩
    (∏ i, c.originalInternalResidue Q i) =
      (∏ i, c.originalInternalResidue P i)^2 * c.originalInternalResidue Q center := by
  classical
  let : NeZero (originalSelectedCount (hD := hD) P) := ⟨ne_of_gt hB⟩
  have hCQ := originalOrdinaryClosure_selected_count (hD := hD) P Q z hQ
  let center : Fin (originalSelectedCount (hD := hD) Q - 1) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by rw [hCQ]; omega⟩
  let active := c.originalInternalResidue Q center
  obtain ⟨_, hdata⟩ := c.originalClosure_profile_height_residue_cycle P Q z hQ active
  have hr (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
      c.originalInternalResidue Q i = completeResponseCycle (c.originalInternalResidue P) active
        (i.val : ZMod (originalSelectedCount (hD := hD) P)) :=
    (hdata (by rfl) i).2.2
  let e : (Fin (originalSelectedCount (hD := hD) P - 1) ⊕ Fin 1) ⊕
      Fin (originalSelectedCount (hD := hD) P - 1) ≃
        Fin (originalSelectedCount (hD := hD) Q - 1) :=
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
      (finCongr (by omega))
  have hup (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      c.originalInternalResidue Q (e (.inl (.inl i))) = c.originalInternalResidue P i := by
    rw [hr]
    exact completeResponseCycle_prefix (c.originalInternalResidue P) active i
  have hlow (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      c.originalInternalResidue Q (e (.inr i)) = c.originalInternalResidue P i := by
    have hi : (e (.inr i)).val = originalSelectedCount (hD := hD) P + i.val := by
      change originalSelectedCount (hD := hD) P - 1 + 1 + i.val =
        originalSelectedCount (hD := hD) P + i.val
      omega
    rw [hr, hi, Nat.cast_add, ZMod.natCast_self, zero_add]
    exact completeResponseCycle_prefix (c.originalInternalResidue P) active i
  have hmiddle : c.originalInternalResidue Q (e (.inl (.inr 0))) = active := rfl
  rw [Fintype.prod_equiv e.symm (c.originalInternalResidue Q)
    (fun i => c.originalInternalResidue Q (e i))
    (fun i => by rw [Equiv.apply_symm_apply])]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [hup, hlow, Fin.prod_univ_one, hmiddle]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
